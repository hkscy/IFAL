/*
* IFAL AA server reference implementation.
* 
* This is intended ONLY for evaluating the performance of IFAL.
* Absolutely no guarantees of security or functional correctness are provided. 
* 
* Chris Hicks 2019
*
* Requires Crypto++ library version 6 or greater.
*
* compile using:
* g++ -g3 -ggdb -O0 -DDEBUG -Wall -Wextra IFAL_server.cpp -o IFALserver -lcryptopp -lpthread
* g++ -g -O2 -DNDEBUG -Wall -Wextra IFAL_server.cpp -o IFALserver -lcryptopp -lpthread
*/

#include <iostream>
using std::cout;
using std::cerr;
using std::endl;

#include <sstream>
using std::ostringstream;

#include <string>
using std::string;

#include <stdexcept>
using std::runtime_error;

#include <cstdlib>
using std::exit;

#include <cstdint>

#include <cmath>
using std::pow;

#include <bitset>
using std::bitset;

#include <tuple>
using std::tuple;
using std::make_tuple;
using std::get;

#include "cryptopp/osrng.h"
using CryptoPP::AutoSeededRandomPool;

// ECC crypto
#include "cryptopp/eccrypto.h"
using CryptoPP::ECP;
using CryptoPP::ECDSA;
using CryptoPP::DL_GroupParameters_EC;

// SHA-256 hash
#include "cryptopp/sha.h"
using CryptoPP::SHA256;

// AES block cipher -- we're using this in ECB mode as an 'invertible KDF'
#include "cryptopp/aes.h"
using CryptoPP::AES;

#include "cryptopp/modes.h"
using CryptoPP::ECB_Mode;

#include "cryptopp/queue.h"
using CryptoPP::ByteQueue;

#include "cryptopp/oids.h"
using CryptoPP::OID;

// ASN1 is a namespace, not an object
#include "cryptopp/asn.h"
using namespace CryptoPP::ASN1;

#include "cryptopp/integer.h"
using CryptoPP::Integer;

#include "cryptopp/modarith.h"
using CryptoPP::ModularArithmetic;

// Avoid run-away memory usage for modular multiplication and exponentiation.
#include "cryptopp/nbtheory.h"

#include "cryptopp/cryptlib.h"
using CryptoPP::ByteOrder;

#include "cryptopp/filters.h"
using CryptoPP::StringSource;
using CryptoPP::StringSink;
using CryptoPP::StreamTransformationFilter;
using CryptoPP::HashFilter;

#include "cryptopp/hex.h"
using CryptoPP::HexEncoder;

#include "cryptopp/files.h"
using CryptoPP::FileSink;

#include <cryptopp/hkdf.h>
using CryptoPP::HKDF;

// For benchmarking
#include <chrono>
#include <thread>
using Clock = std::chrono::steady_clock;
using std::chrono::time_point;
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using namespace std::literals::chrono_literals;
using std::this_thread::sleep_for;

/*
* IFAL policy files specify the following:
*     - t_valid - the time (e.g. in seconds) an IFAL certificate is valid.
*     - t_overlap - the time that two consecutive certificates are allowed to overlap.
*     - n_certs - the number of IFAL certificates in an IFAL file.
*     - n_epochs - the number of epochs in an IFAL file.
*/
struct policy {
    uint32_t t_valid;
    uint32_t t_overlap;
    uint32_t n_certs;
    uint32_t n_epochs;
};

/* Toggle options */
bool verbose = false;
bool benchmarking = true;

/* Initialise atomic secure counter */
/* IFAL paper suggests 6-byte fixed size; check size on increment. */
std::atomic<int> sc(0);

/* 
* Convert CryptoPP Integer to std::string
* Input: 
*     Integer cPPInt - CryptoPP Integer
* Returns: 
*     string result - std::string representation of cPPInt
*/
static string cPPIntegerToString(const Integer& cPPInt)
{
    std::ostringstream oss;
    oss << cPPInt;
    string result(oss.str());
    return result;
}

/*
* Convert binary string to CryptoPP Integer
* Input: 
*     string str - binary std::string (~ a byte array)
* Returns: 
*     CryptoPP Integer
*/
static Integer BinTocPPInteger(const string& str)
{   
    Integer result( reinterpret_cast<const uint8_t *>(str.c_str()), str.length() );
    return result;
}

/*
* Pseudonym k encryption function
* Inputs: 
*     uint8_t* kSC - secure counter symmetric key
*     Integer pseudonymK - Integer uid||sc value for pseudonym signature
* Returns:
*     string k2Output - encrypted uid||sc as raw string
*/
static string encryptPseudonymK(const uint8_t* kSC, const Integer& pseudonymK)
{   
    /* Convert fixed-size pseudonymK from string to byte array. */
    int byteCount = 15;
    uint8_t k2SeedArray[byteCount];
    pseudonymK.Encode(k2SeedArray,byteCount);

    /* Make sure byteCount is <= 15 (otherwise the encryption will be > one block) */
    if(byteCount > 15) {
        cerr << "sc||uid overflows one AES block. Retry." << endl;
        exit(1);
    }

    string k2Output;
    try /* Encrypt sc||uid with kSC */
    {
        ECB_Mode< AES >::Encryption k2(kSC, 16);
        /* The StreamTransformationFilter adds padding as required. */ 
        StringSource(k2SeedArray, byteCount, true, new StreamTransformationFilter(k2,
            new StringSink(k2Output)
            ) /* StreamTransformationFilter */     
        ); /* StringSource */
    }
    catch(const CryptoPP::Exception& k2) 
    {
        cerr << k2.what() << endl;
        exit(1);
    }
    return k2Output; 
}

/*
* Pseudonym k decryption function
* Inputs: 
*     uint8_t* kSC - secure counter symmetric key
*     string pseudonymK - Encrypted uid||sc value from IFAL signature
* Returns:
*     string recovered - Decrypted uid||sc as raw string
*/
static string decryptPseudonymK(const uint8_t* kSC, const string& pseudonymK)
{
    string recovered;
    try
    {
        ECB_Mode< AES >::Decryption d;
        d.SetKey(kSC, 16);

        /* The StreamTransformationFilter removes padding as required. */
        StringSource s(pseudonymK, true, 
            new StreamTransformationFilter(d,
                new StringSink(recovered)
            ) /* StreamTransformationFilter */
        ); /* StringSource */
        return recovered;
    }
    catch(const CryptoPP::Exception& e)
    {
        cerr << e.what() << endl;
        exit(1);
    }
}

/*
* AA Pseudonym Certificate Signing function
* Inputs: 
*     string unsignedPseudonym - unsigned pseudonym `certificate'
*     Integer uid - UID of requesting vehicle
*     uint8_t* kSC - secure counter symmetric key
*     ByteQueue aaPrivateKey - Private IFAL signing key of AA
* Returns:
*     string signature -- IFAL Signature on unsignedPseudonym w.r.t aaPrivateKey
*/
static string certSign(const string& unsignedPseudonym, const Integer& uid, const uint8_t* kSC, 
    const ECDSA<ECP, SHA256>::PrivateKey aaPrivateKey)
{
    if(verbose) {
        cout << "Creating new signature on pseudonym: " << endl;
        cout << "\t- pseudonym: " << unsignedPseudonym << endl;
    }

    AutoSeededRandomPool prng;
    sc++;
    if (sc == pow(2,48)-1) /* Re-key the server when sc = sc_max */
    {
        cerr << "AA secure counter full. Re-key server." << endl;
        exit(1);
    }

    /* ----------    Compute K2 KDF. k = k2(kSC,sc||uid)    ---------- */ 
    string kSCstring;
    kSCstring.clear();
    StringSource(kSC, 16, true, new HexEncoder( new StringSink(kSCstring) ));

    if(verbose) {
        cout << "\t- kSC key: " << kSCstring << endl;
        cout << "\t- Secure counter: " << sc << endl;
    }

    /* Compute sc||uid, uid is suggest 8 bytes and sc suggest 6 bytes. */ 
    Integer k2Seed(sc);
    k2Seed <<= 80; /* move sc 80 bits left so we can append uid */
    k2Seed += uid; /* append uid */
    
    /* Convert k2Seed to string for print only */
    string k2SeedStr = cPPIntegerToString(k2Seed);
    
    /* Encrypt k2 seed using k2 */
    string k2Output = encryptPseudonymK(kSC, k2Seed);
    Integer k2Out = BinTocPPInteger(k2Output);

    if(verbose) {
        cout << "\t- sc||uid: " << k2Seed << endl;
        cout << "\t- k2SeedStr: " << k2SeedStr  << "\n";
        cout << "\t- k2: " << k2Out << endl;
    }

    if ( k2Out.IsZero() ) { // zero is not in the subgroup 
        cerr << "k2 == 0. Retry." << endl;
        exit(1);
    }

    /* Compute (x,y) = k.G */

    /* Extract Component values */
    Integer p   = aaPrivateKey.GetGroupParameters().GetCurve().GetField().GetModulus();
    Integer a   = aaPrivateKey.GetGroupParameters().GetCurve().GetA();
    Integer b   = aaPrivateKey.GetGroupParameters().GetCurve().GetB();
    Integer Gx  = aaPrivateKey.GetGroupParameters().GetSubgroupGenerator().x;
    Integer Gy  = aaPrivateKey.GetGroupParameters().GetSubgroupGenerator().y;
    Integer n   = aaPrivateKey.GetGroupParameters().GetSubgroupOrder();
    Integer kAA = aaPrivateKey.GetPrivateExponent();

    /* Construct Point element(s); */
    ECP curve(p,a,b);
    ECP::Point G(Gx,Gy);

    /* Compute k = k2 x G */
    ECP::Point k = curve.ECP::ScalarMultiply( G, k2Out ); 

    /* Compute r = k_x mod n. */
    Integer r = k.x % n;

    if(verbose) {
        cout << "\t- aaPrivateKey: " << std::hex << kAA << endl;
        cout << "\t- k.x: " << k.x << endl;
        cout << "\t- r: " << r << endl;
    }
    
    if ( r.IsZero() ) {
        cerr << "r == 0. Retry." << endl;
        exit(1);
    }

    /* Compute HASH(unsigned pseudonym) */
    SHA256 hash;
    uint8_t digest[SHA256::DIGESTSIZE];
    SHA256().CalculateDigest(digest, reinterpret_cast<const uint8_t *>(unsignedPseudonym.c_str()), unsignedPseudonym.length());

    /* Compute s = k^-1(h + kAA*r) mod n */
    ModularArithmetic arith(n);
    Integer kInv( arith.MultiplicativeInverse(k2Out) );
    Integer s = Integer(a_times_b_mod_c(kInv,( Integer(digest, SHA256::DIGESTSIZE) + a_times_b_mod_c(kAA,r,n) ),n));
    
    if(verbose) {
        cout << "\t- h: " << cPPIntegerToString(Integer(digest, SHA256::DIGESTSIZE)) << endl;
        cout << "\t- k^-1: " << kInv << endl; // Verify kInv: cout << (kInv*k2Out % n) << endl;
        cout << "\t- s: " << s << endl;
    }

    Integer rs = (r<<256)+s;
    uint8_t rsArray[rs.ByteCount()];
    rs.Encode(rsArray, rs.ByteCount());
    string signature( reinterpret_cast<const char *>(rsArray), rs.ByteCount() );

    return signature;
}

/*
* AA Certificate File Creation algorithm
* Inputs: 
*     policy cert_policy - IFAL policy file (t_valid, t_overlap, n_certs, n_epochs)
*     Integer uid - UID of requesting vehicle
*     uint8_t* kSC - secure counter symmetric key
*     ByteQueue privateKey - Private IFAL signing key of AA
* Returns:
*     bool result -- outcome of file writing {0,1}
*/
bool generateCertificateFile(const policy cert_policy, const Integer& uid, const uint8_t* kSC, 
    const ECDSA<ECP, SHA256>::PrivateKey aaPrivateKey,
    const ECDSA<ECP, SHA256>::PublicKey aaPublicKey) {

    AutoSeededRandomPool prng;

    /* Derived policy parameters */
    uint32_t n_ce = cert_policy.n_certs / cert_policy.n_epochs;    /* Number of certificates per epoch */
    uint32_t t_step = cert_policy.t_valid - cert_policy.t_overlap; /* Time difference between consecutive certificates */

    if (verbose) {
        cout << "n_ce: " << n_ce << "\nt_step: " << t_step << endl;
    }

    /* Extract modulus value and public key from private key */
    Integer p   = aaPrivateKey.GetGroupParameters().GetCurve().GetField().GetModulus();
    Integer a   = aaPrivateKey.GetGroupParameters().GetCurve().GetA();
    Integer b   = aaPrivateKey.GetGroupParameters().GetCurve().GetB();
    Integer n = aaPrivateKey.GetGroupParameters().GetSubgroupOrder();
    
    const ECP::Point& q = aaPublicKey.GetPublicElement();
    const Integer& Qx = q.x;
    const Integer& Qy = q.y;

    /* Construct curve and public key point; */
    ECP curve(p,a,b);
    ECP::Point Q(Qx,Qy);

    /* Salt if desired */
    string salt = "";

    /* Write header containing policy to file */

    /* Ganerate all the certificates in the file */
    uint32_t i_epoch = 0;
    for (i_epoch = 0; i_epoch < 1; i_epoch++)
    {
        /* Generate activation code per epoch */
        uint8_t k_j[16];
        prng.GenerateBlock(k_j, 16);

        /* For each certificate in the epoch */
        uint32_t i_cert = 0;
        for (i_cert = 0; i_cert < n_ce; i_cert++)
        {
            /* Compute K1(k_j, i_cert) */
            uint8_t kdfK1[SHA256::DIGESTSIZE];
            HKDF<SHA256> hkdf;
            hkdf.DeriveKey( kdfK1, sizeof(kdfK1), static_cast<const uint8_t *>(k_j), sizeof(k_j), 
                                                  reinterpret_cast<const uint8_t *>(salt.c_str()), salt.length(), 
                                                  reinterpret_cast<const uint8_t *>(&i_cert), sizeof(uint32_t) );
            Integer k_1(kdfK1, 16); /* Reduce output of SHA256 to 128 -- this greatly improves performance */
            /* Reduce k_1 output modulo subgroup size */
            k_1%=n;

            /* Derive pseudonym public key: P_i = P_TE x k_1 */
            ECP::Point P_i = curve.ECP::ScalarMultiply( Q, k_1 );

            /* Sign pseudonym public key */
            uint8_t P_i_encoded[curve.ECP::EncodedPointSize()];
            curve.ECP::EncodePoint(P_i_encoded, P_i, false);
            string P_i_string(reinterpret_cast<const char *>(P_i_encoded), sizeof(P_i_encoded));

            /* Compute pseudonym certificate on P_i w.r.t AA private key */
            string pCert = certSign(P_i_string, uid, kSC, aaPrivateKey);
        }

    }
    return true;
}

int main( int, char** ) {

    AutoSeededRandomPool prng;
    ByteQueue aaPrivateKey, aaPublicKey;

    /* ------               Generate Parameters             ------ */
    /* Parameters are:                                             */
    /*  - (aaPublicKey, aaPrivateKey) public-private key pair      */
    /*  - secureCounter for pseudonym certificate issuance         */
    /*  - kSC symmetric encryption key for secureCounter           */
    /*                                                             */
    /* Note: Using secp256r1 == NIST P-256                         */

    if(verbose)
        cout << "Generating IFAL AA parameters: " << endl;

    /* Generate private key */
    ECDSA<ECP, SHA256>::PrivateKey privKey;
    privKey.Initialize( prng, secp256r1() );
    privKey.Save( aaPrivateKey );

    /* Create public key */
    ECDSA<ECP, SHA256>::PublicKey pubKey;
    privKey.MakePublicKey( pubKey );
    pubKey.Save( aaPublicKey );

    /* Generate a random secure counter symmetric key (128-bits) */
    uint8_t kSC[16];
    prng.GenerateBlock(kSC, 16);

    if(verbose) {
        cout << "\t- Secure counter symmetric key: ";
        StringSource(kSC, 16, true, new HexEncoder(new FileSink(std::cout)));
        cout << "\t- Secure counter: " << sc << "\n" << endl;
    }

    uint32_t t_valid = 600;                 /* 10 minutes per certificate */
    uint32_t t_overlap = 120;               /* 2 minutes overlap */
    uint32_t n_certs = 311040000/t_valid;   /* 10 years worth of certificates */
    uint32_t n_epochs = 40;                 /* 90 days per epoch */

    /* Initialise policy */
    policy cert_policy{t_valid, t_overlap, n_certs, n_epochs};

    /* Placeholder uid */
    Integer uid("115789795854948412110701");

    time_point<Clock> start = Clock::now();

    /* GenerateCertificateFile */
    generateCertificateFile(cert_policy, uid, kSC, privKey, pubKey);
    
    if(benchmarking) {
        time_point<Clock> end = Clock::now();
        milliseconds diff = duration_cast<milliseconds>(end - start);
        cout << "Creating certificate file took: " << diff.count() << "ms" << endl;
    }

    string pseudonm = "Richard";
    
    
    string signature = certSign(pseudonm, uid, kSC, privKey);
    /* Load public key (in ByteQueue, X509 format) */
    ECDSA<ECP, SHA256>::Verifier verifier( aaPublicKey );
    bool result = verifier.VerifyMessage( (const uint8_t*)pseudonm.data(),
                                                          pseudonm.size(),
                                                  (const uint8_t*)signature.data(),
                                                                  signature.size() );
    if(result)
        cout << "\nVerified signature on message" << endl;
    else
        cerr << "Failed to verify signature on message" << endl;
    
    return 0;
}
