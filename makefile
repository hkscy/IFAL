all:
	g++ -g -O3 -DNDEBUG -Wall -Wextra IFAL_server.cpp -o IFALserver -lcryptopp -lpthread