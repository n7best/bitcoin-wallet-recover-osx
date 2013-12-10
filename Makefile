wallet-recover: main.cpp
	g++ -L/usr/local/BerkeleyDB.4.8/lib -I/usr/local/BerkeleyDB.4.8/include -I/usr/include/c5 -ggdb -Wall -O2 -o wallet-recover main.cpp -lcryptopp -ldb-4.8
