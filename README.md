# tls_mini
Complete TLS+Crypto Implementation in a single Python file!

## Features
* Written purely in Python using minimal features not included in standard Python environment
* Supports most modern TLS 1.2 cipher suites
* Performs basic X.509 certificate verification
* Reasonably optimized but still pretty slow (it's pure Python after all)

## TLS Features
* Supports RSA-signed certificates
* Supports RSA, DHE, ECDHE key exchange
* Suuports AES-CBC and AES-GCM cipher suites with 16 or 32 byte key size

## What's included
* TLS-style structure encoder/decoder
* AES in ECB, CBC, or GCM mode
* SHA1 / SHA256 / SHA384
* HMAC
* Elliptic curve primitives
* RSA encryption and verification
* ASN.1 parser
* X.509 parser skeleton

## Disclaimer
Written for educational purposes. In other words, this library is about as *secure* as plastic water bottle.
