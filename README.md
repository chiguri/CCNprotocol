CCNprotocol
===========

[![wercker status](https://app.wercker.com/status/d9413c8560fe41a47f573f8d00bf1a64/s "wercker status")](https://app.wercker.com/project/bykey/d9413c8560fe41a47f573f8d00bf1a64)

CCN (Content-Centric Networking) protocol description and verification in Coq (Tested by Coq 8.6)

## Files

There are 10 main files and 6 examples.

* MiscSpec.v : some lemmas for lists/options used in proofs, but not defined in standard libraries.
* CCNTopology.v : module-type for network topology
* CCNProtocol.v : CCN protocol definition for the topology
* CCNProtocolLemma.v : some lemmas for the protocol
* CCNVerification.v : main specifications for CCN protocol and proofs of them
* CCNProtocolOrthogonality.v : filtering events for specific content
* CCNContentManagement.v : module-type for content management function
* CCNProtocolWithCM.v : CCN protocol definition with content management
* CCNProtocolLemmaWithCM.v : some lemmas for the protocol with content management
* CCNVerificationWithCM.v : main specifications for CCN protocol and proofs
* CCNLine.v : instance of network topology, half-line
* CCNTree.v : instance of network topology, binary-tree
* CCNSimpleNetwork.v : instance of network topology, 7 nodes
* CCNSimpleNetworkFIFO.v : instance of content management function with CCNSimpleNetwork.v (FIFO)
* CCNSimpleNetworkFIFOMixed.v : instance of content management function with CCNSimpleNetwork.v (Mixed with FIFO and No-limit strage)
* CCNSimpleNetworkLRU.v : instance of content management function with CCNSimpleNetwork.v (Least Recently Used strategy)


## Build

Install Coq 8.6.1 (maybe any version of 8.5 can be used) and use "make" command.
Makefile is generated by coq_makefile (with little modification).
For documents, "make html" or "make gallinahtml" can be used.


## License

The BSD 3-Clause License
(See License in the repository)


## Papers

* Sosuke Moriguchi, Takashi Morishima, Mizuki Goto, Kazuko Takahashi, "Formalization of the Behavior of Content-Centric Networking", The 10th International Conference on Future Networks and Communications, Aug., 2015. (See [Release/Tag "FNC15"](https://github.com/chiguri/CCNprotocol/releases/tag/FNC15) and [the paper (Elsevior, open access)](http://www.sciencedirect.com/science/article/pii/S1877050915016786))
* Sosuke Moriguchi, Takashi Morishima, Mizuki Goto, Kazuko Takahashi, "Verification of Content-Centric Networking Using Proof Assistant", IEICE TRANSACTIONS on Communications, Vol.E99-B, No.11, pp.2297-2304, Nov., 2016. (See [Release/Tag "IEICE16"](https://github.com/chiguri/CCNprotocol/releases/tag/IEICE16)).

