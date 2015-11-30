CCNprotocol
===========

CCN protocol description and verification in Coq

There are 6 main files and 3 examples

* MiscSpec.v : some lemmas for lists/options used in proofs, but not defined in standard libraries.
* CCNTopology.v : module-type for network topology
* CCNProtocol.v : CCN protocol definition for the topology
* CCNProtocolLemma.v : some lemmas for the protocol
* CCNVerification.v : main specifications for CCN protocol and proofs of them
* CCNContentEvent.v : filtering events for specific content
* CCNLine.v : instance of network topology, half-line
* CCNTree.v : instance of network topology, binary-tree
* CCNSimpleNetwork.v : instance of network topology, 7 nodes
