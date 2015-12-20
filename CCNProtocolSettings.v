(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Module Type for Resource Management in each Node *)

(* Consistency may be a little bit difficult to prove *)
Require Import List.
Import ListNotations.

Require CCNTopology.
Require CCNProtocol.


Module Type CCN_Protocol_Settings.

Declare Module Topology : CCNTopology.CCN_Network.
Module OldProtocol := CCNProtocol.CCN_Protocol Topology.

Import Topology.
Import OldProtocol.

(* Re-definition of data *)
Definition Packet := OldProtocol.Packet.
Definition Event := OldProtocol.Event.

(** RMF : Resource Management Function, function from event list to content *)
Parameter RMF : Node -> forall c : Content_Name, list Event -> option (Content c).

(** InitCS should keep its own resources. *)
Parameter RMF_keep_InitCS :
  forall (n : Node) (c : Content_Name), InitCS n c -> forall es : list Event, exists C : Content c, RMF n c es = Some C.

(** Nodes other than InitCS does not have contents initially. *)
Parameter RMF_not_create_content :
  forall (n : Node) (c : Content_Name), ~InitCS n c -> RMF n c [] = None.

(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Parameter resource_control_consistency :
  forall (n : Node) (c : Content_Name) (es es' : list Event), RMF n c es = None -> (forall C : Content c, ~In (StoreData n c C) es') -> RMF n c (es' ++ es) = None.

End CCN_Protocol_Settings.

