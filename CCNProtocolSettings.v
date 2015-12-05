(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Module Type for Resource Control in each Node *)

(* Consistency may be a little difficult to prove *)
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

(** Content_get from event list with resource control *)
Parameter RCContent_get : Node -> forall c : Content_Name, list Event -> option (Content c).

(** InitCS should keep its own resources. *)
Parameter resource_control_keep_InitCS :
  forall (n : Node) (c : Content_Name), InitCS n c -> forall es : list Event, exists C : Content c, RCContent_get n c es = Some C.

(** Nodes other than InitCS does not have contents initially. *)
Parameter resource_control_not_create_content :
  forall (n : Node) (c : Content_Name), ~InitCS n c -> RCContent_get n c [] = None.

(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Parameter resource_control_consistency :
  forall (n : Node) (c : Content_Name) (es es' : list Event), RCContent_get n c es = None -> (forall C : Content c, ~In (StoreData n c C) es') -> RCContent_get n c (es' ++ es) = None.

End CCN_Protocol_Settings.

