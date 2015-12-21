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

(** CMF : Content Management Function, function from event list to content *)
Parameter CMF : Node -> forall c : Content_Name, list Event -> option (Content c).

(** InitCS should keep its own contents. *)
Parameter CMF_keep_InitCS :
  forall (v : Node) (c : Content_Name), InitCS v c -> forall es : list Event, exists C : Content c, CMF v c es = Some C.

(** Nodes other than InitCS does not have contents initially. *)
Parameter CMF_not_create_content :
  forall (v : Node) (c : Content_Name), ~InitCS v c -> CMF v c [] = None.

Definition CMF_reply_consistency (v : Node) (c : Content_Name) (es : list Event) :=
  forall (es1 es2 : list Event),
   es = es1 ++ ReplyData v c :: es2 -> CMF v c es2 <> None.

(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Parameter CMF_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event), CMF_reply_consistency v c (es' ++ es) -> CMF v c es = None -> (forall C : Content c, ~In (StoreData v c C) es') -> CMF v c (es' ++ es) = None.

End CCN_Protocol_Settings.

