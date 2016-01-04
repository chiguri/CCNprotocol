(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Module Type for Network Topology
This formalization assumes that network/FIBs are not changed. *)

Require Import List.



Module Type CCN_Network.

(** Nodes of Network *)
Parameter Node : Set.
(** Node can be distinguished *)
Parameter Node_eq_dec : forall v1 v2 : Node, {v1 = v2} + {v1 <> v2}.


(** Connecting Nodes with a given node *) 
Parameter Connected_list : Node -> list Node.
(** Connection between two nodes *)
Definition Connected v1 v2 := In v2 (Connected_list v1).
(** Connections must be symmetric *)
Parameter Connected_sym : forall v1 v2 : Node, Connected v1 v2 -> Connected v2 v1.


(** Identifier of Content *)
Parameter Content_Name : Set.
(** Identifier can be distinguished *)
Parameter Content_Name_eq_dec : forall c1 c2 : Content_Name, {c1 = c2} + {c1 <> c2}.

(** Content body *)
Parameter Content : Content_Name -> Set.



(** Initial Content Server *)
Parameter InitCS : Node -> Content_Name -> Prop.
(** Initial Content Servers are distincted *)
Parameter InitCS_dec : forall (v : Node) (c : Content_Name), {InitCS v c} + {~ InitCS v c}.

(** Initial Content Server can produce Content data *)
Parameter InitContent_Data : forall (v : Node) (c : Content_Name), InitCS v c -> Content c.

(** FIB for node and content names pointing nodes for interest packets forwarding *)
Parameter FIB_list : Node -> Content_Name -> list Node.
(** FIB : interest packet for content name c from v1 is forwarded to v2 *)
Definition FIB (v1 : Node) (c : Content_Name) (v2 : Node) := In v2 (FIB_list v1 c).

(** FIB must point connected nodes *)
Parameter FIB_Connected : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> Connected v1 v2.


(** node can reach content-servers by tracing FIBs *)
(* We are not sure this predicate is in this module or Protocol module.
   If someone wants to discuss the "reachability", they should declare this themselves.
   From this viewpoint, we put the predicate here. *)
Inductive FIBreachable : Node -> Content_Name -> Prop :=
| cs_flag : forall (v : Node) (c : Content_Name), InitCS v c -> FIBreachable v c
| fib_flag : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> FIBreachable v2 c -> FIBreachable v1 c.


End CCN_Network.


