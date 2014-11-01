Require Import List.

(** FIBs are fixed *)
Module Type CCN_Network.

(** Network Topology *)

(** Nodes of Network *)
Parameter Node : Set.
(** Node can be distincted *)
Parameter Node_eq_dec : forall v1 v2 : Node, {v1 = v2} + {v1 <> v2}.


(** Connected Nodes from one node *) 
Parameter Connected_list : Node -> list Node.
(** Connection between two nodes *)
Definition Connected v1 v2 := In v2 (Connected_list v1).
(** Connections must be symmetric *)
Parameter Connected_sym : forall v1 v2 : Node, Connected v1 v2 -> Connected v2 v1.

(** Connected or not can be distincted *)
Lemma Connected_dec : forall v1 v2 : Node, {Connected v1 v2} + {~ Connected v1 v2}.
unfold Connected.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.
(* Connected_listからするべきかは不明 *)


(** Identifier of Content *)
Parameter Content_Name : Set.
(** Identifier can be distincted *)
Parameter Content_Name_eq_dec : forall c1 c2 : Content_Name, {c1 = c2} + {c1 <> c2}.

Lemma Content_Name_eq_left : forall c : Content_Name, exists x : c = c, Content_Name_eq_dec c c = left x.
intro.
destruct (Content_Name_eq_dec c c).
exists e; auto.
elim n; auto.
Qed.

Lemma Content_Name_neq_right : forall c1 c2 : Content_Name, c1 <> c2 -> exists x : c1 <> c2, Content_Name_eq_dec c1 c2 = right x.
intros.
destruct (Content_Name_eq_dec c1 c2).
elim H; auto.
exists n; auto.
Qed.

(** Content body *)
Parameter Content : Content_Name -> Set.



(** Initial Content Server *)
Parameter InitCS : Node -> Content_Name -> Prop.
(** Initial Content Servers are distincted *)
Parameter InitCS_dec : forall (v : Node) (c : Content_Name), {InitCS v c} + {~ InitCS v c}.

(** Initial Content Server can produce Content data *)
(* 初期のCSならばデータが作れる *)
Parameter InitContent_Data : forall (v : Node) (c : Content_Name), InitCS v c -> Content c.
(* Content cの要素は一致するか否か：だませるから一致しない？（Hashをだます必要があるが） *)

(** FIB network *)
(** FIB for node and content names pointing nodes for interest packets forwarding *)
Parameter FIB_list : Node -> Content_Name -> list Node.
(** FIB : interest packet for content name c from v1 is forwarded to v2 *)
Definition FIB (v1 : Node) (c : Content_Name) (v2 : Node) := In v2 (FIB_list v1 c).

(** FIB pointed or not can be distincted *)
Lemma FIB_dec : forall (v1 v2 : Node) (c : Content_Name), {FIB v1 c v2} + {~ FIB v1 c v2}.
unfold FIB.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.
(* Defined? *)

(* FIBはつながった先を向いている *)
(** FIB must point connected nodes *)
Parameter FIB_Connected : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> Connected v1 v2.


(** node can reach content server tracing FIB *)
Inductive FIBreachable : Node -> Content_Name -> Prop :=
| cs_flag : forall (v : Node) (c : Content_Name), InitCS v c -> FIBreachable v c
| fib_flag : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> FIBreachable v2 c -> FIBreachable v1 c.


End CCN_Network.


