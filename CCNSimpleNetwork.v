Require Import List.
Import ListNotations.

Require CCNTopology.


(** Sample module for CCN protocol verification : only 7 nodes *)
Module CCN_SimpleNetwork <: CCNTopology.CCN_Network.


Inductive Nodes : Set :=
| U | R1 | R2 | R3 | R4 | S1 | S2.
Definition Node := Nodes.


Definition Node_eq_dec : forall v1 v2 : Node, {v1 = v2} + {v1 <> v2}.
intros; decide equality.
Qed.


Definition Connected_list (v : Node) : list Node :=
match v with
| U  => [R1; R3]
| R1 => [U ; R2]
| R2 => [R1; S1; R4]
| R3 => [U ; S2]
| R4 => [R2; S2]
| S1 => [R2]
| S2 => [R3; R4]
end.

Definition Connected v1 v2 := In v2 (Connected_list v1).

Lemma Connected_sym : forall v1 v2 : Node, Connected v1 v2 -> Connected v2 v1.
unfold Connected; intros; destruct v1; destruct v2; simpl in *; intuition; discriminate.
Qed.


Lemma Connected_dec : forall v1 v2 : Node, {Connected v1 v2} + {~ Connected v1 v2}.
unfold Connected.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.



Inductive Content_Names : Set :=
| c1 | c2.
Definition Content_Name := Content_Names.

Lemma Content_Name_eq_dec : forall c1 c2 : Content_Name, {c1 = c2} + {c1 <> c2}.
decide equality.
Qed.

Lemma Content_Name_eq_left : forall c : Content_Name, exists x : c = c, Content_Name_eq_dec c c = left x.
intro.
destruct (Content_Name_eq_dec c c).
exists e; auto.
elim n; auto.
Qed.

Lemma Content_Name_neq_right : forall c1' c2' : Content_Name, c1' <> c2' -> exists x : c1' <> c2', Content_Name_eq_dec c1' c2' = right x.
intros.
destruct (Content_Name_eq_dec c1' c2').
contradiction.
exists n; auto.
Qed.

(** Content body : we do not care what it is. *)
Variables Content1 Content2 : Set.
Definition Content (c : Content_Name) :=
match c with
| c1 => Content1
| c2 => Content2
end.


Definition InitCS (v : Node) (c : Content_Name) :=
match c with
| c1 => v = S1
| c2 => v = S2
end.

Lemma InitCS_dec : forall (v : Node) (c : Content_Name), {InitCS v c} + {~ InitCS v c}.
intros; unfold InitCS.
destruct c; apply Node_eq_dec.
Qed.


Axiom InitContent_Data : forall (v : Node) (c : Content_Name), InitCS v c -> Content c.



Definition FIB_list (v : Node) (c : Content_Name) : list Node :=
match c with
| c1 =>
  match v with
  | R1 => [R2]
  | R2 => [S1]
  | R4 => [R2]
  | _  => []
  end
| c2 =>
  match v with
  | R1 => [R2]
  | R2 => [R4]
  | R3 => [S2]
  | R4 => [S2]
  | _  => []
  end
end.

Definition FIB (v1 : Node) (c : Content_Name) (v2 : Node) := In v2 (FIB_list v1 c).


Lemma FIB_dec : forall (v1 v2 : Node) (c : Content_Name), {FIB v1 c v2} + {~ FIB v1 c v2}.
unfold FIB.
intros.
destruct c1; apply in_dec; apply Node_eq_dec.
Qed.


Lemma FIB_Connected : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> Connected v1 v2.
unfold FIB; unfold Connected; unfold FIB_list; intros.
destruct c; destruct v1; destruct v2; simpl in *; intuition.
Qed.


(** node can reach content server tracing FIB *)
Inductive FIBreachable : Node -> Content_Name -> Prop :=
| cs_flag : forall (v : Node) (c : Content_Name), InitCS v c -> FIBreachable v c
| fib_flag : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> FIBreachable v2 c -> FIBreachable v1 c.


End CCN_SimpleNetwork.


Require CCNVerification.

Module CCN_SimpleNetwork_Verification := CCNVerification.CCN_Protocol_Verification CCN_SimpleNetwork.
Import CCN_SimpleNetwork_Verification.



