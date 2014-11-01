Require Import List.
Import ListNotations.

Require CCNTopology.


(** Sample module for CCN protocol verification : just a half-line topology, and its end-point has all contents. *)
Module CCN_Line <: CCNTopology.CCN_Network.


Definition Node := nat.

Definition Node_eq_dec : forall v1 v2 : Node, {v1 = v2} + {v1 <> v2}.
intros; decide equality.
Qed.


Definition Connected_list (v : Node) : list Node :=
match v with
| O => [ 1 ]
| S v' => [v'; S v]
end.

Definition Connected v1 v2 := In v2 (Connected_list v1).

Lemma Connected_sym : forall v1 v2 : Node, Connected v1 v2 -> Connected v2 v1.
unfold Connected; intros; destruct v1; simpl in *.
 destruct H as [ H | [] ]; subst.
  simpl; auto.
 destruct H as [ H | [ H | [] ] ]; subst.
  unfold Connected_list; destruct v2; simpl; auto.
  unfold Connected_list; destruct v1; simpl; auto.
Qed.


Lemma Connected_dec : forall v1 v2 : Node, {Connected v1 v2} + {~ Connected v1 v2}.
unfold Connected.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.




Definition Content_Name := nat.

Lemma Content_Name_eq_dec : forall c1 c2 : Content_Name, {c1 = c2} + {c1 <> c2}.
decide equality.
Qed.

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

(** Content body : we do not care what it is. *)
Variable Content : Content_Name -> Set.



Definition InitCS (v : Node) (c : Content_Name) := v = 0.

Lemma InitCS_dec : forall (v : Node) (c : Content_Name), {InitCS v c} + {~ InitCS v c}.
intros; unfold InitCS; apply Node_eq_dec.
Qed.


Axiom InitContent_Data : forall (v : Node) (c : Content_Name), InitCS v c -> Content c.



Definition FIB_list (v : Node) (c : Content_Name) : list Node :=
match v with
| O => nil
| S v' => [ v' ]
end.

Definition FIB (v1 : Node) (c : Content_Name) (v2 : Node) := In v2 (FIB_list v1 c).


Lemma FIB_dec : forall (v1 v2 : Node) (c : Content_Name), {FIB v1 c v2} + {~ FIB v1 c v2}.
unfold FIB.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.


Lemma FIB_Connected : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> Connected v1 v2.
unfold FIB; intros.
destruct v1; simpl in H.
 elim H.
 destruct H as [ H | [] ].
  rewrite H; unfold Connected.
   simpl; auto.
Qed.


(** node can reach content server tracing FIB *)
Inductive FIBreachable : Node -> Content_Name -> Prop :=
| cs_flag : forall (v : Node) (c : Content_Name), InitCS v c -> FIBreachable v c
| fib_flag : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> FIBreachable v2 c -> FIBreachable v1 c.


End CCN_Line.


Require CCNVerification.

Module CCN_Line_Verification := CCNVerification.CCN_Protocol_Verification CCN_Line.
Import CCN_Line_Verification.

