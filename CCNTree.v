Require Import List.
Import ListNotations.

Require CCNTopology.


(** Sample module for CCN protocol verification : a tree topology, and its root has all contents. *)
Module CCN_Tree <: CCNTopology.CCN_Network.


Definition Node := nat.

Definition Node_eq_dec : forall v1 v2 : Node, {v1 = v2} + {v1 <> v2}.
intros; decide equality.
Qed.


Require Import Div2.
Require Import Even.
Require Import Plus.

Definition Connected_list (v : Node) : list Node :=
match v with
| O => [ 1 ; 2 ]
| S v' => [ S (double v) ; (double (S v)); div2 v']
end.

Definition Connected v1 v2 := In v2 (Connected_list v1).

Lemma div2_double : forall n, div2 (double n) = n.
induction n; simpl.
 auto.
 rewrite plus_comm.
  simpl.
   unfold double in IHn; rewrite IHn.
    auto.
Qed.


Lemma Connected_sym : forall v1 v2 : Node, Connected v1 v2 -> Connected v2 v1.
unfold Connected; intros; destruct v1.
 destruct H as [ H | [ H | [] ] ]; subst.
  simpl; auto.
  simpl; auto.
 destruct H as [ H | [ H | [ H | [] ] ] ]; subst.
  unfold Connected_list.
   rewrite div2_double; simpl; auto.
  unfold Connected_list.
   simpl.
    right; right; left.
     rewrite <- plus_n_Sm.
     assert (v1 + S v1 = S (2 * v1)).
      simpl.
       rewrite plus_n_Sm.
        f_equal; apply plus_n_O.
      f_equal.
       rewrite H.
        apply div2_double_plus_one.
  unfold Connected_list.
   destruct even_or_odd with v1.
    rewrite <- even_double with v1.
     destruct v1.
      simpl; auto.
      destruct v1.
       simpl; auto.
       simpl div2.
        simpl; auto.
     auto.
    rewrite double_S.
     rewrite <- odd_double with v1.
      repeat (destruct v1; simpl; auto).
      auto.
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
| S v' => [ div2 v' ]
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
  rewrite <- H; unfold Connected.
   unfold Connected_list.
    simpl; auto.
Qed.


(** node can reach content server tracing FIB *)
Inductive FIBreachable : Node -> Content_Name -> Prop :=
| cs_flag : forall (v : Node) (c : Content_Name), InitCS v c -> FIBreachable v c
| fib_flag : forall (v1 v2 : Node) (c : Content_Name), FIB v1 c v2 -> FIBreachable v2 c -> FIBreachable v1 c.


End CCN_Tree.


Require CCNVerification.

Module CCN_Line_Verification := CCNVerification.CCN_Protocol_Verification CCN_Tree.
Import CCN_Line_Verification.

