(* misc. specifications *)
Lemma option_Some_None :
  forall (A : Type) (x : option A), (forall a : A, x <> Some a) -> x = None.
intros.
destruct x.
destruct (H a); auto.
auto.
Qed.

Lemma option_None_Some :
  forall (A : Type) (x : option A), x <> None -> exists y : A, x = Some y.
intros.
destruct x.
exists a; auto.
elim H; auto.
Qed.


Section Sum_eq.

Context {A : Type}.
Context (eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}).

Lemma sum_eq_left : forall (a : A), exists x : a = a, eq_dec a a = left x.
intro.
destruct (eq_dec a a).
exists e; auto.
elim n; auto.
Qed.

Lemma sum_neq_right : forall a1 a2 : A, a1 <> a2 -> exists x : a1 <> a2, eq_dec a1 a2 = right x.
intros.
destruct (eq_dec a1 a2).
elim H; auto.
exists n; auto.
Qed.

End Sum_eq.



Section Exists.

Context {A : Type}.

Require Import List.

Lemma exists_longer : forall (P : list A -> Prop) (l : list A),
  (exists l' : list A, P (l' ++ l)) -> exists l' : list A, P l'.
intros.
 destruct H.
  exists (x ++ l); auto.
Qed.


Lemma exists_app_assoc_l : forall (P : list A -> Prop) (l1 l2 : list A) (f : list A -> list A),
 (exists l : list A, P ((f l ++ l1) ++ l2))
 -> exists l : list A, P (f l ++ l1 ++ l2).
intros.
 destruct H.
  exists x; rewrite app_assoc; auto.
Qed.



Lemma exists_app_assoc_r : forall (P : list A -> Prop) (l1 l2 : list A) (f : list A -> list A),
 (exists l : list A, P (f l ++ l1 ++ l2))
 -> exists l : list A, P ((f l ++ l1) ++ l2).
intros.
 destruct H.
  exists x; rewrite <- app_assoc; auto.
Qed.



End Exists.



Section List.

Require Import List.
Lemma in_change : forall (A : Type) (a1 a2 : A) (as1 as2 : list A),
 In a1 (as1 ++ a2 :: as2) -> a1 = a2 \/ In a1 (as1 ++ as2).
intros.
 apply in_app_or in H.
  simpl in H; intuition.
Qed.

End List.