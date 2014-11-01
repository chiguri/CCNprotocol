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
