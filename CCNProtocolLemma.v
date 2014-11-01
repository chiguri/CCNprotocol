(** About some specifications for CCN_Protocol *)
Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.


(** Lemma for verification *)
Module CCN_Protocol_Lemma (N : CCNTopology.CCN_Network).
(** To use lemmas in this file, we use "Export" rather than "Import".
    Otherwise, Coq cannot unify constructors in CCNProtocol.
    Instead, we should use only "Import CCN_Protocol_Lemma" in verification file;
   otherwise, Coq cannot determine which definitions to use. *)
Export N.

Module Protocol := CCNProtocol.CCN_Protocol N.
Export Protocol.

(*
The following lemma requires "Content is distinctive" (absolutely true),
but in CCNTopology, we do not define such specification.
Fortunately, we do not need "full" distinctiveness, but only "request is in list or not".
So we prove just it.

Lemma event_eq_dec : forall e1 e2 : Event, { e1 = e2 } + { e1 <> e2 }.
intros.
destruct e1; destruct e2; try (right; intro H; inversion H; fail).
 destruct (Node_eq_dec n n0).
  destruct (Content_Name_eq_dec c c0).
   left; subst; auto.
   right; intro H; inversion H; elim n1; auto.
  right; intro H; inversion H; elim n1; auto.
 destruct (Node_eq_dec n n0).
  destruct (Content_Name_eq_dec c c0).
   left; subst; auto.
   right; intro H; inversion H; elim n1; auto.
  right; intro H; inversion H; elim n1; auto.
 destruct (Node_eq_dec n n1).
  destruct (Node_eq_dec n0 n2).
   destruct (Content_Name_eq_dec c c0).
    left; subst; auto.
    right; intro H; inversion H; elim n3; auto.
   right; intro H; inversion H; elim n3; auto.
  right; intro H; inversion H; elim n3; auto.
 destruct (Node_eq_dec n n0).
  destruct (Content_Name_eq_dec c c0).
   left; subst; auto.
   right; intro H; inversion H; elim n1; auto.
  right; intro H; inversion H; elim n1; auto.
 destruct (Node_eq_dec n n0).
  destruct (Content_Name_eq_dec c c0).
   left; subst; auto.
   right; intro H; inversion H; elim n1; auto.
  right; intro H; inversion H; elim n1; auto.
 destruct (Node_eq_dec n n0).
  destruct (Content_Name_eq_dec c c1).
   (* How can we say to say c0 : Content c and c2 : Content c1 are equal or not? *)
Admitted.
*)

(*
This is valid, but not used.

Lemma event_request_eq_dec : forall (v : Node) (c : Content_Name) (e : Event), { Request v c = e } + { Request v c <> e }.
intros; destruct e; try (right; intro H; inversion H; fail).
 destruct (Node_eq_dec v n).
  destruct (Content_Name_eq_dec c c0).
   left; subst; auto.
   right; intro H; inversion H; elim n0; auto.
  right; intro H; inversion H; elim n0; auto.
Qed.
*)

(** decision procedure that a request is in event list or not *)
Lemma in_dec_request : forall (v : Node) (c : Content_Name) (es : list Event), { In (Request v c) es } + { ~ In (Request v c) es }.
intros v c es; induction es.
 right; intro H; inversion H.
 destruct IHes.
  left; right; auto.
  destruct a; try (right; intro H; destruct H as [H | H]; [inversion H | apply n; auto]; fail).
   destruct (Node_eq_dec v n0).
    destruct (Content_Name_eq_dec c c0).
     subst; left; simpl; auto.
     right; intro H; destruct H as [H | H].
      inversion H; elim n1; auto.
      auto.
    right; intro H; destruct H as [H | H].
     inversion H; elim n1; auto.
     auto.
Qed.








Lemma PIT_list_not_nil_ForwardInterest :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   PIT_list v c es <> nil ->
   In (ForwardInterest v c) es.
Admitted.


End CCN_Protocol_Lemma.




