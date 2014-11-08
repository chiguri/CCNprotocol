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
Lemma in_dec_request : forall (v : Node) (c : Content_Name) (es : list Event),
  { In (Request v c) es } + { ~ In (Request v c) es }.
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



Lemma in_dec_forward : forall (v : Node) (c : Content_Name) (es : list Event), 
  { In (ForwardInterest v c) es } + { ~ In (ForwardInterest v c) es }.
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



Lemma Content_get_InitCS_or_StoreData :
 forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   Content_get v c es = Some C ->
   InitCS v c \/ In (StoreData v c C) es.
intros; induction H; simpl in H0; auto.
 destruct InitCS_dec with v c.
  auto.
  inversion H0.
 destruct (IHCCNprotocol H0); auto.
  simpl; repeat right; auto.
 destruct (IHCCNprotocol H0); auto.
  simpl; repeat right; auto.
 destruct (IHCCNprotocol H0); auto.
  simpl; repeat right; auto.
 destruct (IHCCNprotocol H0); auto.
  simpl; repeat right; auto.
 destruct Node_eq_dec with v v'.
  destruct Content_Name_eq_dec with c c0.
   subst; cbv in H0.
    inversion H0; subst; simpl; auto.
   destruct (IHCCNprotocol H0); auto.
    simpl; repeat right; auto.
  destruct (IHCCNprotocol H0); auto.
   simpl; repeat right; auto.
 destruct Node_eq_dec with v v'.
  destruct Content_Name_eq_dec with c c0.
   subst; cbv in H0.
    inversion H0; subst; simpl; auto.
   destruct (IHCCNprotocol H0); auto.
    simpl; repeat right; auto.
  destruct (IHCCNprotocol H0); auto.
   simpl; repeat right; auto.
 destruct Node_eq_dec with v v'.
  destruct Content_Name_eq_dec with c c0.
   subst; cbv in H0.
    inversion H0; subst; simpl; auto.
   destruct (IHCCNprotocol H0); auto.
    simpl; repeat right; auto.
  destruct (IHCCNprotocol H0); auto.
   simpl; repeat right; auto.
Qed.
   



Lemma InitCS_Content_get :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   InitCS v c ->
   Content_get v c es <> None.
intros; induction H; simpl; auto.
 destruct InitCS_dec with v c.
  intro H; inversion H.
  elim n; auto.
 destruct Node_eq_dec with v v'; auto.
  destruct Content_Name_eq_dec; auto.
   subst; intro H3; cbv in H3; inversion H3.
 destruct Node_eq_dec with v v'; auto.
  destruct Content_Name_eq_dec; auto.
   subst; intro H3; cbv in H3; inversion H3.
 destruct Node_eq_dec with v v'; auto.
  destruct Content_Name_eq_dec; auto.
   subst; intro H3; cbv in H3; inversion H3.
Qed. 



Lemma ForwardInterest_Not_Content_get :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol (ForwardInterest v c :: es) ps ->
   Content_get v c (ForwardInterest v c :: es) = None.
intros; remember (ForwardInterest v c :: es); revert v c es Heql; induction H; intros; subst; try discriminate.
 inversion Heql; subst; auto.
 eauto.
 eauto.
 eauto.
Qed.




Lemma split_Request_CCNprotocol :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ Request v c :: es2) ps ->
   exists ps' : list Packet,
    CCNprotocol (Request v c :: es2) ps'.
Proof with eauto.
intros; remember (es1 ++ Request v c :: es2); revert v c es1 es2 Heql; induction H; intros; subst...
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H]; inversion H.
 destruct es1.
  simpl in Heql; inversion Heql; subst.
   exists (Broadcast_Interest v0 c0 ++ ps).
    econstructor...
  simpl in Heql; inversion Heql; subst...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H4; inversion H4...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H4; inversion H4...
Qed.



Lemma split_ForwardInterest_CCNprotocol :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardInterest v c :: es2) ps ->
   exists ps' : list Packet,
    CCNprotocol (ForwardInterest v c :: es2) ps'.
Proof with eauto.
intros; remember (es1 ++ ForwardInterest v c :: es2); revert v c es1 es2 Heql; induction H; intros; subst...
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H]; inversion H.
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  subst.
   exists (FIB_Interest v0 c0 ++ ps1 ++ ps2).
    econstructor...
  destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H4; inversion H4...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H4; inversion H4...
Qed.





Lemma Not_Content_get_PIT_or_Interest :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardInterest v c :: es2) ps ->
   FIBreachable v c ->
   exists v' : Node,
    Content_get v' c (es1 ++ ForwardInterest v c :: es2) = None ->
     In (AddPIT v' v c) es1 \/ In (Interest v v' c) ps.
Proof with eauto.
intros v c es1 es2 ps H; remember (es1 ++ ForwardInterest v c :: es2); revert v c es1 es2 Heql; induction H; intros; subst.
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H0]; inversion H0.
 destruct es1; simpl in Heql; inversion Heql.
Admitted.



Lemma PIT_list_not_nil_ForwardInterest :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   PIT_list v c es <> nil ->
   In (ForwardInterest v c) es.
intros v c es ps H; revert v c; induction H; intros; simpl in *; auto;
 destruct (Node_eq_dec v0 v'); auto;
  destruct (Content_Name_eq_dec c0 c); subst; auto.
Qed.


End CCN_Protocol_Lemma.




