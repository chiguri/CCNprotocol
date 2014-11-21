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
Fortunately, we do not need "full" distinctiveness, but only "request/forward is in list or not".
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
   subst; intro H4; cbv in H4; inversion H4.
 destruct Node_eq_dec with v v'; auto.
  destruct Content_Name_eq_dec; auto.
   subst; intro H5; cbv in H5; inversion H5.
 destruct Node_eq_dec with v v'; auto.
  destruct Content_Name_eq_dec; auto.
   subst; intro H5; cbv in H5; inversion H5.
Qed.




Lemma StoreData_Content_get :
 forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   In (StoreData v c C) es ->
   Content_get v c es <> None.
intros; induction H; simpl in H0; auto.
 destruct H0.
  discriminate.
  eauto.
 destruct H0 as [ ? | [ ? | ? ] ].
  discriminate.
  discriminate.
  eauto.
 destruct H0.
  discriminate.
  eauto.
 destruct H0.
  discriminate.
  eauto.
 destruct H0.
  simpl.
   destruct Node_eq_dec with v v'.
    destruct Content_Name_eq_dec with c c0.
     subst; cbv.
      intro; discriminate.
     inversion H0; elim n; auto.
    inversion H0; elim n; auto.
  simpl; intro H5; unfold not in IHCCNprotocol.
   destruct Node_eq_dec with v v';
       destruct Content_Name_eq_dec with c c0;
        eauto.
    subst; cbv in H5; discriminate.
 destruct H0 as [ H0 | [ H0 | H0 ] ].
  simpl.
   destruct Node_eq_dec with v v'.
    destruct Content_Name_eq_dec with c c0.
     subst; cbv.
      intro; discriminate.
     inversion H0; elim n; auto.
    inversion H0; elim n; auto.
  discriminate.
  simpl; intro H5; unfold not in IHCCNprotocol.
   destruct Node_eq_dec with v v';
       destruct Content_Name_eq_dec with c c0;
        eauto.
    subst; cbv in H5; discriminate.
 destruct H0 as [ H0 | [ H0 | H0 ] ].
  simpl.
   destruct Node_eq_dec with v v'.
    destruct Content_Name_eq_dec with c c0.
     subst; cbv.
      intro; discriminate.
     inversion H0; elim n; auto.
    inversion H0; elim n; auto.
  discriminate.
  simpl; intro H5; unfold not in IHCCNprotocol.
   destruct Node_eq_dec with v v';
       destruct Content_Name_eq_dec with c c0;
        eauto.
    subst; cbv in H5; discriminate.
Qed.




Lemma ForwardInterest_Not_Content_get :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol (ForwardInterest v c :: es) ps ->
   Content_get v c (ForwardInterest v c :: es) = None.
intros; remember (ForwardInterest v c :: es); revert v c es Heql; induction H; intros; subst; try discriminate; eauto.
 inversion Heql; subst; auto.
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
  subst; destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H5; inversion H5...
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
  subst; destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql.
  subst; destruct es1; simpl in H5; inversion H5...
Qed.




Lemma split_StoreData_CCNprotocol :
 forall (v : Node) (c : Content_Name) (C : Content c) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ StoreData v c C :: es2) ps ->
   exists ps' : list Packet,
    CCNprotocol (StoreData v c C :: es2) ps'.
Proof with eauto.
intros; remember (es1 ++ StoreData v c C :: es2); revert v c C es1 es2 Heql; induction H; intros; subst...
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H]; inversion H.
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
  exists (ps1 ++ ps2).
   subst; eapply ccn_store_data...
 destruct es1; simpl in Heql; inversion Heql...
  exists (PIT_Data v0 c C es ++ ps1 ++ ps2).
   subst; eapply ccn_forward_data...
  destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql...
  exists (PIT_Data v0 c C es ++ ps1 ++ ps2).
   subst; eapply ccn_store_forward...
  destruct es1; simpl in H5; inversion H5...
Qed.




Lemma Content_get_app_In_Store_Data :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event),
  Content_get v c es2 = None ->
   Content_get v c (es1 ++ es2) <> None ->
   exists (C : Content c),
    In (StoreData v c C) es1.
Proof with eauto.
intros; induction es1; intros; simpl in *...
 elim H0...
 destruct a; try (destruct IHes1; eauto; fail).
  destruct Node_eq_dec with v n.
   destruct Content_Name_eq_dec with c c0.
    subst; cbv in H0.
     exists c1; auto.
    destruct IHes1...
   destruct IHes1...
Qed.





Lemma Connected_In_Broadcast_Interest :
 forall (v1 v2 : Node) (c : Content_Name),
  Connected v1 v2 ->
   In (Interest v1 v2 c) (Broadcast_Interest v1 c).
intros v1 v2 c; unfold Connected; unfold Broadcast_Interest; generalize (Connected_list v1);
    revert v1 v2 c; induction l; intros; simpl in H.
 elim H.
 destruct H; subst; simpl; eauto.
Qed.



Lemma FIB_In_FIB_Interest :
 forall (v1 v2 : Node) (c : Content_Name),
  FIB v1 c v2 ->
   In (Interest v1 v2 c) (FIB_Interest v1 c).
intros v1 v2 c; unfold FIB; unfold FIB_Interest; generalize (FIB_list v1 c);
    revert v1 v2 c; induction l; intros; simpl in H.
 elim H.
 destruct H; subst; simpl; eauto.
Qed.



Lemma PIT_In_PIT_Data :
 forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es : list Event),
  In v2 (PIT_list v1 c es) ->
   In (Data v1 v2 c C) (PIT_Data v1 c C es).
intros v1 v2 c C es; unfold PIT_Data; generalize (PIT_list v1 c es);
    revert v1 v2 c C es; induction l; intros; simpl in H.
 contradiction.
 destruct H; subst; simpl; eauto.
Qed. 




Lemma In_PIT_list_In_AddPIT :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   Content_get v2 c es = None ->
   In v1 (PIT_list v2 c es) ->
   In (AddPIT v2 v1 c) es.
Proof with eauto.
intros; induction H; simpl in *...
 destruct Node_eq_dec with v2 v'...
  destruct Content_Name_eq_dec with c c0...
   simpl in H1; destruct H1; subst...
 destruct Node_eq_dec with v2 v'...
  destruct Content_Name_eq_dec with c c0...
   simpl in H1; destruct H1; subst...
 destruct Node_eq_dec with v2 v'...
  destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
 destruct Node_eq_dec with v2 v'...
  destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
 destruct Node_eq_dec with v2 v'...
  destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
Qed.



Lemma In_AddPIT_In_PIT_list :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   Content_get v2 c es = None ->
   In (AddPIT v2 v1 c) es ->
   In v1 (PIT_list v2 c es).
Proof with eauto.
intros; induction H; simpl in *...
 destruct H1.
  discriminate.
  eauto.
 destruct H1 as [ H1 | [ H1 | H1 ] ].
  discriminate.
  inversion H1; subst.
   destruct Node_eq_dec with v2 v2.
    destruct Content_Name_eq_dec with c c.
     simpl...
     elim n...
    elim n...
  assert (H6 := IHCCNprotocol H0 H1).
   destruct Node_eq_dec with v2 v'; destruct Content_Name_eq_dec with c c0; simpl...
 destruct H1 as [ H1 | H1 ].
  inversion H1; subst.
   destruct Node_eq_dec with v2 v2.
    destruct Content_Name_eq_dec with c c.
     simpl...
     elim n...
    elim n...
  assert (H7 := IHCCNprotocol H0 H1).
   destruct Node_eq_dec with v2 v'; destruct Content_Name_eq_dec with c c0; simpl...
 destruct H1.
  discriminate.
  eauto.
 destruct H1.
  discriminate.
  destruct Node_eq_dec with v2 v'...
   destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
 destruct H1 as [ H1 | [ H1 | H1 ] ].
  discriminate.
  discriminate.
  destruct Node_eq_dec with v2 v'...
   destruct Content_Name_eq_dec with c c0...
    subst; cbv in H0; discriminate.
 destruct H1 as [ H1 | [ H1 | H1 ] ].
  discriminate.
  discriminate.
  destruct Node_eq_dec with v2 v'...
   destruct Content_Name_eq_dec with c c0...
    subst; cbv in H0; discriminate.
Qed.



Lemma Not_Content_get_PIT_or_Interest :
 forall (v1 v2 : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardInterest v1 c :: es2) ps ->
   FIB v1 c v2 ->
   FIBreachable v2 c ->
   Content_get v2 c (es1 ++ ForwardInterest v1 c :: es2) = None ->
    In (AddPIT v2 v1 c) (es1 ++ ForwardInterest v1 c :: es2) \/ In (Interest v1 v2 c) ps.
Proof with eauto.
intros v1 v2 c es1 es2 ps H; remember (es1 ++ ForwardInterest v1 c :: es2);
   revert es1 es2 Heql; induction H; intros; subst; simpl in *.
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H2]; inversion H2.
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   right; apply in_or_app; auto.
 destruct es1; simpl in Heql; inversion Heql; simpl.
  right; apply in_or_app; left.
   apply FIB_In_FIB_Interest; auto.
  subst; destruct es1; inversion Heql; subst.
   simpl; destruct IHCCNprotocol with es1 es2...
    apply in_change in H3; destruct H3...
     inversion H3; subst...
     right; apply in_or_app...
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   apply in_change in H4; destruct H4...
    inversion H4; subst; auto.
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H2; destruct H2...
   inversion H2; subst.
    destruct H4.
     elim (InitCS_Content_get _ _ _ _ H H4)...
     unfold FIB in H4; rewrite H1 in H4; simpl in H4; elim H4.
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H2; destruct H2...
   inversion H2; subst.
    left; eapply In_PIT_list_In_AddPIT...
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   apply in_change in H1; destruct H1...
    inversion H1; subst.
     rewrite H4 in H0; discriminate.
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct IHCCNprotocol with es1 es2...
   destruct Node_eq_dec with v2 v'...
    destruct Content_Name_eq_dec with c c0...
     subst; cbv in H5; discriminate.
   apply in_change in H3; destruct H3...
    inversion H3.
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct es1; simpl in Heql; inversion Heql; subst.
   destruct IHCCNprotocol with es1 es2...
    destruct Node_eq_dec with v2 v'...
     destruct Content_Name_eq_dec with c c0...
     subst; cbv in H6; discriminate.
   apply in_change in H3; destruct H3.
    inversion H3.
    right.
     apply in_or_app; auto.
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct es1; simpl in Heql; inversion Heql; subst.
   destruct IHCCNprotocol with es1 es2...
    destruct Node_eq_dec with v2 v'...
     destruct Content_Name_eq_dec with c c0...
     subst; cbv in H6; discriminate.
   apply in_change in H3; destruct H3.
    inversion H3.
    right.
     apply in_or_app; auto.
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H1; destruct H1...
   inversion H1.
Qed.



Lemma Content_get_Data_or_Interest :
 forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardInterest v1 c :: es2) ps ->
   FIB v1 c v2 ->
   FIBreachable v2 c ->
   Content_get v2 c (es1 ++ ForwardInterest v1 c :: es2) = Some C ->
   Content_get v1 c (es1 ++ ForwardInterest v1 c :: es2) = None ->
    In (Data v2 v1 c C) ps \/ In (Interest v1 v2 c) ps.
Proof with eauto.
intros v1 v2 c C es1 es2 ps H; remember (es1 ++ ForwardInterest v1 c :: es2);
   revert es1 es2 Heql; induction H; intros; subst; simpl in *.
 symmetry in Heql.
  destruct (app_eq_nil _ _ Heql) as [_ H3]; inversion H3.
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   left; apply in_or_app...
   right; apply in_or_app...
 destruct es1; simpl in Heql; inversion Heql; simpl.
  right; apply in_or_app; left.
   apply FIB_In_FIB_Interest; auto.
  subst; destruct es1; inversion Heql; subst.
   simpl; destruct IHCCNprotocol with es1 es2...
    apply in_change in H3; destruct H3...
     discriminate.
     left; apply in_or_app...
    apply in_change in H3; destruct H3...
     inversion H3; subst...
      rewrite H6 in H0; discriminate.
     right; apply in_or_app...
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   apply in_change in H4; destruct H4...
    discriminate.
   apply in_change in H4; destruct H4...
    inversion H4; subst...
     rewrite H7 in H0; discriminate.
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H2; destruct H2...
   discriminate.
  apply in_change in H2; destruct H2...
   inversion H2; subst.
    rewrite H5 in H0; discriminate.
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H2; destruct H2...
   discriminate.
  apply in_change in H2; destruct H2...
   inversion H2; subst.
    rewrite H5 in H0; discriminate.
 destruct es1; simpl in Heql; inversion Heql; subst; simpl.
  destruct IHCCNprotocol with es1 es2...
   apply in_change in H1; destruct H1...
    discriminate.
   apply in_change in H1; destruct H1...
    inversion H1; subst.
     rewrite H4 in H0; inversion H0...
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct Node_eq_dec with v2 v'.
   destruct Content_Name_eq_dec with c c0.
    subst; cbv in H6; inversion H6; subst.
     destruct (Not_Content_get_PIT_or_Interest _ v' _ _ _ _ H)...
      assert (H8 := In_AddPIT_In_PIT_list _ _ _ _ _ H H0 H3).
       destruct (in_split _ _ H8) as [ x1 [ x2 H9 ] ].
        rewrite H2 in H9; apply app_cons_not_nil in H9; contradiction.
      apply in_change in H3; destruct H3.
       discriminate.
       auto.
    destruct Node_eq_dec with v1 v'.
     subst; rewrite H7 in H6; discriminate.
     destruct IHCCNprotocol with es1 es2...
      apply in_change in H3; destruct H3...
       inversion H3; subst.
        rewrite H6 in H0; discriminate.
      apply in_change in H3; destruct H3...
       inversion H3.
   destruct Content_Name_eq_dec with c c0.
    destruct Node_eq_dec with v1 v'.
     subst; cbv in H7; discriminate.
     destruct IHCCNprotocol with es1 es2...
      apply in_change in H3; destruct H3...
       inversion H3; subst.
        elim n0...
      apply in_change in H3; destruct H3...
       inversion H3.
    destruct IHCCNprotocol with es1 es2...
     destruct Node_eq_dec with v1 v'; auto.
     apply in_change in H3; destruct H3...
      inversion H3; subst.
       elim n0...
     apply in_change in H3; destruct H3...
      discriminate.
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct es1; simpl in Heql; inversion Heql; subst.
   destruct Node_eq_dec with v2 v'.
    destruct Content_Name_eq_dec with c c0.
     subst; cbv in H6.
      destruct (Not_Content_get_PIT_or_Interest _ v' _ _ _ _ H)...
       left; apply in_or_app; left.
        assert (H8 := In_AddPIT_In_PIT_list _ _ _ _ _ H H0 H3).
         inversion H6; subst.
          apply PIT_In_PIT_Data...
       right; apply in_or_app; right.
        apply in_change in H3; destruct H3...
         discriminate.
     destruct IHCCNprotocol with es1 es2...
      destruct Node_eq_dec with v1 v'...
      apply in_change in H3; destruct H3.
       inversion H3; subst.
        elim n...
       left; apply in_or_app...
      apply in_change in H3; destruct H3.
       inversion H3.
       right; apply in_or_app...
    destruct Node_eq_dec with v1 v'.
     destruct Content_Name_eq_dec with c c0.
      subst; cbv in H7; discriminate.
      destruct IHCCNprotocol with es1 es2...
       apply in_change in H3; destruct H3.
        inversion H3; subst.
         elim n0...
        left; apply in_or_app...
       apply in_change in H3; destruct H3.
        inversion H3.
        right; apply in_or_app...
     destruct IHCCNprotocol with es1 es2...
      apply in_change in H3; destruct H3.
       inversion H3; subst.
        elim n0...
       left; apply in_or_app...
      apply in_change in H3; destruct H3.
       discriminate.
       right; apply in_or_app...
 destruct es1; simpl in Heql; inversion Heql; subst.
  destruct es1; simpl in Heql; inversion Heql; subst.
   destruct Node_eq_dec with v2 v'.
    destruct Content_Name_eq_dec with c c0.
     subst; cbv in H6.
      destruct (Not_Content_get_PIT_or_Interest _ v' _ _ _ _ H)...
       left; apply in_or_app; left.
        assert (H8 := In_AddPIT_In_PIT_list _ _ _ _ _ H H0 H3).
         inversion H6; subst.
          apply PIT_In_PIT_Data...
       right; apply in_or_app; right.
        apply in_change in H3; destruct H3...
         discriminate.
     destruct IHCCNprotocol with es1 es2...
      destruct Node_eq_dec with v1 v'...
      apply in_change in H3; destruct H3.
       inversion H3; subst.
        elim n...
       left; apply in_or_app...
      apply in_change in H3; destruct H3.
       discriminate.
       right; apply in_or_app...
    destruct Node_eq_dec with v1 v'.
     destruct Content_Name_eq_dec with c c0.
      subst; cbv in H7; discriminate.
      destruct IHCCNprotocol with es1 es2...
       apply in_change in H3; destruct H3.
        inversion H3; subst.
         elim n0...
        left; apply in_or_app...
       apply in_change in H3; destruct H3.
        inversion H3.
        right; apply in_or_app...
     destruct IHCCNprotocol with es1 es2...
      apply in_change in H3; destruct H3.
       inversion H3; subst.
        elim n0...
       left; apply in_or_app...
      apply in_change in H3; destruct H3.
       discriminate.
       right; apply in_or_app...
 destruct IHCCNprotocol with es1 es2...
  apply in_change in H1; destruct H1...
   inversion H1; subst.
    elim H0...
  apply in_change in H1; destruct H1...
   discriminate.
Qed.




Lemma ForwardInterest_PIT_list_not_nil :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   Content_get v c es = None ->
   In (ForwardInterest v c) es ->
   PIT_list v c es <> [].
Proof with eauto.
intros; induction H; simpl in *...
 destruct H1...
  discriminate.
 destruct H1 as [H1 | [ H1 | H1 ] ].
  intro H6; destruct Node_eq_dec with v v'.
   destruct Content_Name_eq_dec with c c0.
    discriminate.
    inversion H1. symmetry in H9...
   inversion H1. symmetry in H9...
  discriminate.
  destruct Node_eq_dec with v v';
      destruct Content_Name_eq_dec with c c0...
   intro; discriminate.
 destruct H1.
  discriminate.
  destruct Node_eq_dec with v v';
      destruct Content_Name_eq_dec with c c0...
   intro; discriminate.
 destruct H1.
  discriminate.
  eauto.
 destruct H1.
  discriminate.
  destruct Node_eq_dec with v v';
      destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
 destruct H1 as [H1 | [ H1 | H1 ] ].
  discriminate.
  destruct Node_eq_dec with v v'.
   destruct Content_Name_eq_dec with c c0.
    subst; cbv in H0; discriminate.
    inversion H1; elim n...
   inversion H1; elim n...
  destruct Node_eq_dec with v v';
      destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
 destruct H1 as [H1 | [ H1 | H1 ] ].
  discriminate.
  destruct Node_eq_dec with v v'.
   destruct Content_Name_eq_dec with c c0.
    subst; cbv in H0; discriminate.
    inversion H1; elim n...
   inversion H1; elim n...
  destruct Node_eq_dec with v v';
      destruct Content_Name_eq_dec with c c0...
   subst; cbv in H0; discriminate.
Qed.




Lemma Not_ForwardInterest_PIT_list_nil :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   Content_get v c es = None ->
   ~ In (ForwardInterest v c) es ->
   PIT_list v c es = [].
Proof with eauto.
intros; induction H; simpl in *...
 assert (~ In (ForwardInterest v c) es) by auto.
  destruct Node_eq_dec with v v'...
   destruct Content_Name_eq_dec with c c0...
   subst; elim H1...
 assert (~ In (ForwardInterest v c) es) by auto.
  destruct Node_eq_dec with v v'...
   destruct Content_Name_eq_dec with c c0...
   subst; elim H3...
 assert (~ In (ForwardInterest v c) es) by auto.
  destruct Node_eq_dec with v v'...
   destruct Content_Name_eq_dec with c c0...
    subst; cbv in H0; discriminate.
 assert (~ In (ForwardInterest v c) es) by auto.
  destruct Node_eq_dec with v v'...
   destruct Content_Name_eq_dec with c c0...
 assert (~ In (ForwardInterest v c) es) by auto.
  destruct Node_eq_dec with v v'...
   destruct Content_Name_eq_dec with c c0...
Qed.






Lemma Request_or_Forward_with_Data_StoreData :
 forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
  In (Request v1 c) es \/  In (ForwardInterest v1 c) es ->
  CCNprotocol es ps ->
   Content_get v1 c es = None ->
   In (Data v2 v1 c C) ps ->
   exists (es' : list Event) (ps' : list Packet),
    CCNprotocol (StoreData v1 c C :: es' ++ es) ps'.
Proof with eauto.
intros.
 apply in_split in H2; destruct H2 as [ ps1 [ ps2 H2 ] ]; subst.
  destruct in_dec_request with v1 c es;
      destruct in_dec_forward with v1 c es.
   exists [ForwardData v1 c]; simpl.
    exists ((PIT_Data v1 c C es) ++ ps1 ++ ps2).
     apply ccn_store_forward with (v := v2) (ps1 := ps1) (ps2 := ps2)...
      eapply ForwardInterest_PIT_list_not_nil...
   exists nil; simpl.
    exists (ps1 ++ ps2).
     apply ccn_store_data with (v := v2) (ps1 := ps1) (ps2 := ps2)...
      eapply Not_ForwardInterest_PIT_list_nil...
   exists [ForwardData v1 c]; simpl.
    exists ((PIT_Data v1 c C es) ++ ps1 ++ ps2).
     apply ccn_forward_data with (v := v2) (ps1 := ps1) (ps2 := ps2)...
      eapply ForwardInterest_PIT_list_not_nil...
   destruct H; [ elim n | elim n0 ]...
Qed.
   



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




