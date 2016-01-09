(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Lemmas for verification of the protocol *)

Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.
Require CCNContentManagement.
Require CCNProtocolWithCM.


Module CCN_Protocol_Lemma_CM (N : CCNContentManagement.CCN_Content_Management).

Import N.
Import Topology.

Module Protocol := CCNProtocolWithCM.CCN_Protocol_CM N.
Import Protocol.


Lemma CMF_None_Not_InitCS :
 forall (v : Node) (c : Content_Name) (es : list Event),
  CMF v c es = None -> ~InitCS v c.
intros; intro.
destruct CMF_keep_InitCS with v c es; auto.
rewrite H1 in H; discriminate.
Qed.


Lemma CMF_reply_consistency_app :
 forall (v : Node) (c : Content_Name) (es es' : list Event),
  CMF_reply_consistency v c es ->
   ~In (ReplyData v c) es' ->
   CMF_reply_consistency v c (es' ++ es).
intros; induction es'; simpl in *.
 now auto.
 unfold CMF_reply_consistency in *; intros.
 destruct es1; simpl in *.
  inversion H1; elim H0; now auto.
  inversion H1; subst; clear H1.
   now eauto.
Qed.
  

Lemma CMF_reply_consistency_split :
 forall (v : Node) (c : Content_Name) (es es' : list Event),
  CMF_reply_consistency v c (es' ++ es) ->
   CMF_reply_consistency v c es.
intros; unfold CMF_reply_consistency in *; intros.
subst.
apply H with (es' ++ es1).
now apply app_assoc.
Qed.



Lemma CCN_reply_consistency :
  forall (es : list Event) (ps : list Packet),
    CCNprotocol es ps -> forall (v : Node) (c : Content_Name), CMF_reply_consistency v c es.
intros.
unfold CMF_reply_consistency.
induction H; intros es1 es2 Heq; destruct es1; simpl in Heq; inversion Heq; subst; eauto.
+destruct es1; simpl in Heq; inversion Heq; subst; eauto.
+apply IHCCNprotocol with [].
 simpl; now auto.
+apply IHCCNprotocol with (e :: es1).
 simpl; now auto.
+apply IHCCNprotocol with [].
 simpl; now auto.
+apply IHCCNprotocol with (e :: es1).
 simpl; now auto.
+rewrite H0; intro H1; inversion H1.
+destruct es1; simpl in Heq; inversion Heq; subst; eauto.
+destruct es1; simpl in Heq; inversion Heq; subst; eauto.
+apply IHCCNprotocol with [].
 simpl; now auto.
+apply IHCCNprotocol with (e :: es1).
 simpl; now auto.
Qed.





(** Connected or not should be decidable : this is proven from the requirements of network [N]. *)
Lemma Connected_dec : forall v1 v2 : Node, {Connected v1 v2} + {~ Connected v1 v2}.
unfold Connected.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.


(** FIB pointed or not should be decidable : this is proven from the requirements of network [N]. *)
Lemma FIB_dec : forall (v1 v2 : Node) (c : Content_Name), {FIB v1 c v2} + {~ FIB v1 c v2}.
unfold FIB.
intros.
apply in_dec.
apply Node_eq_dec.
Qed.



(** Small lemma for decision procedure of content_name *)
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



(** decision procedure that forwarding interest packet is in event list or not *)
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



(** decision procedure that replying data exists in event list or not *)
Lemma in_dec_replydata : forall (v : Node) (c : Content_Name) (es : list Event), 
  { In (ReplyData v c) es } + { ~In (ReplyData v c) es }.
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
     inversion H; elim n1; now auto.
     now auto.
Qed.



(** decision procedure that storing data exists in event list or not *)
Lemma in_dec_storedata : forall (v : Node) (c : Content_Name) (es : list Event), 
  { exists (C : Content c), In (StoreData v c C) es } + { forall (C : Content c), ~In (StoreData v c C) es }.
intros v c es; induction es.
 right; intros C H; inversion H.
 destruct IHes.
  left; destruct e as [C e]; exists C; right; now auto.
  destruct a; try (right; intros C H; destruct H as [H | H]; [inversion H | apply n with C; auto]; fail).
   destruct (Node_eq_dec v n0).
    destruct (Content_Name_eq_dec c c0).
     subst; left; exists c1; simpl; auto.
     right; intros C H; destruct H as [H | H].
      inversion H; elim n1; now auto.
      apply n with C; now auto.
    right; intros C H; destruct H as [H | H].
     inversion H; elim n1; now auto.
     apply n with C; now auto.
Qed.



Lemma in_dec_interestpacket : forall (v1 v2 : Node) (c : Content_Name) (ps : list Packet),
  { In (Interest v1 v2 c) ps } + { ~In (Interest v1 v2 c) ps }.
intros v1 v2 c ps; induction ps.
 right; intro H; inversion H.
 destruct IHps.
  left; right; auto.
  destruct a; try (right; intro H; destruct H as [H | H]; [inversion H | apply n; auto]; fail).
   destruct (Node_eq_dec v1 n0).
    destruct (Node_eq_dec v2 n1).
     destruct (Content_Name_eq_dec c c0).
      subst; left; simpl; now auto.
      right; intro H; destruct H as [H | H].
       inversion H; elim n2; now auto.
       now auto.
     right; intro H; destruct H as [H | H].
      inversion H; elim n2; now auto.
      now auto.
    right; intro H; destruct H as [H | H].
     inversion H; elim n2; now auto.
     now auto.
Qed.



Lemma in_dec_datapacket : forall (v1 v2 : Node) (c : Content_Name) (ps : list Packet),
  { exists (C : Content c), In (Data v1 v2 c C) ps } + { forall (C : Content c), ~In (Data v1 v2 c C) ps }.
intros v1 v2 c ps; induction ps.
 right; intros C H; inversion H.
 destruct IHps.
  left; destruct e as [C e]; exists C; right; now auto.
  destruct a; try (right; intros C H; destruct H as [H | H]; [inversion H | apply n with C; auto]; fail).
   destruct (Node_eq_dec v1 n0).
    destruct (Node_eq_dec v2 n1).
     destruct (Content_Name_eq_dec c c0).
      subst; left; exists c1; simpl; auto.
      right; intros C H; destruct H as [H | H].
       inversion H; elim n2; now auto.
       apply n with C; now auto.
     right; intros C H; destruct H as [H | H].
      inversion H; elim n2; now auto.
      apply n with C; now auto.
    right; intros C H; destruct H as [H | H].
     inversion H; elim n2; now auto.
     apply n with C; now auto.
Qed.




Lemma in_dec_PIT_list : forall (v1 v2 : Node) (c : Content_Name) (es : list Event),
 { In v2 (PIT_list v1 c es) } + { ~In v2 (PIT_list v1 c es) }.
intros v1 v2 c es; induction es; simpl in *.
 right; now auto.
 destruct IHes.
  destruct a; intuition.
   destruct Node_eq_dec; try (destruct Content_Name_eq_dec); subst; intuition.
   destruct Node_eq_dec; try (destruct Content_Name_eq_dec); subst; intuition.
  destruct a; intuition.
   destruct Node_eq_dec; try (destruct Content_Name_eq_dec); subst; intuition.
   destruct Node_eq_dec with v2 n1; subst.
    left; simpl; now auto.
    right; intro H; destruct H as [H | H].
     elim n2; symmetry; now auto.
     now auto.
   destruct Node_eq_dec; try (destruct Content_Name_eq_dec); subst; intuition.
Qed.



(** a node is sent requests by another node, they connect each other *)
Lemma Broadcast_Interest_Connected :
 forall (v v1 v2 : Node) (c1 c2 : Content_Name),
  In (Interest v1 v2 c1) (Broadcast_Interest v c2) ->
   Connected v1 v2.
unfold Connected, Broadcast_Interest; intros.
 destruct (Node_eq_dec v1 v).
  subst; remember (Connected_list v).
   clear Heql; induction l.
    simpl in H; contradiction.
    simpl in H; destruct H.
     inversion H; subst; simpl; auto.
     simpl; auto.
  remember (Connected_list v).
   clear Heql; induction l.
    simpl in H; contradiction.
    simpl in H; destruct H.
     inversion H; subst; elim n; auto.
     auto.
Qed.



(** a node is forwarded requests by another node, they connect each other *)
Lemma FIB_Interest_Connected :
 forall (v v1 v2 : Node) (c1 c2 : Content_Name),
  In (Interest v1 v2 c1) (FIB_Interest v c2) ->
   Connected v1 v2.
unfold Connected, FIB_Interest; intros.
 apply Broadcast_Interest_Connected with v c1 c2.
  unfold Broadcast_Interest.
   apply In_map_conservative with (l1 := FIB_list v c2).
    intro; apply FIB_Connected.
    auto.
Qed.




Lemma Event_nil_Packet_nil :
 forall (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   es = [] ->
   ps = [].
intros; induction H; auto.
+inversion H0.
+inversion H0.
+inversion H0.
+assert (Hn := IHCCNprotocol H0); destruct ps1; simpl in Hn; inversion Hn.
+assert (Hn := IHCCNprotocol H0); destruct ps1; simpl in Hn; inversion Hn.
+inversion H0.
+inversion H0.
+inversion H0.
+inversion H0.
+assert (Hn := IHCCNprotocol H0); destruct ps1; simpl in Hn; inversion Hn.
Qed.



(** If a node has contents, then it is an initial content server or it has stored already *)
Lemma CMF_InitCS_or_StoreData :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   CMF v c es <> None ->
   InitCS v c \/ exists (C : Content c), In (StoreData v c C) es.
intros; induction H; auto.
+destruct InitCS_dec with v c.
  auto.
  rewrite CMF_not_create_content in H0.
   elim H0; now auto.
   now auto.
+case_eq (CMF v c es); intros.
  destruct IHCCNprotocol; auto.
   intro H4; rewrite H4 in H3; now inversion H3.
   destruct H4; right; eexists; right; now eauto.
  rewrite cons_app in H0.
   rewrite (CMF_consistency v c es [Request v0 c0]) in H0.
    elim H0; now auto.
    apply CMF_reply_consistency_app.
     eapply CCN_reply_consistency; now eauto.
     intro Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
+case_eq (CMF v c es); intros.
  destruct IHCCNprotocol; auto.
   intro H6; rewrite H6 in H5; now inversion H5.
   destruct H6; right; eexists; simpl; now eauto.
  rewrite cons_app2 in H0.
   rewrite (CMF_consistency v c) in H0.
    elim H0; now auto.
    apply CMF_reply_consistency_app.
     eapply CCN_reply_consistency; now eauto.
     intro Hn; destruct Hn as [Hn | [Hn | Hn]]; now inversion Hn.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
+case_eq (CMF v c es); intros.
  destruct IHCCNprotocol; auto.
   intro H7; rewrite H7 in H6; now inversion H6.
   destruct H7; right; eexists; simpl; now eauto.
  rewrite cons_app in H0.
   rewrite (CMF_consistency v c) in H0.
    elim H0; now auto.
    apply CMF_reply_consistency_app.
     eapply CCN_reply_consistency; now eauto.
     intro Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
+case_eq (CMF v c es); intros.
  destruct IHCCNprotocol; auto.
   intro H4; rewrite H4 in H3; now inversion H3.
   destruct H4; right; eexists; simpl; now eauto.
  rewrite cons_app in H0.
   rewrite (CMF_consistency v c) in H0.
    elim H0; now auto.
    simpl; eapply CCN_reply_consistency.
     eapply ccn_reply_data; now eauto.
     now auto.
    intros ? Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
+destruct Node_eq_dec with v v'; subst.
  destruct Content_Name_eq_dec with c c0; subst.
   right; exists C; simpl; now auto.
   case_eq (CMF v' c es); intros.
    destruct IHCCNprotocol; auto.
     intro H5; rewrite H5 in H4; now inversion H4.
     destruct H5; right; eexists; simpl; now eauto.
    rewrite cons_app in H0.
     rewrite (CMF_consistency v' c) in H0.
      elim H0; now auto.
      simpl; eapply CCN_reply_consistency.
       eapply ccn_store_data; now eauto.
      now auto.
      intros ? Hn; destruct Hn as [Hn | Hn]; inversion Hn; subst.
       elim n; now auto.
  case_eq (CMF v c es); intros.
   destruct IHCCNprotocol; auto.
    intro H5; rewrite H5 in H4; now inversion H4.
    destruct H5; right; eexists; simpl; now eauto.
   rewrite cons_app in H0.
    rewrite (CMF_consistency v c) in H0.
     elim H0; now auto.
     simpl; eapply CCN_reply_consistency.
      eapply ccn_store_data; now eauto.
     now auto.
     intros ? Hn; destruct Hn as [Hn | Hn]; inversion Hn; subst.
      elim n; now auto.
+destruct Node_eq_dec with v v'; subst.
  destruct Content_Name_eq_dec with c c0; subst.
   right; exists C; simpl; now auto.
   case_eq (CMF v' c es); intros.
    destruct IHCCNprotocol; auto.
     intro H5; rewrite H5 in H4; now inversion H4.
     destruct H5; right; eexists; simpl; now eauto.
    rewrite cons_app2 in H0.
     rewrite (CMF_consistency v' c) in H0.
      elim H0; now auto.
      simpl; eapply CCN_reply_consistency.
       eapply ccn_forward_data; now eauto.
      now auto.
      intros ? Hn; destruct Hn as [Hn | [Hn | Hn]]; inversion Hn; subst.
       elim n; now auto.
  case_eq (CMF v c es); intros.
   destruct IHCCNprotocol; auto.
    intro H5; rewrite H5 in H4; now inversion H4.
    destruct H5; right; eexists; simpl; now eauto.
   rewrite cons_app2 in H0.
    rewrite (CMF_consistency v c) in H0.
     elim H0; now auto.
     simpl; eapply CCN_reply_consistency.
      eapply ccn_forward_data; now eauto.
     now auto.
     intros ? Hn; destruct Hn as [Hn | [Hn | Hn]]; inversion Hn; subst.
      elim n; now auto.
+destruct Node_eq_dec with v v'; subst.
  destruct Content_Name_eq_dec with c c0; subst.
   right; exists C; simpl; now auto.
   case_eq (CMF v' c es); intros.
    destruct IHCCNprotocol; auto.
     intro H5; rewrite H5 in H4; now inversion H4.
     destruct H5; right; eexists; simpl; now eauto.
    rewrite cons_app2 in H0.
     rewrite (CMF_consistency v' c) in H0.
      elim H0; now auto.
      simpl; eapply CCN_reply_consistency.
       eapply ccn_store_forward; now eauto.
      now auto.
      intros ? Hn; destruct Hn as [Hn | [Hn | Hn]]; inversion Hn; subst.
       elim n; now auto.
  case_eq (CMF v c es); intros.
   destruct IHCCNprotocol; auto.
    intro H5; rewrite H5 in H4; now inversion H4.
    destruct H5; right; eexists; simpl; now eauto.
   rewrite cons_app2 in H0.
    rewrite (CMF_consistency v c) in H0.
     elim H0; now auto.
     simpl; eapply CCN_reply_consistency.
      eapply ccn_store_forward; now eauto.
     now auto.
     intros ? Hn; destruct Hn as [Hn | [Hn | Hn]]; inversion Hn; subst.
      elim n; now auto.
Qed.




(** If a node requests a content, it does not have the content *)
Lemma Request_Not_CMF :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol (Request v c :: es) ps ->
   CMF v c (Request v c :: es) = None.
intros; remember (Request v c :: es); revert v c es Heql; induction H; intros; subst; try discriminate; eauto.
 inversion Heql; subst.
 apply CMF_consistency with _ _ _ [Request v0 c0] in H0.
  simpl in H0; auto.
  simpl; eapply CCN_reply_consistency.
   eapply ccn_request; eauto.
  simpl; intros C H1.
   destruct H1; auto; now discriminate.
Qed.





(** If a node forwards an interest packet, it does not have the content requested by the packet *)
Lemma ForwardInterest_Not_CMF :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol (ForwardInterest v c :: es) ps ->
   CMF v c (ForwardInterest v c :: es) = None.
intros; remember (ForwardInterest v c :: es); revert v c es Heql; induction H; intros; subst; try discriminate; eauto.
 inversion Heql; subst.
 apply CMF_consistency with v0 c0 es [ForwardInterest v0 c0; AddPIT v0 v c0] in H0.
  simpl in H0; now auto.
  eapply CCN_reply_consistency; simpl.
   eapply ccn_forward_interest; now eauto.
  simpl; intros C H3.
   destruct H3 as [? | [? | ?]]; auto; now inversion H3.
Qed.



(** If a snapshot (network state) complies the behaviors of the CCN protocol and there have been a request, the snapshot at the request complied. *)
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



(** If a snapshot complies the behaviors of the CCN protocol and there have been a forwarding event, the snapshot at the event complied. *)
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



Lemma split_ForwardData_CCNprotocol :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardData v c :: es2) ps ->
   exists ps' : list Packet,
    CCNprotocol es2 ps'.
Proof with eauto.
intros; remember (es1 ++ ForwardData v c :: es2); revert v c es1 es2 Heql; induction H; intros; subst...
 destruct es1; simpl in Heql; inversion Heql.
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  destruct es1; simpl in H5; inversion H5...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql...
 destruct es1; simpl in Heql; inversion Heql.
  destruct es1; simpl in H5; inversion H5...
   subst; now eauto.
 destruct es1; simpl in Heql; inversion Heql.
  destruct es1; simpl in H5; inversion H5...
   subst; now eauto.
Qed.


(** If a snapshot complies the behaviors of the CCN protocol and a node has stored a content, the snapshot at the storing event complied. *)
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



(** If a node did not have a content at a snapshot but has it currently, it stored between the snaoshot and now. *)
Lemma CMF_app_In_Store_Data :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event),
  CMF v c es2 = None ->
   CMF v c (es1 ++ es2) <> None ->
   CMF_reply_consistency v c (es1 ++ es2) ->
   exists (C : Content c),
    In (StoreData v c C) es1.
Proof with eauto.
intros; induction es1; intros; simpl in *...
 elim H0...
 case_eq (CMF v c (es1 ++ es2)); intros.
 destruct IHes1; eauto.
  intro H3; rewrite H3 in H2; discriminate.
  apply CMF_reply_consistency_split with [a].
   simpl; now auto.
  rewrite cons_app in H0; destruct a.
  +rewrite CMF_consistency in H0.
    elim H0; now auto.
    simpl; now auto.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
  +rewrite CMF_consistency in H0.
    elim H0; now auto.
    simpl; now auto.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
  +rewrite CMF_consistency in H0.
    elim H0; now auto.
    simpl; now auto.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
  +rewrite CMF_consistency in H0.
    elim H0; now auto.
    simpl; now auto.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
  +rewrite CMF_consistency in H0.
    elim H0; now auto.
    simpl; now auto.
    now auto.
    intros C Hn; destruct Hn as [Hn | Hn]; now inversion Hn.
  +destruct Node_eq_dec with n v.
    destruct Content_Name_eq_dec with c0 c.
     subst; exists c1; now auto.
     rewrite CMF_consistency in H0.
      elim H0; now auto.
      simpl; now auto.
      now auto.
      intros C Hn; destruct Hn as [Hn | Hn]; inversion Hn.
       subst; elim n0; now auto.
    rewrite CMF_consistency in H0.
     elim H0; now auto.
     simpl; now auto.
     now auto.
     intros C Hn; destruct Hn as [Hn | Hn]; inversion Hn.
      subst; elim n0; now auto.
Qed.




(** a node sends interest packets to another node in a request if they connect *)
Lemma Connected_In_Broadcast_Interest :
 forall (v1 v2 : Node) (c : Content_Name),
  Connected v1 v2 ->
   In (Interest v1 v2 c) (Broadcast_Interest v1 c).
intros v1 v2 c; unfold Connected; unfold Broadcast_Interest; generalize (Connected_list v1);
    revert v1 v2 c; induction l; intros; simpl in H.
 elim H.
 destruct H; subst; simpl; eauto.
Qed.



(** a node forwards interest packets to only nodes in FIB *)
Lemma FIB_In_FIB_Interest :
 forall (v1 v2 : Node) (c : Content_Name),
  FIB v1 c v2 ->
   In (Interest v1 v2 c) (FIB_Interest v1 c).
intros v1 v2 c; unfold FIB; unfold FIB_Interest; generalize (FIB_list v1 c);
    revert v1 v2 c; induction l; intros; simpl in H.
 elim H.
 destruct H; subst; simpl; eauto.
Qed.



(** a node forwards data packets to only nodes in PIT entries *)
Lemma PIT_In_PIT_Data :
 forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es : list Event),
  In v2 (PIT_list v1 c es) ->
   In (Data v1 v2 c C) (PIT_Data v1 c C es).
intros v1 v2 c C es; unfold PIT_Data; generalize (PIT_list v1 c es);
    revert v1 v2 c C es; induction l; intros; simpl in H.
 contradiction.
 destruct H; subst; simpl; eauto.
Qed. 



(** If a node is forwarded data packets, it is in PIT entries *)
Lemma In_PIT_Data_In_PIT :
 forall (v1 v2 : Node) (c1 c2 : Content_Name) (C1 : Content c1) (C2 : Content c2) (es : list Event),
  In (Data v1 v2 c2 C2) (PIT_Data v1 c1 C1 es) ->
   In v2 (PIT_list v1 c1 es).
intros v1 v2 c1 c2 C1 C2 es; unfold PIT_Data; generalize (PIT_list v1 c1 es);
    revert v1 v2 c1 c2 C1 C2 es; induction l; intros; simpl in H.
 contradiction.
 simpl; destruct H.
  inversion H; subst; auto.
  auto.
Qed.



(** If a node is in PIT entries of another's, there should be an event adding the node to PIT *)
Lemma In_PIT_list_In_AddPIT :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event),
  In v1 (PIT_list v2 c es) ->
   In (AddPIT v2 v1 c) es.
Proof with auto.
intros; induction es; simpl in *...
 destruct a...
  destruct Node_eq_dec with v2 n...
   subst; destruct Content_Name_eq_dec with c c0...
    subst; destruct H as [H | H].
     subst; now auto.
     now auto.
  destruct Node_eq_dec with v2 n...
   subst; destruct Content_Name_eq_dec with c c0...
    contradiction.
Qed.





(** If a node has forwarded interest packets but does not have contents, PIT entries are not empty (there exist PIT entries) *) 
Lemma ForwardInterest_PIT_list_not_nil :
 forall (v : Node) (c : Content_Name) (es1 es2 : list Event) (ps : list Packet),
  CCNprotocol (es1 ++ ForwardInterest v c :: es2) ps ->
   CMF v c (es1 ++ ForwardInterest v c :: es2) = None ->
   (forall (C : Content c), ~In (StoreData v c C) es1) ->
   PIT_list v c (es1 ++ ForwardInterest v c :: es2) <> [].
Proof with eauto.
intros v c es1 es2; remember (es1 ++ ForwardInterest v c :: es2).
intros ps H; revert v c es1 es2 Heql; induction H; intros; simpl; eauto.
+destruct es1; simpl in Heql; inversion Heql.
+destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
 apply IHCCNprotocol with es1 es2.
  -now auto.
  -apply CMF_consistency.
   *apply CCN_reply_consistency with ps; now auto.
   *destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
    apply ForwardInterest_Not_CMF with x; now auto.
   *intros C H4; apply H3 with C; right; now auto.
  -intros C H4; apply H3 with C; right; now auto.
+destruct Node_eq_dec.
  destruct Content_Name_eq_dec.
  -intro Hn; inversion Hn.
  -clear e; destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    elim n; now auto.
    destruct es1; simpl in H8; inversion H8; subst; clear H8.
     apply IHCCNprotocol with es1 es2; auto.
      apply CMF_consistency.
       eapply CCN_reply_consistency; now eauto.
       destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
        apply ForwardInterest_Not_CMF with x; now auto.
       intros C H6; apply H5 with C; right; right; now auto.
      intros C H6; apply H5 with C; right; right; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    elim n; now auto.
    destruct es1; simpl in H8; inversion H8; subst; clear H8.
     apply IHCCNprotocol with es1 es2; auto.
      apply CMF_consistency.
       eapply CCN_reply_consistency; now eauto.
       destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
        apply ForwardInterest_Not_CMF with x; now auto.
       intros C H6; apply H5 with C; right; right; now auto.
      intros C H6; apply H5 with C; right; right; now auto.
+destruct Node_eq_dec.
  destruct Content_Name_eq_dec.
  -intro Hn; inversion Hn.
  -clear e; destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    apply IHCCNprotocol with es1 es2; auto.
     apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C H7; apply H6 with C; right; now auto.
     intros C H7; apply H6 with C; right; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    apply IHCCNprotocol with es1 es2; auto.
     apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C H7; apply H6 with C; right; now auto.
     intros C H7; apply H6 with C; right; now auto.
+destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
 apply IHCCNprotocol with es1 es2.
  -now auto.
  -apply CMF_consistency.
   *eapply CCN_reply_consistency; now eauto.
   *destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
    apply ForwardInterest_Not_CMF with x; now auto.
   *intros C0 H4; apply H3 with C0; right; now auto.
  -intros C0 H4; apply H3 with C0; right; now auto.
+destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
 apply IHCCNprotocol with es1 es2.
  -now auto.
  -apply CMF_consistency.
   *eapply CCN_reply_consistency; now eauto.
   *destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
    apply ForwardInterest_Not_CMF with x; now auto.
   *intros C0 H6; apply H5 with C0; right; now auto.
  -intros C0 H6; apply H5 with C0; right; now auto.
+destruct Node_eq_dec.
  destruct Content_Name_eq_dec; subst.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    elim (H5 C); left; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    destruct es1; simpl in H7; inversion H7; subst; clear H7.
    apply IHCCNprotocol with es1 es2; auto.
    *apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C0 H6; apply H5 with C0; right; right; now auto.
    *intros C0 H6; apply H5 with C0; right; right; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    destruct es1; simpl in H8; inversion H8; subst; clear H8.
    apply IHCCNprotocol with es1 es2; auto.
    *apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C0 H6; apply H5 with C0; right; right; now auto.
    *intros C0 H6; apply H5 with C0; right; right; now auto.
+destruct Node_eq_dec.
  destruct Content_Name_eq_dec; subst.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    elim (H5 C); left; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    destruct es1; simpl in H7; inversion H7; subst; clear H7.
    apply IHCCNprotocol with es1 es2; auto.
    *apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C0 H6; apply H5 with C0; right; right; now auto.
    *intros C0 H6; apply H5 with C0; right; right; now auto.
  -destruct es1; simpl in Heql; inversion Heql; subst; clear Heql.
    destruct es1; simpl in H8; inversion H8; subst; clear H8.
    apply IHCCNprotocol with es1 es2; auto.
    *apply CMF_consistency.
      eapply CCN_reply_consistency; now eauto.
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H).
       apply ForwardInterest_Not_CMF with x; now auto.
      intros C0 H6; apply H5 with C0; right; right; now auto.
    *intros C0 H6; apply H5 with C0; right; right; now auto.
Qed.



Lemma PIT_list_ForwardInterest :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   In v1 (PIT_list v2 c es) ->
   exists (es1 es2 : list Event),
    es = es2 ++ ForwardInterest v2 c :: es1 /\ forall (C : Content c), ~In (StoreData v2 c C) es2.
intros; revert v1 v2 H0; induction H; intros; simpl in *.
+contradiction.
+destruct (IHCCNprotocol v1 v2 H2) as [es1 [es2 [H3 H4]]].
 exists es1, (Request v c0 :: es2); split.
  simpl; rewrite H3; now auto.
  intros C H5; destruct H5.
   now inversion H5.
   apply H4 with C; now auto.
+destruct Node_eq_dec with v2 v'.
  subst; destruct Content_Name_eq_dec with c c0.
   subst; destruct H0.
    subst; exists (AddPIT v' v c0 :: es), []; split; simpl.
     now auto.
     intros _ Hn; now auto.
    destruct (IHCCNprotocol v1 v' H4) as [es1 [es2 [H5 H6]]].
     exists es1, (ForwardInterest v' c0 :: AddPIT v' v c0 :: es2); split.
      simpl; rewrite H5; now auto.
      intros C H7; destruct H7 as [H7 | [H7 | H7]].
       now inversion H7.
       now inversion H7.
       apply H6 with C; now auto.
   destruct (IHCCNprotocol v1 v2 H4) as [es1 [es2 [H5 H6]]].
    exists es1, (ForwardInterest v' c0 :: AddPIT v' v c0 :: es2); split.
     simpl; rewrite H5; now auto.
     intros C H7; destruct H7 as [H7 | [H7 | H7]].
      now inversion H7.
      now inversion H7.
      apply H6 with C; now auto.
+destruct Node_eq_dec with v2 v'.
  subst; destruct Content_Name_eq_dec with c c0.
   subst; destruct H5.
    case_eq (PIT_list v' c0 es); intros.
     elim H3; now auto.
     subst; destruct (IHCCNprotocol n v') as [es1 [es2 [H6 H7]]].
      rewrite H5; simpl; now auto.
      exists es1, (AddPIT v' v1 c0 :: es2); split; simpl.
       rewrite H6; now auto.
       intros C Hn; destruct Hn as [Hn | Hn].
        now inversion Hn.
        apply H7 with C; now auto.
    destruct (IHCCNprotocol v1 v' H4) as [es1 [es2 [H5 H6]]].
     exists es1, (AddPIT v' v c0 :: es2); split.
      simpl; rewrite H5; now auto.
      intros C H7; destruct H7 as [H7 | H7].
       now inversion H7.
       apply H6 with C; now auto.
   destruct (IHCCNprotocol v1 v' H5) as [es1 [es2 [H6 H7]]].
    exists es1, (AddPIT v' v c0 :: es2); split.
     simpl; rewrite H6; now auto.
     intros C H8; destruct H8 as [H8 | H8].
      now inversion H8.
      apply H7 with C; now auto.
  destruct (IHCCNprotocol v1 v2 H5) as [es1 [es2 [H6 H7]]].
   exists es1, (AddPIT v' v c0 :: es2); split.
    simpl; rewrite H6; now auto.
    intros C H8; destruct H8 as [H8 | H8].
     now inversion H8.
     apply H7 with C; now auto.
+now eauto.
+now eauto.
+destruct (IHCCNprotocol _ _ H2) as [es1 [es2 [H3 H4]]].
 exists es1, (ReplyData v' c0 :: es2); split.
  simpl; rewrite H3; now auto.
  intros C0 H5; destruct H5.
   now inversion H5.
   apply H4 with C0; now auto.
+destruct (IHCCNprotocol _ _ H4) as [es1 [es2 [H5 H6]]].
  exists es1, (StoreData v' c0 C :: es2); split.
   simpl; rewrite H5; now auto.
   intros C0 H7; destruct H7.
    inversion H7; subst.
     rewrite H2 in H4; simpl in H4; now auto.
    apply H6 with C0; now auto.
+destruct Node_eq_dec with v2 v'.
  destruct Content_Name_eq_dec with c c0.
   simpl in H4; contradiction.
   subst; destruct (IHCCNprotocol _ _ H4) as [es1 [es2 [H5 H6]]].
    exists es1, (StoreData v' c0 C :: ForwardData v' c0 :: es2); split.
     simpl; rewrite H5; now auto.
     intros C0 H7; destruct H7 as [H7 | [H7 | H7]].
      inversion H7; subst.
       apply n; now auto.
      now inversion H7.
      apply H6 with C0; now auto.
  subst; destruct (IHCCNprotocol _ _ H4) as [es1 [es2 [H5 H6]]].
   exists es1, (StoreData v' c0 C :: ForwardData v' c0 :: es2); split.
    simpl; rewrite H5; now auto.
    intros C0 H7; destruct H7 as [H7 | [H7 | H7]].
     inversion H7; subst.
      apply n; now auto.
     now inversion H7.
     apply H6 with C0; now auto.
+destruct Node_eq_dec with v2 v'.
  destruct Content_Name_eq_dec with c c0.
   simpl in H4; contradiction.
   subst; destruct (IHCCNprotocol _ _ H4) as [es1 [es2 [H5 H6]]].
    exists es1, (StoreData v' c0 C :: ForwardData v' c0 :: es2); split.
     simpl; rewrite H5; now auto.
     intros C0 H7; destruct H7 as [H7 | [H7 | H7]].
      inversion H7; subst.
       apply n; now auto.
      now inversion H7.
      apply H6 with C0; now auto.
  subst; destruct (IHCCNprotocol _ _ H4) as [es1 [es2 [H5 H6]]].
   exists es1, (StoreData v' c0 C :: ForwardData v' c0 :: es2); split.
    simpl; rewrite H5; now auto.
    intros C0 H7; destruct H7 as [H7 | [H7 | H7]].
     inversion H7; subst.
      apply n; now auto.
     now inversion H7.
     apply H6 with C0; now auto.
+now eauto.
Qed.



Lemma PIT_list_no_StoreData_append :
 forall (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
  forall (es1 es2 : list Event) (v : Node) (c : Content_Name),
   es = es1 ++ es2 ->
    (forall C : Content c, ~In (StoreData v c C) es1) ->
    exists pit : list Node, PIT_list v c es = pit ++ PIT_list v c es2.
intros es ps H; induction H; simpl; intros es1 es2 v1 c' Heq HNIN; inversion Heq; clear Heq; subst.
+destruct es1.
  destruct es2.
   exists []; simpl; now auto.
   simpl in H0; inversion H0.
  simpl in H0; inversion H0.
+destruct es1.
  destruct es2.
   simpl in H3; inversion H3.
   destruct (IHCCNprotocol [] es2 v1 c').
    simpl in *; inversion H3; now auto.
    simpl; now auto.
    rewrite H1; destruct e; simpl; eauto.
     destruct Node_eq_dec.
      destruct Content_Name_eq_dec; subst.
       exists (x ++ [n0]); simpl; now auto.
       now eauto.
      now eauto.
     destruct Node_eq_dec.
      destruct Content_Name_eq_dec.
       simpl; now eauto.
       now eauto.
      now eauto.
  simpl in H3; inversion H3; subst; clear H3.
   destruct (IHCCNprotocol es1 es2 v1 c').
    now auto.
    intros C Hn; apply HNIN with C; right; now auto.
    rewrite H1; now eauto.
+destruct es1.
  destruct es2.
   simpl in H5; inversion H5.
   destruct es2.
    simpl in H5; inversion H5.
    simpl in H5; inversion H5; simpl; exists nil; auto.
  destruct es1.
   destruct es2.
    simpl in H5; inversion H5.
    simpl in H5; inversion H5; simpl; exists nil; auto.
   simpl in H5; inversion H5; subst.
    destruct (IHCCNprotocol es1 es2 v1 c'); auto.
     intros C Hn; apply HNIN with C; simpl; now auto.
     rewrite H3.
     destruct Node_eq_dec.
      destruct Content_Name_eq_dec.
       exists (v :: x); simpl; now auto.
       now eauto.
      now eauto.
+destruct es1.
  destruct es2.
   simpl in H6; inversion H6.
   simpl in *; inversion H6; simpl; exists nil; now auto.
  simpl in H6; inversion H6; subst.
   destruct (IHCCNprotocol es1 es2 v1 c'); auto.
    intros C Hn; apply HNIN with C; simpl; now auto.
    rewrite H4.
    destruct Node_eq_dec.
     destruct Content_Name_eq_dec.
      exists (v :: x); simpl; now auto.
      now eauto.
     now eauto.
+now eauto.
+now eauto.
+destruct es1.
  destruct es2; simpl in *; inversion H3; subst.
   exists []; now auto.
  simpl in H3; inversion H3; subst.
   destruct (IHCCNprotocol es1 es2 v1 c'); auto.
    intros C' Hn; apply HNIN with C'; simpl; now auto.
    rewrite H1; now eauto.
+destruct es1.
  destruct es2; simpl in *; inversion H5; subst.
   exists []; now auto.
  simpl in H5; inversion H5; subst.
   destruct (IHCCNprotocol es1 es2 v1 c'); auto.
    intros C' Hn; apply HNIN with C'; simpl; now auto.
    rewrite H3; now eauto.
+destruct es1.
  destruct es2; simpl in *; inversion H5; subst; exists []; simpl; now auto.
  simpl in H5; destruct es1; simpl in *; inversion H5; subst; simpl.
   exists []; now auto.
   destruct (IHCCNprotocol es1 es2 v1 c'); auto.
    intros C' Hn; apply HNIN with C'; simpl; now auto.
    rewrite H3.
     exists x; destruct Node_eq_dec; [destruct Content_Name_eq_dec | ]; auto.
      subst; elim HNIN with C; now auto.
+destruct es1.
  destruct es2; simpl in *; inversion H5; subst; exists []; simpl; now auto.
  simpl in H5; destruct es1; simpl in *; inversion H5; subst; simpl.
   exists []; now auto.
   destruct (IHCCNprotocol es1 es2 v1 c'); auto.
    intros C' Hn; apply HNIN with C'; simpl; now auto.
    rewrite H3.
     exists x; destruct Node_eq_dec; [destruct Content_Name_eq_dec | ]; auto.
      subst; elim HNIN with C; now auto.
+now eauto.
Qed.



Lemma ForwardData_Not_CCN :
 forall (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   forall (es' : list Event) (v : Node) (c : Content_Name),
    es <> ForwardData v c :: es'.
intros es ps H; induction H; intros es' vx c' Heq; inversion Heq; clear Heq; subst.
+apply IHCCNprotocol with es' vx c'; now auto.
+apply IHCCNprotocol with es' vx c'; now auto.
+apply IHCCNprotocol with es' vx c'; now auto.
Qed.





Lemma StoreData_PIT_ForwardData :
 forall (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
  forall (es1 es2 : list Event) (v : Node) (c : Content_Name) (C : Content c),
   es = StoreData v c C :: es1 ++ es2 ->
   PIT_list v c es2 <> nil ->
   (forall C' : Content c, ~In (StoreData v c C') es1) ->
    exists es'' : list Event, es1 ++ es2 = ForwardData v c :: es''.
intros es ps H; induction H; simpl; intros es1 es2 v1 c' C' Heq HPIT HNIN; inversion Heq; clear Heq; subst.
+eapply IHCCNprotocol; now eauto.
+eapply IHCCNprotocol; now eauto.
+clear H7; destruct es1.
  destruct es2.
   unfold In_Request in H2; simpl in H2; now elim H2.
   elim HPIT; now auto.
  destruct PIT_list_no_StoreData_append with ((e :: es1) ++ es2) (ps1 ++ Data v v1 c' C :: ps2) (e :: es1) es2 v1 c'; auto.
   rewrite H3 in H2; destruct (PIT_list v1 c' es2).
    elim HPIT; now auto.
    destruct x; simpl in H2; now inversion H2.
+now eauto.
+now eauto.
+eapply IHCCNprotocol; now eauto.
Qed.



Lemma ForwardInterest_AddPIT :
 forall (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
  forall (es1 : list Event) (v : Node) (c : Content_Name),
   es = ForwardInterest v c :: es1 ->
   exists (es2 : list Event) (v' : Node), es1 = AddPIT v v' c :: es2.
intros es ps H; induction H; intros es1' v1 c' Heq; inversion Heq; subst; eauto.
Qed.




Lemma StoreData_tail :
 forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event),
  In (StoreData v c C) es ->
   exists (es1 es2 : list Event),
    (exists (C' : Content c), es = es2 ++ StoreData v c C' :: es1) /\
    forall (C' : Content c), ~In (StoreData v c C') es1.
intros v c C es; revert C; induction es; intros.
 simpl in H; now elim H.
 destruct H as [H | H].
  subst.
   destruct in_dec_storedata with v c es.
    destruct e.
     destruct (IHes x H) as [es1 [es2 [[C' Hl] Hr]]].
      subst.
      exists es1, (StoreData v c C :: es2); split.
       eexists; simpl; now eauto.
       now auto.
    exists es, []; simpl; split.
     now eauto.
     now auto.
  destruct (IHes _ H) as [es1 [es2 [[C' Hl] Hr]]]; subst.
   exists es1, (a :: es2); simpl; split.
    now eauto.
    now auto.
Qed.




Lemma StoreData_StoreData_or_DataPacket :
 forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   forall (es1 es2 : list Event),
    es = es2 ++ StoreData v2 c C :: ForwardData v2 c :: es1 ->
     v1 <> v2 ->
     In v1 (PIT_list v2 c es1) ->
     PIT_list v1 c es1 <> nil ->
     (exists C' : Content c, In (StoreData v1 c C') es2) \/ (exists C' : Content c, In (Data v2 v1 c C') ps).
intros vs vt c' C' es ps H; induction H; intros es1 es2 Heq Hneq HIn Hnnil.
+destruct es2; simpl in Heq; now inversion Heq.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
  left; eexists; right; now eauto.
  right; eexists; apply in_or_app; now eauto.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct es2; simpl in H6; inversion H6; clear H6; subst.
 destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
  left; eexists; right; right; now eauto.
  right; exists C0; apply in_or_app; apply in_app_or in HI; simpl in *; now intuition.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
  left; eexists; right; now eauto.
  right; exists C0; apply in_or_app; apply in_app_or in HI; simpl in *; now intuition.
+destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; subst; auto.
  left; now eauto.
  right; exists C0; apply in_or_app; apply in_app_or in HI; simpl in *; now intuition.
+destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; subst; auto.
  left; now eauto.
  right; exists C0; apply in_or_app; apply in_app_or in HI; simpl in *; now intuition.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
  left; eexists; right; now eauto.
  right; exists C0; right; apply in_or_app; apply in_app_or in HI; simpl in *; now intuition.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
  edestruct ForwardData_Not_CCN.
   exact H.
   reflexivity.
  destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
   left; eexists; right; now eauto.
   apply in_app_or in HI; destruct HI as [HI | [HI | HI]].
    right; eexists; apply in_or_app; now eauto.
    inversion HI; subst; left.
     eexists; left; reflexivity.
    right; eexists; apply in_or_app; now eauto.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
  right; exists C.
   apply in_or_app; left.
    apply PIT_In_PIT_Data; now auto.
  destruct es2; simpl in H6; inversion H6; clear H6; subst.
   destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
    left; eexists; right; right; now eauto.
    apply in_app_or in HI; destruct HI as [HI | [HI | HI]].
     right; eexists; apply in_or_app; right; apply in_or_app; now eauto.
     inversion HI; subst; left.
      eexists; left; reflexivity.
     right; eexists; apply in_or_app; right; apply in_or_app; now eauto.
+destruct es2; simpl in Heq; inversion Heq; clear Heq; subst.
  right; exists C.
   apply in_or_app; left.
    apply PIT_In_PIT_Data; now auto.
  destruct es2; simpl in H6; inversion H6; clear H6; subst.
   destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; auto.
    left; eexists; right; right; now eauto.
    apply in_app_or in HI; destruct HI as [HI | [HI | HI]].
     right; eexists; apply in_or_app; right; apply in_or_app; now eauto.
     inversion HI; subst; left.
      eexists; left; reflexivity.
     right; eexists; apply in_or_app; right; apply in_or_app; now eauto.
+destruct IHCCNprotocol with es1 es2 as [[C0 HI] | [C0 HI]]; subst; auto.
  left; now eauto.
  apply in_app_or in HI; simpl in *; destruct HI as [HI | [HI | HI]].
   right; exists C0; apply in_or_app; now eauto.
   inversion HI; subst.
    clear H6 HI.
    assert (exists C'' : Content c', In (StoreData vs c' C'') (es2 ++ [StoreData vt c' C'; ForwardData vt c'])).
    {
     destruct in_dec_storedata with vs c' (es2 ++ [StoreData vt c' C'; ForwardData vt c']).
      now auto.
      destruct PIT_list_no_StoreData_append with (es2 ++ StoreData vt c' C' :: ForwardData vt c' :: es1) (ps1 ++ Data vt vs c' C :: ps2) (es2 ++ [StoreData vt c' C'; ForwardData vt c']) es1 vs c'; simpl; auto.
       rewrite <- app_assoc; simpl; now auto.
       rewrite H1 in H2.
       elim Hnnil.
       destruct x; simpl in H2; inversion H2; now auto.
    }
    destruct H2 as [C'' H2].
     apply in_app_or in H2; destruct H2 as [H2 | [H2 | H2]].
      left; eexists; now eauto.
      inversion H2; elim Hneq; now auto.
      now inversion H2.
   right; exists C0; apply in_or_app; now eauto.
Qed.



Lemma Not_PIT_Data_StoreData_Interest :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   In v2 (FIB_list v1 c) ->
   forall (es1 es2 : list Event),
    es = es1 ++ ForwardInterest v1 c :: es2 ->
     FIBreachable v2 c ->
     ~ In v1 (PIT_list v2 c es) ->
     CMF v1 c (ForwardInterest v1 c :: es2) = None ->
     (forall C : Content c, ~ In (Data v2 v1 c C) ps) ->
     (forall C : Content c, ~ In (StoreData v1 c C) es1) ->
     In (Interest v1 v2 c) ps.
intros vs vt c' es ps H HFIB; induction H; intros esl esr Heq HFIBr HNIn HCMF HNData HNStore.
+destruct esl; simpl in Heq; now inversion Heq.
+destruct esl; simpl in Heq; inversion Heq; subst.
 apply in_or_app; right; eapply IHCCNprotocol; eauto.
  intros C Hn; apply HNData with C; apply in_or_app; now auto.
  intros C Hn; apply HNStore with C; simpl; now auto.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
  apply in_or_app; left.
   unfold FIB_Interest.
    apply in_split in HFIB; destruct HFIB as [f1 [f2 HFIB]]; rewrite HFIB.
    rewrite map_app; simpl.
    apply in_or_app; simpl; now auto.
   destruct esl; simpl in H6; inversion H6; clear H6; subst.
   assert (In (Interest vs vt c') (ps1 ++ Interest v v' c :: ps2)).
    eapply IHCCNprotocol; eauto.
     intro Hn; apply HNIn; simpl.
      destruct Node_eq_dec with vt v'; destruct Content_Name_eq_dec with c' c; simpl; now auto.
     intros C Hn; apply HNData with C; apply in_or_app; right.
      apply in_app_or in Hn; simpl in Hn; now intuition.
     intros C Hn; apply HNStore with C; simpl; now auto.
   apply in_app_or in H3; destruct H3 as [H3 | [H3 | H3]]; intuition.
    inversion H3; subst.
    simpl in HNIn.
    destruct Node_eq_dec with vt vt.
     destruct Content_Name_eq_dec with c' c'.
      elim HNIn; simpl; now auto.
      elim n; now auto.
     elim n; now auto.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
  assert (In (Interest vs vt c') (ps1 ++ Interest v v' c :: ps2)).
   eapply IHCCNprotocol; eauto.
    intro Hn; apply HNIn; simpl.
     destruct Node_eq_dec with vt v'; destruct Content_Name_eq_dec with c' c; simpl; now auto.
    intros C Hn; apply HNData with C; apply in_or_app.
     apply in_app_or in Hn; simpl in Hn; now intuition.
    intros C Hn; apply HNStore with C; simpl; now auto.
  apply in_app_or in H4; destruct H4 as [H4 | [H4 | H4]]; intuition.
   inversion H4; subst.
   simpl in HNIn.
   destruct Node_eq_dec with vt vt.
    destruct Content_Name_eq_dec with c' c'.
     elim HNIn; simpl; now auto.
     elim n; now auto.
    elim n; now auto.
+subst; assert (In (Interest vs vt c') (ps1 ++ Interest v v' c :: ps2)).
  eapply IHCCNprotocol; eauto.
   intros C Hn; apply HNData with C; apply in_or_app.
    apply in_app_or in Hn; simpl in Hn; now intuition.
   apply in_app_or in H2; destruct H2 as [H2 | [H2 | H2]]; intuition.
    inversion H2; subst.
    destruct HFIBr.
     destruct CMF_keep_InitCS with v c (esl ++ ForwardInterest vs c :: esr); auto.
      rewrite H0 in H4; now inversion H4.
     unfold FIB in H3.
      rewrite H1 in H3; simpl in H3; now inversion H3.
+subst; assert (In (Interest vs vt c') (ps1 ++ Interest v v' c :: ps2)).
  eapply IHCCNprotocol; eauto.
   intros C Hn; apply HNData with C; apply in_or_app.
    apply in_app_or in Hn; simpl in Hn; now intuition.
   apply in_app_or in H2; destruct H2 as [H2 | [H2 | H2]]; intuition.
    inversion H2; subst.
    elim HNIn; now auto.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
  assert (In (Interest vs vt c') (ps1 ++ Interest v v' c :: ps2)).
   eapply IHCCNprotocol; eauto.
    intros C' Hn; apply HNData with C'; right; apply in_or_app; apply in_app_or in Hn; simpl in Hn; intuition.
     now inversion H2.
    intros C' Hn; apply HNStore with C'; simpl; now auto.
    right; apply in_app_or in H1; apply in_or_app; simpl in H1; intuition.
     inversion H1; subst.
     elim HNData with C; simpl; now auto.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
  assert (In (Interest vs vt c') (ps1 ++ Data v v' c C :: ps2)).
   eapply IHCCNprotocol; eauto.
    intros C' Hn; apply HNData with C'; apply in_or_app; simpl; apply in_app_or in Hn; simpl in Hn; intuition.
     inversion H4; subst.
     elim HNStore with C; simpl; now auto.
    intros C' Hn; apply HNStore with C'; simpl; now auto.
    apply in_app_or in H3; apply in_or_app; simpl in H3; intuition.
     now inversion H3.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct esl; simpl in H6; inversion H6; clear H6; subst.
  assert (In (Interest vs vt c') (ps1 ++ Data v v' c C :: ps2)).
   eapply IHCCNprotocol; eauto.
    simpl in HNIn.
     destruct Node_eq_dec with vt v'.
      destruct Content_Name_eq_dec; subst.
       intro Hn.
        apply HNData with C.
        apply in_or_app; left.
        unfold PIT_Data.
        apply in_split in Hn; destruct Hn as [es' [es'' Hn]]; rewrite Hn.
        rewrite map_app; simpl.
        apply in_or_app; simpl; now auto.
       now auto.
      now auto.
    intros C' Hn; apply HNData with C'; apply in_or_app; simpl; apply in_app_or in Hn; simpl in Hn; intuition.
     inversion H4; subst.
     elim HNStore with C; simpl; now auto.
    intros C' Hn; apply HNStore with C'; simpl; now auto.
    apply in_app_or in H3; apply in_or_app; simpl in H3; intuition.
     now inversion H3.
+destruct esl; simpl in Heq; inversion Heq; clear Heq; subst.
 destruct esl; simpl in H6; inversion H6; clear H6; subst.
  assert (In (Interest vs vt c') (ps1 ++ Data v v' c C :: ps2)).
   eapply IHCCNprotocol; eauto.
    simpl in HNIn.
     destruct Node_eq_dec with vt v'.
      destruct Content_Name_eq_dec; subst.
       intro Hn.
        apply HNData with C.
        apply in_or_app; left.
        unfold PIT_Data.
        apply in_split in Hn; destruct Hn as [es' [es'' Hn]]; rewrite Hn.
        rewrite map_app; simpl.
        apply in_or_app; simpl; now auto.
       now auto.
      now auto.
    intros C' Hn; apply HNData with C'; apply in_or_app; simpl; apply in_app_or in Hn; simpl in Hn; intuition.
     inversion H4; subst.
     elim HNStore with C; simpl; now auto.
    intros C' Hn; apply HNStore with C'; simpl; now auto.
    apply in_app_or in H3; apply in_or_app; simpl in H3; intuition.
     now inversion H3.
+subst; assert (In (Interest vs vt c') (ps1 ++ Data v v' c C :: ps2)).
  eapply IHCCNprotocol; eauto.
   intros C' Hn; apply HNData with C'; apply in_or_app.
    apply in_app_or in Hn; simpl in Hn; intuition.
    inversion H3; subst.
    destruct ForwardInterest_PIT_list_not_nil with vs c' esl esr (ps1 ++ Data vt vs c' C :: ps2); auto.
    apply CMF_consistency; auto.
    apply CCN_reply_consistency with (ps1 ++ Data vt vs c' C :: ps2); now auto.
  apply in_app_or in H2; apply in_or_app; simpl in H2; intuition.
   now inversion H1.
Qed.


(** If PIT entries are not empty, the node has forwarded some interest packets *)
Lemma PIT_list_not_nil_ForwardInterest :
 forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   PIT_list v c es <> nil ->
   In_ForwardInterest v c es = true.
intros v c es ps H; revert v c; induction H; intros; simpl in *; auto;
 destruct (Node_eq_dec v0 v'); auto;
  destruct (Content_Name_eq_dec c0 c); subst; auto.
Qed.



End CCN_Protocol_Lemma_CM.




