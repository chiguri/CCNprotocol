(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Functor from Network Topology to correctness proofs of the CCN protocol *)

Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.
Require CCNProtocolLemma.


Module CCN_Protocol_Verification (N : CCNTopology.CCN_Network).
Import N.

Module Protocol_Lemma := CCNProtocolLemma.CCN_Protocol_Lemma N.
Import Protocol_Lemma.

Import Protocol.

(** All Interest packets are sent between connected nodes *)
Theorem CCN_Packet_Interest_Connected :
  forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   CCNprotocol es ps ->
    In (Interest v1 v2 c) ps ->
     Connected v1 v2.
Proof with eauto.
intros v1 v2 c es ps H; revert v1 v2 c; unfold Connected; induction H; simpl; intros; subst.
+contradiction.
+apply in_app_or in H2; destruct H2...
  eapply Broadcast_Interest_Connected...
+apply in_app_or in H4; destruct H4.
  eapply FIB_Interest_Connected...
  apply IHCCNprotocol with (c0 := c0).
   apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H5; apply in_or_app; destruct H5; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0).
  simpl in H2; destruct H2.
   inversion H1.
   apply in_app_or in H1; apply in_or_app; destruct H1; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H4; apply in_or_app; destruct H4; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H4; destruct H4.
   unfold PIT_Data in H3.
    elimtype False.
     eapply map_not_in.
      Focus 2. eauto.
      simpl; intros; intro.
       inversion H4.
   apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H4; destruct H4.
   unfold PIT_Data in H3.
    elimtype False.
     eapply map_not_in.
      Focus 2. eauto.
      simpl; intros; intro.
       inversion H4.
   apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0).
  apply in_app_or in H2; apply in_or_app; destruct H2; simpl...
Qed.



(** All PIT entries point only connected nodes *)
Lemma CCN_PIT_Connected :
 forall (v1 v2 : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps ->
   In (AddPIT v2 v1 c) es ->
   Connected v1 v2.
Proof with eauto.
intros; induction H; simpl in *...
+contradiction.
+destruct H0.
  inversion H0.
  eauto.
+destruct H0 as [ H0 | [ H0 | H0 ] ].
  inversion H0.
  inversion H0; subst.
   apply CCN_Packet_Interest_Connected with c es (ps1 ++ Interest v1 v2 c :: ps2)...
    apply in_or_app; simpl...
   eauto.
+destruct H0 as [ H0 | H0 ]...
  inversion H0; subst.
   apply CCN_Packet_Interest_Connected with c es (ps1 ++ Interest v1 v2 c :: ps2)...
    apply in_or_app; simpl...
+destruct H0 as [ H0 | H0 ]...
  inversion H0.
+destruct H0 as [ H0 | H0 ]...
  inversion H0.
+destruct H0 as [ H0 | [ H0 | H0 ] ].
  inversion H0.
  inversion H0.
  eauto.
+destruct H0 as [ H0 | [ H0 | H0 ] ].
  inversion H0.
  inversion H0.
  eauto.
Qed.




(** All data packets are sent between connected nodes *)
Theorem CCN_Packet_Data_Connected :
  forall (v1 v2 : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
   CCNprotocol es ps ->
    In (Data v1 v2 c C) ps ->
     Connected v1 v2.
Proof with eauto.
intros v1 v2 c C es ps H; revert v1 v2 c C; unfold Connected; induction H; simpl; intros; subst.
+contradiction.
+apply in_app_or in H2; destruct H2.
  unfold Broadcast_Interest in H1.
   elimtype False.
    eapply map_not_in.
     Focus 2. eauto.
      simpl; intros; intro.
       inversion H2.
  eauto.
+apply in_app_or in H4; destruct H4.
  unfold FIB_Interest in H3.
   elimtype False.
    eapply map_not_in.
     Focus 2. eauto.
      simpl; intros; intro.
       inversion H4.
  apply IHCCNprotocol with (c0 := c0) (C := C).
   apply in_or_app; apply in_app_or in H3; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0) (C := C).
  apply in_or_app; apply in_app_or in H5; destruct H5; simpl...
+apply IHCCNprotocol with (c0 := c0) (C := C).
  apply in_or_app; apply in_app_or in H3; destruct H3; simpl...
+apply IHCCNprotocol with (c0 := c0) (C := C).
  apply in_or_app; apply in_app_or in H3; destruct H3; simpl...
+simpl in H2; destruct H2.
  inversion H1; subst.
   apply CCN_Packet_Interest_Connected with (v1 := v2) (v2 := v1) (c := c0) in H.
    apply Connected_sym in H.
     unfold Connected in H...
    apply in_or_app; simpl...
  apply IHCCNprotocol with (c0 := c0) (C := C0). (* we use C, but printed as C0...? *)
   apply in_or_app; simpl; apply in_app_or in H1; destruct H1...
+apply IHCCNprotocol with (c0 := c0) (C0 := C0).
  apply in_or_app; simpl; apply in_app_or in H4; destruct H4...
+apply in_app_or in H4; destruct H4.
  destruct Node_eq_dec with v1 v'.
   subst; apply In_PIT_Data_In_PIT in H3.
    eapply In_PIT_list_In_AddPIT in H3...
     apply Connected_sym.
      eapply CCN_PIT_Connected...
   unfold PIT_Data in H3.
    elimtype False; eapply map_not_in.
     Focus 2. eauto.
     intros; simpl; intro; elim n.
      inversion H4; auto.
  apply IHCCNprotocol with (c0 := c0) (C0 := C0).
   apply in_or_app; simpl; apply in_app_or in H3; destruct H3...
+apply in_app_or in H4; destruct H4.
  destruct Node_eq_dec with v1 v'.
   subst; apply In_PIT_Data_In_PIT in H3.
    eapply In_PIT_list_In_AddPIT in H3...
     apply Connected_sym.
      eapply CCN_PIT_Connected...
   unfold PIT_Data in H3.
    elimtype False; eapply map_not_in.
     Focus 2. eauto.
     intros; simpl; intro; elim n.
      inversion H4; auto.
  apply IHCCNprotocol with (c0 := c0) (C0 := C0).
   apply in_or_app; simpl; apply in_app_or in H3; destruct H3...
+apply IHCCNprotocol with (c0 := c0) (C0 := C0).
  apply in_or_app; simpl; apply in_app_or in H2; destruct H2...
Qed.






(** Forward lemma for forwarding interest packets *)
Lemma CCN_Forward_Interest :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   FIBreachable v c ->
    CCNprotocol (ForwardInterest v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ ForwardInterest v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) (es' ++ ForwardInterest v c :: es))
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ ForwardInterest v c :: es) ps'').
Proof with eauto.
intros v c es ps H; revert es ps; induction H; intros.
 elim (InitCS_Content_get _ _ _ _ H0 H).
  eapply ForwardInterest_Not_Content_get...
 case_eq (Content_get v1 c (es' ++ ForwardInterest v1 c :: es)); intros.
  left; destruct (Content_get_InitCS_or_StoreData _ _ _ _ _ H2 H3).
   elim (InitCS_Content_get _ _ _ _ H1 H4).
    eapply ForwardInterest_Not_Content_get...
   exists c0; auto.
  right; destruct in_dec_forward with v2 c (es' ++ ForwardInterest v1 c :: es).
   destruct (in_split _ _ i) as [ es1 [es2 H4 ]].
    assert (CCNprotocol (es1 ++ ForwardInterest v2 c :: es2) ps').
     rewrite <- H4; auto.
     destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H5).
      destruct (IHFIBreachable _ _ H6 _ _ H5) as [ [ C H7 ] | [ C [ es0 [ ps0 H7 ] ] ] ].
       assert (H8 := StoreData_Content_get _ _ _ _ _ H5 H7).
        apply option_None_Some in H8; destruct H8.
         rewrite <- H4 in *.
          destruct Content_get_Data_or_Interest with v1 v2 c x0 es' es ps'...
           exists x0; apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps')...
            right; apply in_or_app; simpl...
           destruct (in_split _ _ H9) as [ ps1 [ ps2 H10 ] ]; subst.
            assert (H10 := ccn_reply_data _ _ _ _ _ _ _ _ H2 H8 eq_refl).
             exists x0; apply exists_longer with (l := [ReplyData v2 c]).
              apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c x0 :: l) ps'')).
               apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v1 c x0 :: ps1 ++ ps2)...
                right; apply in_or_app; right; apply in_or_app; simpl...
                simpl...
       assert (In (StoreData v2 c C) (StoreData v2 c C :: es0 ++ es1 ++ ForwardInterest v2 c :: es2)) by (simpl; auto).
        assert (H9 := StoreData_Content_get _ _ _ _ _ H7 H8).
         apply option_None_Some in H9; destruct H9.
          case_eq (Content_get v1 c (StoreData v2 c C :: es0 ++ es1 ++ ForwardInterest v2 c :: es2)); intros.
           destruct (Content_get_app_In_Store_Data _ _ (StoreData v2 c C :: es0) _ H3).
            rewrite H4 in *; simpl app; intro H11; rewrite H10 in H11; discriminate.
            destruct (in_split _ _ H11) as [ l1 [ l2 H12 ] ].
             rewrite app_comm_cons in H7; rewrite H12 in H7.
              rewrite <- app_assoc in H7; simpl in H7.
               destruct (split_StoreData_CCNprotocol _ _ _ _ _ _ H7).
                rewrite H4; exists x1; exists l2; exists x2...
           exists x0.
            destruct (Content_get_Data_or_Interest v1 v2 c x0 (StoreData v2 c C :: es0 ++ es') es ps0)...
             simpl; rewrite <- app_assoc; rewrite H4...
             simpl; rewrite <- app_assoc; rewrite H4...
             simpl; rewrite <- app_assoc; rewrite H4...
             apply exists_longer with (l := StoreData v2 c C :: es0).
              apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c x0 :: l) ps'')).
               apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps0)...
                right; apply in_or_app; right; apply in_or_app; simpl...
                rewrite H4; simpl...
                simpl.
                 destruct Node_eq_dec with v1 v2.
                  subst; rewrite H9 in H10; discriminate.
                  simpl in H10; destruct Node_eq_dec with v1 v2.
                   elim n...
                   rewrite H4...
             apply exists_longer with (l := ReplyData v2 c :: StoreData v2 c C :: es0).
              apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c x0 :: l) ps'')).
               destruct (in_split _ _ H11) as [ l1 [ l2 H12 ] ].
                rewrite H12 in H7; assert (H13 := ccn_reply_data _ _ _ _ _ _ _ _ H7 H9 eq_refl).
                 apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v1 c x0 :: l1 ++ l2)...
                  right; apply in_or_app; right; apply in_or_app; simpl...
                  rewrite H4; simpl...
                  simpl.
                   destruct Node_eq_dec with v1 v2.
                    subst; rewrite H9 in H10; discriminate.
                    simpl in H10; destruct Node_eq_dec with v1 v2.
                     elim n...
                     rewrite H4...
                  simpl...
  case_eq (Content_get v2 c (es' ++ ForwardInterest v1 c :: es)); intros.
   destruct (Content_get_Data_or_Interest _ _ _ _ _ _ _ H2 H H0 H4 H3).
    exists c0; apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps')...
     right; apply in_or_app; simpl...
    exists c0; apply exists_longer with (l := [ReplyData v2 c]).
     apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c c0 :: l) ps'')).
      destruct (in_split _ _ H5) as [ l1 [ l2 H6 ] ]; subst.
       assert (H6 := ccn_reply_data _ _ _ _ _ _ _ _ H2 H4 eq_refl).
        simpl.
         apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v1 c c0 :: l1 ++ l2)...
          right; simpl; right; apply in_or_app; simpl...
          simpl...
   assert (PIT_list v2 c (es' ++ ForwardInterest v1 c :: es) = []).
    case_eq (PIT_list v2 c (es' ++ ForwardInterest v1 c :: es)); intros.
     auto.
     elim n.
      eapply PIT_list_not_nil_ForwardInterest...
       intro H6; rewrite H5 in H6; discriminate.
    destruct (Not_Content_get_PIT_or_Interest _ v2 _ _ _ _ H2)...
     assert (H7 := In_AddPIT_In_PIT_list _ _ _ _ _ H2 H4 H6).
      rewrite H5 in H7; simpl in H7; contradiction.
     destruct (in_split _ _ H6) as [ ps1 [ ps2 H7 ] ]; subst.
      assert (FIB_list v2 c <> nil).
       intro; destruct H0.
        eapply InitCS_Content_get.
         exact H2.
         eauto.
         auto.
        unfold FIB in H0.
         rewrite H7 in H0; simpl in H0...
       assert (H8 := ccn_forward_interest _ _ _ _ _ _ _ H2 H4 H5 H7 eq_refl).
        destruct (IHFIBreachable _ _ H8 nil _ H8); clear IHFIBreachable; simpl in *.
         destruct H9 as [ C [ H9 | [ H9 | H9 ] ] ].
          discriminate.
          discriminate.
          elim (StoreData_Content_get _ _ _ _ _ H2 H9)...
         destruct H9 as [ C [ es'' [ ps'' H9 ] ] ].
          case_eq (Content_get v1 c
                   (StoreData v2 c C :: es'' ++
                       ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++
                       ForwardInterest v1 c :: es)); intros.
           assert (exists C0 : Content c, In (StoreData v1 c C0) (StoreData v2 c C :: es'')).
            apply Content_get_app_In_Store_Data with (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es)...
             simpl app; intro H11; rewrite H11 in H10; discriminate.
            destruct H11 as [ C0 H11 ].
             destruct (in_split _ _ H11) as [ es1 [ es2 H12 ] ].
              rewrite app_comm_cons in H9.
               rewrite H12 in H9; rewrite <- app_assoc in H9; simpl app in H9.
                destruct (split_StoreData_CCNprotocol _ _ _ _ _ _ H9).
                 exists C0; exists (es2 ++ ForwardInterest v2 c :: [AddPIT v2 v1 c]); exists x.
                  rewrite <- app_assoc; simpl...
           assert (H11 := StoreData_Content_get v2 c C _ _ H9 (or_introl eq_refl)).
            apply option_None_Some in H11; destruct H11.
             repeat rewrite app_comm_cons in H9; rewrite app_assoc in H9.
              destruct (Content_get_Data_or_Interest _ _ _ x _ _ _ H9 H)...
               rewrite <- app_assoc; simpl app...
               rewrite <- app_assoc; simpl app...
               exists x; apply exists_longer with (l := StoreData v2 c C :: es'' ++ ForwardInterest v2 c :: [AddPIT v2 v1 c]).
                apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c x :: l) ps'')).
                 destruct (in_split _ _ H12) as [ l1 [ l2 H13 ] ].
                  apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps'')...
                   right; apply in_or_app; right; apply in_or_app; simpl...
                   simpl; rewrite <- app_assoc; simpl.
                    rewrite <- app_assoc in H9...
                   simpl app; rewrite <- app_assoc; simpl app...
               destruct (in_split _ _ H12) as [ ps3 [ ps4 H13 ] ]; subst.
                rewrite <- app_assoc in H9; simpl app in H9; assert (H14 := ccn_reply_data _ _ _ _ _ _ _ _ H9 H11 eq_refl).
                 exists x; apply exists_longer with (l := ReplyData v2 c :: StoreData v2 c C :: es'' ++ ForwardInterest v2 c :: [AddPIT v2 v1 c]).
                  apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v1 c x :: l) ps'')).
                   apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v1 c x :: ps3 ++ ps4).
                    right; apply in_or_app; right; apply in_or_app; simpl...
                    simpl app; rewrite <- app_assoc...
                    simpl app; rewrite <- app_assoc...
                    simpl...
Qed.






(** Forward lemma for requests *)
Theorem CCN_Forward_Request :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   (exists v' : Node, Connected v v' /\ FIBreachable v' c) ->
    CCNprotocol (Request v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ Request v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) (es' ++ Request v c :: es))
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ Request v c :: es) ps'').
Proof with eauto.
intros; destruct H as [ v2 [ H H2 ] ].
 assert (Content_get v c (Request v c :: es) = None) by (eapply Request_Not_Content_get; eauto).
  case_eq (Content_get v c (es' ++ Request v c :: es)); intros.
   left; destruct (Content_get_app_In_Store_Data _ _ es' _ H3).
    rewrite H4; intro H5; discriminate.
    destruct (in_split _ _ H5) as [ es0 [ es1 H6 ] ]; subst.
     exists x; apply in_or_app; left; apply in_or_app; simpl...
   right; destruct in_dec_forward with v2 c (es' ++ Request v c :: es).
    destruct (in_split _ _ i) as [ es1 [ es2 H5 ] ].
     rewrite H5 in H1; destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H1).
      destruct (CCN_Forward_Interest _ _ _ _ H2 H6 _ _ H1) as [ [ C H7 ] | [ C [ es0 [ ps0 H7 ] ] ] ].
       assert (H8 := StoreData_Content_get _ _ _ _ _ H1 H7).
        apply option_None_Some in H8; destruct H8.
         rewrite <- H5 in *; destruct (Request_Content_get_Data_or_Interest _ _ _ _ _ _ _ H1 H H2 H8 H4).
          destruct (in_split _ _ H9) as [ ps1 [ ps2 H10 ] ].
           exists x0; apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps')...
            left; apply in_or_app; simpl...
          destruct (in_split _ _ H9) as [ ps1 [ ps2 H10 ] ]; subst.
           assert (H10 := ccn_reply_data _ _ _ _ _ _ _ _ H1 H8 eq_refl).
            exists x0; apply exists_longer with (l := [ReplyData v2 c]).
             apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c x0 :: l) ps'')).
              apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v c x0 :: ps1 ++ ps2)...
               left; apply in_or_app; right; apply in_or_app; simpl...
               simpl...
       case_eq (Content_get v c (StoreData v2 c C :: es0 ++ es1 ++ ForwardInterest v2 c :: es2)); intros.
        destruct (Content_get_app_In_Store_Data _ _ (StoreData v2 c C :: es0) _ H4).
         rewrite H5; simpl app; rewrite H8; intro; discriminate.
         destruct (in_split _ _ H9) as [ es3 [ es4 H10 ] ].
          exists x0; rewrite app_comm_cons in H7; rewrite H10 in H7.
           rewrite <- app_assoc in H7; simpl in H7; destruct (split_StoreData_CCNprotocol _ _ _ _ _ _ H7).
            exists es4; exists x1.
             rewrite H5; auto.
        assert (In (StoreData v2 c C) (StoreData v2 c C :: es0 ++ es1 ++ ForwardInterest v2 c :: es2)).
         simpl...
         assert (H10 := StoreData_Content_get v2 c C _ _ H7 H9).
          apply option_None_Some in H10; destruct H10.
           rewrite <- H5 in *; rewrite app_comm_cons in H7; rewrite app_assoc in H7.
            rewrite app_comm_cons in H8, H10; rewrite app_assoc in H8, H10.
             destruct (Request_Content_get_Data_or_Interest _ _ _ _ _ _ _ H7 H H2 H10 H8).
              exists x0; destruct (in_split _ _ H11) as [ es3 [ es4 H12 ] ].
               apply exists_longer with (l := StoreData v2 c C :: es0).
                apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c x0 :: l) ps'')).
                 simpl; apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps0)...
                  left; simpl; right; apply in_or_app; right; apply in_or_app; simpl...
                  simpl in H7; rewrite <- app_assoc in H7...
                  simpl app in H8; rewrite <- app_assoc in H8...
             destruct (in_split _ _ H11) as [ ps1 [ ps2 H12 ] ]; subst.
              assert (H13 := ccn_reply_data _ _ _ _ _ _ _ _ H7 H10 eq_refl).
               exists x0; apply exists_longer with (l := ReplyData v2 c :: StoreData v2 c C :: es0).
                apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c x0 :: l) ps'')).
                 apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v c x0 :: ps1 ++ ps2)...
                  left; apply in_or_app; right; apply in_or_app; simpl...
                  simpl; simpl in H13; rewrite <- app_assoc in H13...
                  simpl app in H8; rewrite <- app_assoc in H8; simpl...
                  simpl...
  case_eq (Content_get v2 c (es' ++ Request v c :: es)); intros.
   destruct (Request_Content_get_Data_or_Interest _ _ _ _ _ _ _ H1 H H2 H5 H4).
    exists c0; apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps')...
     left; apply in_or_app; simpl...
    exists c0; apply exists_longer with (l := [ReplyData v2 c]).
     apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c c0 :: l) ps'')).
      destruct (in_split _ _ H6) as [ l1 [ l2 H7 ] ]; subst.
       assert (H7 := ccn_reply_data _ _ _ _ _ _ _ _ H1 H5 eq_refl).
        simpl.
         apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v c c0 :: l1 ++ l2)...
          left; simpl; right; apply in_or_app; simpl...
          simpl...
   assert (PIT_list v2 c (es' ++ Request v c :: es) = []).
    case_eq (PIT_list v2 c (es' ++ Request v c :: es)); intros.
     auto.
     elim n.
      eapply PIT_list_not_nil_ForwardInterest...
       rewrite H6; intro; discriminate.
    destruct (Request_Not_Content_get_PIT_or_Interest _ v2 _ _ _ _ H1)...
     assert (H8 := In_AddPIT_In_PIT_list _ _ _ _ _ H1 H5 H7).
      rewrite H6 in H8; simpl in H8; contradiction.
     destruct (in_split _ _ H7) as [ ps1 [ ps2 H8 ] ]; subst.
      assert (FIB_list v2 c <> nil).
       intro; destruct H2.
        eapply InitCS_Content_get.
         exact H1.
         eauto.
         auto.
        unfold FIB in H2.
         rewrite H8 in H2; simpl in H2...
       assert (H9 := ccn_forward_interest _ _ _ _ _ _ _ H1 H5 H6 H8 eq_refl).
        destruct (CCN_Forward_Interest _ _ _ _ H2 H9 nil _ H9); simpl in *.
         destruct H10 as [ C [ H10 | [ H10 | H10 ] ] ].
          discriminate.
          discriminate.
          elim (StoreData_Content_get _ _ _ _ _ H1 H10)...
         destruct H10 as [ C [ es'' [ ps'' H10 ] ] ].
          case_eq (Content_get v c
                   (StoreData v2 c C :: es'' ++
                       ForwardInterest v2 c :: AddPIT v2 v c :: es' ++
                       Request v c :: es)); intros.
           assert (exists C0 : Content c, In (StoreData v c C0) (StoreData v2 c C :: es'')).
            apply Content_get_app_In_Store_Data with (ForwardInterest v2 c :: AddPIT v2 v c :: es' ++ Request v c :: es)...
             simpl app; intro H12; rewrite H12 in H11; discriminate.
            destruct H12 as [ C0 H12 ].
             destruct (in_split _ _ H12) as [ es1 [ es2 H13 ] ].
              rewrite app_comm_cons in H10.
               rewrite H13 in H10; rewrite <- app_assoc in H10; simpl app in H10.
                destruct (split_StoreData_CCNprotocol _ _ _ _ _ _ H10).
                 exists C0; exists (es2 ++ ForwardInterest v2 c :: [AddPIT v2 v c]); exists x.
                  rewrite <- app_assoc; simpl...
           assert (H12 := StoreData_Content_get v2 c C _ _ H10 (or_introl eq_refl)).
            apply option_None_Some in H12; destruct H12.
             repeat rewrite app_comm_cons in H10; rewrite app_assoc in H10.
              destruct (Request_Content_get_Data_or_Interest _ _ _ x _ _ _ H10 H)...
               rewrite <- app_assoc; simpl app...
               rewrite <- app_assoc; simpl app...
               exists x; apply exists_longer with (l := StoreData v2 c C :: es'' ++ ForwardInterest v2 c :: [AddPIT v2 v c]).
                apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c x :: l) ps'')).
                 destruct (in_split _ _ H13) as [ l1 [ l2 H14 ] ].
                  apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := ps'')...
                   left; apply in_or_app; right; apply in_or_app; simpl...
                   simpl; rewrite <- app_assoc; simpl.
                    rewrite <- app_assoc in H10...
                   simpl app; rewrite <- app_assoc; simpl app...
               destruct (in_split _ _ H13) as [ ps3 [ ps4 H14 ] ]; subst.
                rewrite <- app_assoc in H10; simpl app in H10; assert (H14 := ccn_reply_data _ _ _ _ _ _ _ _ H10 H12 eq_refl).
                 exists x; apply exists_longer with (l := ReplyData v2 c :: StoreData v2 c C :: es'' ++ ForwardInterest v2 c :: [AddPIT v2 v c]).
                  apply (exists_app_assoc_r (fun l => exists ps'' : list Packet, CCNprotocol (StoreData v c x :: l) ps'')).
                   apply Request_or_Forward_with_Data_StoreData with (v2 := v2) (ps := Data v2 v c x :: ps3 ++ ps4).
                    left; apply in_or_app; right; apply in_or_app; simpl...
                    simpl app; rewrite <- app_assoc...
                    simpl app; rewrite <- app_assoc...
                    simpl...
Qed.



(** If FIBreachable for any nodes, any contents, we can omit conditions from theorem *) 
Theorem CCN_Forward_Request' :
  (forall (v : Node) (c : Content_Name), FIBreachable v c) ->
   forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
    CCNprotocol (Request v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ Request v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) (es' ++ Request v c :: es))
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ Request v c :: es) ps'').
Proof with auto.
intros.
apply CCN_Forward_Request with (ps := ps) (ps' := ps')...
 destruct (H v c).
  assert (H3 := Request_Not_Content_get v c es ps H0).
   elim (InitCS_Content_get _ _ _ _ H0 H2)...
  exists v2; split...
   apply FIB_Connected with (c := c)...
Qed.



(** Backward lemma *)
Theorem CCN_Backward :
  forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
   CCNprotocol (StoreData v c C :: es) ps ->
    In (Request v c) es \/ In (ForwardInterest v c) es.
intros v c C es.
remember (StoreData v c C :: es) as es'.
intros ps H.
revert v c C es Heqes'; induction H; intros;
 (inversion Heqes'; fail || eauto).
 subst; auto.
 subst; right; right.
 eapply PIT_list_not_nil_ForwardInterest; eauto.
 subst; left; right; auto.
Qed.




End CCN_Protocol_Verification.



