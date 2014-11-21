Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.
Require CCNProtocolLemma.


Module CCN_Protocol_Verification (N : CCNTopology.CCN_Network).

Module Protocol_Lemma := CCNProtocolLemma.CCN_Protocol_Lemma N.
Import Protocol_Lemma.




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
           admit.
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






Theorem CCN_Forward_Request :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   FIBreachable v c ->
    CCNprotocol (Request v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ Request v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) (es' ++ Request v c :: es))
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ Request v c :: es) ps'').
Admitted.




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



