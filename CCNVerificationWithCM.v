(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Functor from Network Topology to correctness proofs of the CCN protocol with Content Management *)

Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.

Require CCNContentManagement.
Require CCNProtocolWithCM.
Require CCNProtocolLemmaWithCM.

Module CCN_Protocol_Verification_CM (N : CCNContentManagement.CCN_Content_Management).
Import N.
Import Topology.

Module Protocol_Lemma := CCNProtocolLemmaWithCM.CCN_Protocol_Lemma_CM N.
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
  apply in_app_or in H3; apply in_or_app; destruct H3; simpl...
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
    apply In_PIT_list_In_AddPIT in H3.
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
  apply in_or_app; simpl; apply in_app_or in H3; destruct H3...
Qed.






(** Forward lemma for forwarding interest packets *)
Lemma CCN_Forward_Interest :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   FIBreachable v c ->
    CCNprotocol (ForwardInterest v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ ForwardInterest v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) es')
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ ForwardInterest v c :: es) ps'').
Proof with eauto.
intros v c es ps H; revert es ps; induction H; intros.
 destruct (CMF_keep_InitCS _ _ H (ForwardInterest v c :: es)).
  erewrite ForwardInterest_Not_CMF in H2...
   now inversion H2.
 assert (CMF v1 c (ForwardInterest v1 c :: es) = None).
 {
  eapply ForwardInterest_Not_CMF...
 }
 destruct Node_eq_dec with v1 v2.
  subst; eauto.
  destruct in_dec_storedata with v1 c es'.
   now auto.
   assert (CMF v1 c (es' ++ ForwardInterest v1 c :: es) = None).
   {
    apply CMF_consistency; auto.
    eapply CCN_reply_consistency...
   }
   right.
   destruct in_dec_datapacket with v2 v1 c ps'.
    destruct e as [C i]; destruct (in_split _ _ i) as [ ps1 [ps2 H5 ]]; subst; clear i.
     exists C.
     assert (PIT_list v1 c (es' ++ ForwardInterest v1 c :: es) <> []).
     {
      eapply ForwardInterest_PIT_list_not_nil; now eauto.
     }
     exists [ForwardData v1 c], (PIT_Data v1 c C (es' ++ ForwardInterest v1 c :: es) ++ ps1 ++ ps2); simpl; case_eq (In_Request v1 c (es' ++ ForwardInterest v1 c :: es)); intros.
      eapply ccn_store_forward; eauto.
      eapply ccn_forward_data; eauto.
    destruct in_dec_PIT_list with v2 v1 c (ForwardInterest v1 c :: es).
     destruct (PIT_list_ForwardInterest v1 v2 c _ ps H1 i) as [es1 [es2 [Heq Hi]]].
      assert (CCNprotocol (es2 ++ ForwardInterest v2 c :: es1) ps).
      {
       rewrite <- Heq; now auto.
      }
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H5).
      destruct (IHFIBreachable es1 x H6 (es' ++ es2) ps') as [IH | IH].
       rewrite <- app_assoc; rewrite <- Heq; now auto.
       destruct IH as [C IH]; apply in_app_or in IH; destruct IH as [IH | IH]; [ | elim Hi with C; now auto ].
        apply StoreData_tail in IH.
        destruct IH as [esr [esl [[C' IHl] IH]]]; subst.
        rewrite <- app_assoc in H2, H4; simpl in H2, H4.
         assert (H7 := split_StoreData_CCNprotocol _ _ _ _ _ _ H2); destruct H7 as [ps'' H7].
         destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ ForwardInterest v1 c :: es) ps'' esr (ForwardInterest v1 c :: es) v2 c C'; auto.
          intro H8; rewrite H8 in i; simpl in i; now auto.
          rewrite H8 in H2.
           destruct esr; simpl in H8; inversion H8; subst.
           destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ ForwardInterest v1 c :: es) ps''.
            simpl in *; now auto.
           destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl ++ StoreData v2 c C' :: ForwardData v2 c :: esr ++ ForwardInterest v1 c :: es) ps' (esr ++ ForwardInterest v1 c :: es) esl; auto.
            destruct PIT_list_no_StoreData_append with (esr ++ ForwardInterest v1 c :: es) x0 esr (ForwardInterest v1 c :: es) v2 c; auto.
             intros C'' Hn; apply IH with C''; simpl; now auto.
             rewrite H10; apply in_or_app; now auto.
            right; apply ForwardInterest_PIT_list_not_nil with x0; auto.
             apply CMF_consistency.
              eapply CCN_reply_consistency; now eauto.
              now auto.
              intros C'' Hn; apply n0 with C''; apply in_or_app; simpl; now auto.
             intros C'' Hn; apply n0 with C''; apply in_or_app; simpl; now auto.
            destruct H10.
             elim n0 with x1; apply in_or_app; now auto.
            destruct H10.
             elim n1 with x1; now auto.
       destruct IH as [C [es'' [ps'' IH]]].
       destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'' ++ es').
        destruct e as [C' HIn].
         destruct HIn as [HIn | HIn].
          inversion HIn; subst; elim n; now auto.
          apply in_app_or in HIn; destruct HIn as [HIn | HIn].
           apply in_split in HIn; destruct HIn as [esl [esr ?]].
            rewrite H7 in IH.
            repeat rewrite <- app_assoc in IH; simpl in IH.
            rewrite <- Heq in IH.
            exists C', esr; apply split_StoreData_CCNprotocol with (StoreData v2 c C :: esl) ps''.
            simpl; now auto.
           elim n0 with C'; now auto.
        destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'' ++ es') as [esr' [esl' [[C' Heq'] HNIn]]].
         left; now auto.
         repeat rewrite <- app_assoc in IH; rewrite app_assoc with _ _ es' _ in IH.
         rewrite app_comm_cons in IH; rewrite Heq' in IH.
         rewrite <- Heq in IH.
         rewrite <- app_assoc in IH; simpl in IH.
         destruct split_StoreData_CCNprotocol with v2 c C' esl' (esr' ++ ForwardInterest v1 c :: es) ps''; auto.
         destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr' ++ ForwardInterest v1 c :: es) x0 esr' (ForwardInterest v1 c :: es) v2 c C'; auto.
          intro He; rewrite He in i; simpl in i; now auto.
          destruct esr'; inversion H8; subst.
          destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr' ++ ForwardInterest v1 c :: es) x0; simpl; auto.
          destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ ForwardInterest v1 c :: es) ps'' (esr' ++ ForwardInterest v1 c :: es) esl'; auto.
           destruct PIT_list_no_StoreData_append with (esr' ++ ForwardInterest v1 c :: es) x1 esr' (ForwardInterest v1 c :: es) v2 c; auto.
            intros C'' Hn; apply HNIn with C''; simpl; now auto.
            rewrite H10; apply in_or_app; now auto.
           right; apply ForwardInterest_PIT_list_not_nil with x1; auto.
            apply CMF_consistency; auto.
             apply CCN_reply_consistency with x1; now auto.
             intros C'' Hn; rewrite Heq' in n2; apply n2 with C''; apply in_or_app; simpl; now auto.
            intros C'' Hn; rewrite Heq' in n2; apply n2 with C''; apply in_or_app; simpl; now auto.
           destruct H10 as [C'' H10].
            elim n2 with C''; rewrite Heq'; apply in_or_app; simpl; now auto.
           destruct H10 as [C'' H10].
            apply in_split in H10; destruct H10 as [ps1 [ps2 ?]]; subst.
            exists C'', (ForwardData v1 c :: StoreData v2 c C :: es''), (PIT_Data v1 c C'' (StoreData v2 c C :: es'' ++ es' ++ ForwardInterest v1 c :: es) ++ ps1 ++ ps2).
            simpl; rewrite app_assoc; rewrite app_comm_cons; rewrite Heq'.
            repeat rewrite <- app_assoc; simpl.
            case_eq (In_Request v1 c (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ ForwardInterest v1 c :: es)); intro.
             simpl; apply ccn_store_forward with v2 ps1 ps2; auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply CMF_consistency; auto.
                rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                rewrite <- Heq'; now auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               rewrite <- Heq'; intro.
               destruct PIT_list_no_StoreData_append with ((StoreData v2 c C :: es'' ++ es') ++ ForwardInterest v1 c :: es) (ps1 ++ Data v2 v1 c C'' :: ps2) (StoreData v2 c C :: es'' ++ es') (ForwardInterest v1 c :: es) v1 c; auto.
                rewrite Heq'; rewrite <- app_assoc; simpl; now auto.
                elim ForwardInterest_PIT_list_not_nil with v1 c (nil : list Event) es ps; simpl; auto.
                 rewrite H11 in H12; simpl in H12; destruct (PIT_list v1 c es).
                  now auto.
                  destruct x2; simpl in H12; now inversion H12.
             simpl; apply ccn_forward_data with v2 ps1 ps2; auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply CMF_consistency; auto.
                rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                rewrite <- Heq'; now auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               rewrite <- Heq'; intro.
               destruct PIT_list_no_StoreData_append with ((StoreData v2 c C :: es'' ++ es') ++ ForwardInterest v1 c :: es) (ps1 ++ Data v2 v1 c C'' :: ps2) (StoreData v2 c C :: es'' ++ es') (ForwardInterest v1 c :: es) v1 c; auto.
                rewrite Heq'; rewrite <- app_assoc; simpl; now auto.
                elim ForwardInterest_PIT_list_not_nil with v1 c (nil : list Event) es ps; simpl; auto.
                 rewrite H11 in H12; simpl in H12; destruct (PIT_list v1 c es).
                  now auto.
                  destruct x2; simpl in H12; now inversion H12.
     destruct in_dec_PIT_list with v2 v1 c (es' ++ ForwardInterest v1 c :: es).
      destruct (PIT_list_ForwardInterest v1 v2 c _ _ H2 i) as [es1 [es2 [Heq Hi]]].
      assert (CCNprotocol (es2 ++ ForwardInterest v2 c :: es1) ps').
      {
       rewrite <- Heq; now auto.
      }
      destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H5).
      destruct (IHFIBreachable es1 x H6 es2 ps') as [IH | IH]; auto.
       destruct IH as [C IH]; elim Hi with C; now auto.
       destruct IH as [C [es'' [ps'' IH]]].
        destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'' ++ es').
         destruct e as [C' [HIn | HIn]].
          inversion HIn; subst; elim n; now auto.
          apply in_app_or in HIn; destruct HIn as [HIn | HIn].
           apply in_split in HIn; destruct HIn as [esl [esr ?]].
            rewrite H7 in IH.
            repeat rewrite <- app_assoc in IH; simpl in IH.
            rewrite <- Heq in IH.
            exists C', esr; apply split_StoreData_CCNprotocol with (StoreData v2 c C :: esl) ps''.
            simpl; now auto.
           elim n0 with C'; now auto.
         destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr' [esl' [[C' Heq'] HNIn]]].
          left; now auto.
          rewrite <- Heq in IH.
           rewrite app_comm_cons in IH; rewrite Heq' in IH.
           rewrite <- app_assoc in IH; simpl in IH.
           destruct split_StoreData_CCNprotocol with v2 c C' esl' (esr' ++ es' ++ ForwardInterest v1 c :: es) ps''; auto.
           destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr' ++ es' ++ ForwardInterest v1 c :: es) x0 esr' (es' ++ ForwardInterest v1 c :: es) v2 c C'; auto.
            intro He; rewrite He in i; simpl in i; now auto.
            destruct esr'; inversion H8; subst.
             destruct es'; inversion H10; subst.
              simpl in i.
               destruct Node_eq_dec with v2 v2.
                destruct Content_Name_eq_dec with c c.
                 simpl in i; contradiction.
                 elim n4; now auto.
                elim n4; now auto.
             destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr' ++ es' ++ ForwardInterest v1 c :: es) x0; simpl; auto.
              destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ es' ++ ForwardInterest v1 c :: es) ps'' (esr' ++ es' ++ ForwardInterest v1 c :: es) esl'; auto.
               destruct PIT_list_no_StoreData_append with (esr' ++ es' ++ ForwardInterest v1 c :: es) x1 esr' (es' ++ ForwardInterest v1 c :: es) v2 c; auto.
                intros C'' Hn; apply HNIn with C''; simpl; now auto.
                rewrite H10; apply in_or_app; now auto.
               right; rewrite app_assoc; apply ForwardInterest_PIT_list_not_nil with x1; auto.
                rewrite <- app_assoc; now auto.
                apply CMF_consistency; auto.
                 rewrite <- app_assoc; apply CCN_reply_consistency with x1; now auto.
                 intros C'' Hn; apply in_app_or in Hn; destruct Hn.
                  apply n3 with C''; rewrite app_comm_cons; rewrite Heq'; apply in_or_app; now intuition.
                  apply n0 with C''; now auto.
                intros C'' Hn; apply in_app_or in Hn; destruct Hn.
                 apply n3 with C''; rewrite app_comm_cons; rewrite Heq'; apply in_or_app; now intuition.
                 apply n0 with C''; now auto.
               destruct H10 as [C'' H10].
                elim n3 with C''; rewrite app_comm_cons; rewrite Heq'; apply in_or_app; left; apply in_or_app; simpl; now auto.
               destruct H10 as [C'' H10].
                apply in_split in H10; destruct H10 as [ps1 [ps2 ?]]; subst.
                exists C'', (ForwardData v1 c :: StoreData v2 c C :: es''), (PIT_Data v1 c C'' (StoreData v2 c C :: es'' ++ es' ++ ForwardInterest v1 c :: es) ++ ps1 ++ ps2).
                simpl; rewrite app_comm_cons; rewrite Heq'.
                repeat rewrite <- app_assoc; simpl.
                case_eq (In_Request v1 c (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ es' ++ ForwardInterest v1 c :: es)); intro.
                 simpl; apply ccn_store_forward with v2 ps1 ps2; auto.
                  repeat rewrite app_comm_cons; rewrite app_assoc.
                   apply CMF_consistency; auto.
                    rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                    rewrite <- Heq'; intros Cx Hn.
                     elim n3 with Cx; destruct Hn.
                      left; now auto.
                      right; apply in_or_app; now auto.
                    repeat rewrite app_comm_cons; rewrite app_assoc.
                     rewrite <- Heq'; intro.
                   destruct PIT_list_no_StoreData_append with ((StoreData v2 c C :: es'' ++ es') ++ ForwardInterest v1 c :: es) (ps1 ++ Data v2 v1 c C'' :: ps2) (StoreData v2 c C :: es'') (es' ++ ForwardInterest v1 c :: es) v1 c.
                    simpl; rewrite <- app_assoc; rewrite app_comm_cons; rewrite Heq'.
                     rewrite <- app_assoc; simpl; now auto.
                    simpl in *; rewrite app_assoc; now auto.
                    intros Cx Hn; destruct Hn as [Hn | Hn].
                     inversion Hn; elim n; now auto.
                     apply n3 with Cx; right; apply in_or_app; now auto.
                     elim ForwardInterest_PIT_list_not_nil with v1 c es' es ps'; auto.
                     simpl in *; rewrite <- app_assoc in H12; rewrite H11 in H12.
                     destruct (PIT_list v1 c (es' ++ ForwardInterest v1 c :: es)).
                      now auto.
                      destruct x2; simpl in H12; now inversion H12.
                 simpl; apply ccn_forward_data with v2 ps1 ps2; auto.
                  repeat rewrite app_comm_cons; rewrite app_assoc.
                   apply CMF_consistency; auto.
                    rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                    rewrite <- Heq'; intros Cx Hn.
                     elim n3 with Cx; destruct Hn.
                      left; now auto.
                      right; apply in_or_app; now auto.
                    repeat rewrite app_comm_cons; rewrite app_assoc.
                     rewrite <- Heq'; intro.
                   destruct PIT_list_no_StoreData_append with ((StoreData v2 c C :: es'' ++ es') ++ ForwardInterest v1 c :: es) (ps1 ++ Data v2 v1 c C'' :: ps2) (StoreData v2 c C :: es'') (es' ++ ForwardInterest v1 c :: es) v1 c.
                    simpl; rewrite <- app_assoc; rewrite app_comm_cons; rewrite Heq'.
                     rewrite <- app_assoc; simpl; now auto.
                    simpl in *; rewrite app_assoc; now auto.
                    intros Cx Hn; destruct Hn as [Hn | Hn].
                     inversion Hn; elim n; now auto.
                     apply n3 with Cx; right; apply in_or_app; now auto.
                     elim ForwardInterest_PIT_list_not_nil with v1 c es' es ps'; auto.
                     simpl in *; rewrite <- app_assoc in H12; rewrite H11 in H12.
                     destruct (PIT_list v1 c (es' ++ ForwardInterest v1 c :: es)).
                      now auto.
                      destruct x2; simpl in H12; now inversion H12.
      assert (In (Interest v1 v2 c) ps').
      {
       eapply Not_PIT_Data_StoreData_Interest; eauto.
      }
      apply in_split in H5; destruct H5 as [psl [psr H5]]; subst.
      case_eq (CMF v2 c (es' ++ ForwardInterest v1 c :: es)); intros.
       assert (CCNprotocol (ReplyData v2 c :: es' ++ ForwardInterest v1 c :: es) (Data v2 v1 c c0 :: psl ++ psr)).
       {
        apply ccn_reply_data with v1 c0 psl psr; now auto.
       }
       exists c0, [ForwardData v1 c; ReplyData v2 c], (PIT_Data v1 c c0 (ReplyData v2 c :: es' ++ ForwardInterest v1 c :: es) ++ psl ++ psr).
        case_eq (In_Request v1 c (ReplyData v2 c :: es' ++ ForwardInterest v1 c :: es)); intro; simpl.
         apply ccn_store_forward with v2 ([]:list Packet) (psl ++ psr); simpl; auto.
          rewrite cons_app; apply CMF_consistency; simpl; auto.
           apply CCN_reply_consistency with (Data v2 v1 c c0 :: psl ++ psr); auto.
           intros C Hn; destruct Hn as [Hn | []]; now inversion Hn.
          intro Hn.
           destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; auto.
           destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
           destruct H9; rewrite Hn in H8; rewrite H9 in H8; simpl in H8.
           destruct Node_eq_dec with v1 v1.
            destruct Content_Name_eq_dec with c c.
             destruct x; simpl in H8; now inversion H8.
             elim n4; now auto.
            elim n4; now auto.
         apply ccn_forward_data with v2 ([]:list Packet) (psl ++ psr); simpl; auto.
          rewrite cons_app; apply CMF_consistency; simpl; auto.
           apply CCN_reply_consistency with (Data v2 v1 c c0 :: psl ++ psr); auto.
           intros C Hn; destruct Hn as [Hn | []]; now inversion Hn.
          intro Hn.
           destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; auto.
           destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
           destruct H9; rewrite Hn in H8; rewrite H9 in H8; simpl in H8.
           destruct Node_eq_dec with v1 v1.
            destruct Content_Name_eq_dec with c c.
             destruct x; simpl in H8; now inversion H8.
             elim n4; now auto.
            elim n4; now auto.
       case_eq (PIT_list v2 c (es' ++ ForwardInterest v1 c :: es)); intros.
        assert (CCNprotocol (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) (FIB_Interest v2 c ++ psl ++ psr)).
        {
         apply ccn_forward_interest with psl psr; auto.
         destruct H0.
          destruct CMF_keep_InitCS with v c (es' ++ ForwardInterest v1 c :: es); auto.
           rewrite H5 in H7; inversion H7.
          intro Hn; unfold FIB in H0.
           rewrite Hn in H0; now auto.
        }
        destruct (IHFIBreachable _ _ H7 [] _ H7).
         destruct H8; simpl in H8; contradiction.
         destruct H8 as [C [es'' [ps'' IH]]].
         destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'').
          destruct e.
           apply in_split in H8.
            destruct H8 as [esl [esr H8]].
             rewrite app_comm_cons in IH; rewrite H8 in IH; rewrite <- app_assoc in IH; simpl in IH.
             destruct split_StoreData_CCNprotocol with v1 c x esl (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) ps''; auto.
             exists x, (esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]), x0.
             rewrite <- app_assoc; simpl; now auto.
          simpl in IH; destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr [esl [[C' HI] HNIN]]]; simpl; auto.
           rewrite app_comm_cons in IH; rewrite HI in IH; rewrite <- app_assoc in IH; simpl in IH.
           destruct split_StoreData_CCNprotocol with v2 c C' esl (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) ps''; auto.
           destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x esr (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) v2 c C'; auto.
            simpl; intro He.
             destruct Node_eq_dec with v2 v2.
              destruct Content_Name_eq_dec with c c.
               now inversion He.
              elim n5; now auto.
             elim n5; now auto.
            destruct esr; inversion H9; subst.
             destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x; auto.
             simpl in H8; destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (StoreData v2 c C' :: ForwardData v2 c :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) (nil : list Event); simpl; auto.
              destruct PIT_list_no_StoreData_append with (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 esr (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) v2 c; auto.
               intros C'' Hn; apply HNIN with C''; simpl; now auto.
               rewrite H11.
                apply in_or_app; right; simpl.
                destruct Node_eq_dec with v2 v2.
                 destruct Content_Name_eq_dec with c c.
                  simpl; now auto.
                  elim n5; now auto.
                 elim n5; now auto.
              assert (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es = (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es') ++ ForwardInterest v1 c :: es) by (rewrite <- app_assoc; simpl; now auto).
              right; rewrite H11 in *; apply ForwardInterest_PIT_list_not_nil with x0; auto.
               apply CMF_consistency; auto.
                eapply CCN_reply_consistency; now eauto.
                intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | Hn]]].
                 apply n4 with C''; rewrite HI; apply in_or_app; simpl; now auto.
                 now inversion Hn.
                 now inversion Hn.
                 apply n0 with C''; now auto.
               intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | Hn]]].
                apply n4 with C''; rewrite HI; apply in_or_app; simpl; now auto.
                now inversion Hn.
                now inversion Hn.
                apply n0 with C''; now auto.
              destruct H11 as [? []].
              destruct H11 as [C'' Hi]; apply in_split in Hi; destruct Hi as [psl' [psr' ?]]; subst.
               exists C'', (ForwardData v1 c :: StoreData v2 c C' :: ForwardData v2 c :: esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]); eexists.
               simpl; rewrite <- app_assoc; simpl; case_eq (In_Request v1 c (StoreData v2 c C' :: ForwardData v2 c :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es)); intro.
                eapply ccn_store_forward; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  assert (CMF v1 c ([ForwardInterest v2 c; AddPIT v2 v1 c] ++ es' ++ ForwardInterest v1 c :: es) = None).
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | [Hn | []]]; now inversion Hn.
                   simpl in *; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n; now auto.
                   now inversion Hn.
                   apply n4 with Cx.
                    destruct esl; simpl in HI; inversion HI; subst; simpl.
                     now auto.
                     right; apply in_or_app; simpl; now auto.
                 simpl.
                  destruct Node_eq_dec.
                   elim n; now auto.
                   destruct PIT_list_no_StoreData_append with (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 (esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]) (es' ++ ForwardInterest v1 c :: es) v1 c; simpl; auto.
                    rewrite <- app_assoc; simpl; now auto.
                    intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | []]]].
                     apply n4 with Cx; destruct esl; simpl in HI; inversion HI; subst; simpl.
                      now auto.
                      right; apply in_or_app; simpl; now auto.
                     now inversion Hn.
                     now inversion Hn.
                    intro Hn; rewrite Hn in H12.
                     destruct x; simpl in H12; try (inversion H12; fail).
                      destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; simpl; auto.
                       rewrite H13 in H12.
                       destruct x; simpl in H12; try (inversion H12; fail).
                       destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
                       destruct H14; subst; simpl in H12.
                       destruct Node_eq_dec with v1 v1.
                        destruct Content_Name_eq_dec with c c.
                         now inversion H12.
                         elim n6; now auto.
                        elim n6; now auto.
                eapply ccn_forward_data; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  assert (CMF v1 c ([ForwardInterest v2 c; AddPIT v2 v1 c] ++ es' ++ ForwardInterest v1 c :: es) = None).
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | [Hn | []]]; now inversion Hn.
                   simpl in *; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n; now auto.
                   now inversion Hn.
                   apply n4 with Cx.
                    destruct esl; simpl in HI; inversion HI; subst; simpl.
                     now auto.
                     right; apply in_or_app; simpl; now auto.
                 simpl.
                  destruct Node_eq_dec.
                   elim n; now auto.
                   destruct PIT_list_no_StoreData_append with (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 (esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]) (es' ++ ForwardInterest v1 c :: es) v1 c; simpl; auto.
                    rewrite <- app_assoc; simpl; now auto.
                    intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | []]]].
                     apply n4 with Cx; destruct esl; simpl in HI; inversion HI; subst; simpl.
                      now auto.
                      right; apply in_or_app; simpl; now auto.
                     now inversion Hn.
                     now inversion Hn.
                    intro Hn; rewrite Hn in H12.
                     destruct x; simpl in H12; try (inversion H12; fail).
                      destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; simpl; auto.
                       rewrite H13 in H12.
                       destruct x; simpl in H12; try (inversion H12; fail).
                       destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
                       destruct H14; subst; simpl in H12.
                       destruct Node_eq_dec with v1 v1.
                        destruct Content_Name_eq_dec with c c.
                         now inversion H12.
                         elim n6; now auto.
                        elim n6; now auto.
        assert (PIT_list v2 c (es' ++ ForwardInterest v1 c :: es) <> nil).
        {
         intro Hn; rewrite Hn in H6; now inversion H6.
        }
        assert (CCNprotocol (AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) (psl ++ psr)).
        {
         apply ccn_add_pit with psl psr; auto.
         destruct H0.
          destruct CMF_keep_InitCS with v c (es' ++ ForwardInterest v1 c :: es); auto.
           rewrite H5 in H8; inversion H8.
          intro Hn; unfold FIB in H0.
           rewrite Hn in H0; now auto.
        }
        destruct PIT_list_ForwardInterest with n4 v2 c (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) as [esr [esl [Heq HNIn]]]; simpl; auto.
         rewrite H6; simpl; now auto.
         assert (CCNprotocol (esl ++ ForwardInterest v2 c :: esr) (psl ++ Interest v1 v2 c :: psr)).
         {
          rewrite <- Heq; now auto.
         }
         destruct split_ForwardInterest_CCNprotocol with v2 c esl esr (psl ++ Interest v1 v2 c :: psr); auto.
         destruct IHFIBreachable with esr x (AddPIT v2 v1 c :: esl) (psl ++ psr); auto.
          simpl; rewrite <- Heq; now auto.
          destruct H11 as [C [H11 | H11]].
           now inversion H11.
           elim HNIn with C; now auto.
          clear H9 H10; simpl in H11; rewrite <- Heq in H11; clear esr esl x Heq HNIn; destruct H11 as [C [es'' [ps'' IH]]].
           destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr [esl [[C' HI] HNIN]]]; simpl; auto.
           rewrite app_comm_cons in IH; rewrite HI in IH; rewrite <- app_assoc in IH; simpl in IH.
           destruct split_StoreData_CCNprotocol with v2 c C' esl (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) ps''; auto.
           destruct in_dec_storedata with v1 c (StoreData v2 c C' :: esr).
           {
            destruct e.
             apply in_split in H10.
              destruct H10 as [esl' [esr' H10]].
               rewrite app_comm_cons in H9; rewrite H10 in H9; rewrite <- app_assoc in H9; simpl in H9.
               destruct split_StoreData_CCNprotocol with v1 c x0 esl' (esr' ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x; auto.
               exists x0, (esr' ++ [AddPIT v2 v1 c]), x1.
               rewrite <- app_assoc; simpl; now auto.
           }
           destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x esr (AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) v2 c C'; auto.
            simpl.
             destruct Node_eq_dec with v2 v2.
              destruct Content_Name_eq_dec with c c.
               intro He; now inversion He.
              elim n6; now auto.
             elim n6; now auto.
            destruct esr; inversion H10; subst; clear H10.
             destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x; auto.
             simpl in H8; destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (StoreData v2 c C' :: ForwardData v2 c :: esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) (nil : list Event); simpl; auto.
              destruct PIT_list_no_StoreData_append with (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 esr (AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) v2 c; auto.
               intros C'' Hn; apply HNIN with C''; simpl; now auto.
               rewrite H11.
                apply in_or_app; right; simpl.
                destruct Node_eq_dec with v2 v2.
                 destruct Content_Name_eq_dec with c c.
                  simpl; now auto.
                  elim n6; now auto.
                 elim n6; now auto.
              assert (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es = (esr ++ AddPIT v2 v1 c :: es') ++ ForwardInterest v1 c :: es) by (rewrite <- app_assoc; simpl; now auto).
              right; rewrite H11; apply ForwardInterest_PIT_list_not_nil with x0; auto.
               rewrite <- H11; now auto.
               apply CMF_consistency.
                rewrite <- H11; apply CCN_reply_consistency with x0; now auto.
                now auto.
                intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | Hn]].
                 apply n5 with C''; simpl; now auto.
                 now inversion Hn.
                 apply n0 with C''; now auto.
               intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | Hn]].
                apply n5 with C''; simpl; now auto.
                now inversion Hn.
                apply n0 with C''; now auto.
              destruct H11 as [? []].
              destruct H11 as [C'' Hi]; apply in_split in Hi; destruct Hi as [psl' [psr' ?]]; subst.
               exists C'', (ForwardData v1 c :: StoreData v2 c C' :: ForwardData v2 c :: esr ++ [AddPIT v2 v1 c]); eexists.
               simpl; rewrite <- app_assoc; simpl; case_eq (In_Request v1 c (StoreData v2 c C' :: ForwardData v2 c :: esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es)); intro.
                eapply ccn_store_forward; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  simpl; rewrite cons_app.
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | []]; now inversion Hn.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n; now auto.
                   now inversion Hn.
                   apply n5 with Cx; simpl; now auto.
                 simpl.
                  destruct Node_eq_dec.
                   elim n; now auto.
                   destruct PIT_list_no_StoreData_append with (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 (esr ++ [AddPIT v2 v1 c]) (es' ++ ForwardInterest v1 c :: es) v1 c; simpl; auto.
                    rewrite <- app_assoc; simpl; now auto.
                    intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | []]].
                     apply n5 with Cx; simpl; now auto.
                     now inversion Hn.
                    intro Hn; rewrite Hn in H12.
                     destruct x; simpl in H12; try (inversion H12; fail).
                      destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; simpl; auto.
                       rewrite H13 in H12.
                       destruct x; simpl in H12; try (inversion H12; fail).
                       destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
                       destruct H14; subst; simpl in H12.
                       destruct Node_eq_dec with v1 v1.
                        destruct Content_Name_eq_dec with c c.
                         now inversion H12.
                         apply n7; now auto.
                        apply n7; now auto.
                eapply ccn_forward_data; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  simpl; rewrite cons_app.
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | []]; now inversion Hn.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n; now auto.
                   now inversion Hn.
                   apply n5 with Cx; simpl; now auto.
                 simpl.
                  destruct Node_eq_dec.
                   elim n; now auto.
                   destruct PIT_list_no_StoreData_append with (esr ++ AddPIT v2 v1 c :: es' ++ ForwardInterest v1 c :: es) x0 (esr ++ [AddPIT v2 v1 c]) (es' ++ ForwardInterest v1 c :: es) v1 c; simpl; auto.
                    rewrite <- app_assoc; simpl; now auto.
                    intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | []]].
                     apply n5 with Cx; simpl; now auto.
                     now inversion Hn.
                    intro Hn; rewrite Hn in H12.
                     destruct x; simpl in H12; try (inversion H12; fail).
                      destruct PIT_list_no_StoreData_append with (es' ++ ForwardInterest v1 c :: es) (psl ++ Interest v1 v2 c :: psr) es' (ForwardInterest v1 c :: es) v1 c; simpl; auto.
                       rewrite H13 in H12.
                       destruct x; simpl in H12; try (inversion H12; fail).
                       destruct ForwardInterest_AddPIT with (ForwardInterest v1 c :: es) ps es v1 c; auto.
                       destruct H14; subst; simpl in H12.
                       destruct Node_eq_dec with v1 v1.
                        destruct Content_Name_eq_dec with c c.
                         now inversion H12.
                         apply n7; now auto.
                        apply n7; now auto.
Qed.






(** Forward lemma for requests *)
Theorem CCN_Forward_Request :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   (exists v' : Node, Connected v v' /\ FIBreachable v' c) ->
    CCNprotocol (Request v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ Request v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) es')
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ Request v c :: es) ps'').
Proof with eauto.
intros v1 c es ps CH; destruct CH as [v2 [H H0]]; intros.
 assert (CMF v1 c (Request v1 c :: es) = None).
 {
  eapply Request_Not_CMF...
 }
 destruct in_dec_storedata with v1 c es'; auto.
 assert (CMF v1 c (es' ++ Request v1 c :: es) = None).
 {
  apply CMF_consistency; auto.
  eapply CCN_reply_consistency...
 }
 right.
 destruct in_dec_datapacket with v2 v1 c ps'.
  destruct e as [C i]; destruct (in_split _ _ i) as [ ps1 [ps2 H5 ]]; subst; clear i.
   exists C.
   assert (In_Request v1 c (es' ++ Request v1 c :: es) = true).
   {
    apply Request_In_Request with (ps1 ++ Data v2 v1 c C :: ps2); now auto.
   }
   case_eq (PIT_list v1 c (es' ++ Request v1 c :: es)); intros.
    exists [], (ps1 ++ ps2); simpl.
     eapply ccn_store_data; now eauto.
    exists [ForwardData v1 c], (PIT_Data v1 c C (es' ++ Request v1 c :: es) ++ ps1 ++ ps2); simpl.
     eapply ccn_store_forward; eauto.
     intro Hn; rewrite Hn in H6; now inversion H6.
  destruct Node_eq_dec with v1 v2.
   subst; case_eq (PIT_list v2 c (es' ++ Request v2 c :: es)); intros.
    assert (In (Interest v2 v2 c) ps').
    {
     apply Request_Not_PIT_Data_StoreData_Interest with (es' ++ Request v2 c :: es) es' es; auto.
     intro Hn; rewrite H5 in Hn; simpl in Hn; now auto.
    }
    apply in_split in H6; destruct H6 as [ps1 [ps2 H6]]; subst.
     assert (CCNprotocol (ForwardInterest v2 c :: AddPIT v2 v2 c :: es' ++ Request v2 c :: es) (FIB_Interest v2 c ++ ps1 ++ ps2)).
     {
      apply ccn_forward_interest with ps1 ps2; auto.
      intro Hn; destruct H0.
       destruct CMF_keep_InitCS with v c (Request v c :: es); auto.
        rewrite H3 in H6; now inversion H6.
       unfold FIB in H0.
        rewrite Hn in H0; simpl in H0; now auto.
     }
     destruct CCN_Forward_Interest with v2 c (AddPIT v2 v2 c :: es' ++ Request v2 c :: es) (FIB_Interest v2 c ++ ps1 ++ ps2) ([] : list Event) (FIB_Interest v2 c ++ ps1 ++ ps2); auto.
      destruct H7 as [_ []].
      simpl in H7; destruct H7 as [C [es'' [ps'' H7]]].
       exists C, (es'' ++ [ForwardInterest v2 c; AddPIT v2 v2 c]), ps''.
       rewrite <- app_assoc; simpl; now auto.
    destruct PIT_list_ForwardInterest with n1 v2 c (es' ++ Request v2 c :: es) ps' as [esl [esr [H6 H7]]]; auto.
     rewrite H5; simpl; now auto.
     rewrite H6 in *; destruct split_ForwardInterest_CCNprotocol with v2 c esr esl ps'; auto.
      destruct CCN_Forward_Interest with v2 c esl x esr ps'; auto.
      destruct H9 as [C H9]; elim H7 with C; now auto.
   destruct in_dec_PIT_list with v2 v1 c (Request v1 c :: es).
    destruct (PIT_list_ForwardInterest v1 v2 c _ ps H1 i) as [es1 [es2 [Heq Hi]]].
     assert (CCNprotocol (es2 ++ ForwardInterest v2 c :: es1) ps).
     {
      rewrite <- Heq; now auto.
     }
     destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H5).
     destruct (CCN_Forward_Interest v2 c es1 x H0 H6 (es' ++ es2) ps') as [IH | IH].
      rewrite <- app_assoc; rewrite <- Heq; now auto.
      destruct IH as [C IH]; apply in_app_or in IH; destruct IH as [IH | IH]; [ | elim Hi with C; now auto ].
       apply StoreData_tail in IH.
       destruct IH as [esr [esl [[C' IHl] IH]]]; subst.
       rewrite <- app_assoc in H2, H4; simpl in H2, H4.
        assert (H7 := split_StoreData_CCNprotocol _ _ _ _ _ _ H2); destruct H7 as [ps'' H7].
        destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ Request v1 c :: es) ps'' esr (Request v1 c :: es) v2 c C'; auto.
         intro H8; rewrite H8 in i; simpl in i; now auto.
         rewrite H8 in H2.
          destruct esr; simpl in H8; inversion H8; subst.
          destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ Request v1 c :: es) ps''.
           simpl in *; now auto.
          destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl ++ StoreData v2 c C' :: ForwardData v2 c :: esr ++ Request v1 c :: es) ps' (esr ++ Request v1 c :: es) esl; auto.
           destruct PIT_list_no_StoreData_append with (esr ++ Request v1 c :: es) x0 esr (Request v1 c :: es) v2 c; auto.
            intros C'' Hn; apply IH with C''; simpl; now auto.
            rewrite H10; apply in_or_app; now auto.
           left; apply In_Request_No_StoreData with x0; auto.
            simpl.
             destruct Node_eq_dec.
              destruct Content_Name_eq_dec.
               now auto.
               elim n2; now auto.
              elim n2; now auto.
            intros C'' Hn; apply n with C''; apply in_or_app; simpl; now auto.
           destruct H10.
            elim n with x1; apply in_or_app; now auto.
           destruct H10.
            elim n0 with x1; now auto.
      destruct IH as [C [es'' [ps'' IH]]].
      destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'' ++ es').
       destruct e as [C' HIn].
        destruct HIn as [HIn | HIn].
         inversion HIn; subst; elim n1; now auto.
         apply in_app_or in HIn; destruct HIn as [HIn | HIn].
          apply in_split in HIn; destruct HIn as [esl [esr ?]].
           rewrite H7 in IH.
           repeat rewrite <- app_assoc in IH; simpl in IH.
           rewrite <- Heq in IH.
           exists C', esr; apply split_StoreData_CCNprotocol with (StoreData v2 c C :: esl) ps''.
           simpl; now auto.
          elim n with C'; now auto.
       destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'' ++ es') as [esr' [esl' [[C' Heq'] HNIn]]].
        left; now auto.
        repeat rewrite <- app_assoc in IH; rewrite app_assoc with _ _ es' _ in IH.
        rewrite app_comm_cons in IH; rewrite Heq' in IH.
        rewrite <- Heq in IH.
        rewrite <- app_assoc in IH; simpl in IH.
        destruct split_StoreData_CCNprotocol with v2 c C' esl' (esr' ++ Request v1 c :: es) ps''; auto.
        destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr' ++ Request v1 c :: es) x0 esr' (Request v1 c :: es) v2 c C'; auto.
         intro He; rewrite He in i; simpl in i; now auto.
         destruct esr'; inversion H8; subst.
         destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr' ++ Request v1 c :: es) x0; simpl; auto.
         destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ Request v1 c :: es) ps'' (esr' ++ Request v1 c :: es) esl'; auto.
          destruct PIT_list_no_StoreData_append with (esr' ++ Request v1 c :: es) x1 esr' (Request v1 c :: es) v2 c; auto.
           intros C'' Hn; apply HNIn with C''; simpl; now auto.
           rewrite H10; apply in_or_app; now auto.
          left; apply Request_In_Request with x1; auto.
           intros C'' Hn; apply n2 with C''; rewrite Heq'; apply in_or_app; simpl; now auto.
          destruct H10 as [C'' H10].
           elim n2 with C''; rewrite Heq'; apply in_or_app; simpl; now auto.
          destruct H10 as [C'' H10].
           apply in_split in H10; destruct H10 as [ps1 [ps2 ?]]; subst.
           exists C''; case_eq (PIT_list v1 c ((esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ Request v1 c :: es))); intros.
            exists (StoreData v2 c C :: es''), (ps1 ++ ps2).
             rewrite app_assoc; rewrite <- app_comm_cons; rewrite Heq'.
             rewrite <- app_assoc; simpl.
             apply ccn_store_data with v2 ps1 ps2; auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply CMF_consistency; auto.
                rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                rewrite <- Heq'; now auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply Request_In_Request with (ps1 ++ Data v2 v1 c C'' :: ps2).
                rewrite <- app_assoc; simpl in *; now auto.
                rewrite <- Heq'; now auto.
            exists (ForwardData v1 c :: StoreData v2 c C :: es''), (PIT_Data v1 c C'' (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ Request v1 c :: es) ++ ps1 ++ ps2).
             rewrite <- app_comm_cons; rewrite app_assoc; rewrite <- app_comm_cons; rewrite Heq'.
             rewrite <- app_assoc; simpl.
             apply ccn_store_forward with v2 ps1 ps2; auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply CMF_consistency; auto.
                rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                rewrite <- Heq'; now auto.
              repeat rewrite app_comm_cons; rewrite app_assoc.
               apply Request_In_Request with (ps1 ++ Data v2 v1 c C'' :: ps2).
                rewrite <- app_assoc; simpl in *; now auto.
                rewrite <- Heq'; now auto.
              intro Hn; rewrite Hn in H10; now inversion H10.
    destruct in_dec_PIT_list with v2 v1 c (es' ++ Request v1 c :: es).
     destruct (PIT_list_ForwardInterest v1 v2 c _ _ H2 i) as [es1 [es2 [Heq Hi]]].
     assert (CCNprotocol (es2 ++ ForwardInterest v2 c :: es1) ps').
     {
      rewrite <- Heq; now auto.
     }
     destruct (split_ForwardInterest_CCNprotocol _ _ _ _ _ H5).
     destruct (CCN_Forward_Interest v2 c es1 x H0 H6 es2 ps') as [IH | IH]; auto.
      destruct IH as [C IH]; elim Hi with C; now auto.
      destruct IH as [C [es'' [ps'' IH]]].
       destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'' ++ es').
        destruct e as [C' [HIn | HIn]].
         inversion HIn; subst; elim n1; now auto.
         apply in_app_or in HIn; destruct HIn as [HIn | HIn].
          apply in_split in HIn; destruct HIn as [esl [esr ?]].
           rewrite H7 in IH.
           repeat rewrite <- app_assoc in IH; simpl in IH.
           rewrite <- Heq in IH.
           exists C', esr; apply split_StoreData_CCNprotocol with (StoreData v2 c C :: esl) ps''.
           simpl; now auto.
          elim n with C'; now auto.
        destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr' [esl' [[C' Heq'] HNIn]]].
         left; now auto.
         rewrite <- Heq in IH.
          rewrite app_comm_cons in IH; rewrite Heq' in IH.
          rewrite <- app_assoc in IH; simpl in IH.
          destruct split_StoreData_CCNprotocol with v2 c C' esl' (esr' ++ es' ++ Request v1 c :: es) ps''; auto.
          destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr' ++ es' ++ Request v1 c :: es) x0 esr' (es' ++ Request v1 c :: es) v2 c C'; auto.
           intro He; rewrite He in i; simpl in i; now auto.
           destruct esr'; inversion H8; subst.
            destruct es'; inversion H10; subst.
             simpl in i.
              destruct Node_eq_dec with v2 v2.
               destruct Content_Name_eq_dec with c c.
                simpl in i; contradiction.
                elim n4; now auto.
               elim n4; now auto.
            destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr' ++ es' ++ Request v1 c :: es) x0; simpl; auto.
             destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (esl' ++ StoreData v2 c C' :: ForwardData v2 c :: esr' ++ es' ++ Request v1 c :: es) ps'' (esr' ++ es' ++ Request v1 c :: es) esl'; auto.
              destruct PIT_list_no_StoreData_append with (esr' ++ es' ++ Request v1 c :: es) x1 esr' (es' ++ Request v1 c :: es) v2 c; auto.
               intros C'' Hn; apply HNIn with C''; simpl; now auto.
               rewrite H10; apply in_or_app; now auto.
              left; rewrite app_assoc; apply Request_In_Request with x1; auto.
               rewrite <- app_assoc; now auto.
               intros C'' Hn; apply n3 with C''.
                rewrite app_comm_cons; rewrite Heq'.
                rewrite <- app_assoc.
                apply in_or_app; simpl; now auto.
              destruct H10 as [C'' H10].
               elim n3 with C''; rewrite app_comm_cons; rewrite Heq'; apply in_or_app; left; apply in_or_app; simpl; now auto.
              destruct H10 as [C'' H10].
               apply in_split in H10; destruct H10 as [ps1 [ps2 ?]]; subst.
               exists C''.
               case_eq (PIT_list v1 c (esl' ++ StoreData v2 c C' :: (ForwardData v2 c :: esr') ++ es' ++ Request v1 c :: es)); intros.
                exists (StoreData v2 c C :: es''), (ps1 ++ ps2).
                 apply ccn_store_data with v2 ps1 ps2; auto.
                  simpl; rewrite app_comm_cons; rewrite Heq'.
                   repeat rewrite <- app_assoc; simpl in *; now auto.
                  apply CMF_consistency; auto.
                   simpl; rewrite app_comm_cons; rewrite Heq'.
                    rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                   intros C0 Hn; apply n3 with C0.
                    destruct Hn; simpl; auto; right; apply in_or_app; now auto.
                  rewrite app_assoc; apply Request_In_Request with (ps1 ++ Data v2 v1 c C'' :: ps2).
                   rewrite Heq'; repeat rewrite <- app_assoc; simpl in *; now auto.
                   now apply n3.
                  rewrite Heq'; rewrite <- app_assoc; simpl in *; now auto.
                exists (ForwardData v1 c :: StoreData v2 c C :: es''), (PIT_Data v1 c C'' (StoreData v2 c C :: es'' ++ es' ++ Request v1 c :: es) ++ ps1 ++ ps2).
                 rewrite <- app_comm_cons; apply ccn_store_forward with v2 ps1 ps2; auto.
                  simpl; rewrite app_comm_cons; rewrite Heq'.
                   repeat rewrite <- app_assoc; simpl in *; now auto.
                  apply CMF_consistency; auto.
                   simpl; rewrite app_comm_cons; rewrite Heq'.
                    rewrite <- app_assoc; simpl; apply CCN_reply_consistency with (ps1 ++ Data v2 v1 c C'' :: ps2); now auto.
                   intros C0 Hn; apply n3 with C0.
                    destruct Hn; simpl; auto; right; apply in_or_app; now auto.
                  rewrite app_assoc; apply Request_In_Request with (ps1 ++ Data v2 v1 c C'' :: ps2).
                   rewrite Heq'; repeat rewrite <- app_assoc; simpl in *; now auto.
                   now apply n3.
                  rewrite Heq'; rewrite <- app_assoc; simpl in *; intro Hn; rewrite Hn in H10; now inversion H10.
     assert (In (Interest v1 v2 c) ps').
     {
      eapply Request_Not_PIT_Data_StoreData_Interest; eauto.
     }
     apply in_split in H5; destruct H5 as [psl [psr H5]]; subst.
     case_eq (CMF v2 c (es' ++ Request v1 c :: es)); intros.
      assert (CCNprotocol (ReplyData v2 c :: es' ++ Request v1 c :: es) (Data v2 v1 c c0 :: psl ++ psr)).
      {
       apply ccn_reply_data with v1 c0 psl psr; now auto.
      }
      exists c0.
      case_eq (PIT_list v1 c (ReplyData v2 c :: es' ++ Request v1 c :: es)); intros.
       exists [ReplyData v2 c], (psl ++ psr).
        apply ccn_store_data with v2 ([]:list Packet) (psl ++ psr); simpl; auto.
         rewrite cons_app; apply CMF_consistency; simpl; auto.
          apply CCN_reply_consistency with (Data v2 v1 c c0 :: psl ++ psr); auto.
          intros C Hn; destruct Hn as [Hn | []]; now inversion Hn.
         apply Request_In_Request with (psl ++ Interest v1 v2 c :: psr); auto.
       exists [ForwardData v1 c; ReplyData v2 c], (PIT_Data v1 c c0 (ReplyData v2 c :: es' ++ Request v1 c :: es) ++ psl ++ psr).
        apply ccn_store_forward with v2 ([]:list Packet) (psl ++ psr); simpl; auto.
         rewrite cons_app; apply CMF_consistency; simpl; auto.
          apply CCN_reply_consistency with (Data v2 v1 c c0 :: psl ++ psr); auto.
          intros C Hn; destruct Hn as [Hn | []]; now inversion Hn.
         apply Request_In_Request with (psl ++ Interest v1 v2 c :: psr); auto.
         intro Hn; simpl in H7; rewrite Hn in H7; now inversion H7.
      case_eq (PIT_list v2 c (es' ++ Request v1 c :: es)); intros.
       assert (CCNprotocol (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) (FIB_Interest v2 c ++ psl ++ psr)).
       {
        apply ccn_forward_interest with psl psr; auto.
        destruct H0.
         destruct CMF_keep_InitCS with v c (es' ++ Request v1 c :: es); auto.
          rewrite H5 in H7; inversion H7.
         intro Hn; unfold FIB in H0.
          rewrite Hn in H0; now auto.
       }
       destruct (CCN_Forward_Interest _ _ _ _ H0 H7 [] _ H7).
        destruct H8; simpl in H8; contradiction.
        destruct H8 as [C [es'' [ps'' IH]]].
        destruct in_dec_storedata with v1 c (StoreData v2 c C :: es'').
         destruct e.
          apply in_split in H8.
           destruct H8 as [esl [esr H8]].
            rewrite app_comm_cons in IH; rewrite H8 in IH; rewrite <- app_assoc in IH; simpl in IH.
            destruct split_StoreData_CCNprotocol with v1 c x esl (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) ps''; auto.
            exists x, (esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]), x0.
            rewrite <- app_assoc; simpl; now auto.
         simpl in IH; destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr [esl [[C' HI] HNIN]]]; simpl; auto.
          rewrite app_comm_cons in IH; rewrite HI in IH; rewrite <- app_assoc in IH; simpl in IH.
          destruct split_StoreData_CCNprotocol with v2 c C' esl (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) ps''; auto.
          destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x esr (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) v2 c C'; auto.
           simpl; intro He.
            destruct Node_eq_dec with v2 v2.
             destruct Content_Name_eq_dec with c c.
              now inversion He.
             elim n5; now auto.
            elim n5; now auto.
           destruct esr; inversion H9; subst.
            destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x; auto.
            simpl in H8; destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (StoreData v2 c C' :: ForwardData v2 c :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) (nil : list Event); simpl; auto.
             destruct PIT_list_no_StoreData_append with (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x0 esr (ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es) v2 c; auto.
              intros C'' Hn; apply HNIN with C''; simpl; now auto.
              rewrite H11.
               apply in_or_app; right; simpl.
               destruct Node_eq_dec with v2 v2.
                destruct Content_Name_eq_dec with c c.
                 simpl; now auto.
                 elim n5; now auto.
                elim n5; now auto.
             assert (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es = (esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es') ++ Request v1 c :: es) by (rewrite <- app_assoc; simpl; now auto).
             left; repeat rewrite app_comm_cons; rewrite app_assoc.
              apply Request_In_Request with x0.
               rewrite <- app_assoc; simpl; now auto.
               intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | Hn]]].
                elim n4 with C''; rewrite HI; apply in_or_app; simpl; now auto.
                now inversion Hn.
                now inversion Hn.
                apply n with C''; now auto.
             destruct H11 as [? []].
             destruct H11 as [C'' Hi]; apply in_split in Hi; destruct Hi as [psl' [psr' ?]]; subst.
              exists C''.
              case_eq (PIT_list v1 c (StoreData v2 c C' :: ForwardData v2 c :: esr ++ ForwardInterest v2 c :: AddPIT v2 v1 c :: es' ++ Request v1 c :: es)); intros.
               exists (StoreData v2 c C' :: ForwardData v2 c :: esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]); eexists.
                simpl; rewrite <- app_assoc; simpl.
                eapply ccn_store_data; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  assert (CMF v1 c ([ForwardInterest v2 c; AddPIT v2 v1 c] ++ es' ++ Request v1 c :: es) = None).
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | [Hn | []]]; now inversion Hn.
                   simpl in *; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply n4 with Cx.
                    rewrite HI.
                     apply in_or_app; simpl; now auto.
                 repeat rewrite app_comm_cons; rewrite app_assoc; apply Request_In_Request with (psl' ++ Data v2 v1 c C'' :: psr'); simpl; auto.
                  rewrite <- app_assoc; simpl; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | Hn]]].
                    apply n4 with Cx.
                     rewrite HI.
                      apply in_or_app; simpl; now auto.
                    now inversion Hn.
                    now inversion Hn.
                    apply n with Cx; now auto.
               exists (ForwardData v1 c :: StoreData v2 c C' :: ForwardData v2 c :: esr ++ [ForwardInterest v2 c; AddPIT v2 v1 c]); eexists.
                simpl; rewrite <- app_assoc; simpl.
                eapply ccn_store_forward; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  assert (CMF v1 c ([ForwardInterest v2 c; AddPIT v2 v1 c] ++ es' ++ Request v1 c :: es) = None).
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | [Hn | []]]; now inversion Hn.
                   simpl in *; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply n4 with Cx.
                    rewrite HI.
                     apply in_or_app; simpl; now auto.
                 repeat rewrite app_comm_cons; rewrite app_assoc; apply Request_In_Request with (psl' ++ Data v2 v1 c C'' :: psr'); simpl; auto.
                  rewrite <- app_assoc; simpl; now auto.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply in_app_or in Hn; destruct Hn as [Hn | [Hn | [Hn | Hn]]].
                    apply n4 with Cx.
                     rewrite HI.
                      apply in_or_app; simpl; now auto.
                    now inversion Hn.
                    now inversion Hn.
                    apply n with Cx; now auto.
                 intro Hn; rewrite Hn in H11; now inversion H11.
       assert (PIT_list v2 c (es' ++ Request v1 c :: es) <> nil).
       {
        intro Hn; rewrite Hn in H6; now inversion H6.
       }
       assert (CCNprotocol (AddPIT v2 v1 c :: es' ++ Request v1 c :: es) (psl ++ psr)).
       {
        apply ccn_add_pit with psl psr; auto.
        destruct H0.
         destruct CMF_keep_InitCS with v c (es' ++ Request v1 c :: es); auto.
          rewrite H5 in H8; inversion H8.
         intro Hn; unfold FIB in H0.
          rewrite Hn in H0; now auto.
       }
       destruct PIT_list_ForwardInterest with n4 v2 c (es' ++ Request v1 c :: es) (psl ++ Interest v1 v2 c :: psr) as [esr [esl [Heq HNIn]]]; simpl; auto.
        rewrite H6; simpl; now auto.
        assert (CCNprotocol (esl ++ ForwardInterest v2 c :: esr) (psl ++ Interest v1 v2 c :: psr)).
        {
         rewrite <- Heq; now auto.
        }
        destruct split_ForwardInterest_CCNprotocol with v2 c esl esr (psl ++ Interest v1 v2 c :: psr); auto.
        destruct CCN_Forward_Interest with v2 c esr x (AddPIT v2 v1 c :: esl) (psl ++ psr); auto.
         simpl; rewrite <- Heq; now auto.
         destruct H11 as [C [H11 | H11]].
          now inversion H11.
          elim HNIn with C; now auto.
         clear H9 H10; simpl in H11; rewrite <- Heq in H11; clear esr esl x Heq HNIn; destruct H11 as [C [es'' [ps'' IH]]].
          destruct StoreData_tail with v2 c C (StoreData v2 c C :: es'') as [esr [esl [[C' HI] HNIN]]]; simpl; auto.
          rewrite app_comm_cons in IH; rewrite HI in IH; rewrite <- app_assoc in IH; simpl in IH.
          destruct split_StoreData_CCNprotocol with v2 c C' esl (esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) ps''; auto.
          destruct in_dec_storedata with v1 c (StoreData v2 c C' :: esr).
          {
           destruct e.
            apply in_split in H10.
             destruct H10 as [esl' [esr' H10]].
              rewrite app_comm_cons in H9; rewrite H10 in H9; rewrite <- app_assoc in H9; simpl in H9.
              destruct split_StoreData_CCNprotocol with v1 c x0 esl' (esr' ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x; auto.
              exists x0, (esr' ++ [AddPIT v2 v1 c]), x1.
              rewrite <- app_assoc; simpl; now auto.
          }
          destruct StoreData_PIT_ForwardData with (StoreData v2 c C' :: esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x esr (AddPIT v2 v1 c :: es' ++ Request v1 c :: es) v2 c C'; auto.
           simpl.
            destruct Node_eq_dec with v2 v2.
             destruct Content_Name_eq_dec with c c.
              intro He; now inversion He.
             elim n6; now auto.
            elim n6; now auto.
           destruct esr; inversion H10; subst; clear H10.
            destruct split_ForwardData_CCNprotocol with v2 c [StoreData v2 c C'] (esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x; auto.
            simpl in H8; destruct StoreData_StoreData_or_DataPacket with v1 v2 c C' (StoreData v2 c C' :: ForwardData v2 c :: esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x (esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) (nil : list Event); simpl; auto.
             destruct PIT_list_no_StoreData_append with (esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es) x0 esr (AddPIT v2 v1 c :: es' ++ Request v1 c :: es) v2 c; auto.
              intros C'' Hn; apply HNIN with C''; simpl; now auto.
              rewrite H11.
               apply in_or_app; right; simpl.
               destruct Node_eq_dec with v2 v2.
                destruct Content_Name_eq_dec with c c.
                 simpl; now auto.
                 elim n6; now auto.
                elim n6; now auto.
             assert (esr ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es = (esr ++ AddPIT v2 v1 c :: es') ++ Request v1 c :: es) by (rewrite <- app_assoc; simpl; now auto).
             left; rewrite H11 in *; apply Request_In_Request with x0; auto.
              intros C'' Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | Hn]].
               apply n5 with C''; simpl; now auto.
               now inversion Hn.
               apply n with C''; now auto.
             destruct H11 as [? []].
             destruct H11 as [C'' Hi]; apply in_split in Hi; destruct Hi as [psl' [psr' ?]]; subst.
              exists C''.
              case_eq (PIT_list v1 c ((StoreData v2 c C' :: ForwardData v2 c :: esr) ++ AddPIT v2 v1 c :: es' ++ Request v1 c :: es)); intros.
               exists (StoreData v2 c C' :: ForwardData v2 c :: esr ++ [AddPIT v2 v1 c]); eexists.
                simpl; rewrite <- app_assoc; simpl.
                eapply ccn_store_data; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  simpl; rewrite cons_app.
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | []]; now inversion Hn.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply n5 with Cx; simpl; now auto.
                 repeat rewrite app_comm_cons; rewrite app_assoc.
                  apply Request_In_Request with (psl' ++ Data v2 v1 c C'' :: psr').
                   rewrite <- app_assoc; simpl in *; now auto.
                   intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | Hn]].
                    apply n5 with Cx; now auto.
                    now inversion Hn.
                    apply n with Cx; now auto.
               exists (ForwardData v1 c :: StoreData v2 c C' :: ForwardData v2 c :: esr ++ [AddPIT v2 v1 c]); eexists.
                simpl; rewrite <- app_assoc; simpl.
                eapply ccn_store_forward; eauto.
                 repeat rewrite app_comm_cons; apply CMF_consistency.
                  simpl; apply CCN_reply_consistency with (psl' ++ Data v2 v1 c C'' :: psr'); now auto.
                  simpl; rewrite cons_app.
                   apply CMF_consistency; simpl; auto.
                    eapply CCN_reply_consistency; now eauto.
                    intros Cx Hn; destruct Hn as [Hn | []]; now inversion Hn.
                  intros Cx Hn; destruct Hn as [Hn | [Hn | Hn]].
                   inversion Hn; apply n1; now auto.
                   now inversion Hn.
                   apply n5 with Cx; simpl; now auto.
                 repeat rewrite app_comm_cons; rewrite app_assoc.
                  apply Request_In_Request with (psl' ++ Data v2 v1 c C'' :: psr').
                   rewrite <- app_assoc; simpl in *; now auto.
                   intros Cx Hn; apply in_app_or in Hn; destruct Hn as [Hn | [Hn | Hn]].
                    apply n5 with Cx; now auto.
                    now inversion Hn.
                    apply n with Cx; now auto.
                 intro Hn; simpl app in H11; rewrite Hn in H11; now inversion H11.
Qed.



(** If FIBreachable for any nodes, any contents, we can omit conditions from theorem *) 
Theorem CCN_Forward_Request' :
  (forall (v : Node) (c : Content_Name), FIBreachable v c) ->
   forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
    CCNprotocol (Request v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ Request v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) es')
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ Request v c :: es) ps'').
Proof with auto.
intros.
apply CCN_Forward_Request with (ps := ps) (ps' := ps')...
 destruct (H v c).
  assert (H3 := Request_Not_CMF v c es ps H0).
   destruct (CMF_keep_InitCS _ _ H2 (Request v c :: es)); rewrite H3 in H4; now inversion H4.
  exists v2; split...
   apply FIB_Connected with (c := c)...
Qed.



(** Backward lemma *)
Theorem CCN_Backward :
  forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps : list Packet),
   CCNprotocol (StoreData v c C :: es) ps ->
    In_Request v c es = true \/ In_ForwardInterest v c es = true.
intros v c C es.
remember (StoreData v c C :: es) as es'.
intros ps H.
revert v c C es Heqes'; induction H; intros;
 (inversion Heqes'; fail || subst; eauto).
 simpl.
 right; eapply PIT_list_not_nil_ForwardInterest; eauto.
Qed.




End CCN_Protocol_Verification_CM.



