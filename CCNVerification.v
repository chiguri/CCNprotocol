Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.
Require CCNProtocolLemma.


Module CCN_Protocol_Verification (N : CCNTopology.CCN_Network).

Module Protocol_Lemma := CCNProtocolLemma.CCN_Protocol_Lemma N.
Import Protocol_Lemma.




Lemma CCN_Forward' :
  forall (v : Node) (c : Content_Name) (es : list Event) (ps : list Packet),
   FIBreachable v c ->
    CCNprotocol (ForwardInterest v c :: es) ps ->
     forall (es' : list Event) (ps' : list Packet),
      CCNprotocol (es' ++ ForwardInterest v c :: es) ps' ->
       (exists C : Content c, In (StoreData v c C) (es' ++ ForwardInterest v c :: es))
       \/ (exists (C : Content c) (es'' : list Event) (ps'' : list Packet),
             CCNprotocol (StoreData v c C :: es'' ++ es' ++ ForwardInterest v c :: es) ps'').
intros v c es ps H; revert es ps; induction H; intros.
 elim (InitCS_Content_get _ _ _ _ H0 H).
  eapply ForwardInterest_Not_Content_get; eauto.
 case_eq (Content_get v1 c (es' ++ ForwardInterest v1 c :: es)); intros.
  left; destruct (Content_get_InitCS_or_StoreData _ _ _ _ _ H2 H3).
   elim (InitCS_Content_get _ _ _ _ H1 H4).
    eapply ForwardInterest_Not_Content_get; eauto.
   exists c0; auto.
  right; destruct in_dec_forward with v2 c (es' ++ ForwardInterest v1 c :: es).
(*
 v2のForwardInterestの有無、
*)
Admitted.


Theorem CCN_Forward :
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
 subst; right; right. eapply PIT_list_not_nil_ForwardInterest; eauto.
 subst; left; right; auto.
Qed.


End CCN_Protocol_Verification.



