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
   admit.
  case_eq (Content_get v2 c (es' ++ ForwardInterest v1 c :: es)); intros.
   (* Interest Packetが残っているか、既にデータを返しているはず *)
    
(*
 v2のForwardInterestがある場合は、ForwardInterestより後ろにStoreDataがあり、PITは空ではないはずである。
  よってDataが送られる。パケットの保持に関する定理が必要か。StoreDataがまだないなら、なにかのイベント列がある。
  ここからDataが送られているはず。（PITは空ではないので）
 v2のForwardInterestがない場合は、ForwardInterestで投げたInterestパケットが保持されているはず（要補題）。
  あとはコンテンツが既にあるかが問題であり、なければForwardInterestが発行されて以下略。
  コンテンツが既にあるならReplyDataが発行されてパケットが来るのでコンストラクタ適用しておしまい。

なお、ある時点でContent_getがNone、それ以降のある時点でContent_getがSomeを返すなら、その間に存在する、という
補題が必要そう。
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



