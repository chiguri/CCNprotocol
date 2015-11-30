(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Functor from Network Topology to specifications/proofs about filtering all Events and Packets about single Content_Name.

      This guarantees that each event does not use shared resource in this settings.
      (Be careful that if we add limit of ContentStores, we cannot prove this since other contents change the state of ContentStores.)
 *)


Require Import List.
Import ListNotations.

Require Import MiscSpec.

Require CCNTopology.
Require CCNProtocol.


(* CCNのイベントをコンテンツ毎にフィルターするとやはり大丈夫という定理を示す *)
(* Verification自体はいらないはず。 *)

Module CCN_Protocol_Content (N : CCNTopology.CCN_Network).
Import N.

Module Protocol := CCNProtocol.CCN_Protocol N.
Import Protocol.


Definition packet_content_name (p : Packet) : Content_Name :=
match p with
| Interest _ _ c => c
| Data _ _ c _ => c
end.


Definition event_content_name (e : Event) : Content_Name :=
match e with
| Request _ c => c
| ForwardInterest _ c => c
| AddPIT _ _ c => c
| ReplyData _ c => c
| ForwardData _ c => c
| StoreData _ c _ => c
end.


Fixpoint content_list {A : Type} (cname : A -> Content_Name) (c : Content_Name) (al : list A) : list A :=
match al with
| [] => []
| a :: al' =>
  if Content_Name_eq_dec c (cname a)
     then a :: content_list cname c al'
     else content_list cname c al'
end.


Definition content_packets := content_list packet_content_name.
Definition content_events := content_list event_content_name.

Arguments content_packets /.
Arguments content_events /.


Lemma content_list_app :
 forall {A : Type} (cname : A -> Content_Name) (c : Content_Name) (al1 al2 : list A),
  content_list cname c (al1 ++ al2) = content_list cname c al1 ++ content_list cname c al2.
Proof.
intros A cname c al1; induction al1; intros; simpl in *.
 now auto.
 destruct Content_Name_eq_dec with c (cname a).
  simpl; f_equal; now auto.
  now auto.
Qed.



Lemma Broadcast_Interest_content :
 forall (v : Node) (c : Content_Name),
  content_packets c (Broadcast_Interest v c) = Broadcast_Interest v c.
unfold Broadcast_Interest.
intro v.
generalize (Connected_list v).
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -f_equal; now auto.
 -elim n; now auto.
Qed.


Lemma Broadcast_Interest_not_content :
 forall (v : Node) (c c' : Content_Name),
  c <> c' ->
   content_packets c (Broadcast_Interest v c') = [].
unfold Broadcast_Interest.
intro v.
generalize (Connected_list v).
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -elim H; now auto.
 -now auto.
Qed.



Lemma FIB_Interest_content :
 forall (v : Node) (c : Content_Name),
  content_packets c (FIB_Interest v c) = FIB_Interest v c.
unfold FIB_Interest.
intros v c.
generalize (FIB_list v c).
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -f_equal; now auto.
 -elim n; now auto.
Qed.


Lemma FIB_Interest_not_content :
 forall (v : Node) (c c' : Content_Name),
  c <> c' ->
   content_packets c (FIB_Interest v c') = [].
unfold FIB_Interest.
intros v c c'.
generalize (FIB_list v c').
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -elim H; now auto.
 -now auto.
Qed.



Lemma PIT_Data_content :
 forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event),
  content_packets c (PIT_Data v c C es) = PIT_Data v c C es.
unfold PIT_Data.
intros v c C es.
generalize (PIT_list v c es).
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -f_equal; now auto.
 -elim n; now auto.
Qed.


Lemma PIT_Data_not_content :
 forall (v : Node) (c c' : Content_Name) (C : Content c') (es : list Event),
  c <> c' ->
   content_packets c (PIT_Data v c' C es) = [].
unfold PIT_Data.
intros v c c' C es.
generalize (PIT_list v c' es).
induction l; intros; simpl.
+now auto.
+destruct Content_Name_eq_dec.
 -elim H; now auto.
 -now auto.
Qed.



Lemma content_list_cons :
 forall {A : Type} (cname : A -> Content_Name) (c : Content_Name) (a : A) (al : list A),
  c = cname a ->
   content_list cname c (a :: al) = a :: (content_list cname c al).
intros; simpl.
destruct Content_Name_eq_dec.
 now auto.
 elim n; now auto.
Qed.


Lemma content_list_cons_not :
 forall {A : Type} (cname : A -> Content_Name) (c : Content_Name) (a : A) (al : list A),
  c <> cname a ->
   content_list cname c (a :: al) = content_list cname c al.
intros; simpl.
destruct Content_Name_eq_dec.
 elim H; now auto.
 now auto.
Qed.



Lemma Content_get_events :
 forall (v : Node) (c : Content_Name) (es : list Event),
  Content_get v c es = Content_get v c (content_events c es).
induction es.
 simpl; now auto.
 simpl.
 destruct Content_Name_eq_dec.
 +simpl.
  destruct a; auto.
  destruct Node_eq_dec; auto.
  destruct Content_Name_eq_dec; now auto.
 +destruct a; auto.
  simpl in n.
  destruct Node_eq_dec; auto.
  destruct Content_Name_eq_dec.
   elim n; now auto.
   now auto.
Qed.


Lemma content_PIT_list :
 forall (v : Node) (c : Content_Name) (es : list Event),
  PIT_list v c (content_list event_content_name c es) = PIT_list v c es.
induction es; simpl.
 now auto.
 destruct Content_Name_eq_dec.
 +destruct a; auto.
  -simpl.
   destruct Node_eq_dec; auto.
   destruct Content_Name_eq_dec.
    f_equal; now auto.
    now auto.
  -simpl.
   destruct Node_eq_dec; auto.
   destruct Content_Name_eq_dec; now auto.
 +destruct a; auto.
  -destruct Node_eq_dec; auto.
   destruct Content_Name_eq_dec.
    elim n; simpl; now auto.
    now auto.
  -destruct Node_eq_dec; auto.
   destruct Content_Name_eq_dec.
    elim n; simpl; now auto.
    now auto.
Qed.



Lemma content_PIT_Data :
 forall (v : Node) (c : Content_Name) (C : Content c) (es : list Event),
  PIT_Data v c C es = PIT_Data v c C (content_list event_content_name c es).
unfold PIT_Data.
intros; rewrite content_PIT_list; now auto.
Qed.


Lemma content_In :
 forall {A : Type} (cname : A -> Content_Name) (c : Content_Name) (a : A) (al : list A),
  c = cname a ->
   (In a (content_list cname c al) <-> In a al).
intros; induction al; simpl.
split; now auto.
destruct IHal.
split.
+destruct Content_Name_eq_dec; simpl; intro.
 -destruct H2; now auto.
 -now auto.
+intro; destruct Content_Name_eq_dec; simpl.
 -destruct H2; now auto.
 -destruct H2.
   subst.
    elim n; now auto.
   now auto.
Qed.




Theorem CCNProtocol_single_content :
 forall (c : Content_Name) (es : list Event) (ps : list Packet),
  CCNprotocol es ps -> CCNprotocol (content_events c es) (content_packets c ps).
Proof.
intros c es ps H; induction H; simpl in *; subst.
+now constructor.
+rewrite content_list_app.
 destruct Content_Name_eq_dec.
 -subst.
  rewrite Broadcast_Interest_content.
  apply ccn_request with (content_list packet_content_name c0 ps); auto.
  rewrite <- Content_get_events; now auto.
 -rewrite Broadcast_Interest_not_content.
  simpl; now auto.
  now auto.  
+repeat rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol.
 simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  rewrite FIB_Interest_content.
  apply ccn_forward_interest with (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *rewrite content_PIT_list; now auto.
  *now auto.
  *now auto.
 -rewrite FIB_Interest_not_content; simpl; now auto.
+rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_add_pit with (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *rewrite content_PIT_list; now auto.
  *rewrite content_PIT_list; now auto.
  *now auto.
  *now auto.
 -now auto.
+rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_drop_interest_fib with v v' c0 (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *now auto.
  *now auto.
 -now auto.
+rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_drop_interest_pit with v v' c0 (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *rewrite content_PIT_list; now auto.
  *now auto.
 -now auto.
+simpl.
 rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_reply_data with v C (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *now auto.
 -now auto.
+rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_store_data with v (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *apply content_In; now auto.
  *rewrite content_PIT_list; now auto.
  *now auto.
 -now auto.
+simpl; repeat rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  rewrite PIT_Data_content.
  apply ccn_forward_data with v (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *intro.
   apply content_In in H3; now auto.
  *rewrite content_PIT_list; now auto.
  *rewrite content_PIT_Data; now auto.
 -rewrite PIT_Data_not_content; simpl; now auto.
+repeat rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  rewrite PIT_Data_content.
  apply ccn_store_forward with v (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *apply content_In; now auto.
  *rewrite content_PIT_list; now auto.
  *rewrite content_PIT_Data; now auto.
 -rewrite PIT_Data_not_content; simpl; now auto.
+rewrite content_list_app.
 rewrite content_list_app in IHCCNprotocol; simpl in IHCCNprotocol.
 destruct Content_Name_eq_dec.
 -subst.
  apply ccn_drop_data with v v' c0 C (content_packets c0 ps1) (content_packets c0 ps2).
  *now auto.
  *rewrite <- Content_get_events; now auto.
  *now auto.
 -now auto.
Qed.




End CCN_Protocol_Content.

