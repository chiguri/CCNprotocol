(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Network sample : simple network with only 7 nodes (bound) *)
(** * Content Management sample : each node can store 3 contents which are used most recently *)


Require Import List.
Import ListNotations.

Require CCNProtocol.
Require CCNContentManagement.
Require Import CCNSimpleNetwork.

Require Import Arith.


Module CCN_SimpleNetworkLRU <: CCNContentManagement.CCN_Content_Management.

Module Topology := CCN_SimpleNetwork.
Import Topology.

Module OldProtocol := CCNProtocol.CCN_Protocol Topology.
Import OldProtocol.


Fixpoint cache_exist (c : Content_Name) (cache : list Content_Name) : bool :=
match cache with
| nil => false
| c' :: cache' =>
  match Content_Name_eq_dec c c' with
  | left _ => true
  | _ => cache_exist c cache'
  end
end.


(* Here, "used" means "stored" or "replied". The storage keeps 3 contents. *)
Fixpoint LRU (v : Node) (c : Content_Name) (es : list Event) (cache : list Content_Name) : option (Content c) :=
if ge_dec (length cache) 3 then
  if cache_exist c cache then
    match es with
    | nil => None
    | StoreData v' c' C :: es' =>
       match Node_eq_dec v v' with
       | left _ =>
          match Content_Name_eq_dec c c' with
          | left x => Some (eq_rec_r (fun t => Content t) C x)
          | _ => LRU v c es' cache
          end
       | _ => LRU v c es' cache
       end
    | _ :: es' => LRU v c es' cache
    end
  else None
else
  match es with
  | nil => None
  | StoreData v' c' C :: es' =>
     match Node_eq_dec v v' with
     | left _ =>
        match Content_Name_eq_dec c c' with
        | left x => Some (eq_rec_r (fun t => Content t) C x)
        | _ => LRU v c es' (if cache_exist c' cache then cache
                            else c' :: cache)
        end
     | _ => LRU v c es' cache
     end
  | ReplyData v' c' :: es' =>
     match Node_eq_dec v v' with
     | left _ =>
        match InitCS_dec v c with
        | left _ => LRU v c es' cache
        | _ => LRU v c es' (if cache_exist c' cache then cache
                            else c' :: cache)
        end
     | _ => LRU v c es' cache
     end
  | _ :: es' => LRU v c es' cache
  end.


Definition CMF (v : Node) (c : Content_Name) (es : list Event) : option (Content c) :=
match InitCS_dec v c with
| left x => Some (InitContent_Data v c x)
| _ => LRU v c es []
end.


(** InitCS should keep its own resources. *)
Lemma CMF_keep_InitCS :
  forall (v : Node) (c : Content_Name), InitCS v c -> forall es : list Event, exists C : Content c, CMF v c es = Some C.
intros.
unfold CMF.
destruct InitCS_dec.
+eexists; eauto.
+elim n; now auto.
Qed.


(** Nodes other than InitCS does not have contents initially. *)
Lemma CMF_not_create_content :
  forall (v : Node) (c : Content_Name), ~InitCS v c -> CMF v c [] = None.
intros.
unfold CMF.
destruct InitCS_dec.
+elim H; now auto.
+simpl; now auto.
Qed.


Definition CMF_reply_consistency (es : list Event) :=
  forall (v : Node) (c : Content_Name) (es1 es2 : list Event),
   es = es1 ++ ReplyData v c :: es2 -> CMF v c es2 <> None.



Lemma CMF_reply_consistency_less :
 forall (es : list Event) (e : Event),
  CMF_reply_consistency (e :: es) -> CMF_reply_consistency es.
unfold CMF_reply_consistency; intros.
apply H with (e :: es1).
simpl; rewrite H0; now auto.
Qed.


Require Import Permutation.

Lemma cache_exist_permutation :
 forall (c : Content_Name) (l l' : list Content_Name),
  Permutation l l' ->
   cache_exist c l = cache_exist c l'.
intros; induction H.
 now auto.
 simpl; destruct Content_Name_eq_dec; now auto.
 simpl; destruct Content_Name_eq_dec; destruct Content_Name_eq_dec; now auto.
 rewrite IHPermutation1; now auto.
Qed.

Lemma LRU_permutation :
 forall (v : Node) (c : Content_Name) (es : list Event) (l l' : list Content_Name),
  Permutation l l' ->
   LRU v c es l = LRU v c es l'.
induction es; intros.
 simpl.
  destruct (cache_exist c l), (cache_exist c l'), ge_dec, ge_dec; now auto.
 simpl.
  rewrite (Permutation_length H).
  rewrite (cache_exist_permutation c _ _ H).
  destruct ge_dec.
   destruct (cache_exist c l'); auto.
    destruct a; auto.
    destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; subst; auto.
   destruct a; auto.
    destruct Node_eq_dec; auto.
     rewrite (cache_exist_permutation c0 _ _ H).
     destruct InitCS_dec; auto.
     destruct (cache_exist c0 l'); auto.
    destruct Node_eq_dec; auto.
     destruct Content_Name_eq_dec; auto.
     rewrite (cache_exist_permutation c0 _ _ H).
     destruct (cache_exist c0 l'); auto.
Qed.

Lemma cache_exist_In :
 forall (c : Content_Name) (l : list Content_Name),
  cache_exist c l = true -> In c l.
induction l; simpl; intro.
 inversion H.
 destruct Content_Name_eq_dec.
  subst; auto.
  right; now auto.
Qed.

Lemma cache_exist_not_In :
 forall (c : Content_Name) (l : list Content_Name),
  cache_exist c l = false -> ~In c l.
induction l; simpl; intro; intro.
 now auto.
 destruct Content_Name_eq_dec.
  inversion H.
  destruct H0.
   subst; apply n; now auto.
   apply IHl; now auto.
Qed.

Lemma cache_exist_LRU_not_StoreData :
 forall (v : Node) (c : Content_Name) (es : list Event) (l : list Content_Name),
  cache_exist c l = true ->
   LRU v c es l = None ->
   forall (C : Content c), ~In (StoreData v c C) es.
intros v c es; induction es; intros; simpl; intro.
 now auto.
 simpl in H0.
 rewrite H in H0.
 destruct H1.
  subst.
   destruct ge_dec.
    destruct Node_eq_dec.
     destruct Content_Name_eq_dec.
      now inversion H0.
      elim n; now auto.
     elim n; now auto.
    destruct Node_eq_dec.
     destruct Content_Name_eq_dec.
      now inversion H0.
      elim n0; now auto.
     elim n0; now auto.
  destruct ge_dec.
   unfold not in IHes; destruct a; eauto.
    destruct Node_eq_dec; eauto.
    destruct Content_Name_eq_dec; subst; eauto.
    now inversion H0.
   unfold not in IHes; destruct a; eauto.
    destruct Node_eq_dec; eauto.
     destruct InitCS_dec; eauto.
     subst; case_eq (cache_exist c0 l); intro H2; rewrite H2 in H0.
      eauto.
      apply IHes with (c0 :: l) C; auto.
       simpl; destruct Content_Name_eq_dec; now auto.
    destruct Node_eq_dec; eauto.
     destruct Content_Name_eq_dec.
      now inversion H0.
      subst; case_eq (cache_exist c0 l); intro H2; rewrite H2 in H0.
       eauto.
       apply IHes with (c0 :: l) C; auto.
        simpl; destruct Content_Name_eq_dec; now auto.
Qed.

Lemma cache_exist_not_StoreData_LRU_none :
 forall (v : Node) (c : Content_Name) (es : list Event) (l : list Content_Name),
  cache_exist c l = true ->
   (forall (C : Content c), ~In (StoreData v c C) es) ->
   LRU v c es l = None.
intros v c es; induction es; intros; simpl.
 rewrite H; destruct ge_dec; now auto.
 assert (forall C : Content c, ~ In (StoreData v c C) es).
  intros C H1; apply H0 with C; right; now auto.
 rewrite H; destruct ge_dec.
  destruct a; auto.
   destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; subst; auto.
    elim H0 with c3; left; now auto.
  destruct a; auto; destruct Node_eq_dec; auto.
   destruct InitCS_dec; auto.
    case_eq (cache_exist c0 l); intro H2; auto.
    apply IHes; auto.
    simpl; destruct Content_Name_eq_dec; now auto.
   destruct Content_Name_eq_dec; subst.
    elim H0 with c3; left; now auto.
    case_eq (cache_exist c0 l); intro H2; auto.
    apply IHes; auto.
    simpl; destruct Content_Name_eq_dec; now auto.
Qed.



Require Import Omega.

Lemma LRU_l_app :
 forall (v : Node) (c : Content_Name) (es : list Event) (l l' : list Content_Name),
   CMF_reply_consistency es ->
    ~InitCS v c ->
    LRU v c es l = None ->
    cache_exist c l = false ->
    cache_exist c (l'++l) = false ->
    LRU v c es (l'++l) = None.
intros v c es; induction es; intros.
 simpl.
  rewrite H3; destruct ge_dec; now auto.
 simpl in H1; simpl.
  rewrite H3; destruct ge_dec with (length (l'++l)) 3; auto.
  assert (CMF_reply_consistency es) by (apply CMF_reply_consistency_less with a; auto).
  destruct ge_dec.
   elim n; rewrite app_length; omega.
   destruct a; auto.
   +destruct Node_eq_dec; auto.
    destruct InitCS_dec; auto.
    case_eq (cache_exist c0 l); intro H5; rewrite H5 in H1.
     assert (cache_exist c0 (l'++l) = true).
      clear -H5; induction l'.
       simpl; now auto.
       simpl; destruct Content_Name_eq_dec; now auto.
      rewrite H6; now auto.
     case_eq (cache_exist c0 (l' ++ l)); intro H6.
      assert (In c0 l').
       assert (In c0 (l'++l)) by (apply cache_exist_In; auto).
       apply in_app_or in H7; destruct H7.
        now auto.
        elim (cache_exist_not_In c0 l H5); now auto.
       apply in_split in H7; destruct H7 as [l1 [l2 ?]]; subst.
       assert (Permutation ((l1 ++ c0 :: l2) ++ l) (l1 ++ l2 ++ c0 :: l)).
         rewrite <- app_assoc.
         apply Permutation_app_head.
         simpl; apply Permutation_cons_app; now apply Permutation_refl.
        assert (LRU n1 c es ((l1 ++ c0 :: l2) ++ l) = LRU n1 c es (l1 ++ l2 ++ c0 :: l)) by (apply LRU_permutation; auto).
        rewrite H8.
        rewrite app_assoc.
        apply (IHes (c0 :: l) (l1 ++ l2)); auto.
         simpl.
          destruct Content_Name_eq_dec.
           subst; rewrite H3 in H6; now inversion H6.
           now auto.
         rewrite <- app_assoc; assert (cache_exist c ((l1 ++ c0 :: l2) ++ l) = cache_exist c (l1 ++ l2 ++ c0 :: l)) by (apply cache_exist_permutation; auto).
          rewrite <- H9; now auto.
      destruct Content_Name_eq_dec with c c0.
       subst.
        assert (forall (C : Content c0), ~In (StoreData n1 c0 C) es).
         apply cache_exist_LRU_not_StoreData with (c0 :: l); auto.
          simpl; destruct Content_Name_eq_dec.
           now auto.
           elim n3; now auto.
          apply cache_exist_not_StoreData_LRU_none.
           simpl; destruct Content_Name_eq_dec.
            now auto.
            elim n3; now auto.
           now auto.
       assert (Permutation (c0 :: l' ++ l) (l' ++ c0 :: l)).
        apply Permutation_cons_app; now apply Permutation_refl.
        assert (LRU v c es (c0 :: l' ++ l) = LRU v c es (l' ++ c0 :: l)) by (apply LRU_permutation; auto).
        rewrite H8; apply IHes; auto.
         simpl; destruct Content_Name_eq_dec.
          elim n3; now auto.
          now auto.
         assert (cache_exist c (c0 :: l' ++ l) = cache_exist c (l' ++ c0 :: l)) by (apply cache_exist_permutation; auto).
          rewrite <- H9; simpl; destruct Content_Name_eq_dec.
           elim n3; now auto.
           now auto.
   +destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; auto.
    case_eq (cache_exist c0 l); intro H5; rewrite H5 in H1.
     assert (cache_exist c0 (l'++l) = true).
      clear -H5; induction l'.
       simpl; now auto.
       simpl; destruct Content_Name_eq_dec; now auto.
      rewrite H6; now auto.
     case_eq (cache_exist c0 (l' ++ l)); intro H6.
      assert (In c0 l').
       assert (In c0 (l'++l)) by (apply cache_exist_In; auto).
       apply in_app_or in H7; destruct H7.
        now auto.
        elim (cache_exist_not_In c0 l H5); now auto.
       apply in_split in H7; destruct H7 as [l1 [l2 ?]]; subst.
       assert (Permutation ((l1 ++ c0 :: l2) ++ l) (l1 ++ l2 ++ c0 :: l)).
         rewrite <- app_assoc.
         apply Permutation_app_head.
         simpl; apply Permutation_cons_app; now apply Permutation_refl.
        assert (LRU n1 c es ((l1 ++ c0 :: l2) ++ l) = LRU n1 c es (l1 ++ l2 ++ c0 :: l)) by (apply LRU_permutation; auto).
        rewrite H8.
        rewrite app_assoc.
        apply (IHes (c0 :: l) (l1 ++ l2)); auto.
         simpl.
          destruct Content_Name_eq_dec.
           elim n2; now auto.
           now auto.
         rewrite <- app_assoc; assert (cache_exist c ((l1 ++ c0 :: l2) ++ l) = cache_exist c (l1 ++ l2 ++ c0 :: l)) by (apply cache_exist_permutation; auto).
          rewrite <- H9; now auto.
      assert (Permutation (c0 :: l' ++ l) (l' ++ c0 :: l)).
       apply Permutation_cons_app; now apply Permutation_refl.
       assert (LRU v c es (c0 :: l' ++ l) = LRU v c es (l' ++ c0 :: l)) by (apply LRU_permutation; auto).
       rewrite H8; apply IHes; auto.
        simpl; destruct Content_Name_eq_dec.
         elim n2; now auto.
         now auto.
        assert (cache_exist c (c0 :: l' ++ l) = cache_exist c (l' ++ c0 :: l)) by (apply cache_exist_permutation; auto).
         rewrite <- H9; simpl; destruct Content_Name_eq_dec.
          elim n2; now auto.
          now auto.
Qed.



(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Lemma CMF_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event), CMF_reply_consistency (es' ++ es) -> CMF v c es = None -> (forall C : Content c, ~In (StoreData v c C) es') -> CMF v c (es' ++ es) = None.
intros.
unfold CMF in *.
destruct InitCS_dec with v c.
now auto.
induction es'; simpl.
 now auto.
 assert (CMF_reply_consistency (es' ++ es)).
  apply CMF_reply_consistency_less with a.
   rewrite app_comm_cons; now auto.
 assert (LRU v c (es' ++ es) [] = None).
  apply IHes'; auto.
   intros C ?; apply H1 with C; right; now auto.
 destruct a; auto; destruct Node_eq_dec; auto.
 +destruct InitCS_dec; auto.
  destruct Content_Name_eq_dec with c c0; subst.
   elim H with n0 c0 ([]:list Event) (es' ++ es).
    simpl; now auto.
    unfold CMF; destruct InitCS_dec.
     elim n; now auto.
     now auto.
   rewrite <- app_nil_r with Content_Name [c0]; apply LRU_l_app; auto.
    simpl; destruct Content_Name_eq_dec.
     elim n1; now auto.
     now auto.
 +destruct Content_Name_eq_dec; subst.
   elim H1 with c3; simpl; now auto.
   rewrite <- app_nil_r with Content_Name [c0]; apply LRU_l_app; auto.
    simpl; destruct Content_Name_eq_dec.
     elim n1; now auto.
     now auto.
Qed.


End CCN_SimpleNetworkLRU.


Require CCNVerificationWithCM.

Module CCN_SimpleNetwork_Verification := CCNVerificationWithCM.CCN_Protocol_Verification_CM CCN_SimpleNetworkLRU.
Import CCN_SimpleNetwork_Verification.


