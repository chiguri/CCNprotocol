(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Network sample : simple network with only 7 nodes (bound) *)
(** * Content Management sample : R1, R2, R3 and R4 can store only one content, and each of others can store 3 contents which are used most recently in the node *)


Require Import List.
Import ListNotations.

Require CCNProtocol.
Require CCNContentManagement.
Require Import CCNSimpleNetwork.

Module CCN_SimpleNetworkFIFOMixed <: CCNContentManagement.CCN_Content_Management.

Module Topology := CCN_SimpleNetwork.
Import Topology.

Module OldProtocol := CCNProtocol.CCN_Protocol Topology.
Import OldProtocol.

Fixpoint FIFO_1 (v : Node) (c : Content_Name) (es : list Event) : option (Content c) :=
match es with
| nil => None
| StoreData v' c' C :: es' =>
   match Node_eq_dec v v' with
   | left _ => match Content_Name_eq_dec c c' with
               | left x => eq_rec_r (fun t => option (Content t)) (Some C) x
               | _ => None (* Because v uses its storage for c' *)
               end
   | _ => FIFO_1 v c es'
   end
| _ :: es' => FIFO_1 v c es'
end.


Definition CMF (v : Node) (c : Content_Name) (es : list Event) : option (Content c) :=
match v with
| R1 | R2 | R3 | R4 =>
   match InitCS_dec v c with
   | left x => Some (InitContent_Data v c x)
   | _ => FIFO_1 v c es
   end
| _ => Content_get v c es
end.


(** InitCS should keep its own resources. *)
Lemma CMF_keep_InitCS :
  forall (v : Node) (c : Content_Name), InitCS v c -> forall es : list Event, exists C : Content c, CMF v c es = Some C.
intros.
unfold CMF.
destruct InitCS_dec.
Focus 2.
elim n; now auto.
destruct v.
+induction es.
  simpl.
   destruct InitCS_dec.
    now eauto.
    elim n; now auto.
  destruct a; simpl; auto.
   destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; subst; eauto.
     cbv.
     destruct c0; now eauto.
+eexists; eauto.
+eexists; eauto.
+eexists; eauto.
+eexists; eauto.
+induction es.
  simpl.
   destruct InitCS_dec.
    now eauto.
    elim n; now auto.
  destruct a; simpl; auto.
   destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; subst; eauto.
     cbv.
     destruct c0; now eauto.
+induction es.
  simpl.
   destruct InitCS_dec.
    now eauto.
    elim n; now auto.
  destruct a; simpl; auto.
   destruct Node_eq_dec; auto.
    destruct Content_Name_eq_dec; subst; eauto.
     cbv.
     destruct c0; now eauto.
Qed.


(** Nodes other than InitCS does not have contents initially. *)
Lemma CMF_not_create_content :
  forall (v : Node) (c : Content_Name), ~InitCS v c -> CMF v c [] = None.
intros.
unfold CMF.
unfold Content_get.
destruct InitCS_dec.
+elim H; now auto.
+destruct v; simpl; now auto.
Qed.


Definition CMF_reply_consistency (es : list Event) :=
  forall (v : Node) (c : Content_Name) (es1 es2 : list Event),
   es = es1 ++ ReplyData v c :: es2 -> CMF v c es2 <> None.


Lemma Content_get_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event), Content_get v c es = None -> (forall C : Content c, ~In (StoreData v c C) es') -> Content_get v c (es' ++ es) = None.
intros; induction es'; simpl; auto.
assert (forall C : Content c, ~In (StoreData v c C) es').
 intros C ?; apply H0 with C; right; now auto.
destruct a; auto.
destruct Node_eq_dec; auto.
destruct Content_Name_eq_dec; auto.
subst; elim H0 with c3; left; now auto.
Qed.


Lemma FIFO_1_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event),
   ~InitCS v c ->
    FIFO_1 v c es = None ->
    (forall C : Content c, ~In (StoreData v c C) es') ->
    FIFO_1 v c (es' ++ es) = None.
intros; induction es'.
 simpl; now auto.
 assert (forall C : Content c, ~ In (StoreData v c C) es').
  intros C ?; apply H1 with C; right; now auto.
  simpl; destruct a; auto.
  destruct Node_eq_dec; auto.
  destruct Content_Name_eq_dec; auto.
  subst; elim H1 with c3; left; now auto.
Qed.



(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Lemma CMF_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event), CMF_reply_consistency (es' ++ es) -> CMF v c es = None -> (forall C : Content c, ~In (StoreData v c C) es') -> CMF v c (es' ++ es) = None.
intros v c es es' _.
unfold CMF.
destruct v; try (apply Content_get_consistency; auto); destruct InitCS_dec; try (apply FIFO_1_consistency); auto.
Qed.


End CCN_SimpleNetworkFIFOMixed.

Require CCNVerificationWithCM.

Module CCN_SimpleNetwork_Verification := CCNVerificationWithCM.CCN_Protocol_Verification_CM CCN_SimpleNetworkFIFOMixed.
Import CCN_SimpleNetwork_Verification.


