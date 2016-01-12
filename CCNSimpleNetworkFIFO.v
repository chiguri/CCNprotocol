(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Network sample : simple network with only 7 nodes (bound) *)


Require Import List.
Import ListNotations.

Require CCNProtocol.
Require CCNContentManagement.
Require Import CCNSimpleNetwork.

Module CCN_SimpleNetworkFIFO <: CCNContentManagement.CCN_Content_Management.

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
match InitCS_dec v c with
| left x => Some (InitContent_Data v c x)
| _ => FIFO_1 v c es
end.


(** InitCS should keep its own resources. *)
Lemma CMF_keep_InitCS :
  forall (v : Node) (c : Content_Name), InitCS v c -> forall es : list Event, exists C : Content c, CMF v c es = Some C.
intros.
unfold CMF.
destruct InitCS_dec with v c.
+eexists; eauto.
+elim n; now auto.
Qed.


(** Nodes other than InitCS does not have contents initially. *)
Lemma CMF_not_create_content :
  forall (v : Node) (c : Content_Name), ~InitCS v c -> CMF v c [] = None.
intros.
unfold CMF.
destruct InitCS_dec with v c.
+elim H; now auto.
+simpl; now auto.
Qed.


Definition CMF_reply_consistency (v : Node) (es : list Event) :=
  forall (c : Content_Name) (es1 es2 : list Event),
   es = es1 ++ ReplyData v c :: es2 -> CMF v c es2 <> None.


(** If once the node seems not to have requested contents, it will not have until it will receive and store the contents. *)
Lemma CMF_consistency :
  forall (v : Node) (c : Content_Name) (es es' : list Event), CMF_reply_consistency v (es' ++ es) -> CMF v c es = None -> (forall C : Content c, ~In (StoreData v c C) es') -> CMF v c (es' ++ es) = None.
intros v c es es' _ H H0.
unfold CMF in *.
destruct InitCS_dec with v c.
+now auto.
+induction es'.
 -simpl; now auto.
 -destruct a; try (apply IHes'; intros C ?; apply H0 with C; right; now auto).
  simpl.
  destruct Node_eq_dec with v n0.
  *destruct Content_Name_eq_dec with c c0; subst.
    elim (H0 c3).
     left; now auto.
    now auto.
  *apply IHes'.
   intros C ?.
   apply H0 with C.
   right; now auto.
Qed.


End CCN_SimpleNetworkFIFO.


Require CCNVerificationWithCM.

Module CCN_SimpleNetwork_Verification := CCNVerificationWithCM.CCN_Protocol_Verification_CM CCN_SimpleNetworkFIFO.
Import CCN_SimpleNetwork_Verification.


