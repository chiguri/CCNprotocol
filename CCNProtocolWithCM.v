(* Written by Sosuke Moriguchi (chiguri), Kwansei Gakuin University *)

(** * Functor from Network Topology with Protocol Setting to a CCN protocol on the network complying content managements. *)

Require Import List.
Import ListNotations.

Require CCNTopology.
Require CCNContentManagement.


Module CCN_Protocol_CM (N : CCNContentManagement.CCN_Content_Managements).
Import N.
Export OldProtocol.
Import Topology.



(** Definition of behaviors of the CCN protocol *)
Inductive CCNprotocol : list Event -> list Packet -> Prop :=
| ccn_init : CCNprotocol nil nil
| ccn_request : forall (v : Node) (c : Content_Name) (es : list Event) (ps ps' : list Packet),
   CCNprotocol es ps ->
    CMF v c es = None ->
    ps' = Broadcast_Interest v c ++ ps ->
    CCNprotocol (Request v c :: es) ps'
| ccn_forward_interest : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    CMF v' c es = None ->
    PIT_list v' c es = nil ->
    FIB_list v' c <> nil ->
    ps' = FIB_Interest v' c ++ ps1 ++ ps2 ->
    CCNprotocol (ForwardInterest v' c :: AddPIT v' v c :: es) ps'
| ccn_add_pit : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    CMF v' c es = None ->
    PIT_list v' c es <> nil ->
    ~ In v (PIT_list v' c es) ->
    FIB_list v' c <> nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol (AddPIT v' v c :: es) ps'
| ccn_drop_interest_fib : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    CMF v' c es = None ->
    FIB_list v' c = nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'
| ccn_drop_interest_pit : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    CMF v' c es = None ->
    In v (PIT_list v' c es) ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'
| ccn_reply_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    CMF v' c es = Some C ->
    ps' = Data v' v c C :: ps1 ++ ps2 ->
    CCNprotocol (ReplyData v' c :: es) ps'
| ccn_store_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    CMF v' c es = None ->
    In (Request v' c) es ->
    PIT_list v' c es = nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: es) ps'
| ccn_forward_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    CMF v' c es = None ->
    ~ In (Request v' c) es ->
    PIT_list v' c es <> nil ->
    ps' = (PIT_Data v' c C es) ++ ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: ForwardData v' c :: es) ps'
| ccn_store_forward : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    CMF v' c es = None ->
    In (Request v' c) es ->
    PIT_list v' c es <> nil ->
    ps' = (PIT_Data v' c C es) ++ ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: ForwardData v' c :: es) ps'
| ccn_drop_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    CMF v' c es <> None ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'.


End CCN_Protocol_CM.

