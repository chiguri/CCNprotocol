
Require Import List.
Import ListNotations.

Require CCNTopology.



(** Module (functor) using CCN_Network (topology) N *)
(** This makes CCN protocol on N *)
Module CCN_Protocol (N : CCNTopology.CCN_Network).
Import N.

(** Packet in network *)
Inductive Packet : Set :=
| Interest : Node -> Node -> Content_Name -> Packet
| Data : Node -> Node -> forall c : Content_Name, Content c -> Packet.


(** Event in CCS Network *)
Inductive Event :=
| Request : Node -> Content_Name -> Event
| ForwardInterest : Node -> Content_Name -> Event
| AddPIT : Node -> Node -> Content_Name -> Event
| ReplyData : Node -> Content_Name -> Event
| ForwardData : Node -> Content_Name -> Event (* Dataを送るとPITが消去 *)
| StoreData : Node -> forall c : Content_Name, Content c -> Event.
(* CSからのData削除を入れるか考え中だが、今回は見送り。
入れるとしたらInitCSに注意すること。あとはstraightforward。 *)
(* あと、性質に使わないのでpacket dropについてeventにしていないが、
もし必要ならばすること。多分基本的にはなにも変わらない。 *)


(** Get Content : If this returns None, the content is not stored / CS match fails *)
Fixpoint Content_get (v : Node) (c : Content_Name) (es : list Event) : option (Content c) :=
match es with
| nil =>
   match InitCS_dec v c with
   | left x => Some (InitContent_Data v c x)
   | right _ => None
   end
| StoreData v' c' C :: es' =>
   match (Node_eq_dec v v', Content_Name_eq_dec c c') with
   | (left _, left x) => eq_rec_r (fun t => option (Content t)) (Some C) x
   | _ => Content_get v c es'
   end
| _ :: es' => Content_get v c es'
end.



(** Get PIT list : If this returns nil, no PIT is checked / PIT match fails *)
Fixpoint PIT_list (v : Node) (c : Content_Name) (es : list Event) : list Node :=
match es with
| nil => nil
| AddPIT v1 v2 c' :: es' =>
    match Node_eq_dec v v1 with
    | left _ => match Content_Name_eq_dec c c' with
                | left _ => v2 :: PIT_list v c es'
                | right _ => PIT_list v c es'
                end
    | right _ => PIT_list v c es'
    end
| ForwardData v' c' :: es' =>
    match Node_eq_dec v v' with
    | left _ => match Content_Name_eq_dec c c' with
                | left _ => nil
                | right _ => PIT_list v c es'
                end
    | right _ => PIT_list v c es'
    end
| _ :: es' => PIT_list v c es'
end.



(** list of interest packet (used in request) *)
Definition Broadcast_Interest (v : Node) (c : Content_Name) : list Packet :=
  map (fun v' => Interest v v' c) (Connected_list v).

(** list of interest packet (used in forwarding interest packet *)
Definition FIB_Interest (v : Node) (c : Content_Name) : list Packet :=
  map (fun v' => Interest v v' c) (FIB_list v c). 

Definition PIT_Data (v : Node) (c : Content_Name) (C : Content c) (es : list Event) : list Packet :=
  map (fun v' => Data v v' c C) (PIT_list v c es).

(*
疑問：問い：FIB_reachableであることはForwardを満たすことの必要十分条件か？
答え：RequestがFIBマッチをするならYes、FIBマッチをせずに全方向に投げるならNo.
Noの根拠：A-B-CというトポロジーでAの持つコンテンツについて、CはFIBをBに向けていないとする。
BはFIBでAを指すいるとき、上の条件に対してデータが帰ってくるかについては綺麗に分かれる。
問い：ノードはRequest時にFIBマッチをするか？
答え：論文を読む限りNo。拡散する、とだけ書いてあるため。
*)

(** Definition of CCN protocol *)
(** CCNprotocol event-list packet-list *)
Inductive CCNprotocol : list Event -> list Packet -> Prop :=
| ccn_init : CCNprotocol nil nil
| ccn_request : forall (v : Node) (c : Content_Name) (es : list Event) (ps ps' : list Packet),
   CCNprotocol es ps ->
    Content_get v c es = None ->
    ps' = Broadcast_Interest v c ++ ps ->
    CCNprotocol (Request v c :: es) ps'
| ccn_forward_interest : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    Content_get v' c es = None ->
    PIT_list v' c es = nil ->
    FIB_list v' c <> nil ->
    ps' = FIB_Interest v' c ++ ps1 ++ ps2 ->
    CCNprotocol (ForwardInterest v' c :: AddPIT v' v c :: es) ps'
| ccn_add_pit : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    Content_get v' c es = None ->
    PIT_list v' c es <> nil ->
    ~ In v (PIT_list v' c es) ->
    FIB_list v' c <> nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol (AddPIT v' v c :: es) ps'
| ccn_drop_interest_fib : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    Content_get v' c es = None ->
    FIB_list v' c = nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'
| ccn_drop_interest_pit : forall (v v' : Node) (c : Content_Name) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    Content_get v' c es = None ->
    In v (PIT_list v' c es) ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'
| ccn_rpsly_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Interest v v' c :: ps2) ->
    Content_get v' c es = Some C ->
    ps' = Data v' v c C :: ps1 ++ ps2 ->
    CCNprotocol (ReplyData v' c :: es) ps'
| ccn_store_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    In (Request v' c) es ->
    PIT_list v' c es = nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: es) ps'
| ccn_forward_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    ~ In (Request v' c) es ->
    PIT_list v' c es <> nil ->
    ps' = (PIT_Data v' c C es) ++ ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: ForwardData v' c :: es) ps'
| ccn_store_forward : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    In (Request v' c) es ->
    PIT_list v' c es <> nil ->
    ps' = (PIT_Data v' c C es) ++ ps1 ++ ps2 ->
    CCNprotocol (StoreData v' c C :: ForwardData v' c :: es) ps'
| ccn_drop_data : forall (v v' : Node) (c : Content_Name) (C : Content c) (es : list Event) (ps1 ps2 ps' : list Packet),
   CCNprotocol es (ps1 ++ Data v v' c C :: ps2) ->
    ~ In (Request v' c) es ->
    PIT_list v' c es = nil ->
    ps' = ps1 ++ ps2 ->
    CCNprotocol es ps'.
(* 基本Dataパケットをdropすることはない。例外はInterestパケットをCSを持ってる相手に二回以上連続で送った場合。 *)



(* In で使うからEventのdecision procedureを作ること *)

End CCN_Protocol.
