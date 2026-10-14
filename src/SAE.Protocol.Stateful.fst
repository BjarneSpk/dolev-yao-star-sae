module SAE.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open SAE.Operations
open SAE.Protocol.Total

#set-options "--fuel 0 --ifuel 1"

/// This module contains the stateful part of SAE:
/// the finite state machine of 12.4.8 (IEEE Std 802.11-2024).
///
/// A STA is a principal, identified by its MAC address (the principal name).
/// For each peer, a STA runs protocol instances.
/// The parent process (12.4.8.6.1) keeps a database of the protocol instances
/// indexed by the peer, and dispatches received frames to them.
///
/// There is one function for each pair of a state and an event
/// of the state machine (12.4.8.6.3 to 12.4.8.6.6):
///
///   state      | Init event   | Com event     | Con event
///   -----------+--------------+---------------+---------------
///   Nothing    | nothing_init | nothing_com   | nothing_con
///   Committed  | (ignored)    | committed_com | committed_con
///   Confirmed  | (ignored)    | confirmed_com | confirmed_con
///   Accepted   | nothing_init | nothing_com   | accepted_con
///
/// (A protocol instance in Accepted state does not handle Init and Com events:
/// the parent process creates a new protocol instance in Nothing state.)
///
/// Each of these functions includes the corresponding checks of the parent process,
/// hence they can be called in any order, with any frame:
/// a function returns `None` if it is not the one handling the situation.
/// Otherwise it returns the timestamps of the frames it has sent
/// (the empty list if the frame was silently discarded).
/// receive_frame is the dispatcher of the parent process.

(*** Passwords ***)

/// Each STA stores the password it shares with a peer.

[@@ with_bytes bytes]
type password_key = {
  peer: principal;
}

%splice [ps_password_key] (gen_parser (`password_key))
%splice [ps_password_key_is_well_formed] (gen_is_well_formed_lemma (`password_key))

[@@ with_bytes bytes]
type password_value = {
  password: bytes;
}

%splice [ps_password_value] (gen_parser (`password_value))
%splice [ps_password_value_is_well_formed] (gen_is_well_formed_lemma (`password_value))

instance map_types_passwords: map_types password_key password_value = {
  tag = "SAE.Passwords";
  ps_key_t = ps_password_key;
  ps_value_t = ps_password_value;
}

[@@ "opaque_to_smt"]
val initialize_passwords: principal -> traceful state_id
let initialize_passwords =
  initialize_map password_key password_value

[@@ "opaque_to_smt"]
val install_password: principal -> state_id -> principal -> bytes -> traceful (option unit)
let install_password sta sess_id peer password =
  add_key_value sta sess_id ({peer} <: password_key) ({password} <: password_value)

[@@ "opaque_to_smt"]
val get_password: principal -> state_id -> principal -> traceful (option bytes)
let get_password sta sess_id peer =
  let*? res: password_value = find_value sta sess_id ({peer} <: password_key) in
  return (Some res.password)

(*** Protocol instances ***)

/// State of a protocol instance (12.4.8.2, 12.4.8.5).
/// A protocol instance in Nothing state has no state yet:
/// it is created and handles its first event in the same step.

/// Committed state: the SAE Commit message was sent,
/// nothing was received yet.

[@@ with_bytes bytes]
type committed_data = {
  peer: principal;
  group: nat_lbytes 2;
  pwe: bytes;
  rand: bytes;
  scalar: bytes;
  element: bytes;
  sc: nat_lbytes 2;
  rc: nat_lbytes 2;
}

%splice [ps_committed_data] (gen_parser (`committed_data))
%splice [ps_committed_data_is_well_formed] (gen_is_well_formed_lemma (`committed_data))

/// Confirmed state: the SAE Commit message and the SAE Confirm message were sent,
/// the peer's SAE Commit message was received.
/// Accepted state: additionally, the peer's SAE Confirm message was received.
/// The secret values and the PWE are not needed anymore.

[@@ with_bytes bytes]
type confirmed_data = {
  peer: principal;
  group: nat_lbytes 2;
  scalar: bytes;
  element: bytes;
  peer_scalar: bytes;
  peer_element: bytes;
  kck: bytes;
  pmk: bytes;
  sc: nat_lbytes 2;
  rc: nat_lbytes 2;
}

%splice [ps_confirmed_data] (gen_parser (`confirmed_data))
%splice [ps_confirmed_data_is_well_formed] (gen_is_well_formed_lemma (`confirmed_data))

[@@ with_bytes bytes]
type sae_instance =
  | Committed: st:committed_data -> sae_instance
  | Confirmed: st:confirmed_data -> sae_instance
  | Accepted: st:confirmed_data -> sae_instance

%splice [ps_sae_instance] (gen_parser (`sae_instance))
%splice [ps_sae_instance_is_well_formed] (gen_is_well_formed_lemma (`sae_instance))

instance parseable_serializeable_bytes_sae_instance: parseable_serializeable bytes sae_instance = mk_parseable_serializeable ps_sae_instance

instance local_state_sae_instance: local_state sae_instance = {
  tag = "SAE.Instance";
  format = parseable_serializeable_bytes_sae_instance;
}

(*** Database of the parent process ***)

/// The parent process manages a database of protocol instances
/// indexed by the peer (12.4.8.6.1).
/// For a given peer, there is at most one protocol instance
/// in Committed or Confirmed state,
/// and at most one protocol instance in Accepted state.

[@@ with_bytes bytes]
type instance_ref =
  | NoInstance: instance_ref
  | SomeInstance: sess_id:state_id -> instance_ref

%splice [ps_instance_ref] (gen_parser (`instance_ref))
%splice [ps_instance_ref_is_well_formed] (gen_is_well_formed_lemma (`instance_ref))

[@@ with_bytes bytes]
type database_key = {
  peer: principal;
}

%splice [ps_database_key] (gen_parser (`database_key))
%splice [ps_database_key_is_well_formed] (gen_is_well_formed_lemma (`database_key))

[@@ with_bytes bytes]
type database_value = {
  // the protocol instance in Committed or Confirmed state
  unaccepted: instance_ref;
  // the protocol instance in Accepted state
  accepted: instance_ref;
}

%splice [ps_database_value] (gen_parser (`database_value))
%splice [ps_database_value_is_well_formed] (gen_is_well_formed_lemma (`database_value))

instance map_types_database: map_types database_key database_value = {
  tag = "SAE.Database";
  ps_key_t = ps_database_key;
  ps_value_t = ps_database_value;
}

(*** Definition of events ***)

/// `Committed`/`Confirmed` events: the protocol instance has committed/confirmed (12.4.5.1).
/// `Auth`, `Fail` and `Del` events: the outputs of a protocol instance
/// to the parent process (12.4.8.3).

/// The constructors are ordered by increasing number of fields on purpose:
/// the OCaml code that F* extracts for the Comparse parser of a type
/// with constructors of different arities matches the patterns in order,
/// and reads too far into a value with fewer fields than the pattern
/// (segmentation fault) if a larger constructor comes first.

[@@ with_bytes bytes]
type sae_event =
  | EvFail: sta:principal -> peer:principal -> sae_event
  | EvDel: sta:principal -> peer:principal -> sae_event
  | EvCommitted: sta:principal -> peer:principal -> scalar:bytes -> element:bytes -> sae_event
  | EvConfirmed: sta:principal -> peer:principal -> scalar:bytes -> element:bytes -> peer_scalar:bytes -> peer_element:bytes -> pmk:bytes -> sae_event
  | EvAuth: sta:principal -> peer:principal -> scalar:bytes -> element:bytes -> peer_scalar:bytes -> peer_element:bytes -> pmk:bytes -> sae_event

%splice [ps_sae_event] (gen_parser (`sae_event))
%splice [ps_sae_event_is_well_formed] (gen_is_well_formed_lemma (`sae_event))

instance event_sae_event: event sae_event = {
  tag = "SAE.Event";
  format = mk_parseable_serializeable ps_sae_event;
}

(*** Setup for the stateful code ***)

type sae_global_sess_ids = {
  passwords: state_id;
  database: state_id;
}

/// Result of the functions of the state machine:
/// the timestamps of the frames that were sent.

type sae_output = list timestamp

(*** Labels used to generate randomness ***)

/// The secret values rand and mask belong to a single protocol instance.

val sae_instance_label:
  principal -> state_id ->
  label
let sae_instance_label sta sess_id =
  principal_tag_state_label sta "SAE.Instance" sess_id

(*** Password setup ***)

/// Generation of a password shared by two STAs,
/// and installation in the password store of each STA.

[@@ "opaque_to_smt"]
val setup_password: sae_global_sess_ids -> principal -> sae_global_sess_ids -> principal -> traceful (option unit)
let setup_password gsi_a sta_a gsi_b sta_b =
  let* password = mk_rand NoUsage (sae_password_label sta_a sta_b) 32 in
  install_password sta_a gsi_a.passwords sta_b password;*?
  install_password sta_b gsi_b.passwords sta_a password;*?
  return (Some ())

(*** Parent process: database of protocol instances ***)

[@@ "opaque_to_smt"]
val initialize_database: principal -> traceful state_id
let initialize_database =
  initialize_map database_key database_value

/// The protocol instances for a peer
/// (no instance at all if the peer is not in the database).

[@@ "opaque_to_smt"]
val lookup_instances: sae_global_sess_ids -> principal -> principal -> traceful database_value
let lookup_instances gsi sta peer =
  let* res_opt = find_value sta gsi.database ({peer} <: database_key) in
  match res_opt with
  | Some res -> return (res <: database_value)
  | None -> return ({unaccepted = NoInstance; accepted = NoInstance} <: database_value)

[@@ "opaque_to_smt"]
val store_instances: sae_global_sess_ids -> principal -> principal -> database_value -> traceful (option unit)
let store_instances gsi sta peer instances =
  add_key_value sta gsi.database ({peer} <: database_key) instances

/// The state of the protocol instance in Committed or Confirmed state for a peer.

[@@ "opaque_to_smt"]
val get_unaccepted_instance: sae_global_sess_ids -> principal -> principal -> traceful (option (state_id & sae_instance))
let get_unaccepted_instance gsi sta peer =
  let* instances = lookup_instances gsi sta peer in
  guard_tr (SomeInstance? instances.unaccepted);*?
  let sess_id = SomeInstance?.sess_id instances.unaccepted in
  let*? st: sae_instance = get_state sta sess_id in
  return (Some (sess_id, st))

/// Deletion of a protocol instance
/// (upon a Del or Fail event from the protocol instance).

[@@ "opaque_to_smt"]
val delete_instance: sae_global_sess_ids -> principal -> principal -> state_id -> traceful (option unit)
let delete_instance gsi sta peer sess_id =
  let* instances = lookup_instances gsi sta peer in
  let unaccepted = if instances.unaccepted = SomeInstance sess_id then NoInstance else instances.unaccepted in
  let accepted = if instances.accepted = SomeInstance sess_id then NoInstance else instances.accepted in
  store_instances gsi sta peer {unaccepted; accepted}

/// Upon an Auth event from a protocol instance,
/// the other protocol instance for the same peer is deleted.

[@@ "opaque_to_smt"]
val accept_instance: sae_global_sess_ids -> principal -> principal -> state_id -> traceful (option unit)
let accept_instance gsi sta peer sess_id =
  store_instances gsi sta peer {unaccepted = NoInstance; accepted = SomeInstance sess_id}

(*** Transmission of SAE messages ***)

/// Transmission of an SAE Commit message (12.4.7.3).

[@@ "opaque_to_smt"]
val send_commit: principal -> principal -> nat_lbytes 2 -> bytes -> bytes -> traceful timestamp
let send_commit sta peer group scalar element =
  send_msg (compute_commit_frame sta peer group scalar element)

/// Construction (12.4.5.5) and transmission (12.4.7.4) of an SAE Confirm message
/// with the current value of the send-confirm counter.

[@@ "opaque_to_smt"]
val send_confirm: principal -> confirmed_data -> traceful timestamp
let send_confirm sta st =
  let confirm = compute_confirm st.kck st.sc st.scalar st.element st.peer_scalar st.peer_element in
  send_msg (compute_confirm_frame sta st.peer st.sc confirm)

(*** PWE and secret generation, construction of the SAE Commit message ***)

/// Generation of the PWE from the password shared with the peer,
/// generation of the secret values rand and mask (12.4.5.2),
/// and computation of the scalar and the element (12.4.5.3).
/// mask is only used here (it is deleted afterwards).

type generate_commit_result = {
  pwe: bytes;
  rand: bytes;
  scalar: bytes;
  element: bytes;
}

[@@ "opaque_to_smt"]
val generate_commit: sae_global_sess_ids -> principal -> principal -> state_id -> traceful (option generate_commit_result)
let generate_commit gsi sta peer sess_id =
  let*? password = get_password sta gsi.passwords peer in
  let pwe = compute_pwe password sta peer in
  let* rand = mk_rand NoUsage (sae_instance_label sta sess_id) 32 in
  let* mask = mk_rand NoUsage (sae_instance_label sta sess_id) 32 in
  let*? commit: compute_commit_result = return (compute_commit pwe rand mask) in
  return (Some ({pwe; rand; scalar = commit.scalar; element = commit.element} <: generate_commit_result))

(*** Nothing state (12.4.8.6.3) ***)

/// Nothing state, Init event.
///
/// Parent process: upon an Initiate event (the SME wants to authenticate with `peer`),
/// if there is a protocol instance for the peer in Committed or Confirmed state,
/// the event is ignored.
/// Otherwise, a protocol instance is created and receives an Init event.
///
/// Protocol instance: zero Sc and Rc, select the group,
/// generate the PWE and the secret values,
/// send an SAE Commit message, and transition to Committed state.

[@@ "opaque_to_smt"]
val nothing_init: sae_global_sess_ids -> principal -> principal -> traceful (option sae_output)
let nothing_init gsi sta peer =
  let* instances = lookup_instances gsi sta peer in
  guard_tr (NoInstance? instances.unaccepted);*?
  let* sess_id = new_session_id sta in
  let group = sae_configured_group sta in
  let*? commit = generate_commit gsi sta peer sess_id in
  let st: committed_data = {
    peer; group;
    pwe = commit.pwe; rand = commit.rand;
    scalar = commit.scalar; element = commit.element;
    sc = 0; rc = 0;
  } in
  trigger_event sta (EvCommitted sta peer st.scalar st.element);*
  set_state sta sess_id (Committed st <: sae_instance);*
  store_instances gsi sta peer {instances with unaccepted = SomeInstance sess_id};*?
  let* commit_ts = send_commit sta peer group st.scalar st.element in
  return (Some [commit_ts])

/// Nothing state, Com event.
///
/// Parent process: upon receipt of an SAE Commit message,
/// if there is no protocol instance for the peer in Committed or Confirmed state,
/// a protocol instance is created and receives a Com event,
/// unless there is a protocol instance in Accepted state
/// which was authenticated with the same peer-scalar (the frame is discarded).
///
/// Protocol instance: check the status code and the group,
/// zero Sc and Rc, generate the PWE and the secret values,
/// and process the peer's SAE Commit message.
/// If this fails, discard the frame and send a Del event to the parent process.
/// Otherwise, send an SAE Commit message, increment Sc,
/// send an SAE Confirm message, and transition to Confirmed state.

[@@ "opaque_to_smt"]
val nothing_com: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let nothing_com gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? com: commit_frame = return (decode_commit_frame sta frame) in
  let peer = com.sa in
  let* instances = lookup_instances gsi sta peer in
  guard_tr (NoInstance? instances.unaccepted);*?
  let*? is_known_scalar: bool = (
    match instances.accepted with
    | NoInstance -> return (Some false)
    | SomeInstance accepted_sess_id -> (
      let*? accepted_st: sae_instance = get_state sta accepted_sess_id in
      guard_tr (Accepted? accepted_st);*?
      return (Some ((Accepted?.st accepted_st).peer_scalar = (Commit?.msg com.body).scalar))
    )
  ) in
  if is_known_scalar then
    return (Some [])
  else (
    let* sess_id = new_session_id sta in
    if com.status <> status_success || not (sae_is_supported_group sta (Commit?.msg com.body).group) then (
      trigger_event sta (EvDel sta peer);*
      return (Some [])
    ) else (
      let group = (Commit?.msg com.body).group in
      let*? commit = generate_commit gsi sta peer sess_id in
      match process_commit commit.pwe commit.rand commit.scalar (Commit?.msg com.body).scalar (Commit?.msg com.body).element with
      | None -> (
        trigger_event sta (EvDel sta peer);*
        return (Some [])
      )
      | Some keys -> (
        let*? sc = return (sae_increment_counter 0) in
        let st: confirmed_data = {
          peer; group;
          scalar = commit.scalar; element = commit.element;
          peer_scalar = (Commit?.msg com.body).scalar; peer_element = (Commit?.msg com.body).element;
          kck = keys.kck; pmk = keys.pmk;
          sc; rc = 0;
        } in
        trigger_event sta (EvCommitted sta peer st.scalar st.element);*
        trigger_event sta (EvConfirmed sta peer st.scalar st.element st.peer_scalar st.peer_element st.pmk);*
        set_state sta sess_id (Confirmed st <: sae_instance);*
        store_instances gsi sta peer {instances with unaccepted = SomeInstance sess_id};*?
        let* commit_ts = send_commit sta peer group st.scalar st.element in
        let* confirm_ts = send_confirm sta st in
        return (Some [commit_ts; confirm_ts])
      )
    )
  )

/// Nothing state, Con event.
///
/// Parent process: upon receipt of an SAE Confirm message,
/// if there is no protocol instance for the peer, the frame is discarded.
/// (A protocol instance in Nothing state never receives an SAE Confirm message.)

[@@ "opaque_to_smt"]
val nothing_con: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let nothing_con gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? con: confirm_frame = return (decode_confirm_frame sta frame) in
  let* instances = lookup_instances gsi sta con.sa in
  guard_tr (NoInstance? instances.unaccepted && NoInstance? instances.accepted);*?
  return (Some [])

(*** Committed state (12.4.8.6.4) ***)

/// Committed state, Com event.
///
/// Frames with a nonzero status code or another group are discarded.
/// If the scalar or the element of the peer match those of the protocol instance,
/// the frame is discarded (reflection attack).
/// Otherwise the peer's SAE Commit message is processed.
/// If this fails, send a Fail event to the parent process.
/// Otherwise, increment Sc (thereby setting its value to one),
/// send an SAE Confirm message, and transition to Confirmed state.

[@@ "opaque_to_smt"]
val committed_com: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let committed_com gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? com: commit_frame = return (decode_commit_frame sta frame) in
  let peer = com.sa in
  let*? unaccepted = get_unaccepted_instance gsi sta peer in
  let (sess_id, inst) = unaccepted in
  guard_tr (Committed? inst);*?
  let own = Committed?.st inst in
  if com.status <> status_success then
    return (Some [])
  else if (Commit?.msg com.body).group <> own.group then
    return (Some [])
  else if is_reflected_commit own.scalar own.element (Commit?.msg com.body).scalar (Commit?.msg com.body).element then
    return (Some [])
  else (
    match process_commit own.pwe own.rand own.scalar (Commit?.msg com.body).scalar (Commit?.msg com.body).element with
    | None -> (
      trigger_event sta (EvFail sta peer);*
      delete_instance gsi sta peer sess_id;*?
      return (Some [])
    )
    | Some keys -> (
      let*? sc = return (sae_increment_counter own.sc) in
      let st: confirmed_data = {
        peer; group = own.group;
        scalar = own.scalar; element = own.element;
        peer_scalar = (Commit?.msg com.body).scalar; peer_element = (Commit?.msg com.body).element;
        kck = keys.kck; pmk = keys.pmk;
        sc; rc = own.rc;
      } in
      trigger_event sta (EvConfirmed sta peer st.scalar st.element st.peer_scalar st.peer_element st.pmk);*
      set_state sta sess_id (Confirmed st <: sae_instance);*
      let* confirm_ts = send_confirm sta st in
      return (Some [confirm_ts])
    )
  )

/// Committed state, Con event.
///
/// The peer's SAE Commit message was not received yet:
/// the last SAE Commit message is sent again.

[@@ "opaque_to_smt"]
val committed_con: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let committed_con gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? con: confirm_frame = return (decode_confirm_frame sta frame) in
  let peer = con.sa in
  let*? unaccepted = get_unaccepted_instance gsi sta peer in
  let (sess_id, inst) = unaccepted in
  guard_tr (Committed? inst);*?
  let own = Committed?.st inst in
  let* commit_ts = send_commit sta peer own.group own.scalar own.element in
  return (Some [commit_ts])

(*** Confirmed state (12.4.8.6.5) ***)

/// Confirmed state, Com event.
///
/// Frames with a nonzero status code, or with a group different from
/// the one of the last valid SAE Commit message received, are discarded.
/// Otherwise, increment Sc, and send the SAE Commit message
/// and the SAE Confirm message (with the new Sc value) again.

[@@ "opaque_to_smt"]
val confirmed_com: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let confirmed_com gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? com: commit_frame = return (decode_commit_frame sta frame) in
  let peer = com.sa in
  let*? unaccepted = get_unaccepted_instance gsi sta peer in
  let (sess_id, inst) = unaccepted in
  guard_tr (Confirmed? inst);*?
  let own = Confirmed?.st inst in
  if com.status <> status_success then
    return (Some [])
  else if (Commit?.msg com.body).group <> own.group then
    return (Some [])
  else (
    let*? sc = return (sae_increment_counter own.sc) in
    let st: confirmed_data = {own with sc} in
    set_state sta sess_id (Confirmed st <: sae_instance);*
    let* commit_ts = send_commit sta peer st.group st.scalar st.element in
    let* confirm_ts = send_confirm sta st in
    return (Some [commit_ts; confirm_ts])
  )

/// Confirmed state, Con event.
///
/// The peer's SAE Confirm message is processed (12.4.5.6).
/// If the verification fails, send a Fail event to the parent process.
/// Otherwise, set Rc to the received send-confirm counter, set Sc to 2^16 - 1,
/// send an Auth event to the parent process, and transition to Accepted state.
/// The protocol instance now holds the PMK shared with the peer.

[@@ "opaque_to_smt"]
val confirmed_con: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let confirmed_con gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? con: confirm_frame = return (decode_confirm_frame sta frame) in
  let peer = con.sa in
  let*? unaccepted = get_unaccepted_instance gsi sta peer in
  let (sess_id, inst) = unaccepted in
  guard_tr (Confirmed? inst);*?
  let own = Confirmed?.st inst in
  if not (verify_confirm own.kck (Confirm?.msg con.body).send_confirm own.scalar own.element own.peer_scalar own.peer_element (Confirm?.msg con.body).confirm) then (
    trigger_event sta (EvFail sta peer);*
    delete_instance gsi sta peer sess_id;*?
    return (Some [])
  ) else (
    let st: confirmed_data = {own with rc = (Confirm?.msg con.body).send_confirm; sc = sae_max_counter} in
    trigger_event sta (EvAuth sta peer st.scalar st.element st.peer_scalar st.peer_element st.pmk);*
    set_state sta sess_id (Accepted st <: sae_instance);*
    accept_instance gsi sta peer sess_id;*?
    return (Some [])
  )

(*** Accepted state (12.4.8.6.6) ***)

/// Accepted state, Con event.
///
/// Parent process: the SAE Confirm message is passed to the protocol instance
/// in Accepted state if it is the only protocol instance for the peer.
///
/// Protocol instance: there is no guarantee that the peer received
/// the last SAE Confirm message.
/// If the received send-confirm counter is not greater than Rc,
/// or is equal to 2^16 - 1, the frame is discarded.
/// If the verification of the SAE Confirm message fails, the frame is discarded.
/// Otherwise, set Rc to the received send-confirm counter,
/// and send a new SAE Confirm message (with Sc set to 2^16 - 1).

[@@ "opaque_to_smt"]
val accepted_con: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let accepted_con gsi sta msg_ts =
  let*? frame = recv_msg msg_ts in
  let*? con: confirm_frame = return (decode_confirm_frame sta frame) in
  let peer = con.sa in
  let* instances = lookup_instances gsi sta peer in
  guard_tr (NoInstance? instances.unaccepted && SomeInstance? instances.accepted);*?
  let sess_id = SomeInstance?.sess_id instances.accepted in
  let*? inst: sae_instance = get_state sta sess_id in
  guard_tr (Accepted? inst);*?
  let own = Accepted?.st inst in
  if (Confirm?.msg con.body).send_confirm <= own.rc || (Confirm?.msg con.body).send_confirm = sae_max_counter then
    return (Some [])
  else if not (verify_confirm own.kck (Confirm?.msg con.body).send_confirm own.scalar own.element own.peer_scalar own.peer_element (Confirm?.msg con.body).confirm) then
    return (Some [])
  else (
    let st: confirmed_data = {own with rc = (Confirm?.msg con.body).send_confirm; sc = sae_max_counter} in
    set_state sta sess_id (Accepted st <: sae_instance);*
    let* confirm_ts = send_confirm sta st in
    return (Some [confirm_ts])
  )

(*** Parent process (12.4.8.6.1) ***)

/// Upon an Initiate event, the parent process creates a protocol instance
/// and sends it an Init event
/// (unless there is a protocol instance in Committed or Confirmed state).

[@@ "opaque_to_smt"]
val initiate: sae_global_sess_ids -> principal -> principal -> traceful (option sae_output)
let initiate gsi sta peer =
  nothing_init gsi sta peer

/// Upon receipt of a frame, the parent process dispatches it
/// to the protocol instance for the peer that sent the frame:
/// - an SAE Commit message is passed (as a Com event)
///   to the protocol instance in Committed or Confirmed state if there is one,
///   otherwise to a new protocol instance (in Nothing state).
/// - an SAE Confirm message is passed (as a Con event)
///   to the protocol instance which is not in Accepted state if there is one,
///   otherwise to the protocol instance in Accepted state.
///   If there is no protocol instance, the frame is discarded.

[@@ "opaque_to_smt"]
val receive_frame: sae_global_sess_ids -> principal -> timestamp -> traceful (option sae_output)
let receive_frame gsi sta msg_ts =
  let*? frame_bytes = recv_msg msg_ts in
  let*? frame: auth_frame = return (decode_frame sta frame_bytes) in
  let* instances = lookup_instances gsi sta frame.sa in
  match frame.body, instances.unaccepted, instances.accepted with
  | Commit _, NoInstance, _ ->
    nothing_com gsi sta msg_ts
  | Confirm _, NoInstance, NoInstance ->
    nothing_con gsi sta msg_ts
  | Confirm _, NoInstance, SomeInstance _ ->
    accepted_con gsi sta msg_ts
  | _, SomeInstance sess_id, _ -> (
    let*? inst: sae_instance = get_state sta sess_id in
    match frame.body, inst with
    | Commit _, Committed _ -> committed_com gsi sta msg_ts
    | Confirm _, Committed _ -> committed_con gsi sta msg_ts
    | Commit _, Confirmed _ -> confirmed_com gsi sta msg_ts
    | Confirm _, Confirmed _ -> confirmed_con gsi sta msg_ts
    | _, Accepted _ -> return None
  )
