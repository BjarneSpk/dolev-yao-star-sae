module SAE.Debug

open Comparse
open DY.Core
open DY.Lib
open SAE.Operations
open SAE.Protocol.Total
open SAE.Protocol.Stateful
open SAE.Debug.Printing

(*** Setup ***)

/// Initialization of the password store
/// and of the database of protocol instances of a STA.

val setup_sta: principal -> traceful sae_global_sess_ids
let setup_sta sta =
  let* passwords = initialize_passwords sta in
  let* database = initialize_database sta in
  return {passwords; database}

(*** Helpers ***)

/// The frames sent by a function of the state machine.

val one_frame: sae_output -> option timestamp
let one_frame output =
  match output with
  | [ts] -> Some ts
  | _ -> None

val two_frames: sae_output -> option (timestamp & timestamp)
let two_frames output =
  match output with
  | [ts1; ts2] -> Some (ts1, ts2)
  | _ -> None

val no_frame: sae_output -> option unit
let no_frame output =
  match output with
  | [] -> Some ()
  | _ -> None

/// The PMK of the protocol instance in Accepted state.

val get_accepted_pmk: sae_global_sess_ids -> principal -> principal -> traceful (option bytes)
let get_accepted_pmk gsi sta peer =
  let* instances = lookup_instances gsi sta peer in
  guard_tr (SomeInstance? instances.accepted);*?
  let*? st: sae_instance = get_state sta (SomeInstance?.sess_id instances.accepted) in
  guard_tr (Accepted? st);*?
  return (Some (Accepted?.st st).pmk)

/// Successful termination: both STAs have accepted, and share the PMK.

val check_shared_pmk: sae_global_sess_ids -> principal -> sae_global_sess_ids -> principal -> traceful (option unit)
let check_shared_pmk gsi_a sta_a gsi_b sta_b =
  let*? pmk_a = get_accepted_pmk gsi_a sta_a sta_b in
  let*? pmk_b = get_accepted_pmk gsi_b sta_b sta_a in
  guard_tr (pmk_a = pmk_b);*?
  return (Some ())

/// Printing of the trace, and of the result of a run.
/// `expected` describes the behavior the run checks.

val report: string -> string -> option unit -> traceful (option unit)
let report title expected result =
  let* tr = get_trace in
  let _ = IO.debug_print_string (Printf.sprintf "************* %s *************\n" title) in
  let _ = IO.debug_print_string (trace_to_string sae_trace_to_string_printers tr) in
  let _ = IO.debug_print_string (
    match result with
    | Some _ -> Printf.sprintf "==> OK: %s\n\n" expected
    | None -> Printf.sprintf "==> UNEXPECTED BEHAVIOR (expected: %s)\n\n" expected
  ) in
  return result

(*** Checks on the state of a STA ***)

/// A check is a `traceful` function returning `Some ()` if it succeeds.

val check: bool -> option unit
let check b =
  if b then Some () else None

/// The STA has no protocol instance for the peer.

val has_no_instance: sae_global_sess_ids -> principal -> principal -> traceful bool
let has_no_instance gsi sta peer =
  let* instances = lookup_instances gsi sta peer in
  return (NoInstance? instances.unaccepted && NoInstance? instances.accepted)

val is_committed: sae_global_sess_ids -> principal -> principal -> traceful bool
let is_committed gsi sta peer =
  let* res = get_unaccepted_instance gsi sta peer in
  match res with
  | Some (_, Committed _) -> return true
  | _ -> return false

val is_confirmed: sae_global_sess_ids -> principal -> principal -> traceful bool
let is_confirmed gsi sta peer =
  let* res = get_unaccepted_instance gsi sta peer in
  match res with
  | Some (_, Confirmed _) -> return true
  | _ -> return false

/// The state of the protocol instance in Accepted state, if there is one.

val get_accepted: sae_global_sess_ids -> principal -> principal -> traceful (option confirmed_data)
let get_accepted gsi sta peer =
  let* instances = lookup_instances gsi sta peer in
  guard_tr (SomeInstance? instances.accepted);*?
  let*? st: sae_instance = get_state sta (SomeInstance?.sess_id instances.accepted) in
  guard_tr (Accepted? st);*?
  return (Some (Accepted?.st st))

(*** Attacker ***)

/// The attacker controls the network:
/// it can send arbitrary frames, with an arbitrary sender address (SA).
/// It only uses values it can read on the network (scalars, elements, confirms),
/// or values it makes up.

val garbage: bytes
let garbage =
  sae_string_to_bytes "garbage"

val forge_commit: principal -> principal -> nat_lbytes 2 -> bytes -> bytes -> traceful timestamp
let forge_commit sa da group scalar element =
  send_msg (compute_commit_frame sa da group scalar element)

val forge_commit_with_status: principal -> principal -> nat_lbytes 2 -> nat_lbytes 2 -> bytes -> bytes -> traceful timestamp
let forge_commit_with_status sa da status group scalar element =
  let body = Commit ({group; scalar; element} <: commit_message) in
  send_msg (serialize auth_frame ({sa; da; status; body} <: auth_frame))

val forge_confirm: principal -> principal -> nat_lbytes 2 -> bytes -> traceful timestamp
let forge_confirm sa da send_confirm confirm =
  send_msg (compute_confirm_frame sa da send_confirm confirm)

/// The scalar, the element (or the send-confirm counter and the confirm)
/// of a frame on the network (everybody can read them).

val read_commit: principal -> timestamp -> traceful (option commit_message)
let read_commit receiver ts =
  let*? frame = recv_msg ts in
  let*? com: commit_frame = return (decode_commit_frame receiver frame) in
  return (Some (Commit?.msg com.body))

val read_confirm: principal -> timestamp -> traceful (option confirm_message)
let read_confirm receiver ts =
  let*? frame = recv_msg ts in
  let*? con: confirm_frame = return (decode_confirm_frame receiver frame) in
  return (Some (Confirm?.msg con.body))

(*** Both STAs initiate simultaneously ***)

/// The run of the sequence diagram of the thesis:
/// both STAs receive an Init event, and the SAE Commit messages cross.
///
///   STA-A: Nothing   --Init-->  Committed  --Com--> Confirmed --Con--> Accepted
///   STA-B: Nothing   --Init-->  Committed  --Com--> Confirmed --Con--> Accepted

val run_simultaneous: unit -> traceful (option unit)
let run_simultaneous () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?

  // Nothing state, Init event: both STAs send an SAE Commit message
  let*? out = nothing_init gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in
  let*? out = nothing_init gsi_b sta_b sta_a in
  let*? commit_b = return (one_frame out) in

  // Committed state, Com event: both STAs send an SAE Confirm message
  let*? out = committed_com gsi_b sta_b commit_a in
  let*? confirm_b = return (one_frame out) in
  let*? out = committed_com gsi_a sta_a commit_b in
  let*? confirm_a = return (one_frame out) in

  // Confirmed state, Con event: both STAs accept
  let*? out = confirmed_con gsi_a sta_a confirm_b in
  return (no_frame out);*?
  let*? out = confirmed_con gsi_b sta_b confirm_a in
  return (no_frame out);*?

  check_shared_pmk gsi_a sta_a gsi_b sta_b

(*** One STA initiates ***)

/// Only STA-A receives an Init event.
/// STA-B creates its protocol instance upon receipt of the SAE Commit message.
/// The frames are dispatched by the parent process (`receive_frame`).
///
///   STA-A: Nothing   --Init-->  Committed  --Com--> Confirmed --Con--> Accepted
///   STA-B: Nothing   --Com--------------------->    Confirmed --Con--> Accepted

val run_one_initiator: unit -> traceful (option unit)
let run_one_initiator () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?

  // STA-A, Nothing state, Init event: send an SAE Commit message
  let*? out = initiate gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in

  // STA-B, Nothing state, Com event: send an SAE Commit message and an SAE Confirm message
  let*? out = receive_frame gsi_b sta_b commit_a in
  let*? (commit_b, confirm_b) = return (two_frames out) in

  // STA-A, Committed state, Com event: send an SAE Confirm message
  let*? out = receive_frame gsi_a sta_a commit_b in
  let*? confirm_a = return (one_frame out) in

  // Confirmed state, Con event: both STAs accept
  let*? out = receive_frame gsi_a sta_a confirm_b in
  return (no_frame out);*?
  let*? out = receive_frame gsi_b sta_b confirm_a in
  return (no_frame out);*?

  check_shared_pmk gsi_a sta_a gsi_b sta_b

(*** Dishonest runs ***)

/// STA-A initiates, STA-B answers, STA-A answers:
/// both STAs are in Confirmed state, and both SAE Confirm messages are in flight.
///
///   STA-A: Nothing --Init--> Committed --Com--> Confirmed
///   STA-B: Nothing --Com-------------------->   Confirmed

noeq type confirmed_run = {
  gsi_a: sae_global_sess_ids;
  gsi_b: sae_global_sess_ids;
  commit_a: timestamp;
  commit_b: timestamp;
  confirm_a: timestamp;
  confirm_b: timestamp;
}

val start_run: principal -> principal -> traceful (option confirmed_run)
let start_run sta_a sta_b =
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?
  let*? out = initiate gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in
  let*? out = receive_frame gsi_b sta_b commit_a in
  let*? (commit_b, confirm_b) = return (two_frames out) in
  let*? out = receive_frame gsi_a sta_a commit_b in
  let*? confirm_a = return (one_frame out) in
  return (Some ({gsi_a; gsi_b; commit_a; commit_b; confirm_a; confirm_b} <: confirmed_run))

/// Case 1: the STAs do not share the same password.
///
/// STA-B derives another PWE than STA-A.
/// The model cannot compute the shared secret from the SAE Commit message of STA-A,
/// and STA-B rejects the message (Del event, no protocol instance, no frame sent).
/// In the standard, STA-B would compute some K and fail later,
/// when the SAE Confirm message of STA-A does not verify.

val run_wrong_password: unit -> traceful (option unit)
let run_wrong_password () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  let* password_a = mk_rand NoUsage (join (principal_label sta_a) (principal_label sta_b)) 32 in
  let* password_b = mk_rand NoUsage (join (principal_label sta_a) (principal_label sta_b)) 32 in
  install_password sta_a gsi_a.passwords sta_b password_a;*?
  install_password sta_b gsi_b.passwords sta_a password_b;*?

  let*? out = initiate gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in
  let*? out = receive_frame gsi_b sta_b commit_a in
  return (no_frame out);*?
  let* no_instance = has_no_instance gsi_b sta_b sta_a in
  return (check no_instance)

/// Case 2: reflection of the SAE Commit message.
///
/// STA-A is in Committed state. The attacker sends the scalar and the element
/// of STA-A back to STA-A, as if they came from STA-B.
/// STA-A must silently discard them (12.4.8.6.4, reflection attack),
/// also if only the scalar or only the element are identical.

val run_reflected_commit: unit -> traceful (option unit)
let run_reflected_commit () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?
  let*? out = initiate gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in
  let*? own = read_commit sta_b commit_a in

  // same scalar and same element
  let* forged = forge_commit sta_b sta_a own.group own.scalar own.element in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?
  // same scalar, another element
  let* forged = forge_commit sta_b sta_a own.group own.scalar (dh_pk garbage) in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?
  // another scalar, same element
  let* forged = forge_commit sta_b sta_a own.group (dh_pk garbage) own.element in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* committed = is_committed gsi_a sta_a sta_b in
  return (check committed)

/// Case 3: reflection of the SAE Confirm message.
///
/// Both STAs are in Confirmed state. The attacker sends the SAE Confirm message
/// of STA-A back to STA-A, as if it came from STA-B.
/// The verifier swaps the scalars and the elements, so the verification fails:
/// STA-A sends a Fail event and deletes the protocol instance.
/// The genuine SAE Confirm message of STA-B then finds no protocol instance
/// and is discarded (parent process).
/// STA-B still accepts the genuine SAE Confirm message of STA-A.
/// SAE gives no guarantee that both STAs accept.

val run_reflected_confirm: unit -> traceful (option unit)
let run_reflected_confirm () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let*? run = start_run sta_a sta_b in
  let*? own = read_confirm sta_b run.confirm_a in

  let* forged = forge_confirm sta_b sta_a own.send_confirm own.confirm in
  let*? out = receive_frame run.gsi_a sta_a forged in
  return (no_frame out);*?
  let* no_instance = has_no_instance run.gsi_a sta_a sta_b in
  guard_tr no_instance;*?

  let*? out = receive_frame run.gsi_a sta_a run.confirm_b in
  return (no_frame out);*?
  let* no_instance = has_no_instance run.gsi_a sta_a sta_b in
  guard_tr no_instance;*?

  let*? out = receive_frame run.gsi_b sta_b run.confirm_a in
  return (no_frame out);*?
  let*? accepted = get_accepted run.gsi_b sta_b sta_a in
  return (Some ())

/// Case 4: forged SAE Confirm message.
///
/// Both STAs are in Confirmed state. The attacker sends an SAE Confirm message
/// with a made-up confirm to STA-A. The verification fails:
/// Fail event, the protocol instance is deleted, no PMK is accepted.

val run_forged_confirm: unit -> traceful (option unit)
let run_forged_confirm () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let*? run = start_run sta_a sta_b in

  let* forged = forge_confirm sta_b sta_a 1 garbage in
  let*? out = receive_frame run.gsi_a sta_a forged in
  return (no_frame out);*?
  let* no_instance = has_no_instance run.gsi_a sta_a sta_b in
  return (check no_instance)

/// Case 5: replays after the STAs have accepted.
///
/// Honest run until both STAs are Accepted. The attacker then replays
/// the SAE Commit message and the SAE Confirm message of STA-B to STA-A, and sends
/// SAE Confirm messages with a higher counter but a made-up confirm,
/// and with the counter 2^16 - 1.
/// STA-A silently discards all of them and stays in Accepted state with Rc = 1.

val run_replay_after_accept: unit -> traceful (option unit)
let run_replay_after_accept () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let*? run = start_run sta_a sta_b in
  let*? out = receive_frame run.gsi_a sta_a run.confirm_b in
  return (no_frame out);*?
  let*? out = receive_frame run.gsi_b sta_b run.confirm_a in
  return (no_frame out);*?
  let*? pmk_before = get_accepted run.gsi_a sta_a sta_b in

  // replay of the SAE Confirm message
  let*? out = receive_frame run.gsi_a sta_a run.confirm_b in
  return (no_frame out);*?
  // replay of the SAE Commit message
  let*? out = receive_frame run.gsi_a sta_a run.commit_b in
  return (no_frame out);*?
  // higher counter, made-up confirm
  let* forged = forge_confirm sta_b sta_a 2 garbage in
  let*? out = receive_frame run.gsi_a sta_a forged in
  return (no_frame out);*?
  // counter 2^16 - 1
  let* forged = forge_confirm sta_b sta_a 65535 garbage in
  let*? out = receive_frame run.gsi_a sta_a forged in
  return (no_frame out);*?

  let*? pmk_after = get_accepted run.gsi_a sta_a sta_b in
  return (check (pmk_before.rc = 1 && pmk_after.rc = 1 && pmk_before.pmk = pmk_after.pmk))

/// Case 6: malformed and unexpected frames for a STA without protocol instance.
///
/// STA-A has no protocol instance for STA-B. It silently discards:
/// - an SAE Confirm message (a protocol instance never receives one in Nothing state),
/// - an SAE Commit message with an unsupported group,
/// - an SAE Commit message with a nonzero status code,
/// - an SAE Commit message whose element is not a group element.
///
/// An SAE Commit message from an attacker that does not know the password
/// is also rejected: the model cannot derive a shared secret (see case 1).
/// In the standard, STA-A would answer with a Commit and a Confirm message
/// (this is one password guess of the attacker).

val run_malformed_frames: unit -> traceful (option unit)
let run_malformed_frames () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?
  let scalar = dh_pk garbage in
  let element = dh_pk (sae_string_to_bytes "other garbage") in

  let* forged = forge_confirm sta_b sta_a 1 garbage in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* forged = forge_commit sta_b sta_a 20 scalar element in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* forged = forge_commit_with_status sta_b sta_a 1 19 scalar element in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* forged = forge_commit sta_b sta_a 19 scalar garbage in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* forged = forge_commit sta_b sta_a 19 scalar element in
  let*? out = receive_frame gsi_a sta_a forged in
  return (no_frame out);*?

  let* no_instance = has_no_instance gsi_a sta_a sta_b in
  return (check no_instance)

/// Case 7: unusual order of the messages, and retransmissions.
///
/// - STA-A is in Committed state and receives an SAE Confirm message:
///   it sends its last SAE Commit message again (12.4.8.6.4).
/// - STA-A is in Confirmed state and receives the SAE Commit message again:
///   it increments Sc (Sc = 2) and sends its SAE Commit and its SAE Confirm message again
///   (12.4.8.6.5).
/// - STA-B accepts the new SAE Confirm message (send-confirm = 2, Rc = 2),
///   and then discards the old one (send-confirm = 1 is not greater than Rc).
/// - STA-A accepts the SAE Confirm message of STA-B.

val run_unusual_order: unit -> traceful (option unit)
let run_unusual_order () =
  let sta_a = "STA-A" in
  let sta_b = "STA-B" in
  let* gsi_a = setup_sta sta_a in
  let* gsi_b = setup_sta sta_b in
  setup_password gsi_a sta_a gsi_b sta_b;*?
  let*? out = initiate gsi_a sta_a sta_b in
  let*? commit_a = return (one_frame out) in

  // Committed state, Con event
  let* forged = forge_confirm sta_b sta_a 1 garbage in
  let*? out = receive_frame gsi_a sta_a forged in
  let*? commit_a_again = return (one_frame out) in
  let* committed = is_committed gsi_a sta_a sta_b in
  guard_tr committed;*?

  let*? out = receive_frame gsi_b sta_b commit_a in
  let*? (commit_b, confirm_b) = return (two_frames out) in
  let*? out = receive_frame gsi_a sta_a commit_b in
  let*? confirm_a_1 = return (one_frame out) in

  // Confirmed state, Com event
  let*? out = receive_frame gsi_a sta_a commit_b in
  let*? (commit_a_2, confirm_a_2) = return (two_frames out) in
  let* confirmed = is_confirmed gsi_a sta_a sta_b in
  guard_tr confirmed;*?

  let*? out = receive_frame gsi_b sta_b confirm_a_2 in
  return (no_frame out);*?
  let*? accepted_b = get_accepted gsi_b sta_b sta_a in
  guard_tr (accepted_b.rc = 2);*?

  let*? out = receive_frame gsi_a sta_a confirm_b in
  return (no_frame out);*?

  // Accepted state, Con event with an old counter
  let*? out = receive_frame gsi_b sta_b confirm_a_1 in
  return (no_frame out);*?
  let*? accepted_b = get_accepted gsi_b sta_b sta_a in
  guard_tr (accepted_b.rc = 2);*?

  check_shared_pmk gsi_a sta_a gsi_b sta_b

(*** Run the executions ***)

val debug_simultaneous: unit -> traceful (option unit)
let debug_simultaneous () =
  let* result = run_simultaneous () in
  report "SAE: both STAs initiate simultaneously" "both STAs accepted and share the PMK" result

val debug_one_initiator: unit -> traceful (option unit)
let debug_one_initiator () =
  let* result = run_one_initiator () in
  report "SAE: one STA initiates" "both STAs accepted and share the PMK" result

val debug_wrong_password: unit -> traceful (option unit)
let debug_wrong_password () =
  let* result = run_wrong_password () in
  report "SAE, dishonest 1: the STAs have different passwords"
    "STA-B rejects the SAE Commit message, no protocol instance" result

val debug_reflected_commit: unit -> traceful (option unit)
let debug_reflected_commit () =
  let* result = run_reflected_commit () in
  report "SAE, dishonest 2: reflected SAE Commit message"
    "STA-A discards the reflected messages and stays in Committed state" result

val debug_reflected_confirm: unit -> traceful (option unit)
let debug_reflected_confirm () =
  let* result = run_reflected_confirm () in
  report "SAE, dishonest 3: reflected SAE Confirm message"
    "STA-A fails and deletes its instance, STA-B accepts" result

val debug_forged_confirm: unit -> traceful (option unit)
let debug_forged_confirm () =
  let* result = run_forged_confirm () in
  report "SAE, dishonest 4: forged SAE Confirm message"
    "STA-A fails and deletes its protocol instance" result

val debug_replay_after_accept: unit -> traceful (option unit)
let debug_replay_after_accept () =
  let* result = run_replay_after_accept () in
  report "SAE, dishonest 5: replays after acceptance"
    "STA-A discards all frames, stays Accepted with Rc = 1 and the same PMK" result

val debug_malformed_frames: unit -> traceful (option unit)
let debug_malformed_frames () =
  let* result = run_malformed_frames () in
  report "SAE, dishonest 6: malformed and unexpected frames without protocol instance"
    "STA-A discards all frames and creates no protocol instance" result

val debug_unusual_order: unit -> traceful (option unit)
let debug_unusual_order () =
  let* result = run_unusual_order () in
  report "SAE, unusual order 7: retransmissions and old counters"
    "resent messages, Sc = 2 accepted (Rc = 2), old counter discarded, PMK shared" result

// Run the executions when the module loads
#push-options "--warn_error -272"
let _ = debug_simultaneous () empty_trace
let _ = debug_one_initiator () empty_trace
let _ = debug_wrong_password () empty_trace
let _ = debug_reflected_commit () empty_trace
let _ = debug_reflected_confirm () empty_trace
let _ = debug_forged_confirm () empty_trace
let _ = debug_replay_after_accept () empty_trace
let _ = debug_malformed_frames () empty_trace
let _ = debug_unusual_order () empty_trace
#pop-options
