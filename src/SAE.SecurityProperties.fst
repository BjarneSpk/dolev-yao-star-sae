module SAE.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open SAE.Operations
open SAE.Protocol.Total
open SAE.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Property 1: shared PMK ***)

/// If a STA accepts the peer (Auth event, 12.4.8.3),
/// then a STA confirmed with the same scalars, elements and PMK,
/// unless the password was corrupt when the STA accepted.
/// This STA is the peer, or the STA itself in another protocol instance
/// (the attacker may reflect messages between two instances of the same STA:
/// the parent process allows a single instance per peer,
/// but the attacker may run the STA with several parent processes).
/// SAE does not guarantee that the peer accepts as well (12.4.8.6.6).

val sae_pmk_agreement:
  tr:trace -> i:timestamp ->
  sta:principal -> peer:principal ->
  scalar:bytes -> element:bytes -> peer_scalar:bytes -> peer_element:bytes -> pmk:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i sta (EvAuth sta peer scalar element peer_scalar peer_element pmk)
  )
  (ensures
    is_corrupt (prefix tr i) (sae_password_label sta peer) \/
    event_triggered (prefix tr i) sta (EvConfirmed sta peer peer_scalar peer_element scalar element pmk) \/
    event_triggered (prefix tr i) peer (EvConfirmed peer sta peer_scalar peer_element scalar element pmk)
  )
let sae_pmk_agreement tr i sta peer scalar element peer_scalar peer_element pmk = ()

(*** Properties 2 and 3: secrecy of the password ***)

/// The password stored by `sta` for `peer` is unknown to the attacker,
/// unless a state of `sta` or `peer` is corrupt.
/// This holds against the active attacker, hence against the passive one.

val sae_password_secrecy:
  tr:trace -> sta:principal -> sess_id:state_id ->
  passwords:map password_key password_value ->
  peer:principal -> password:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr sta sess_id passwords /\
    List.Tot.memP ({key = ({peer} <: password_key); value = ({password} <: password_value)} <: map_elem password_key password_value) passwords.key_values /\
    attacker_knows tr password
  )
  (ensures is_corrupt tr (principal_label sta) \/ is_corrupt tr (principal_label peer))
let sae_password_secrecy tr sta sess_id passwords peer password = ()

(*** Property 3: secrecy of the PMK (active attacker) ***)

/// The PMK of a protocol instance in Confirmed or Accepted state
/// is unknown to the attacker, unless the password is corrupt.
/// This holds whatever the attacker sent as the peer's SAE Commit message.

val sae_pmk_secrecy:
  tr:trace -> sta:principal -> sess_id:state_id -> st:confirmed_data ->
  Lemma
  (requires
    trace_invariant tr /\
    (state_was_set tr sta sess_id (Confirmed st <: sae_instance) \/
     state_was_set tr sta sess_id (Accepted st <: sae_instance)) /\
    attacker_knows tr st.pmk
  )
  (ensures is_corrupt tr (sae_password_label sta st.peer))
let sae_pmk_secrecy tr sta sess_id st = ()

(*** Properties 2 and 6: secrecy of the PMK of a matched session ***)

/// If the peer's SAE Commit message was computed by a STA `p`
/// (which confirmed with the same values),
/// the PMK is unknown to the attacker
/// unless the protocol instance of `sta` or a protocol instance of `p` is corrupt.
/// The password does not matter.

val sae_pmk_secrecy_with:
  tr:trace -> sta:principal -> sess_id:state_id -> st:confirmed_data ->
  p:principal -> q:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    (state_was_set tr sta sess_id (Confirmed st <: sae_instance) \/
     state_was_set tr sta sess_id (Accepted st <: sae_instance)) /\
    event_triggered tr p (EvConfirmed p q st.peer_scalar st.peer_element st.scalar st.element st.pmk) /\
    attacker_knows tr st.pmk
  )
  (ensures
    is_corrupt tr (sae_instance_label sta sess_id) \/
    (exists p_sess_id. is_corrupt tr (sae_instance_label p p_sess_id))
  )
let sae_pmk_secrecy_with tr sta sess_id st p q = ()

/// Property 2: in a session between two honest STAs
/// (the peer computed the SAE Commit message that `sta` received,
/// e.g., because the attacker only observed or relayed the messages),
/// the PMK is unknown to the attacker, unless one of the two protocol instances is corrupt.
/// This holds even if the password is corrupt.

val sae_pmk_secrecy_matched:
  tr:trace -> sta:principal -> sess_id:state_id -> st:confirmed_data ->
  Lemma
  (requires
    trace_invariant tr /\
    (state_was_set tr sta sess_id (Confirmed st <: sae_instance) \/
     state_was_set tr sta sess_id (Accepted st <: sae_instance)) /\
    event_triggered tr st.peer (EvConfirmed st.peer sta st.peer_scalar st.peer_element st.scalar st.element st.pmk) /\
    attacker_knows tr st.pmk
  )
  (ensures
    is_corrupt tr (sae_instance_label sta sess_id) \/
    (exists peer_sess_id. is_corrupt tr (sae_instance_label st.peer peer_sess_id))
  )
let sae_pmk_secrecy_matched tr sta sess_id st = ()

/// Property 6: if the password was not corrupt when `sta` accepted
/// (i.e. the `guarded` label below is not corrupt),
/// the attacker does not learn the PMK by corrupting the password later:
/// it needs a protocol instance of `sta` or of its peer.

val sae_pmk_password_forward_secrecy:
  tr:trace -> sta:principal -> sess_id:state_id -> st:confirmed_data ->
  Lemma
  (requires
    trace_invariant tr /\
    state_was_set tr sta sess_id (Accepted st <: sae_instance) /\
    event_triggered tr sta (EvAuth sta st.peer st.scalar st.element st.peer_scalar st.peer_element st.pmk) /\
    attacker_knows tr st.pmk
  )
  (ensures
    is_corrupt tr (guarded (sae_password_label sta st.peer)
      (event_triggered_label sta (EvAuth sta st.peer st.scalar st.element st.peer_scalar st.peer_element st.pmk))) \/
    (exists sta_sess_id. is_corrupt tr (sae_instance_label sta sta_sess_id)) \/
    (exists peer_sess_id. is_corrupt tr (sae_instance_label st.peer peer_sess_id))
  )
let sae_pmk_password_forward_secrecy tr sta sess_id st = ()
