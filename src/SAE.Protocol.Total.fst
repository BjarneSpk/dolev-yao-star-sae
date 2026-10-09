module SAE.Protocol.Total

open Comparse
open DY.Core
open DY.Lib
open SAE.Operations

#set-options "--fuel 0 --ifuel 1"

(*
 *** Simultaneous Authentication of Equals (SAE) ***

 IEEE Std 802.11-2024, clause 12.4

 STA-A and STA-B share a password.
 Each STA can initiate the protocol, possibly both at the same time.

 Commitment exchange (in any order):
 A -> B: SAE Commit {scalar_A, ELEMENT_A, group}
 B -> A: SAE Commit {scalar_B, ELEMENT_B, group}

 Confirmation exchange (in any order):
 A -> B: SAE Confirm {Sc_A, CN(KCK, Sc_A, scalar_A, ELEMENT_A, scalar_B, ELEMENT_B)}
 B -> A: SAE Confirm {Sc_B, CN(KCK, Sc_B, scalar_B, ELEMENT_B, scalar_A, ELEMENT_A)}

 where
   scalar  = (rand + mask) mod r
   ELEMENT = inverse-op(scalar-op(mask, PWE))
   K       = scalar-op(rand, elem-op(scalar-op(peer-scalar, PWE), PEER-ELEMENT))
   KCK | PMK = KDF(H(salt, F(K)), "SAE KCK and PMK", (scalar_A + scalar_B) mod r)

 This module contains the message formats
 and the pure functions of 12.4.5 (SAE protocol).
 Every arithmetic and cryptographic operation is a function of SAE.Operations.
*)

(*** Definition of messages ***)

/// Status codes of Authentication frames (9.4.1.9)

val status_success: nat_lbytes 2
let status_success = 0

/// Finite cyclic groups.
/// The group of a STA is its configuration (12.4.4.1).
/// The model configures group 19 for every STA.

val sae_configured_group: principal -> nat_lbytes 2
let sae_configured_group sta = 19

val sae_is_supported_group: principal -> nat_lbytes 2 -> bool
let sae_is_supported_group sta group =
  group = sae_configured_group sta

/// SAE Commit message (12.4.7.3)

[@@ with_bytes bytes]
type commit_message = {
  group: nat_lbytes 2;
  scalar: bytes;
  element: bytes;
}

%splice [ps_commit_message] (gen_parser (`commit_message))
%splice [ps_commit_message_is_well_formed] (gen_is_well_formed_lemma (`commit_message))

/// SAE Confirm message (12.4.7.4)

[@@ with_bytes bytes]
type confirm_message = {
  send_confirm: nat_lbytes 2;
  confirm: bytes;
}

%splice [ps_confirm_message] (gen_parser (`confirm_message))
%splice [ps_confirm_message_is_well_formed] (gen_is_well_formed_lemma (`confirm_message))

/// SAE messages are distinguished
/// by the Authentication Transaction Sequence Number (12.4.7.1):
/// 1 for an SAE Commit message, 2 for an SAE Confirm message.
/// It is represented by the tag of the following type.

[@@ with_bytes bytes]
type sae_message =
  | Commit: msg:commit_message -> sae_message
  | Confirm: msg:confirm_message -> sae_message

%splice [ps_sae_message] (gen_parser (`sae_message))
%splice [ps_sae_message_is_well_formed] (gen_is_well_formed_lemma (`sae_message))

/// Authentication frame carrying an SAE message (9.3.3.11),
/// with the address of the sender (SA) and the address of the receiver (DA).

[@@ with_bytes bytes]
type auth_frame = {
  sa: principal;
  da: principal;
  status: nat_lbytes 2;
  body: sae_message;
}

%splice [ps_auth_frame] (gen_parser (`auth_frame))
%splice [ps_auth_frame_is_well_formed] (gen_is_well_formed_lemma (`auth_frame))

instance parseable_serializeable_bytes_auth_frame: parseable_serializeable bytes auth_frame = mk_parseable_serializeable ps_auth_frame

(*** Encoding and decoding of frames (12.4.7) ***)

/// Encoding of an SAE Commit message.

[@@ "opaque_to_smt"]
val compute_commit_frame: principal -> principal -> nat_lbytes 2 -> bytes -> bytes -> bytes
let compute_commit_frame sta peer group scalar element =
  let msg = Commit {group; scalar; element} in
  serialize auth_frame {sa = sta; da = peer; status = status_success; body = msg}

/// Encoding of an SAE Confirm message.

[@@ "opaque_to_smt"]
val compute_confirm_frame: principal -> principal -> nat_lbytes 2 -> bytes -> bytes
let compute_confirm_frame sta peer send_confirm confirm =
  let msg = Confirm {send_confirm; confirm} in
  serialize auth_frame {sa = sta; da = peer; status = status_success; body = msg}

/// Decoding of a frame received by `sta`.
/// Frames addressed to another STA are dropped.

[@@ "opaque_to_smt"]
val decode_frame: principal -> bytes -> option auth_frame
let decode_frame sta frame_bytes =
  let? frame = parse auth_frame frame_bytes in
  guard (frame.da = sta);?
  Some frame

/// Authentication frames carrying an SAE Commit or an SAE Confirm message.

type commit_frame = frame:auth_frame{Commit? frame.body}
type confirm_frame = frame:auth_frame{Confirm? frame.body}

/// Decoding of an SAE Commit message received by `sta`.
/// The sender of the frame is the peer of `sta`.

[@@ "opaque_to_smt"]
val decode_commit_frame: principal -> bytes -> option commit_frame
let decode_commit_frame sta frame_bytes =
  match decode_frame sta frame_bytes with
  | Some frame -> if Commit? frame.body then Some frame else None
  | None -> None

/// Decoding of an SAE Confirm message received by `sta`.

[@@ "opaque_to_smt"]
val decode_confirm_frame: principal -> bytes -> option confirm_frame
let decode_confirm_frame sta frame_bytes =
  match decode_frame sta frame_bytes with
  | Some frame -> if Confirm? frame.body then Some frame else None
  | None -> None

(*** PWE and secret generation (12.4.5.2) ***)

/// Generation of the PWE for the configured password
/// and the identities of the two STAs.

[@@ "opaque_to_smt"]
val compute_pwe: bytes -> principal -> principal -> bytes
let compute_pwe password sta peer =
  sae_generate_pwe password (sae_mac_to_bytes sta) (sae_mac_to_bytes peer)

(*** Construction of an SAE Commit message (12.4.5.3) ***)

///   commit-scalar = (rand + mask) mod r
///   COMMIT-ELEMENT = inverse-op(scalar-op(mask, PWE))
/// The secret values rand and mask are rejected
/// if they do not satisfy the conditions of 12.4.5.2.

type compute_commit_result = {
  scalar: bytes;
  element: bytes;
}

[@@ "opaque_to_smt"]
val compute_commit: bytes -> bytes -> bytes -> option compute_commit_result
let compute_commit pwe rand mask =
  guard (sae_are_valid_secrets rand mask);?
  let scalar = sae_add_mod_r rand mask in
  let element = sae_inverse_op (sae_scalar_op mask pwe) in
  Some {scalar; element}

(*** Processing of a peer's SAE Commit message (12.4.5.4) ***)

/// Reflection check:
/// is the scalar or the element of the peer's SAE Commit message
/// identical to the scalar or element sent?
/// (only checked if the state is not Nothing)

[@@ "opaque_to_smt"]
val is_reflected_commit: bytes -> bytes -> bytes -> bytes -> bool
let is_reflected_commit scalar element peer_scalar peer_element =
  peer_scalar = scalar || peer_element = element

/// Verification of the scalar and the element of the peer.

[@@ "opaque_to_smt"]
val verify_peer_commit: bytes -> bytes -> bool
let verify_peer_commit peer_scalar peer_element =
  sae_is_valid_scalar peer_scalar && sae_is_valid_element peer_element

/// Derivation of the shared secret:
///   K = scalar-op(rand, elem-op(scalar-op(peer-commit-scalar, PWE), PEER-COMMIT-ELEMENT))
///   k = F(K)
/// The peer's authentication is rejected if K is the identity element.

[@@ "opaque_to_smt"]
val compute_shared_secret: bytes -> bytes -> bytes -> bytes -> option bytes
let compute_shared_secret pwe rand peer_scalar peer_element =
  let shared_element = sae_scalar_op rand (sae_elem_op (sae_scalar_op peer_scalar pwe) peer_element) in
  guard (not (sae_is_identity_element shared_element));?
  Some (sae_f shared_element)

/// Derivation of the keys:
///   keyseed = H(salt, k)
///   context = (commit-scalar + peer-commit-scalar) mod r
///   sae_kck_and_pmk = KDF-Hash-Length(keyseed, "SAE KCK and PMK", context)
///   SAE-KCK = ExtractBits(sae_kck_and_pmk, 0, Q)
///   PMK = ExtractBits(sae_kck_and_pmk, Q, PMK_bits)
/// The salt is a series of zero octets (no rejected groups).

type sae_keys = {
  kck: bytes;
  pmk: bytes;
}

[@@ "opaque_to_smt"]
val derive_keys: bytes -> bytes -> bytes -> option sae_keys
let derive_keys k scalar peer_scalar =
  let keyseed = sae_h sae_zero_salt k in
  let context = sae_add_mod_r scalar peer_scalar in
  let sae_kck_and_pmk = sae_kdf keyseed sae_kdf_label (sae_d2os context) in
  let? kck = sae_extract_bits sae_kck_and_pmk 0 sae_hash_length in
  let? pmk = sae_extract_bits sae_kck_and_pmk sae_hash_length sae_pmk_length in
  Some {kck; pmk}

/// Processing of the scalar and the element of a peer's SAE Commit message:
/// verification, derivation of the shared secret and of the keys.

[@@ "opaque_to_smt"]
val process_commit: bytes -> bytes -> bytes -> bytes -> bytes -> option sae_keys
let process_commit pwe rand scalar peer_scalar peer_element =
  guard (verify_peer_commit peer_scalar peer_element);?
  let? k = compute_shared_secret pwe rand peer_scalar peer_element in
  derive_keys k scalar peer_scalar

(*** Construction of an SAE Confirm message (12.4.5.5) ***)

///   confirm = CN(SAE-KCK, send-confirm, commit-scalar, COMMIT-ELEMENT,
///                peer-commit-scalar, PEER-COMMIT-ELEMENT)

[@@ "opaque_to_smt"]
val compute_confirm: bytes -> nat_lbytes 2 -> bytes -> bytes -> bytes -> bytes -> bytes
let compute_confirm kck send_confirm scalar element peer_scalar peer_element =
  sae_cn kck (sae_uint16_to_bytes send_confirm) scalar element peer_scalar peer_element

(*** Processing of a peer's SAE Confirm message (12.4.5.6) ***)

///   verifier = CN(SAE-KCK, peer-send-confirm, peer-commit-scalar, PEER-COMMIT-ELEMENT,
///                 commit-scalar, COMMIT-ELEMENT)
/// Verification fails if the verifier differs from the peer's confirm.

[@@ "opaque_to_smt"]
val verify_confirm: bytes -> nat_lbytes 2 -> bytes -> bytes -> bytes -> bytes -> bytes -> bool
let verify_confirm kck peer_send_confirm scalar element peer_scalar peer_element peer_confirm =
  let verifier = sae_cn kck (sae_uint16_to_bytes peer_send_confirm) peer_scalar peer_element scalar element in
  verifier = peer_confirm
