module SAE.Operations

open DY.Core
open DY.Core.Internal.Ord
open Comparse
open DY.Lib.Comparse.Glue

#set-options "--fuel 0 --ifuel 1"

/// This module contains every arithmetic and cryptographic operation
/// used by SAE (IEEE Std 802.11-2024, clause 12.4), each as its own function.
/// The rest of the model only calls these functions,
/// hence an operation can be replaced by changing a single definition.
///
/// DY* has no finite cyclic group with arbitrary base,
/// no modular arithmetic and no element inverse.
/// These operations are therefore encoded as symbolic terms
/// built from the constructors DY* offers.
/// The functions below are the (only) reduction rules of this symbolic algebra.
///
/// Symbolic encoding, with P = PWE (r is the group order, written additively):
///
///   x + y mod r     ~>  DhPub (Concat "SAE.add" (Concat x y))      (x, y sorted)
///   exponent x*P    ~>  KdfExpand (KdfExtract P x) "SAE.scalar-op" 32
///   element  x*P    ~>  DhPub (exponent x*P)
///   element  -E     ~>  DhPub (Concat "SAE.inv" e)                 (E = DhPub e)
///   element  x*(y*P)~>  Dh (exponent x*P) (DhPub (exponent y*P))   (normalized by `dh`)
///
/// We need:
/// - commit: scalar = rand + mask, ELEMENT = −(mask·P)
/// - peer: K = rand_B · ( scalar_A·P + ELEMENT_A )
///    = rand_B · ((rand_A + mask_A)·P − mask_A·P)  // sae_elem_op_reduce
///    = rand_B · (rand_A·P)
///    = rand_A · rand_B · P
///
/// The single non-trivial reduction is the one SAE relies on:
///
///   elem-op(scalar-op(x + y, P), inverse-op(scalar-op(y, P)))  =  scalar-op(x, P)
///
/// Consequences of this encoding:
/// - commit-scalar and COMMIT-ELEMENT are public terms (`DhPub`),
///   although they contain rand and mask.
/// - The exponent of an element depends on both the secret scalar and PWE,
///   hence K = rand_A * rand_B * PWE is only computable
///   with one of the secret values *and* PWE.
/// - K is a `Dh` term, hence both STAs compute the same K.
/// - Terms that cannot be reduced are kept as stuck (but well-defined) terms.
///   They never lead to a shared secret (see `sae_is_identity_element`).
///
/// Limitation: the attacker can only use the functions of DY.Core on these terms.
/// Algebraic manipulations of commit-scalar and COMMIT-ELEMENT
/// beyond the reduction above are not captured by the model.

/// `bytes`-value of an ASCII string (e.g., the label of the KDF).

val sae_string_to_bytes: string -> bytes
let sae_string_to_bytes s =
  serialize string #(mk_parseable_serializeable DY.Lib.Comparse.Parsers.ps_string) s

/// 16-bit unsigned integer to bytes,
/// used for the send-confirm counter and the counter and length of the KDF.

type sae_uint16 = n:nat{n < pow2 (8 `op_Multiply` 2)}

val sae_uint16_to_bytes: sae_uint16 -> bytes
let sae_uint16_to_bytes n =
  serialize nat #(mk_parseable_serializeable DY.Lib.Comparse.Parsers.ps_nat) n

/// Counters (Sc, Rc) are 16-bit unsigned integers (12.4.8.5).
/// The send-confirm counter of an accepted instance is 2^16 - 1 (12.4.8.6.5).

val sae_max_counter: sae_uint16
let sae_max_counter =
  assert_norm (pow2 (8 `op_Multiply` 2) == 65536);
  65535

/// Increment of a counter (fails instead of overflowing).

val sae_increment_counter: sae_uint16 -> option sae_uint16
let sae_increment_counter counter =
  if counter < sae_max_counter then Some (counter + 1)
  else None

/// Data to bytes conversion (12.4.7.2).
/// Symbolic scalars and elements already are octet strings.

val sae_d2os: bytes -> bytes
let sae_d2os x =
  x

/// MAC address of a STA as an octet string.
/// A STA is identified by its MAC address, which is the principal name.

val sae_mac_to_bytes: principal -> bytes
let sae_mac_to_bytes sta =
  sae_string_to_bytes sta

/// MAX and MIN of two bytes values
/// (used on MAC addresses in the PWE generation).

val sae_max: bytes -> bytes -> bytes
let sae_max x y =
  if x `is_less_than` y then y else x

val sae_min: bytes -> bytes -> bytes
let sae_min x y =
  if x `is_less_than` y then x else y

(*** Constants ***)

/// Length (in octets) of the digest of the hash function used for H and CN
/// (SHA-256, see 12.4.2), and of the PMK (12.7.1.3).

val sae_hash_length: n:nat{n <> 0}
let sae_hash_length = 32

val sae_pmk_length: n:nat{n <> 0}
let sae_pmk_length = 32

/// Salt of H when no rejected groups are present:
/// a series of octets of value zero of the length of the digest (12.4.5.4).

val sae_zero_salt: bytes
let sae_zero_salt =
  literal_to_bytes (Seq.create sae_hash_length 0uy)

/// Label of the key derivation (12.4.5.4).

val sae_kdf_label: bytes
let sae_kdf_label =
  sae_string_to_bytes "SAE KCK and PMK"

/// Tags of the symbolic algebra.

val sae_add_tag: bytes
let sae_add_tag =
  sae_string_to_bytes "SAE.add"

val sae_inverse_tag: bytes
let sae_inverse_tag =
  sae_string_to_bytes "SAE.inv"

val sae_elem_op_tag: bytes
let sae_elem_op_tag =
  sae_string_to_bytes "SAE.elem-op"

val sae_scalar_op_tag: bytes
let sae_scalar_op_tag =
  sae_string_to_bytes "SAE.scalar-op"

(*** Hash functions ***)

/// H(salt, ikm) = HMAC-Hash(salt, ikm), used as an extractor (12.4.2).

val sae_h: bytes -> bytes -> bytes
let sae_h salt ikm =
  kdf_extract salt ikm

/// One block of KDF-Hash-Length (12.7.1.6.2):
///   HMAC-Hash(K, i || Label || Context || Length)
/// where i and Length (in bits) are 16-bit unsigned integers.

val sae_kdf_block: bytes -> sae_uint16 -> bytes -> bytes -> sae_uint16 -> bytes
let sae_kdf_block key i label context length =
  kdf_expand key (concat (sae_uint16_to_bytes i) (concat label (concat context (sae_uint16_to_bytes length)))) sae_hash_length

/// KDF-Hash-Length(K, Label, Context) (12.7.1.6.2)
/// for Length = 2 * (length of the digest), i.e., two blocks:
///   result = block 1 || block 2

val sae_kdf: bytes -> bytes -> bytes -> bytes
let sae_kdf key label context =
  let length: sae_uint16 = 8 `op_Multiply` (sae_hash_length + sae_pmk_length) in
  concat (sae_kdf_block key 1 label context length) (sae_kdf_block key 2 label context length)

/// ExtractBits(b, start, len) (start and len in octets).

val sae_extract_bits: bytes -> nat -> nat -> option bytes
let sae_extract_bits b start len =
  let? rest = (
    if start = 0 then Some b
    else (
      let? (_, rest) = split b start in
      Some rest
    )
  ) in
  if length rest = len then Some rest
  else (
    let? (res, _) = split rest len in
    Some res
  )

/// CN(key, counter, X, Y, Z, W) =
///   HMAC-Hash(key, counter || D2OS(X) || D2OS(Y) || D2OS(Z) || D2OS(W)) (12.4.2)

val sae_cn: bytes -> bytes -> bytes -> bytes -> bytes -> bytes -> bytes
let sae_cn key counter x y z w =
  mac_compute key (concat counter (concat (sae_d2os x) (concat (sae_d2os y) (concat (sae_d2os z) (sae_d2os w)))))

(*** Password element ***)

/// Hashing of a secret seed to an element of the group
/// (abstraction of the looping method (12.4.4.2.2, 12.4.4.3.2)
/// and of the hash-to-element method (12.4.4.2.3, 12.4.4.3.3)).

val sae_hash_to_element: bytes -> bytes
let sae_hash_to_element seed =
  hash seed

/// Generation of the password element PWE (12.4.5.2)
/// from the password and the identities (MAC addresses) of the two STAs.
/// PWE is symmetric in the two MAC addresses:
///   PWE = hash-to-element(H(MAX(STA-A-MAC, STA-B-MAC) || MIN(STA-A-MAC, STA-B-MAC), password))

val sae_generate_pwe: bytes -> bytes -> bytes -> bytes
let sae_generate_pwe password mac_a mac_b =
  sae_hash_to_element (sae_h (concat (sae_max mac_a mac_b) (sae_min mac_a mac_b)) password)

(*** Group operations ***)

/// Exponent of the element scalar-op(x, PWE).
/// It depends on both x and PWE.

val sae_exponent: bytes -> bytes -> bytes
let sae_exponent x pwe =
  kdf_expand (kdf_extract pwe x) sae_scalar_op_tag sae_hash_length

/// (x + y) mod r
/// Commutative: the operands are sorted.

val sae_add_mod_r: bytes -> bytes -> bytes
let sae_add_mod_r x y =
  if x `is_less_than` y then
    dh_pk (concat sae_add_tag (concat x y))
  else
    dh_pk (concat sae_add_tag (concat y x))

/// scalar-op(x, E)
/// - E = PWE (not an element term): the element x * PWE
/// - E = y * PWE: the shared element x * (y * PWE) (commutative in x and y)
/// - otherwise: stuck term
/// sae_exponent has to use KdfExpand KdfExtract,
/// since the calculation of K (shared secret) uses scalar-op.
/// If it would also use DhPub,
/// it would be marked with a public label
/// thus violating the secrecy property.

val sae_scalar_op: bytes -> bytes -> bytes
let sae_scalar_op x e =
  match e with
  | DhPub (KdfExpand (KdfExtract pwe y) tag len) ->
    if tag = sae_scalar_op_tag && len = sae_hash_length then
      dh (sae_exponent x pwe) e
    else
      dh_pk (concat sae_scalar_op_tag (concat x e))
  | DhPub _ ->
    dh_pk (concat sae_scalar_op_tag (concat x e))
  | _ ->
    dh_pk (sae_exponent x e)

/// inverse-op(E)

val sae_inverse_op: bytes -> bytes
let sae_inverse_op e =
  match e with
  | DhPub (Concat tag e') ->
    if tag = sae_inverse_tag then
      dh_pk e'
    else
      dh_pk (concat sae_inverse_tag (Concat tag e'))
  | DhPub e' ->
    dh_pk (concat sae_inverse_tag e')
  | _ ->
    dh_pk (concat sae_inverse_tag e)

/// Reduction rule of elem-op:
///   (x + y) * PWE  -  m * PWE  =  y * PWE    if m = x
///                              =  x * PWE    if m = y

val sae_elem_op_reduce: bytes -> bytes -> option bytes
let sae_elem_op_reduce e1 e2 =
  match e1, e2 with
  | DhPub (KdfExpand (KdfExtract pwe1 (DhPub (Concat add_tag (Concat x y)))) tag1 len1),
    DhPub (Concat inv_tag (KdfExpand (KdfExtract pwe2 m) tag2 len2)) ->
    if add_tag = sae_add_tag && inv_tag = sae_inverse_tag &&
       tag1 = sae_scalar_op_tag && tag2 = sae_scalar_op_tag &&
       len1 = sae_hash_length && len2 = sae_hash_length &&
       pwe1 = pwe2
    then (
      // Check whether x or y is the mask to cancel it out (sae_add_mor_r sorts operands)
      if m = x then Some (dh_pk (sae_exponent y pwe1))
      else if m = y then Some (dh_pk (sae_exponent x pwe1))
      else None
    )
    else None
  | _, _ -> None

/// elem-op(E1, E2)
/// Commutative: the reduction is tried in both orders,
/// and the operands of a stuck term are sorted.

val sae_elem_op: bytes -> bytes -> bytes
let sae_elem_op e1 e2 =
  match sae_elem_op_reduce e1 e2 with
  | Some res -> res
  | None -> (
    match sae_elem_op_reduce e2 e1 with
    | Some res -> res
    | None ->
      if e1 `is_less_than` e2 then
        dh_pk (concat sae_elem_op_tag (concat e1 e2))
      else
        dh_pk (concat sae_elem_op_tag (concat e2 e1))
  )

/// F(K): conversion of the shared element to an integer (12.4.4.2.1, 12.4.4.3.1)
/// (e.g., the x-coordinate of a point on an elliptic curve).

val sae_f: bytes -> bytes
let sae_f k =
  k

(*** Validation ***)

/// The following checks have no symbolic counterpart
/// (there are no numbers in the symbolic model).
/// They are kept as functions to stay close to the standard.

/// 1 < x < r (12.4.5.2, 12.4.5.4)

val sae_is_in_range: bytes -> bool
let sae_is_in_range x =
  true

/// Validation of the secret values (12.4.5.2):
/// 1 < rand < r, 1 < mask < r, and (rand + mask) mod r > 1

val sae_are_valid_secrets: bytes -> bytes -> bool
let sae_are_valid_secrets rand mask =
  sae_is_in_range rand && sae_is_in_range mask && sae_is_in_range (sae_add_mod_r rand mask)

/// Scalar validation (12.4.5.4): 1 < scalar < r

val sae_is_valid_scalar: bytes -> bool
let sae_is_valid_scalar scalar =
  sae_is_in_range scalar

/// Element validation (12.4.5.4): the element is an element of the group.

val sae_is_valid_element: bytes -> bool
let sae_is_valid_element element =
  DhPub? element

/// Is K the identity element of the group? (12.4.5.4)
/// Symbolically, K is a proper shared element if and only if it is a `Dh` term.
/// Every other (stuck) term is treated like the identity element,
/// i.e., the peer's authentication is rejected.

val sae_is_identity_element: bytes -> bool
let sae_is_identity_element k =
  match k with
  | Dh _ (DhPub _) -> false
  | _ -> true
