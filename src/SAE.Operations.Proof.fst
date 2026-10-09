module SAE.Operations.Proof

open Comparse
open DY.Core
open DY.Lib
open SAE.Operations
open SAE.Protocol.Total
open DY.Core.Internal.Ord

#set-options "--fuel 0 --ifuel 1"

/// This module contains functional correctness lemmas on the pure part of SAE:
/// two STAs sharing a password and following the protocol
/// derive the same keys and accept each other's SAE Confirm message.
///
/// These Lemmas show that the symbolic encoding of the group operations
/// (see SAE.Operations) behaves like the finite cyclic group it stands for.

val reveal_constructors:
  unit ->
  Lemma (
    (forall msg. hash msg == Hash msg) /\
    (forall sk. dh_pk sk == DhPub sk) /\
    (forall left right. concat left right == Concat left right) /\
    (forall salt ikm. kdf_extract salt ikm == KdfExtract salt ikm) /\
    (forall prk info (len:nat{len <> 0}). kdf_expand prk info len == KdfExpand prk info len)
  )
let reveal_constructors () =
  reveal_opaque (`%hash) (hash);
  reveal_opaque (`%dh_pk) (dh_pk);
  reveal_opaque (`%concat) (concat);
  reveal_opaque (`%kdf_extract) (kdf_extract);
  reveal_opaque (`%kdf_expand) (kdf_expand)

(*** Group operations ***)

/// (x + y) mod r is commutative.
/// sae_add_mod_r sorts its operands with `is_less_than`, like `dh` in DY.Core.Bytes,
/// so the proof follows `dh_shared_secret_lemma`:
/// the order is total, and antisymmetric when both comparisons hold.

val sae_add_mod_r_commutes:
  x:bytes -> y:bytes ->
  Lemma (sae_add_mod_r x y == sae_add_mod_r y x)
let sae_add_mod_r_commutes x y =
  is_less_than_total x y;
  if x `is_less_than` y then (
    if y `is_less_than` x then (
      // x <= y and y <= x: x and y are equal
      is_less_than_antisym x y;
      assert (x == y)
    ) else (
      // only x <= y: both calls sort the operands as (x, y)
      assert (sae_add_mod_r x y == dh_pk (concat sae_add_tag (concat x y)));
      assert (sae_add_mod_r y x == dh_pk (concat sae_add_tag (concat x y)))
    )
  ) else (
    // only y <= x (the order is total): both calls sort the operands as (y, x)
    assert (y `is_less_than` x);
    assert (sae_add_mod_r x y == dh_pk (concat sae_add_tag (concat y x)));
    assert (sae_add_mod_r y x == dh_pk (concat sae_add_tag (concat y x)))
  )

/// The PWE is symmetric in the two MAC addresses.

val sae_generate_pwe_commutes:
  password:bytes -> mac_a:bytes -> mac_b:bytes ->
  Lemma (sae_generate_pwe password mac_a mac_b == sae_generate_pwe password mac_b mac_a)
let sae_generate_pwe_commutes password mac_a mac_b =
  is_less_than_total mac_a mac_b;
  if mac_a `is_less_than` mac_b then (
    if mac_b `is_less_than` mac_a then (
      // mac_a <= mac_b and mac_b <= mac_a: the MAC addresses are equal
      is_less_than_antisym mac_a mac_b;
      assert (mac_a == mac_b)
    ) else (
      // only mac_a <= mac_b: MAX is mac_b and MIN is mac_a in both orders
      assert (sae_max mac_a mac_b == mac_b /\ sae_min mac_a mac_b == mac_a);
      assert (sae_max mac_b mac_a == mac_b /\ sae_min mac_b mac_a == mac_a)
    )
  ) else (
    // only mac_b <= mac_a (the order is total): MAX is mac_a and MIN is mac_b in both orders
    assert (mac_b `is_less_than` mac_a);
    assert (sae_max mac_a mac_b == mac_a /\ sae_min mac_a mac_b == mac_b);
    assert (sae_max mac_b mac_a == mac_a /\ sae_min mac_b mac_a == mac_b)
  )

/// The PWE is not an element term (DhPub), it is a hash.
/// Hence scalar-op(x, PWE) is the element x * PWE,
/// which the reductions below rely on.

val sae_generate_pwe_is_not_element:
  password:bytes -> mac_a:bytes -> mac_b:bytes ->
  Lemma (~(DhPub? (sae_generate_pwe password mac_a mac_b)))
let sae_generate_pwe_is_not_element password mac_a mac_b =
  reveal_constructors ()

/// The reduction SAE relies on:
///   elem-op(scalar-op(rand + mask, PWE), inverse-op(scalar-op(mask, PWE))) = scalar-op(rand, PWE)

val sae_elem_op_reduction:
  pwe:bytes -> rand:bytes -> mask:bytes ->
  Lemma
  (requires ~(DhPub? pwe))
  (ensures
    sae_elem_op (sae_scalar_op (sae_add_mod_r rand mask) pwe) (sae_inverse_op (sae_scalar_op mask pwe))
    == sae_scalar_op rand pwe
  )
let sae_elem_op_reduction pwe rand mask =
  reveal_constructors ()

/// scalar-op(x, scalar-op(y, PWE)) = scalar-op(y, scalar-op(x, PWE)),
/// and this element is not the identity element.

val sae_scalar_op_commutes:
  pwe:bytes -> x:bytes -> y:bytes ->
  Lemma
  (requires ~(DhPub? pwe))
  (ensures
    sae_scalar_op x (sae_scalar_op y pwe) == sae_scalar_op y (sae_scalar_op x pwe) /\
    not (sae_is_identity_element (sae_scalar_op x (sae_scalar_op y pwe)))
  )
let sae_scalar_op_commutes pwe x y =
  reveal_constructors ();
  reveal_opaque (`%dh) (dh);
  dh_shared_secret_lemma (sae_exponent x pwe) (sae_exponent y pwe)

(*** Commitment exchange ***)

/// Two STAs sharing a password generate the same PWE.

val compute_pwe_commutes:
  password:bytes -> sta_a:principal -> sta_b:principal ->
  Lemma (
    compute_pwe password sta_a sta_b == compute_pwe password sta_b sta_a /\
    ~(DhPub? (compute_pwe password sta_a sta_b))
  )
let compute_pwe_commutes password sta_a sta_b =
  reveal_opaque (`%compute_pwe) (compute_pwe);
  sae_generate_pwe_commutes password (sae_mac_to_bytes sta_a) (sae_mac_to_bytes sta_b);
  sae_generate_pwe_is_not_element password (sae_mac_to_bytes sta_a) (sae_mac_to_bytes sta_b)

/// When a STA processes the SAE Commit message of its peer,
/// the shared secret is k = F(rand * (peer-rand * PWE)).

val compute_shared_secret_correct:
  pwe:bytes -> rand:bytes ->
  peer_rand:bytes -> peer_mask:bytes ->
  Lemma
  (requires ~(DhPub? pwe))
  (ensures (
    let peer_scalar = sae_add_mod_r peer_rand peer_mask in
    let peer_element = sae_inverse_op (sae_scalar_op peer_mask pwe) in
    verify_peer_commit peer_scalar peer_element /\
    compute_shared_secret pwe rand peer_scalar peer_element == Some (sae_f (sae_scalar_op rand (sae_scalar_op peer_rand pwe)))
  ))
let compute_shared_secret_correct pwe rand peer_rand peer_mask =
  reveal_opaque (`%verify_peer_commit) (verify_peer_commit);
  reveal_opaque (`%compute_shared_secret) (compute_shared_secret);
  reveal_constructors ();
  sae_elem_op_reduction pwe peer_rand peer_mask;
  sae_scalar_op_commutes pwe rand peer_rand

/// The derivation of the keys succeeds:
/// the KDF output is two blocks of 32 octets, so both extractions succeed.

val derive_keys_succeeds:
  k:bytes -> scalar:bytes -> peer_scalar:bytes ->
  Lemma (Some? (derive_keys k scalar peer_scalar))
let derive_keys_succeeds k scalar peer_scalar =
  reveal_opaque (`%derive_keys) (derive_keys);
  reveal_constructors ();
  reveal_opaque (`%split) (split);
  // The KDF output, as computed in derive_keys
  let keyseed = sae_h sae_zero_salt k in
  let context = sae_d2os (sae_add_mod_r scalar peer_scalar) in
  let length: sae_uint16 = 8 `op_Multiply` (sae_hash_length + sae_pmk_length) in
  let block1 = sae_kdf_block keyseed 1 sae_kdf_label context length in
  let block2 = sae_kdf_block keyseed 2 sae_kdf_label context length in
  let kdf_output = sae_kdf keyseed sae_kdf_label context in
  // It is the concatenation of two blocks of 32 octets
  assert (kdf_output == Concat block1 block2);
  assert_norm (DY.Core.Bytes.length block1 == 32);
  assert_norm (DY.Core.Bytes.length block2 == 32);
  assert_norm (DY.Core.Bytes.length (Concat block1 block2) == 64);
  // so it can be split after 32 octets
  assert (split kdf_output 32 == Some (block1, block2));
  // and both extractions succeed
  assert (sae_extract_bits kdf_output 0 sae_hash_length == Some block1);
  assert (sae_extract_bits kdf_output sae_hash_length sae_pmk_length == Some block2)

/// The derivation of the keys is symmetric in the two scalars:
/// they only appear in the context (scalar + peer-scalar) mod r.

val derive_keys_symmetric:
  k:bytes -> scalar:bytes -> peer_scalar:bytes ->
  Lemma (derive_keys k scalar peer_scalar == derive_keys k peer_scalar scalar)
let derive_keys_symmetric k scalar peer_scalar =
  reveal_opaque (`%derive_keys) (derive_keys);
  sae_add_mod_r_commutes scalar peer_scalar

val derive_keys_commutes:
  k:bytes -> scalar:bytes -> peer_scalar:bytes ->
  Lemma (
    Some? (derive_keys k scalar peer_scalar) /\
    derive_keys k scalar peer_scalar == derive_keys k peer_scalar scalar
  )
let derive_keys_commutes k scalar peer_scalar =
  derive_keys_succeeds k scalar peer_scalar;
  derive_keys_symmetric k scalar peer_scalar

/// When each STA processes the SAE Commit message of the other STA,
/// both derive the same keys.

val process_commit_agreement:
  pwe:bytes ->
  rand_a:bytes -> mask_a:bytes ->
  rand_b:bytes -> mask_b:bytes ->
  Lemma
  (requires
    ~(DhPub? pwe) /\
    sae_are_valid_secrets rand_a mask_a /\
    sae_are_valid_secrets rand_b mask_b
  )
  (ensures (
    let commit_a = compute_commit pwe rand_a mask_a in
    let commit_b = compute_commit pwe rand_b mask_b in
    Some? commit_a /\ Some? commit_b /\ (
      let Some commit_a = commit_a in
      let Some commit_b = commit_b in
      let keys_a = process_commit pwe rand_a commit_a.scalar commit_b.scalar commit_b.element in
      let keys_b = process_commit pwe rand_b commit_b.scalar commit_a.scalar commit_a.element in
      Some? keys_a /\ keys_a == keys_b
    )
  ))
let process_commit_agreement pwe rand_a mask_a rand_b mask_b =
  reveal_opaque (`%compute_commit) (compute_commit);
  reveal_opaque (`%process_commit) (process_commit);
  compute_shared_secret_correct pwe rand_a rand_b mask_b;
  compute_shared_secret_correct pwe rand_b rand_a mask_a;
  sae_scalar_op_commutes pwe rand_a rand_b;
  let k = sae_f (sae_scalar_op rand_a (sae_scalar_op rand_b pwe)) in
  derive_keys_commutes k (sae_add_mod_r rand_a mask_a) (sae_add_mod_r rand_b mask_b)

(*** Confirmation exchange ***)

/// An SAE Confirm message is accepted by the peer:
/// the verifier computed by the peer (with the scalars and elements swapped)
/// is equal to the confirm.

val verify_confirm_correct:
  kck:bytes -> send_confirm:nat_lbytes 2 ->
  scalar:bytes -> element:bytes -> peer_scalar:bytes -> peer_element:bytes ->
  Lemma (
    let confirm = compute_confirm kck send_confirm scalar element peer_scalar peer_element in
    verify_confirm kck send_confirm peer_scalar peer_element scalar element confirm
  )
let verify_confirm_correct kck send_confirm scalar element peer_scalar peer_element =
  reveal_opaque (`%compute_confirm) (compute_confirm);
  reveal_opaque (`%verify_confirm) (verify_confirm)
