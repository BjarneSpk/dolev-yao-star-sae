module SAE.Group.Labels

open DY.Core
open SAE.Group

#set-options "--fuel 0 --ifuel 0"

/// Label and attacker axioms of the abstract group (SAE.Group).
///
/// DY* computes labels (`get_label`) and the bytes invariant structurally,
/// on the constructors of `bytes`.
/// The results of the abstract group operations have no known structure,
/// hence their labels are given by the axioms below.
/// Like the axioms of SAE.Group, they are `assume val`s.
///
/// Two kinds of axioms:
/// 1. The attacker can compute the group operations:
///    every operation preserves publishability and attacker knowledge.
///    These are the counterparts of DY*'s `*_preserves_publishability` lemmas.
/// 2. Labels of the values an honest STA computes:
///    commit-scalar, COMMIT-ELEMENT and the shared element K.
///    Each of them states the real-world condition under which the attacker can compute the value,
///    and comes with preconditions that exclude the cases where this condition is different
///    (e.g., a value used both as a mask and as rand).

(*** Usages of the secret values of an SAE Commit message ***)

/// rand and mask are scalars of the group.
/// The usage of mask records the rand it masks,
/// which ensures that a mask is used for a single commit-scalar.

val sae_rand_usage: usage
let sae_rand_usage = DhKey "SAE.Rand" (Literal Seq.empty)

val sae_mask_usage: bytes -> usage
let sae_mask_usage rand = DhKey "SAE.Mask" rand

(*** 1. The attacker can compute the group operations ***)

/// Publishability is preserved by every operation.

assume val s_add_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> x:bytes -> y:bytes ->
  Lemma
  (requires is_publishable tr x /\ is_publishable tr y)
  (ensures is_publishable tr (s_add x y))

assume val s_neg_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> x:bytes ->
  Lemma
  (requires is_publishable tr x)
  (ensures is_publishable tr (s_neg x))

assume val s_mul_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> x:bytes -> y:bytes ->
  Lemma
  (requires is_publishable tr x /\ is_publishable tr y)
  (ensures is_publishable tr (s_mul x y))

assume val s_inv_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> x:bytes ->
  Lemma
  (requires is_publishable tr x)
  (ensures is_publishable tr (s_inv x))

assume val e_op_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> e1:bytes -> e2:bytes ->
  Lemma
  (requires is_publishable tr e1 /\ is_publishable tr e2)
  (ensures is_publishable tr (e_op e1 e2))

assume val e_inv_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> e:bytes ->
  Lemma
  (requires is_publishable tr e)
  (ensures is_publishable tr (e_inv e))

assume val smul_preserves_publishability:
  {|crypto_invariants|} -> tr:trace -> x:bytes -> e:bytes ->
  Lemma
  (requires is_publishable tr x /\ is_publishable tr e)
  (ensures is_publishable tr (smul x e))

assume val constants_publishable:
  {|crypto_invariants|} -> tr:trace ->
  Lemma (is_publishable tr s_zero /\ is_publishable tr s_one)

/// The attacker knowledge is closed under every operation.

assume val attacker_knows_s_add:
  tr:trace -> x:bytes -> y:bytes ->
  Lemma
  (requires attacker_knows tr x /\ attacker_knows tr y)
  (ensures attacker_knows tr (s_add x y))

assume val attacker_knows_s_neg:
  tr:trace -> x:bytes ->
  Lemma
  (requires attacker_knows tr x)
  (ensures attacker_knows tr (s_neg x))

assume val attacker_knows_s_mul:
  tr:trace -> x:bytes -> y:bytes ->
  Lemma
  (requires attacker_knows tr x /\ attacker_knows tr y)
  (ensures attacker_knows tr (s_mul x y))

assume val attacker_knows_s_inv:
  tr:trace -> x:bytes ->
  Lemma
  (requires attacker_knows tr x)
  (ensures attacker_knows tr (s_inv x))

assume val attacker_knows_e_op:
  tr:trace -> e1:bytes -> e2:bytes ->
  Lemma
  (requires attacker_knows tr e1 /\ attacker_knows tr e2)
  (ensures attacker_knows tr (e_op e1 e2))

assume val attacker_knows_e_inv:
  tr:trace -> e:bytes ->
  Lemma
  (requires attacker_knows tr e)
  (ensures attacker_knows tr (e_inv e))

assume val attacker_knows_smul:
  tr:trace -> x:bytes -> e:bytes ->
  Lemma
  (requires attacker_knows tr x /\ attacker_knows tr e)
  (ensures attacker_knows tr (smul x e))

assume val attacker_knows_constants:
  tr:trace ->
  Lemma (attacker_knows tr s_zero /\ attacker_knows tr s_one)

(*** 2. Labels of the values of an honest STA ***)

/// commit-scalar = (rand + mask) mod r is publishable:
/// mask is a one-time pad for rand.
/// - rand and mask are fresh random values with the same label
///   (whoever learns one of them learns the other from the scalar),
/// - mask is a mask for this rand (its usage), so it pads a single scalar.

assume val commit_scalar_publishable:
  {|crypto_invariants|} -> tr:trace -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    Rand? rand /\ Rand? mask /\ ~(rand == mask) /\
    bytes_invariant tr rand /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr rand == get_label tr mask
  )
  (ensures is_publishable tr (s_add rand mask))

/// COMMIT-ELEMENT = -(mask * P) is publishable:
/// computing mask from it is the discrete logarithm problem.
/// - mask is a mask (its usage): for rand, rand * P is not public,
/// - who learns mask can compute P = mask^-1 * (mask * P),
///   hence the label of mask must be at least as secret as the one of P.

assume val commit_element_publishable:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? mask /\
    bytes_invariant tr p /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr mask
  )
  (ensures is_publishable tr (e_inv (smul mask p)))

/// K = x * (y * P) for two honest secret values x and y (both STAs honest).
/// The attacker can compute K if it knows P and one of x and y:
///   label = join (meet P x) (meet P y)
/// Precondition: who learns x (or y) can also compute P
/// (true for rand and mask: P = mask^-1 * -COMMIT-ELEMENT),
/// which excludes the cases where x * P or y * P is public.

assume val shared_element_label:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> x:bytes -> y:bytes ->
  Lemma
  (requires
    is_base p /\
    bytes_invariant tr p /\ bytes_invariant tr x /\ bytes_invariant tr y /\
    get_label tr p `can_flow tr` get_label tr x /\
    get_label tr p `can_flow tr` get_label tr y
  )
  (ensures (
    let k = smul x (smul y p) in
    bytes_invariant tr k /\
    get_label tr k == join (meet (get_label tr p) (get_label tr x)) (meet (get_label tr p) (get_label tr y))
  ))

/// K = rand * (scalar * P + element) for any publishable scalar and element
/// (the peer may be the attacker).
/// The attacker cannot compute K without P:
/// scalar * P is unknown (scalar is in range, i.e., not 0),
/// and so is rand * P (rand is not a mask).
/// Hence the label of K is join (meet P rand) (meet P l) for some label l.
/// K is not the identity element (checked by the STA, 12.4.5.4).

assume val processed_element_label:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> rand:bytes -> scalar:bytes -> element:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? rand /\
    bytes_invariant tr p /\ bytes_invariant tr rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr rand /\
    is_publishable tr scalar /\ is_publishable tr element /\
    s_is_in_range scalar /\
    not (e_is_identity (smul rand (e_op (smul scalar p) element)))
  )
  (ensures (
    let k = smul rand (e_op (smul scalar p) element) in
    bytes_invariant tr k /\
    (exists (l:label). get_label tr k == join (meet (get_label tr p) (get_label tr rand)) (meet (get_label tr p) l))
  ))
