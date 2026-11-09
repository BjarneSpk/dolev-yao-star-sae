module SAE.Group.Sanity

open DY.Core
open SAE.Group
open SAE.Group.Labels

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// Vacuity checks for the axioms of SAE.Group and SAE.Group.Labels.
/// Not part of the build (not in src/). Run with:
///   make sanity
/// EXPECTED RESULT: every lemma named `bad_*` FAILS to verify,
/// and every lemma named `ok_*` verifies.
/// A `bad_*` lemma that verifies means that the axioms are inconsistent
/// (or leak a secret), and every security property becomes meaningless.
/// A failure only shows that Z3 found no proof, not that none exists.
///
/// Every `bad_*` lemma that applies a label axiom has an `ok_*` twin
/// with the same preconditions and the same axiom calls,
/// which proves what these calls yield instead of False.
/// The twin verifies only if the axioms are applicable in this context.
/// Without it, a `bad_*` lemma whose axiom call fails
/// (e.g., after a precondition was added to the axiom)
/// would still fail, and be reported as OK, without testing anything.

(*** Positive control ***)

val ok_cancel:
  p:bytes -> rand:bytes -> mask:bytes ->
  Lemma (e_op (smul (s_add rand mask) p) (e_inv (smul mask p)) == smul rand p)
let ok_cancel p rand mask = sae_cancel p rand mask

/// Double negation, derived from the field and module axioms
/// (used below to recover mask * P from the COMMIT-ELEMENT).

val ok_s_neg_neg: x:bytes -> Lemma (s_neg (s_neg x) == x)
let ok_s_neg_neg x =
  s_add_zero x;
  s_add_neg (s_neg x);
  s_add_assoc x (s_neg x) (s_neg (s_neg x));
  s_add_neg x;
  s_add_comm s_zero (s_neg (s_neg x));
  s_add_zero (s_neg (s_neg x))

val ok_e_inv_inv: x:bytes -> p:bytes -> Lemma (e_inv (e_inv (smul x p)) == smul x p)
let ok_e_inv_inv x p =
  smul_neg x p;
  smul_neg (s_neg x) p;
  ok_s_neg_neg x

(*** The algebraic axioms do not prove False ***)

val bad_false_algebra:
  x:bytes -> y:bytes -> z:bytes -> p:bytes -> q:bytes ->
  Lemma False
let bad_false_algebra x y z p q =
  s_add_comm x y; s_add_assoc x y z; s_add_zero x; s_add_neg x;
  s_mul_comm x y; s_mul_assoc x y z; s_mul_one x; s_mul_distr x y z;
  e_op_comm p q; e_op_assoc p q (smul x p);
  smul_add x y p; smul_e_op x p q; smul_neg x p; smul_mul x y p; smul_one p

/// Two different bases with the honest-session equation.

val bad_false_bases:
  p1:bytes -> r1:bytes -> m1:bytes -> p2:bytes -> r2:bytes -> m2:bytes ->
  Lemma
  (requires is_base p1 /\ is_base p2 /\ ~(p1 == p2) /\ Rand? r1 /\ Rand? m1 /\ Rand? r2 /\ Rand? m2)
  (ensures False)
let bad_false_bases p1 r1 m1 p2 r2 m2 =
  sae_cancel p1 r2 m2;
  sae_cancel p2 r1 m1;
  smul_comm p1 r1 r2;
  FStar.Classical.move_requires (independent_bases p1 r1 m1 p2 r2) m2

(*** The label axioms do not leak the secrets ***)

/// rand from the publishable commit-scalar.

val ok_rand_from_scalar:
  {|crypto_invariants|} -> tr:trace -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    Rand? rand /\ Rand? mask /\ ~(rand == mask) /\
    bytes_invariant tr rand /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr rand == get_label tr mask /\
    ~(is_corrupt tr (get_label tr rand))
  )
  (ensures is_publishable tr (s_add rand mask))
let ok_rand_from_scalar #ci tr rand mask =
  commit_scalar_publishable tr rand mask

val bad_rand_from_scalar:
  {|crypto_invariants|} -> tr:trace -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    Rand? rand /\ Rand? mask /\ ~(rand == mask) /\
    bytes_invariant tr rand /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr rand == get_label tr mask /\
    ~(is_corrupt tr (get_label tr rand))
  )
  (ensures False)
let bad_rand_from_scalar #ci tr rand mask =
  commit_scalar_publishable tr rand mask;
  constants_publishable tr;
  s_neg_preserves_publishability tr (s_add rand mask);
  s_add_preserves_publishability tr (s_add rand mask) (s_neg (s_add rand mask));
  s_add_neg (s_add rand mask);
  s_add_assoc rand mask (s_neg mask);
  s_add_neg mask;
  s_add_zero rand

/// P from the publishable COMMIT-ELEMENT.

val ok_pwe_from_element:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? mask /\
    bytes_invariant tr p /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr mask /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures is_publishable tr (e_inv (smul mask p)))
let ok_pwe_from_element #ci tr p rand mask =
  commit_element_publishable tr p rand mask

val bad_pwe_from_element:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> rand:bytes -> mask:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? mask /\
    bytes_invariant tr p /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr mask /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures False)
let bad_pwe_from_element #ci tr p rand mask =
  commit_element_publishable tr p rand mask;
  constants_publishable tr;
  e_inv_preserves_publishability tr (e_inv (smul mask p));
  smul_preserves_publishability tr s_one (e_inv (e_inv (smul mask p)));
  smul_preserves_publishability tr s_zero (e_inv (smul mask p));
  smul_neg mask p;
  smul_one (smul mask p)

/// K from the two SAE Commit messages of an honest session (the password is not corrupt).

val ok_k_from_commits:
  {|crypto_invariants|} -> tr:trace -> p:bytes ->
  ra:bytes -> ma:bytes -> rb:bytes -> mb:bytes ->
  Lemma
  (requires
    is_base p /\ bytes_invariant tr p /\
    Rand? ra /\ Rand? ma /\ Rand? rb /\ Rand? mb /\ ~(ra == ma) /\ ~(rb == mb) /\
    bytes_invariant tr ra /\ bytes_invariant tr ma /\ bytes_invariant tr rb /\ bytes_invariant tr mb /\
    ma `has_usage tr` sae_mask_usage ra /\ mb `has_usage tr` sae_mask_usage rb /\
    ra `has_usage tr` sae_rand_usage /\ rb `has_usage tr` sae_rand_usage /\
    get_label tr ra == get_label tr ma /\ get_label tr rb == get_label tr mb /\
    get_label tr p `can_flow tr` get_label tr ra /\ get_label tr p `can_flow tr` get_label tr rb /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures (
    let k = smul ra (smul rb p) in
    is_publishable tr (s_add ra ma) /\ is_publishable tr (s_add rb mb) /\
    is_publishable tr (e_inv (smul ma p)) /\ is_publishable tr (e_inv (smul mb p)) /\
    get_label tr k == join (meet (get_label tr p) (get_label tr ra)) (meet (get_label tr p) (get_label tr rb))
  ))
let ok_k_from_commits #ci tr p ra ma rb mb =
  commit_scalar_publishable tr ra ma;
  commit_scalar_publishable tr rb mb;
  commit_element_publishable tr p ra ma;
  commit_element_publishable tr p rb mb;
  shared_element_label tr p ra rb

val bad_k_from_commits:
  {|crypto_invariants|} -> tr:trace -> p:bytes ->
  ra:bytes -> ma:bytes -> rb:bytes -> mb:bytes ->
  Lemma
  (requires
    is_base p /\ bytes_invariant tr p /\
    Rand? ra /\ Rand? ma /\ Rand? rb /\ Rand? mb /\ ~(ra == ma) /\ ~(rb == mb) /\
    bytes_invariant tr ra /\ bytes_invariant tr ma /\ bytes_invariant tr rb /\ bytes_invariant tr mb /\
    ma `has_usage tr` sae_mask_usage ra /\ mb `has_usage tr` sae_mask_usage rb /\
    ra `has_usage tr` sae_rand_usage /\ rb `has_usage tr` sae_rand_usage /\
    get_label tr ra == get_label tr ma /\ get_label tr rb == get_label tr mb /\
    get_label tr p `can_flow tr` get_label tr ra /\ get_label tr p `can_flow tr` get_label tr rb /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures False)
let bad_k_from_commits #ci tr p ra ma rb mb =
  let sa = s_add ra ma in
  let ea = e_inv (smul ma p) in
  let sb = s_add rb mb in
  let eb = e_inv (smul mb p) in
  commit_scalar_publishable tr ra ma;
  commit_scalar_publishable tr rb mb;
  commit_element_publishable tr p ra ma;
  commit_element_publishable tr p rb mb;
  shared_element_label tr p ra rb;
  // every combination of the public values the attacker can compute
  smul_preserves_publishability tr sa eb;
  smul_preserves_publishability tr sb ea;
  e_op_preserves_publishability tr ea eb;
  e_inv_preserves_publishability tr ea;
  e_inv_preserves_publishability tr eb;
  smul_preserves_publishability tr sa (e_inv eb);
  smul_preserves_publishability tr sb (e_inv ea);
  smul_comm p ra rb;
  sae_cancel p ra ma;
  sae_cancel p rb mb

/// A public scalar times a public element is publishable, while the label axiom
/// for honest K would make it secret: excluded by the precondition of shared_element_label.

val ok_public_times_public:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> x:bytes -> mask:bytes -> rand:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? mask /\
    bytes_invariant tr p /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr mask /\
    is_publishable tr x /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures is_publishable tr (smul x (smul mask p)))
let ok_public_times_public #ci tr p x mask rand =
  commit_element_publishable tr p rand mask;
  e_inv_preserves_publishability tr (e_inv (smul mask p));
  ok_e_inv_inv mask p;
  smul_preserves_publishability tr x (smul mask p)

val bad_public_times_public:
  {|crypto_invariants|} -> tr:trace -> p:bytes -> x:bytes -> mask:bytes -> rand:bytes ->
  Lemma
  (requires
    is_base p /\ Rand? mask /\
    bytes_invariant tr p /\ bytes_invariant tr mask /\
    mask `has_usage tr` sae_mask_usage rand /\
    rand `has_usage tr` sae_rand_usage /\
    get_label tr p `can_flow tr` get_label tr mask /\
    is_publishable tr x /\
    ~(is_corrupt tr (get_label tr p))
  )
  (ensures False)
let bad_public_times_public #ci tr p x mask rand =
  commit_element_publishable tr p rand mask;
  e_inv_preserves_publishability tr (e_inv (smul mask p));
  ok_e_inv_inv mask p;
  smul_preserves_publishability tr x (smul mask p);
  FStar.Classical.move_requires (shared_element_label tr p x) mask
