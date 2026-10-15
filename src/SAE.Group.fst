module SAE.Group

open DY.Core

#set-options "--fuel 0 --ifuel 0"

/// Abstract finite cyclic group of SAE (IEEE Std 802.11-2024, 12.4.4),
/// written additively, with its scalar field Z_r.
///
/// The operations have NO implementation (`assume val`):
/// F* knows nothing about them except the axioms stated in this module
/// (and the label/attacker axioms in SAE.Group.Labels).
/// Every `assume val` is part of the trusted base of the model.
///
/// Scalars and elements are both `bytes`.
///
/// Consistency argument (not checked by F*):
/// all axioms of this module hold in the following model.
/// - Scalars: the field F = Q(X), where X contains one variable per `Rand` term.
///   Every other `bytes` value is mapped to some other element of F
///   (F is countable, so a bijection between `bytes` and F exists
///   that maps every `Rand` term to its variable).
/// - Elements: the F-vector space with one basis vector per output of `hash`
///   (again via a bijection between `bytes` and this countable vector space,
///   mapping `hash seed` to its basis vector).
/// - `s_is_in_range x` iff x <> 0, `e_is_identity e` iff e = 0, `e_is_valid e` is true.

(*** Operations ***)

/// Scalars: the field Z_r.

assume val s_add: bytes -> bytes -> bytes
assume val s_neg: bytes -> bytes
assume val s_mul: bytes -> bytes -> bytes
assume val s_inv: bytes -> bytes
assume val s_zero: bytes
assume val s_one: bytes

/// 1 < x < r (12.4.5.2, 12.4.5.4)

assume val s_is_in_range: bytes -> bool

/// Elements: the cyclic group (point addition, or multiplication modulo p).

assume val e_op: bytes -> bytes -> bytes
assume val e_inv: bytes -> bytes

/// Scalar multiplication x * E (scalar-op).
/// It cannot be defined by repeating e_op: a symbolic scalar is not a number.

assume val smul: bytes -> bytes -> bytes

/// Element validation (12.4.5.4) and the identity check on K (12.4.5.4).

assume val e_is_valid: bytes -> bool
assume val e_is_identity: bytes -> bool

/// A base of the group: an output of hash-to-element (the PWE).
/// Outputs of `hash` for different seeds are treated as independent generators
/// (symbolic assumption, see `independent_bases`).

val is_base: bytes -> prop
let is_base p =
  exists seed. p == hash seed

(*** Field axioms (scalars) ***)

assume val s_add_comm:
  x:bytes -> y:bytes ->
  Lemma (s_add x y == s_add y x)

assume val s_add_assoc:
  x:bytes -> y:bytes -> z:bytes ->
  Lemma (s_add (s_add x y) z == s_add x (s_add y z))

assume val s_add_zero:
  x:bytes ->
  Lemma (s_add x s_zero == x)

assume val s_add_neg:
  x:bytes ->
  Lemma (s_add x (s_neg x) == s_zero)

assume val s_mul_comm:
  x:bytes -> y:bytes ->
  Lemma (s_mul x y == s_mul y x)

assume val s_mul_assoc:
  x:bytes -> y:bytes -> z:bytes ->
  Lemma (s_mul (s_mul x y) z == s_mul x (s_mul y z))

assume val s_mul_one:
  x:bytes ->
  Lemma (s_mul x s_one == x)

assume val s_mul_distr:
  x:bytes -> y:bytes -> z:bytes ->
  Lemma (s_mul x (s_add y z) == s_add (s_mul x y) (s_mul x z))

/// Every scalar in range (in particular every scalar <> 0) has an inverse.

assume val s_mul_inv:
  x:bytes ->
  Lemma
  (requires s_is_in_range x)
  (ensures s_mul x (s_inv x) == s_one)

(*** Group and module axioms (elements) ***)

assume val e_op_comm:
  e1:bytes -> e2:bytes ->
  Lemma (e_op e1 e2 == e_op e2 e1)

assume val e_op_assoc:
  e1:bytes -> e2:bytes -> e3:bytes ->
  Lemma (e_op (e_op e1 e2) e3 == e_op e1 (e_op e2 e3))

/// (x + y) * E = x * E + y * E

assume val smul_add:
  x:bytes -> y:bytes -> e:bytes ->
  Lemma (smul (s_add x y) e == e_op (smul x e) (smul y e))

/// x * (E1 + E2) = x * E1 + x * E2

assume val smul_e_op:
  x:bytes -> e1:bytes -> e2:bytes ->
  Lemma (smul x (e_op e1 e2) == e_op (smul x e1) (smul x e2))

/// (-x) * E = -(x * E)

assume val smul_neg:
  x:bytes -> e:bytes ->
  Lemma (smul (s_neg x) e == e_inv (smul x e))

/// x * (y * E) = (x * y) * E

assume val smul_mul:
  x:bytes -> y:bytes -> e:bytes ->
  Lemma (smul x (smul y e) == smul (s_mul x y) e)

/// 1 * E = E

assume val smul_one:
  e:bytes ->
  Lemma (smul s_one e == e)

(*** Validity, identity and independence ***)

/// x * (y * P) is not the identity element if x and y are in range
/// (Z_r is a field and a base has order r).

assume val smul_not_identity:
  p:bytes -> x:bytes -> y:bytes ->
  Lemma
  (requires is_base p /\ s_is_in_range x /\ s_is_in_range y)
  (ensures not (e_is_identity (smul x (smul y p))))

/// An honest COMMIT-ELEMENT -(mask * P) is a valid element.

assume val commit_element_valid:
  p:bytes -> mask:bytes ->
  Lemma
  (requires is_base p /\ s_is_in_range mask)
  (ensures e_is_valid (e_inv (smul mask p)))

/// Symbolic independence of the bases.
/// When two honest STAs with the bases p1 and p2 process each other's SAE Commit message
/// (rand_i, mask_i fresh random values),
/// they compute the same K only if p1 = p2:
///   rand1 * ((rand2 + mask2) * p1 - mask2 * p2)  =  rand2 * ((rand1 + mask1) * p2 - mask1 * p1)
/// In a real cyclic group p2 = t * p1 for some unknown t,
/// and the equation holds only with negligible probability.

assume val independent_bases:
  p1:bytes -> rand1:bytes -> mask1:bytes ->
  p2:bytes -> rand2:bytes -> mask2:bytes ->
  Lemma
  (requires
    is_base p1 /\ is_base p2 /\
    Rand? rand1 /\ Rand? mask1 /\ Rand? rand2 /\ Rand? mask2 /\
    smul rand1 (e_op (smul (s_add rand2 mask2) p1) (e_inv (smul mask2 p2))) ==
    smul rand2 (e_op (smul (s_add rand1 mask1) p2) (e_inv (smul mask1 p1)))
  )
  (ensures p1 == p2)

(*** Derived lemmas (proved from the axioms) ***)

/// The reduction SAE relies on (12.4.5.4):
///   elem-op(scalar-op(rand + mask, P), inverse-op(scalar-op(mask, P))) = scalar-op(rand, P)

val sae_cancel:
  p:bytes -> rand:bytes -> mask:bytes ->
  Lemma (e_op (smul (s_add rand mask) p) (e_inv (smul mask p)) == smul rand p)
let sae_cancel p rand mask =
  smul_neg mask p;
  smul_add (s_add rand mask) (s_neg mask) p;
  s_add_assoc rand mask (s_neg mask);
  s_add_neg mask;
  s_add_zero rand

/// x * (y * P) = y * (x * P)

val smul_comm:
  p:bytes -> x:bytes -> y:bytes ->
  Lemma (smul x (smul y p) == smul y (smul x p))
let smul_comm p x y =
  smul_mul x y p;
  smul_mul y x p;
  s_mul_comm x y
