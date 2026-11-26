module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.isInt (x : _root_.Formalism.CyclotomicNorms.Fbar g) : IsIntegral (ZMod g) x :=
  Algebra.IsIntegral.isIntegral x

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar {f : (ZMod g)[X]} (hf : f ≠ 0) {x : _root_.Formalism.CyclotomicNorms.Fbar g} :
    x ∈ _root_.Formalism.CyclotomicNorms.rootsBar f ↔ aeval x f = 0 := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, aeval_def]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.nodup_minpoly (x : _root_.Formalism.CyclotomicNorms.Fbar g) : (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) x)).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  exact nodup_roots ((PerfectField.separable_of_irreducible
    (minpoly.irreducible (_root_.GlobalTheory.GoodCharsCompare.isInt x))).map)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_of_rootsBar {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : _root_.Formalism.CyclotomicNorms.rootsBar f = _root_.Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  have key : ∀ {p : (ZMod g)[X]}, p.Monic →
      ((_root_.Formalism.CyclotomicNorms.rootsBar p).map fun a => X - C a).prod = p.map (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)) := by
    intro p hp
    unfold _root_.Formalism.CyclotomicNorms.rootsBar
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      IsAlgClosed.card_roots_eq_natDegree
  apply Polynomial.map_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g))
    (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective
  rw [← key hf, ← key hh, e]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.card_rootsBar (f : (ZMod g)[X]) :
    (_root_.Formalism.CyclotomicNorms.rootsBar f).card = f.natDegree := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

abbrev dg (y : _root_.Formalism.CyclotomicNorms.Fbar g) : ℕ := (minpoly (ZMod g) y).natDegree

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.dg_pos (y : _root_.Formalism.CyclotomicNorms.Fbar g) : 0 < _root_.GlobalTheory.GoodCharsCompare.dg y :=
  minpoly.natDegree_pos (_root_.GlobalTheory.GoodCharsCompare.isInt y)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    y ^ g ^ _root_.GlobalTheory.GoodCharsCompare.dg y = y ∧
    ∀ i < _root_.GlobalTheory.GoodCharsCompare.dg y, ∀ j < _root_.GlobalTheory.GoodCharsCompare.dg y,
      y ^ g ^ i = y ^ g ^ j → i = j := by
  have hg : g.Prime := Fact.out
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {y}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {y}) := Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {y}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) =
      g ^ _root_.GlobalTheory.GoodCharsCompare.dg y := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := IntermediateField.adjoin (ZMod g) {y}),
      ZMod.card, IntermediateField.adjoin.finrank hint]
  have fixed : ∀ k, 0 < k → y ^ g ^ k = y → _root_.GlobalTheory.GoodCharsCompare.dg y ≤ k := by
    intro k hk hy
    let S : Subfield (_root_.Formalism.CyclotomicNorms.Fbar g) :=
      (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k).eqLocusField (RingHom.id _)
    let T : IntermediateField (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) := S.toIntermediateField (fun x => by
      show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x) =
        algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x
      rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow])
    have hKT : IntermediateField.adjoin (ZMod g) {y} ≤ T :=
      IntermediateField.adjoin_simple_le_iff.mpr (by
        show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k y = y
        rw [iterateFrobenius_def, hy])
    have hne : (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero _ hk.ne' hg.one_lt
    have hle : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) ≤ g ^ k := by
      classical
      calc Fintype.card (IntermediateField.adjoin (ZMod g) {y})
          = (Finset.univ.image fun z : IntermediateField.adjoin (ZMod g) {y} =>
              (z : _root_.Formalism.CyclotomicNorms.Fbar g)).card := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.toFinset.card := by
            apply Finset.card_le_card
            intro z hz
            obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
            have hw : (w : _root_.Formalism.CyclotomicNorms.Fbar g) ^ g ^ k = w := by
              rw [← iterateFrobenius_def]
              exact hKT w.2
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hw,
              sub_self]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).natDegree := card_roots' _
        _ = g ^ k := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hk.ne' hg.one_lt
    rw [hcard] at hle
    exact (Nat.pow_le_pow_iff_right hg.one_lt).mp hle
  refine ⟨?_, ?_⟩
  · have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) y)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  · have key : ∀ i j, i < j → j < _root_.GlobalTheory.GoodCharsCompare.dg y → y ^ g ^ i = y ^ g ^ j → False := by
      intro i j hij hj e
      have hfix : y ^ g ^ (j - i) = y := by
        apply (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g i).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add,
          Nat.sub_add_cancel hij.le]
        exact e.symm
      have := fixed (j - i) (Nat.sub_pos_of_lt hij) hfix
      omega
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj e).elim
    · exact h
    · exact (key j i h hi e.symm).elim

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g (f : (ZMod g)[X]) (y : _root_.Formalism.CyclotomicNorms.Fbar g) (i : ℕ)
    (h : aeval y f = 0) : aeval (y ^ g ^ i) f = 0 := by
  induction i with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, pow_mul, ← expand_aeval, ZMod.expand_card, map_pow, ih,
      zero_pow (Fact.out : g.Prime).ne_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
open Classical in
theorem _root_.GlobalTheory.GoodCharsCompare.roots_minpoly (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).toFinset =
      (Finset.range (_root_.GlobalTheory.GoodCharsCompare.dg y)).image fun i => y ^ g ^ i := by
  have h0 : minpoly (ZMod g) y ≠ 0 := minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar h0]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    · calc _ ≤ (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).card := Multiset.toFinset_card_le _
        _ = _ := _root_.GlobalTheory.GoodCharsCompare.card_rootsBar _
    · intro i hi j hj e
      exact (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 i (by simpa using hi) j
        (by simpa using hj) e

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_roots_minpoly {y z : _root_.Formalism.CyclotomicNorms.Fbar g} :
    z ∈ _root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y) ↔ ∃ i, z = y ^ g ^ i := by
  classical
  constructor
  · intro hz
    rw [← Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.roots_minpoly] at hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar
      (minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y))]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_g_of {y : _root_.Formalism.CyclotomicNorms.Fbar g} {d : ℕ} (h : y ^ (g ^ d - 1) = 1) :
    y ^ g ^ d = y := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow d g (Fact.out : g.Prime).pos), pow_succ, h, one_mul]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_sub_one_eq_one_of_pow_pow_eq {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_dg {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) :
    y ^ (g ^ _root_.GlobalTheory.GoodCharsCompare.dg y - 1) = 1 :=
  pow_sub_one_eq_one_of_pow_pow_eq hy (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootC_prim {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1)) (g ^ d - 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC
  exact Complex.isPrimitiveRoot_exp _ (_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_log (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ^ (g ^ d - 1) = 1) :
    ∃ m, ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m := by
  haveI : NeZero (g ^ d - 1) := ⟨(_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'⟩
  obtain ⟨i, -, hi⟩ := (_root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd).eq_pow_of_pow_eq_one
    (ξ := ω y) (by rw [← map_pow, hy, map_one])
  exact ⟨i, hi.symm⟩

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.labelChar_eq (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {x y : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) {m : ℕ}
    (hm : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar ω d x y = ω x ^ m := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hprim := _root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd
  have red : ∀ ξ : ℂ, ξ ^ (g ^ d - 1) = 1 → ∀ k, ξ ^ k = ξ ^ (k % (g ^ d - 1)) := by
    intro ξ hξ k
    conv_lhs => rw [← Nat.mod_add_div k (g ^ d - 1), pow_add, pow_mul, hξ, one_pow, mul_one]
  have hs : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^
      sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} :=
    Nat.sInf_mem (s := {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a}) ⟨m, hm⟩
  have hxn : ω x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hmod : sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} % (g ^ d - 1) =
      m % (g ^ d - 1) := by
    apply hprim.pow_inj (Nat.mod_lt _ npos) (Nat.mod_lt _ npos)
    rw [← red _ hprim.pow_eq_one, ← red _ hprim.pow_eq_one]
    exact hs.symm.trans hm
  rw [red _ hxn, hmod, ← red _ hxn]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_preimage {ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ}
    (hω : Function.Injective ω) {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ (g ^ d - 1) = 1) :
    ∃ y : _root_.Formalism.CyclotomicNorms.Fbar g, y ^ (g ^ d - 1) = 1 ∧ ω y = z := by
  classical
  have hg : g.Prime := Fact.out
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hnF : ((g ^ d - 1 : ℕ) : _root_.Formalism.CyclotomicNorms.Fbar g) ≠ 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow d g hg.pos), Nat.cast_pow, CharP.cast_eq_zero,
      zero_pow hd.ne', zero_sub, Nat.cast_one, neg_ne_zero]
    exact one_ne_zero
  have hsep : (X ^ (g ^ d - 1) - C (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).Separable :=
    separable_X_pow_sub_C 1 hnF one_ne_zero
  have hA : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.card = g ^ d - 1 := by
    unfold nthRoots
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      natDegree_X_pow_sub_C _]
  have himage : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.image ω ⊆
      (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy ⊢
    rw [← map_pow, hy, map_one]
  have hcardB : (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset.card ≤ g ^ d - 1 :=
    (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
  have heq := Finset.eq_of_subset_of_card_le himage
    (by rw [Finset.card_image_of_injective _ hω, hA]; exact hcardB)
  have hzB : z ∈ (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    rw [Multiset.mem_toFinset, mem_nthRoots npos]
    exact hz
  rw [← heq] at hzB
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzB
  rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy
  exact ⟨y, hy, rfl⟩

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootsBar_pow (f : (ZMod g)[X]) (k : ℕ) : _root_.Formalism.CyclotomicNorms.rootsBar (f ^ k) = k • _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, roots_pow]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.sum_shift {z : ℂ} {m e : ℕ} (h : z ^ (m * g ^ e) = z ^ m) (j : ℕ) :
    ∑ i ∈ Finset.range e, (z ^ g ^ j) ^ (m * g ^ i) = ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
  have hper : ∀ i, z ^ (m * g ^ (i + e)) = z ^ (m * g ^ i) := fun i => by
    rw [show m * g ^ (i + e) = m * g ^ e * g ^ i by ring, pow_mul, h, ← pow_mul]
  have shift : ∀ j, ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) =
      ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) + z ^ (m * g ^ (0 + j)) :=
        Finset.sum_range_succ' _ _
      have h2 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) + z ^ (m * g ^ (e + j)) :=
        Finset.sum_range_succ _ _
      have h3 : z ^ (m * g ^ (e + j)) = z ^ (m * g ^ (0 + j)) := by
        rw [add_comm e j, hper, zero_add]
      have h4 : ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) :=
        add_right_cancel (h1.symm.trans (h2.trans (congrArg (HAdd.hAdd _) h3)))
      rw [← ih, ← h4]
      exact Finset.sum_congr rfl fun i _ => by rw [show i + (j + 1) = i + 1 + j by omega]
  rw [← shift j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]
  congr 1
  ring

end GlobalTheory.GoodCharsCompare
end
end

noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_dg_mul_eq_self (y : _root_.Formalism.CyclotomicNorms.Fbar g) (q : ℕ) :
    y ^ g ^ (_root_.GlobalTheory.GoodCharsCompare.dg y * q) = y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_dg_mul {d : ℕ} (hd : 0 < d) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ^ (g ^ d - 1) = 1) : ∃ k, d = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
  have hDpos := _root_.GlobalTheory.GoodCharsCompare.dg_pos y
  have hd' : y ^ g ^ d = y := _root_.GlobalTheory.GoodCharsCompare.pow_g_of hy
  refine ⟨d / _root_.GlobalTheory.GoodCharsCompare.dg y, ?_⟩
  have hr : y ^ g ^ (d % _root_.GlobalTheory.GoodCharsCompare.dg y) = y ^ g ^ 0 := by
    rw [pow_zero, pow_one]
    conv_rhs => rw [← hd', ← Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y), pow_add, pow_mul,
      pow_pow_dg_mul_eq_self]
  have h1 := (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 _ (Nat.mod_lt _ hDpos) 0 hDpos hr
  have h2 := Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y)
  rw [h1, add_zero] at h2
  exact h2.symm

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_sub_one_eq_one_of_pow_pow_eq_self {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.root_pow {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι (ZMod g)} (hM : M.det ≠ 0)
    {p : (ZMod g)[X]} {k : ℕ} (hp : Irreducible p) (hk : M.charpoly = p ^ k) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ∈ _root_.Formalism.CyclotomicNorms.rootsBar M.charpoly) : y ^ (g ^ Fintype.card ι - 1) = 1 := by
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  have hchar0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, ← coeff_zero_eq_aeval_zero',
      map_eq_zero] at hy
    apply hM
    rw [Matrix.det_eq_sign_charpoly_coeff, hy, mul_zero]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar one_ne_zero, map_one] at hy
    exact one_ne_zero hy
  have hyp : aeval y p = 0 := by
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, hk, map_pow] at hy
    exact (pow_eq_zero_iff hk0).mp hy
  have hdvd : minpoly (ZMod g) y ∣ p := minpoly.dvd _ _ hyp
  have hassoc : Associated (minpoly (ZMod g) y) p :=
    associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hp hdvd)
  have hdeg : p.natDegree = _root_.GlobalTheory.GoodCharsCompare.dg y :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm
  have hcard : Fintype.card ι = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hk, natDegree_pow, hdeg, mul_comm]
  apply pow_pow_sub_one_eq_one_of_pow_pow_eq_self hy0
  rw [hcard]
  exact pow_pow_dg_mul_eq_self y k

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.coeff_zero_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    f.coeff 0 ≠ 0 ↔ (0 : _root_.Formalism.CyclotomicNorms.Fbar g) ∉ _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, ← aeval_def,
    ← coeff_zero_eq_aeval_zero', map_eq_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.squarefree_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    Squarefree f ↔ (_root_.Formalism.CyclotomicNorms.rootsBar f).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (IsAlgClosed.splits _), separable_map,
    PerfectField.separable_iff_squarefree]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.primeToPart_map (β : _root_.Formalism.CyclotomicNorms.Fbar g ≃* _root_.Formalism.CyclotomicNorms.Fbar g) (l : ℕ) (x : _root_.Formalism.CyclotomicNorms.Fbar g) :
    _root_.Formalism.CyclotomicNorms.primeToPart l (β x) = β (_root_.Formalism.CyclotomicNorms.primeToPart l x) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [MulEquiv.orderOf_eq, map_pow]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_minpoly {φ : (ZMod g)[X]} (hm : φ.Monic)
    (hi : Irreducible φ) {x : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ _root_.Formalism.CyclotomicNorms.rootsBar φ) : φ = minpoly (ZMod g) x :=
  minpoly.eq_of_irreducible_of_monic hi
    ((_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hm.ne_zero).mp hx) hm

def Ext (ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ)
    (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) : Prop :=
  ∀ u : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ, ((ι u : ℂˣ) : ℂ) = ω u

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_ext {ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ}
    (hι : Function.Injective ι) :
    ∃ ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ, Function.Injective ω ∧ _root_.GlobalTheory.GoodCharsCompare.Ext ι ω := by
  classical
  let f : _root_.Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if h : x = 0 then 0 else ((ι (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((ι (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  refine ⟨ω, ?_, ?_⟩
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have := hι (Units.ext hab)
      simpa using congrArg Units.val this
  · intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]

end GlobalTheory.GoodCharsCompare
