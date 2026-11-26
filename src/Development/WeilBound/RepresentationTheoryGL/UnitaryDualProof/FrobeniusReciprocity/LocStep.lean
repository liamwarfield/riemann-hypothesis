module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.MemBzOfAdjoin
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.UnimodOfIndexSym
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.RelIndexLatConj
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpB
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SliceVanOfFrob

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.Imports
namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unimod [CharZero k] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) :=
  unimod_of_indexSym PositivityTheory.RgUd.T.Desc.SLT.indexSym

end PositivityTheory.RgUd.T.Desc.SLF.Un2
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CharpolyNilpotence.IsNilpotentAevalCharpoly
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Desc.JC

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] {n : ℕ}

theorem trace_aeval_eq_sum (A : Matrix (Fin n) (Fin n) k) (p : k[X]) :
    trace (aeval A p) = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (A ^ i) := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]

theorem isNilpotent_of_trace_pow [CharZero k] (A : Matrix (Fin n) (Fin n) k)
    (h : ∀ m, 1 ≤ m → trace (A ^ m) = 0) : IsNilpotent A := by
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd A.charpoly
    (charpoly_monic A).ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set r := rootMultiplicity 0 A.charpoly
  have hcop : IsCoprime (X ^ (r + 1) : k[X]) q :=
    IsCoprime.pow_left ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 hXq)
  obtain ⟨a, b, hab⟩ := hcop
  have hzero : aeval A (X ^ (r + 1) * q) = 0 := by
    have e : (X ^ (r + 1) * q : k[X]) = X * A.charpoly := by
      rw [hq]
      ring
    rw [e, map_mul, aeval_self_charpoly, mul_zero]
  have hsum : aeval A (a * X ^ (r + 1)) + aeval A (b * q) = 1 := by
    rw [← map_add (f := _), hab, map_one]
  have hprod : aeval A (a * X ^ (r + 1)) * aeval A (b * q) = 0 := by
    rw [← map_mul]
    have e : a * X ^ (r + 1) * (b * q) = (a * b) * (X ^ (r + 1) * q) := by ring
    rw [e, map_mul, hzero, mul_zero]
  have he : aeval A (a * X ^ (r + 1)) = 1 - aeval A (b * q) := eq_sub_of_add_eq hsum
  have hidem : IsIdempotentElem (aeval A (a * X ^ (r + 1))) := by
    unfold IsIdempotentElem
    calc aeval A (a * X ^ (r + 1)) * aeval A (a * X ^ (r + 1))
        = aeval A (a * X ^ (r + 1)) * (1 - aeval A (b * q)) := by rw [← he]
      _ = aeval A (a * X ^ (r + 1)) := by rw [mul_sub, mul_one, hprod, sub_zero]
  have htr : trace (aeval A (a * X ^ (r + 1))) = 0 := by
    rw [trace_aeval_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases i with _ | i
    · simp [coeff_mul_X_pow']
    · rw [h (i + 1) (by omega), mul_zero]
  have hlin : IsIdempotentElem (Matrix.toLinAlgEquiv' (aeval A (a * X ^ (r + 1)))) :=
    hidem.map _
  have hlintr : LinearMap.trace k _ (Matrix.toLinAlgEquiv' (aeval A (a * X ^ (r + 1)))) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change trace (LinearMap.toMatrix' (Matrix.toLin' _)) = 0
    rw [LinearMap.toMatrix'_toLin', htr]
  have hz : aeval A (a * X ^ (r + 1)) = 0 := by
    have := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hlin hlintr
    exact (map_eq_zero_iff _ (AlgEquiv.injective _)).1 this
  refine ⟨r + 1, ?_⟩
  have e : (X ^ (r + 1) : k[X]) = X ^ (r + 1) * (a * X ^ (r + 1)) + b * (X ^ (r + 1) * q) := by
    linear_combination (-(X ^ (r + 1) : k[X])) * hab
  have := congrArg (aeval A) e
  rw [map_add (f := _), map_mul (aeval A) (X ^ (r + 1)), hz, map_mul (aeval A) b, hzero, mul_zero, mul_zero,
    add_zero, map_pow, aeval_X] at this
  exact this

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_pow_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x x₀ : Matrix (Fin n) (Fin n) k}
    (h : pZ Z x = pZ Z x₀) (i : ℕ) (hi : i < 2 * n + 1) : trace (x ^ i) = trace (x₀ ^ i) := by
  have h1 : ((1 : Z) : Matrix (Fin n) (Fin n) k) =
      ∑ j, (Module.finBasis k Z).repr 1 j • ((Module.finBasis k Z j : Z) : Matrix (Fin n) (Fin n) k) := by
    have h0 := congrArg Subtype.val ((Module.finBasis k Z).sum_repr 1)
    rw [← h0, AddSubmonoidClass.coe_finsetSum]
    rfl
  have key : ∀ y : Matrix (Fin n) (Fin n) k, trace (y ^ i) =
      ∑ j, (Module.finBasis k Z).repr 1 j * pZ Z y (⟨i, hi⟩, j) := by
    intro y
    calc trace (y ^ i) = trace (((1 : Z) : Matrix (Fin n) (Fin n) k) * y ^ i) := by simp
      _ = _ := by
        rw [h1, Finset.sum_mul, Matrix.trace_sum]
        simp [pZ, smul_mul_assoc, Matrix.trace_smul]
  rw [key x, key x₀, h]

theorem trace_aeval_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x x₀ : Matrix (Fin n) (Fin n) k}
    (h : pZ Z x = pZ Z x₀) (p : k[X]) (hp : p.natDegree ≤ 2 * n) :
    trace (aeval x p) = trace (aeval x₀ p) := by
  rw [trace_aeval_eq_sum, trace_aeval_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [trace_pow_eq h i (by simp at hi; omega)]

private theorem trace_aeval_eq_of_pZ_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    {x x₀ : Matrix (Fin n) (Fin n) k} (h : pZ Z x = pZ Z x₀) (p : k[X]) :
    trace (aeval x p) = trace (aeval x₀ p) := by
  have hM : (x.charpoly * x₀.charpoly).Monic := (charpoly_monic x).mul (charpoly_monic x₀)
  have hdeg : (x.charpoly * x₀.charpoly).natDegree = 2 * n := by
    rw [(charpoly_monic x).natDegree_mul (charpoly_monic x₀), charpoly_natDegree_eq_dim,
      charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx : aeval x (x.charpoly * x₀.charpoly) = 0 := by
    rw [map_mul, aeval_self_charpoly, zero_mul]
  have hx0 : aeval x₀ (x.charpoly * x₀.charpoly) = 0 := by
    rw [map_mul, aeval_self_charpoly, mul_zero]
  rw [← aeval_modByMonic_eq_self_of_root hx, ← aeval_modByMonic_eq_self_of_root hx0]
  exact trace_aeval_eq h _ ((natDegree_modByMonic_le p hM).trans hdeg.le)

theorem isNilpotent_aeval_charpoly [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    {x x₀ : Matrix (Fin n) (Fin n) k} (h : pZ Z x = pZ Z x₀) : IsNilpotent (aeval x x₀.charpoly) := by
  apply isNilpotent_of_trace_pow
  intro m hm
  rw [← map_pow, trace_aeval_eq_of_pZ_eq h, map_pow, aeval_self_charpoly, zero_pow (by omega),
    Matrix.trace_zero]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pow_eq_zero_of_isNilpotent {N : Matrix (Fin n) (Fin n) k} (hN : IsNilpotent N) : N ^ n = 0 := by
  have h := isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h0 : N.charpoly - X ^ Fintype.card (Fin n) = 0 := h.eq_zero
  rw [sub_eq_zero, Fintype.card_fin] at h0
  have := aeval_self_charpoly N
  rwa [h0, map_pow, aeval_X] at this

theorem jcPoly [CharZero k] : JCPoly (k := k) := by
  classical
  unfold JCPoly
  intro m Z _ y
  by_cases hex : ∃ x₀ ∈ Bz Z, pZ Z x₀ = y
  · obtain ⟨x₀, -, rfl⟩ := hex
    have hsq : Squarefree (UniqueFactorizationMonoid.radical x₀.charpoly) :=
      UniqueFactorizationMonoid.squarefree_radical
    have hsep : (UniqueFactorizationMonoid.radical x₀.charpoly).Separable :=
      PerfectField.separable_iff_squarefree.mpr hsq
    obtain ⟨N, c, hc⟩ := (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd
      (charpoly_monic x₀).ne_zero).mpr dvd_rfl
    set Q := UniqueFactorizationMonoid.radical x₀.charpoly
    obtain ⟨a, b, hab⟩ := hsep
    set T : k[X] := X - b * Q
    have hT : ∀ z : k[X], T.comp z = z + -(b.comp z * Q.comp z) := by
      intro z
      simp [T, sub_comp, mul_comp, sub_eq_add_neg]
    have e1 : ∀ p w : k[X], (p.map C).eval w = p.comp w := fun p w => by
      rw [eval_map]
      rfl
    have step : ∀ z : k[X], ∃ w, Q.comp (T.comp z) = (Q.comp z) ^ 2 * w := by
      intro z
      obtain ⟨s, hs⟩ := Polynomial.binomExpansion (Q.map C) z (-(b.comp z * Q.comp z))
      refine ⟨a.comp z + s * (b.comp z) ^ 2, ?_⟩
      have hab' : a.comp z * Q.comp z + b.comp z * (derivative Q).comp z = 1 := by
        have := congrArg (fun p => p.comp z) hab
        simpa [add_comp, mul_comp] using this
      rw [derivative_map] at hs
      simp only [e1] at hs
      rw [hT, hs]
      linear_combination (-(Q.comp z)) * hab'
    have iter : ∀ j, ∃ w v, Q.comp ((fun p => T.comp p)^[j] X) = Q ^ (2 ^ j) * w ∧
        X - (fun p => T.comp p)^[j] X = Q * v := by
      intro j
      induction j with
      | zero => exact ⟨1, 0, by simp, by simp⟩
      | succ j ih =>
        obtain ⟨w, v, hw, hv⟩ := ih
        obtain ⟨w', hw'⟩ := step ((fun p => T.comp p)^[j] X)
        rw [Function.iterate_succ_apply']
        refine ⟨w ^ 2 * w', v + b.comp ((fun p => T.comp p)^[j] X) * Q ^ (2 ^ j - 1) * w, ?_, ?_⟩
        · rw [hw', hw, pow_succ (2 : ℕ) j, pow_mul]
          ring
        · have hQ : Q ^ (2 ^ j) = Q * Q ^ (2 ^ j - 1) := by
            rw [← pow_succ']
            congr 1
            have := Nat.one_le_two_pow (n := j)
            omega
          rw [hT, hw, hQ]
          linear_combination hv
    obtain ⟨w, v, hw, hv⟩ := iter m
    refine ⟨(fun p => T.comp p)^[m] X, fun x _ hx => ?_⟩
    have hQx : IsNilpotent (aeval x Q) := by
      have h5 := isNilpotent_aeval_charpoly hx
      have hpow : aeval x Q ^ N = aeval x x₀.charpoly * aeval x c := by
        rw [← map_pow, hc, map_mul]
      have hcomm : Commute (aeval x x₀.charpoly) (aeval x c) := by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
      have : IsNilpotent (aeval x Q ^ N) := by
        rw [hpow]
        exact hcomm.isNilpotent_mul_right h5
      exact IsNilpotent.of_pow this
    have hQn : aeval x Q ^ m = 0 := pow_eq_zero_of_isNilpotent hQx
    constructor
    · apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq
      have h0 : aeval (aeval x ((fun p => T.comp p)^[m] X)) Q = 0 := by
        rw [← aeval_comp, hw, map_mul, map_pow]
        rw [pow_eq_zero_of_le (Nat.lt_two_pow_self).le hQn, zero_mul]
      change aeval (Matrix.toLinAlgEquiv' _) Q = 0
      rw [aeval_algEquiv, AlgHom.comp_apply, h0, map_zero]
    · have h1 : x - aeval x ((fun p => T.comp p)^[m] X) = aeval x Q * aeval x v := by
        rw [← map_mul, ← hv, map_sub, aeval_X]
      rw [h1]
      have hcomm : Commute (aeval x Q) (aeval x v) := by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
      exact hcomm.isNilpotent_mul_right hQx
  · exact ⟨0, fun x hx hxy => absurd ⟨x, hx, hxy⟩ hex⟩

end PositivityTheory.RgUd.T.Desc.JC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.AdjointSemisimple.AdjunctionCharZero
namespace PositivityTheory.RgUd.T.AdjPf

open Module PositivityTheory.RgUd.T

theorem dc {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hr : IsReduced Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), x * y = y * x) : x ∈ Z := by
  classical
  haveI : IsReduced Z := hr
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  haveI : IsSemisimpleModule Z (Fin n → k) := inferInstance
  have key : ∀ g : Module.End Z (Fin n → k), ∀ v : Fin n → k,
      Matrix.mulVec x (g v) = g (Matrix.mulVec x v) := by
    intro g v
    set y := LinearMap.toMatrix' (g.restrictScalars k) with hydef
    have hyv : ∀ w, Matrix.mulVec y w = g w := fun w => by
      rw [← Matrix.toLin'_apply, hydef, Matrix.toLin'_toMatrix']
      rfl
    have hy : y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro a ha
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hyv, hyv]
      exact (g.map_smul ⟨a, ha⟩ w).symm
    rw [← hyv, ← hyv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx y hy]
  let f : Module.End (Module.End Z (Fin n → k)) (Fin n → k) :=
    { toFun := fun v => Matrix.mulVec x v
      map_add' := Matrix.mulVec_add x
      map_smul' := fun g v => key g v }
  obtain ⟨r, hr'⟩ := jacobson_density (R := Z) f
    (Finset.univ.image (fun i : Fin n => (Pi.single i (1 : k) : Fin n → k)))
  have hxr : x = (r : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply]
    exact hr' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hxr]
  exact r.2

theorem isSemisimple_of_mem {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hr : IsReduced Z) (z : Matrix (Fin n) (Fin n) k) (hz : z ∈ Z) :
    Module.End.IsSemisimple (Matrix.toLin' z) := by
  set w : Z := ⟨z, hz⟩ with hw
  have hint : IsIntegral k w := IsIntegral.of_finite k w
  have hm0 : minpoly k w ≠ 0 := minpoly.ne_zero hint
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := minpoly k w) ?_ ?_
  · intro x hx
    obtain ⟨r, hr⟩ := hx
    have h1 : Polynomial.aeval w (x * r) = 0 := by
      apply IsReduced.eq_zero
      refine ⟨2, ?_⟩
      rw [pow_two, ← map_mul]
      have hsq : x * r * (x * r) = minpoly k w * r := by rw [hr]; ring
      rw [hsq, map_mul, minpoly.aeval, zero_mul]
    have h2 : minpoly k w ∣ x * r := minpoly.dvd k w h1
    have hxr : x * r ≠ 0 := by
      intro h
      apply hm0
      rw [hr, mul_assoc, h, mul_zero]
    rw [hr, mul_assoc] at h2
    have h3 : x * (x * r) ∣ 1 * (x * r) := by rwa [one_mul]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxr).mp h3)
  · have h0 : Polynomial.aeval z (minpoly k w) = 0 := by
      have h := congrArg Z.val (minpoly.aeval k w)
      rwa [map_zero, ← Polynomial.aeval_algHom_apply] at h
    have h4 := Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom z (minpoly k w)
    rw [h0, map_zero] at h4
    exact h4

end PositivityTheory.RgUd.T.AdjPf

namespace PositivityTheory.RgUd.T

open Module

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjunction_char_zero [CharZero k] : Adj (k := k) := by
  intro n Z hZ s hs hsZ hss
  obtain ⟨hc, hr⟩ := hZ
  set S : Set (Matrix (Fin n) (Fin n) k) := insert s (Z : Set (Matrix (Fin n) (Fin n) k)) with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (rfl | ha) b (rfl | hb)
    · rfl
    · exact (hs b hb).symm
    · exact hs a ha
    · exact hc a ha b hb
  have hSc : S ⊆ Subalgebra.centralizer k S := fun a ha =>
    (Subalgebra.mem_centralizer_iff k).mpr fun g hg => hS g hg a ha
  have hcomm : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ Subalgebra.centralizer k S := Algebra.adjoin_le hSc ha
    have hb' : b ∈ Subalgebra.centralizer k (Subalgebra.centralizer k S : Set (Matrix (Fin n) (Fin n) k)) :=
      Algebra.adjoin_le_centralizer_centralizer k S hb
    exact (Subalgebra.mem_centralizer_iff k).mp hb' a ha'
  have hsemi : ∀ x ∈ adj Z s, Module.End.IsSemisimple (Matrix.toLin' x) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hss
      · exact AdjPf.isSemisimple_of_mem Z hr x hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]
      exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
    | add x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [map_add (f := _)]
      exact Module.End.IsSemisimple.add_of_commute hcm ihx ihy
    | mul x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [Matrix.toLin'_mul, ← Module.End.mul_eq_comp]
      exact Module.End.IsSemisimple.mul_of_commute hcm ihx ihy
  refine ⟨⟨hcomm, ?_⟩, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    have hxs := hsemi x.1 x.2
    have hn : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k)) := by
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      have hm' : (x : Matrix (Fin n) (Fin n) k) ^ m = 0 := by
        rw [← Subalgebra.coe_pow, hm, Subalgebra.coe_zero]
      have h5 := congrArg (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) hm'
      rw [map_pow, map_zero] at h5
      exact h5
    have h6 := Module.End.eq_zero_of_isNilpotent_isSemisimple hn hxs
    exact Subtype.ext ((Matrix.toLin'.map_eq_zero_iff).mp h6)
  · have hsub : (Z : Set (Matrix (Fin n) (Fin n) k)) ⊆ (adj Z s : Set (Matrix (Fin n) (Fin n) k)) :=
      fun z hz => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
    have hle := Subalgebra.centralizer_le k _ _ hsub
    have hne : Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k)) ≠
        Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      intro h
      apply hsZ
      apply AdjPf.dc Z hc hr s
      intro y hy
      rw [← h] at hy
      exact (Subalgebra.mem_centralizer_iff k).mp hy s (Algebra.subset_adjoin (Set.mem_insert _ _))
    have hlt : Subalgebra.toSubmodule (Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k))) <
        Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
      lt_of_le_of_ne (Subalgebra.toSubmodule.monotone hle)
        (fun h => hne (Subalgebra.toSubmodule_injective h))
    exact Submodule.finrank_lt_finrank_of_lt hlt

end PositivityTheory.RgUd.T
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.DescFinal
namespace PositivityTheory.RgUd.T.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sliceVan [CharZero k] : SliceVan (k := k) :=
  SLF.sliceVan_of_frob' PositivityTheory.PfBern.Frob.frobeniusReciprocity SLF.Un2.unimod

theorem descA [CharZero k] : DescA (k := k) := Asm.descA_of JC.jcPoly (sliceVan k)

end PositivityTheory.RgUd.T.Desc.Final
end

namespace PositivityTheory.RgUd.T.Final

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dich [CharZero k] : Dich (k := k) := PositivityTheory.RgUd.T.Alg.dich k
theorem adjP [CharZero k] : Adj (k := k) := adjunction_char_zero k
theorem locStep : LocStep (k := k) := LocStepPf.local_descent_holds
theorem descA [CharZero k] : DescA (k := k) := PositivityTheory.RgUd.T.Desc.Final.descA k
theorem nilpB [CharZero k] : NilpB (k := k) := PositivityTheory.RgUd.T.Nil.Final.nilpB k

theorem van_all [CharZero k] : ∀ (m n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)),
    Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) = m → CR Z → Van Z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n Z hm hZ
    refine nilpB k n Z hZ fun ξ hs hi => locStep k n Z hZ ξ hs hi fun y => ?_
    rcases dich k n Z hZ y with h | ⟨s, hs, hsZ, hss, hy⟩
    · exact Or.inl h
    · obtain ⟨hC, hlt⟩ := adjP k n Z hZ s hs hsZ hss
      exact Or.inr fun ξ' h1 h2 => descA k n Z hZ s hs hsZ hss (ih _ (hm ▸ hlt) n _ rfl hC) y hy ξ' h1 h2

theorem thmT [CharZero k] : PositivityTheory.RgUd.ThmT k := by
  intro n Z hcomm hred ξ hsupp hinv f hf
  exact van_all k _ n Z rfl ⟨hcomm, hred⟩ ξ (fun g hg h0 => hsupp g hg fun p hp => h0 p ⟨hp, Set.mem_univ _⟩)
    (fun g hg f hf => hinv g hg f hf) f hf

end PositivityTheory.RgUd.T.Final
