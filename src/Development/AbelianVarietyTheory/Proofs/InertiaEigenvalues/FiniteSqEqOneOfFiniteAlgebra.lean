module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra
namespace GlobalTheory

theorem finite_sq_eq_one_of_finite_algebra (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Finite (TopologicalSpace.Clopens (PrimeSpectrum A)) :=
    Finite.of_injective (fun s : TopologicalSpace.Clopens (PrimeSpectrum A) => (s : Set (PrimeSpectrum A)))
      SetLike.coe_injective
  haveI : Finite {e : A // IsIdempotentElem e} :=
    Finite.of_equiv _ (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).symm.toEquiv
  set c : A := algebraMap k A (2⁻¹ : k) with hc
  have hc2 : c * 2 = 1 := by
    rw [hc, (map_ofNat (algebraMap k A) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : k) ≠ 0), map_one]
  have hmap : ∀ x : A, x ^ 2 = 1 → IsIdempotentElem (c * (1 + x)) := by
    intro x hx
    unfold IsIdempotentElem
    have : (c * (1 + x)) * (c * (1 + x)) = c * (c * 2) * (1 + x) := by
      linear_combination (c * c) * hx
    rw [this, hc2, mul_one]
  have hinj : Set.InjOn (fun x : A => c * (1 + x)) {x : A | x ^ 2 = 1} := by
    intro x _ y _ hxy
    have h : (2 : A) * (c * (1 + x)) = 2 * (c * (1 + y)) := by simp only at hxy; rw [hxy]
    have e : ∀ z : A, (2 : A) * (c * (1 + z)) = 1 + z := fun z => by
      rw [← mul_assoc, mul_comm (2 : A) c, hc2, one_mul]
    rw [e, e] at h
    exact add_left_cancel h
  have hfin : Set.Finite {e : A | IsIdempotentElem e} :=
    Set.finite_coe_iff.mp (‹Finite {e : A // IsIdempotentElem e}› :)
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨x, hx, rfl⟩; exact hmap x hx)) hinj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebraStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneLe
namespace GlobalTheory.CloseToUnitNorm

theorem norm_eq_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (1 - u)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  have hu : ‖u‖ = 1 := norm_eq_one_of_close u h
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u hu n
  · rw [zpow_neg, zpow_natCast]
    have hn : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e : (u ^ n)⁻¹ - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      field_simp
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hu, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u hu n

end GlobalTheory.CloseToUnitNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDenNotMemOfCountEqZero
open IsDedekindDomain

namespace GlobalTheory

theorem exists_den_not_mem_of_count_eq_zero {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : FractionalIdeal.count K P I = 0)
    {a : K} (ha : a ∈ I) :
    ∃ b c : R, c ∉ P.asIdeal ∧ algebraMap R K c * a = algebraMap R K b := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp [ha0]⟩
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ I :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  have hne : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0
  have hc : 0 ≤ FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) a) :=
    hI ▸ FractionalIdeal.count_mono K P hne hle
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap R K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha0
  have hcoe : ∀ r : R, r ≠ 0 → FractionalIdeal.count K P
      (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r)) =
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P]
    simpa using hr
  have hmul : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x / algebraMap R K y)
      * FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K y) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hyK]
  have hcnt := congrArg (FractionalIdeal.count K P) hmul
  rw [FractionalIdeal.count_mul K P hne (FractionalIdeal.spanSingleton_ne_zero_iff.2 hyK),
    hcoe x hx0, hcoe y hy0] at hcnt
  have hval : P.valuation K (algebraMap R K x / algebraMap R K y) ≤ 1 := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ hx0,
      HeightOneSpectrum.intValuation_if_neg _ hy0, div_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero),
      WithZero.exp_le_exp]
    omega
  have hmem : algebraMap R K x / algebraMap R K y ∈ P.valuationSubringAtPrime K := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hval
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj P.asIdeal.primeCompl
    (⟨_, hmem⟩ : P.valuationSubringAtPrime K)
  refine ⟨b, c, c.2, ?_⟩
  have := congrArg (algebraMap (P.valuationSubringAtPrime K) K) hbc
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  rw [mul_comm]; exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatrices
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

theorem finite_classes_mod_pow (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
    (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (N : ℕ) :
    ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K),
      ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O),
        algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) →
        ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
          x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  classical
  have hfin : Finite (O ⧸ Ideal.span {ϖ ^ (2 * N)}) :=
    IsLocalRing.finite_quotient_iff.mpr
      ⟨2 * N, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  haveI := Fintype.ofFinite (Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}))
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  let lift : O ⧸ Ideal.span {ϖ ^ (2 * N)} → O := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, Ideal.Quotient.mk _ (lift c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  let rep : Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}) →
      Matrix (Fin r ⊕ Fin t) (Fin r) K :=
    fun c => (algebraMap O K (ϖ ^ N))⁻¹ • (c.map lift).map (algebraMap O K)
  refine ⟨Finset.univ.image rep, fun x z hxz => ?_⟩
  have hdiff : ∀ i j, ∃ a : O, a * ϖ ^ (2 * N) = z i j - lift (Ideal.Quotient.mk _ (z i j)) :=
    fun i j => Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp (hlift _).symm)
  choose w hw using hdiff
  refine ⟨rep (z.map (Ideal.Quotient.mk _)), Finset.mem_image_of_mem _ (Finset.mem_univ _), Matrix.of w, ?_⟩
  ext i j
  have hx := congrFun (congrFun hxz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_pow] at hx
  have hz : lift (Ideal.Quotient.mk _ (z i j)) = z i j - w i j * ϖ ^ (2 * N) := by
    rw [hw]; ring
  simp only [rep, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hz, map_sub,
    map_mul, map_pow, Matrix.of_apply, ← hx]
  field_simp
  ring

end GlobalTheory.GenUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatricesStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ N : ℕ, ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K), ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) → ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.GenUnr.finite_classes_mod_pow | exact GlobalTheory.GenUnr.finite_classes_mod_pow | (intros; apply GlobalTheory.GenUnr.finite_classes_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMem
namespace GlobalTheory

private theorem isClosed_submodule_padicInt_finite (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N]
    [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] [TopologicalSpace N] [IsModuleTopology ℤ_[l] N]
    (M : Submodule ℤ_[l] N) : IsClosed (M : Set N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hq := IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ
  rw [← hq.isClosed_preimage]
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[l] (M.comap π)
  have hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) :=
    IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)
  have hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hy
      obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
  rw [← hrange]
  exact (isCompact_range hc).isClosed

theorem exists_idempotent_sub_mem_of_pow_sub_mem (l : ℕ) [Fact l.Prime] {R : Type} [Ring R]
    [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R) :
    ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R),
      (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  letI : TopologicalSpace R := moduleTopology ℤ_[l] R
  haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R
  have hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R) := fun M => isClosed_submodule_padicInt_finite l M
  haveI : T2Space R := by
    rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
    simpa using hcl ⊥
  haveI : CompactSpace R := by
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] R
    have hc : Continuous π := IsModuleTopology.continuous_of_linearMap π
    exact ⟨by simpa [hπ.range_eq] using isCompact_range hc⟩
  obtain ⟨E, hES, hE⟩ := exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_const r)
    (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩
    isClosed_closure.isCompact (by
      intro x hx y hy
      refine map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      refine ⟨i + j + 1, ?_⟩
      show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)
      rw [← pow_add]
      congr 1
      omega)
  refine ⟨E, hE, fun M c h => ?_⟩
  have hC : IsClosed {x : R | x - c ∈ M} := (hcl M).preimage (continuous_id.sub continuous_const)
  exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslate
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem invariant_const_on_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ hΦ x g z hx
  classical
  set z₁ : Matrix (Fin r) (Fin r) O := Matrix.toRows₁ z
  set z₂ : Matrix (Fin t) (Fin r) O := Matrix.toRows₂ z
  set M : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O :=
    Matrix.fromBlocks (1 + ϖ • z₁) 0 (ϖ • z₂) 1 with hMdef
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hres : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).2 hmem
  have hdet : IsUnit M.det := by
    rw [hMdef, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
      ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have h1 : (IsLocalRing.residue O).mapMatrix (1 + ϖ • z₁) = 1 := by
      ext i j
      simp [Matrix.one_apply, hres]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  let h : GL (Fin r ⊕ Fin t) O := M.nonsingInvUnit hdet
  have hh : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) = M := rfl
  set e : Matrix (Fin r ⊕ Fin t) (Fin r) O :=
    Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) with hedef
  have key : M * e = e + ϖ • z := by
    ext (a | a) b <;>
      simp [hMdef, hedef, z₁, z₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.toRows₁, Matrix.toRows₂, Matrix.one_apply, add_mul, Sum.elim_inl,
        Sum.elim_inr, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h1 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) -
      (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, add_sub_cancel_left,
      Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have h2 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈
      Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hinv := hΦ h h1 h2 (e.map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
  rw [← hinv, hh, ← Matrix.mul_assoc, ← Matrix.map_mul, key, ← hx, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslateStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceInvariant_const_on_frame_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  first | exact @GlobalTheory.invariant_const_on_translate | exact GlobalTheory.invariant_const_on_translate | (intros; apply GlobalTheory.invariant_const_on_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPowPrimeOrderEmbeddingsDifferByCoprimePower
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charPowPrimeOrder_embeddings_differ_by_coprime_power :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) C)
  set u : Cˣ := (ζ : Cˣ) with hu
  have hul : u ^ (l ^ n) = 1 := (mem_rootsOfUnity _ _).mp ζ.2
  set k := orderOf u with hk
  have hkd : k ∣ l ^ n := orderOf_dvd_of_pow_eq_one hul
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hkd; exact (NeZero.ne (l ^ n)) (Nat.eq_zero_of_zero_dvd hkd))
  haveI : NeZero k := ⟨hk0.ne'⟩
  have hpu : IsPrimitiveRoot (u : C) k := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)
  have h1 : IsPrimitiveRoot (e (u : C)) k := hpu.map_of_injective e.injective
  have h2 : IsPrimitiveRoot (e' (u : C)) k := hpu.map_of_injective e'.injective
  obtain ⟨i, hik, hi⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hic : i.Coprime k := (h1.pow_iff_coprime hk0 i).mp (by rw [hi]; exact h2)
  refine ⟨i + k, ?_, ?_⟩
  · have hc : (i + k).Coprime k := by simpa using hic
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).mp hkd
    rcases m with _ | m
    · simp at hm
      have : i = 0 := by omega
      subst this
      rw [hm] at hdvd
      exact hl.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))
    · have hlk : l ∣ k := by rw [hm]; exact dvd_pow_self l (Nat.succ_ne_zero m)
      have := Nat.Coprime.coprime_dvd_left hdvd hc
      have := Nat.Coprime.coprime_dvd_right hlk this
      exact hl.one_lt.ne' (by simpa using this)
  · have hEu : e' (u : C) = e (u : C) ^ (i + k) := by
      rw [pow_add, hi, h1.pow_eq_one, mul_one]
    let E : Cˣ →* ℂˣ := Units.map (e : C →* ℂ)
    let E' : Cˣ →* ℂˣ := Units.map (e' : C →* ℂ)
    have hEu' : E' u = E u ^ (i + k) := by
      ext; simp [E, E', hEu]
    intro g
    have hmem : ψ g ∈ rootsOfUnity (l ^ n) C := (mem_rootsOfUnity _ _).mpr (hψ g)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨ψ g, hmem⟩)
    have hj' : u ^ j = ψ g := by
      have := congrArg Subtype.val hj
      simpa [hu] using this
    have key : E' (ψ g) = E (ψ g ^ (i + k)) := by
      rw [← hj', map_zpow, map_pow, map_zpow, hEu', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    have := congrArg Units.val key
    simpa [E, E'] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMem
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem card_quotient_eq_of_pow_sub_self_mem : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  intro R _ P _ q ζ hq hζ hprim hall
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hfix : ∀ x : R ⧸ P, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hall y
  set f : Polynomial (R ⧸ P) := X ^ q - X with hf
  have hdeg : f.natDegree = q := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, mem_roots hf0]
    simp [hf, hfix x]
  haveI : Finite (R ⧸ P) := by
    apply Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))
    intro a b h; simpa using congrArg Subtype.val h
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card (R ⧸ P) = (Finset.univ : Finset (R ⧸ P)).card := rfl
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (fun x _ => hmem x)
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  · set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz
    have hz1 : z ^ (q - 1) = 1 := by rw [hz, ← map_pow, hζ, map_one]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1
    have hord : orderOf z = q - 1 := by
      rw [orderOf_eq_iff (by omega)]
      refine ⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]
    have hinj := pow_injOn_Iio_orderOf (x := z)
    rw [hord] at hinj
    let g : Fin q → R ⧸ P := fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      apply Fin.ext
      by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab
      · omega
      · exact absurd hab.symm (pow_ne_zero _ hz0)
      · exact absurd hab (pow_ne_zero _ hz0)
      · have := hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega)
          (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab
        omega
    have := Nat.card_le_card_of_injective g hg
    simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
open Polynomial IsLocalRing

namespace GlobalTheory

theorem monic_dvd_X_pow_card_sub_one_exists_root :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by
  intro S _ _ _ f hmon hdeg hdvd
  classical
  letI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ : Nat.card (ResidueField S) = Fintype.card (ResidueField S) := Nat.card_eq_fintype_card
  set Q := Fintype.card (ResidueField S) with hQdef
  set g : (ResidueField S)[X] := f.map (residue S) with hgdef
  have hgm : g.Monic := hmon.map _
  have hgdeg : g.natDegree ≠ 0 := by rw [hgdef, hmon.natDegree_map]; exact hdeg
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hdvd' : g ∣ X ^ Q - X := by
    have h1 : g ∣ X ^ (Q - 1) - 1 := by
      have := Polynomial.map_dvd (residue S) hdvd
      simpa [hQ, g] using this
    have : (X ^ Q - X : (ResidueField S)[X]) = X * (X ^ (Q - 1) - 1) := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by omega]
      ring
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  have hne : (X ^ Q - X : (ResidueField S)[X]) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero hQ1
  have hsplit : Splits (X ^ Q - X : (ResidueField S)[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      Polynomial.natDegree_X_pow_sub_X (R := (ResidueField S)) hQ1]
    simp [Q]
  have hgs : Splits g := hsplit.of_dvd hne hdvd'
  obtain ⟨abar, habar⟩ := hgs.exists_eval_eq_zero
    (by rw [degree_eq_natDegree hgm.ne_zero]; exact_mod_cast hgdeg)
  have hchar : ringChar (ResidueField S) ∣ Q := by
    apply (ringChar.spec (ResidueField S) Q).mp
    exact FiniteField.cast_card_eq_zero (ResidueField S)
  have hsep : (X ^ Q - X : (ResidueField S)[X]).Separable :=
    galois_poly_separable (ringChar (ResidueField S)) Q hchar
  have hgsep := hsep.of_dvd hdvd'
  have hder : eval abar (derivative g) ≠ 0 := by
    have := hgsep.aeval_derivative_ne_zero (S := ResidueField S) (x := abar)
      (by simpa [aeval_def] using habar)
    simpa [aeval_def] using this
  obtain ⟨a, rfl⟩ := residue_surjective abar
  have key : ∀ p : S[X], residue S (p.eval a) = (p.map (residue S)).eval (residue S a) := by
    intro p; rw [eval_map, eval₂_hom]
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hmon a
    (by rw [← residue_eq_zero_iff, key]; exact habar)
    (by
      rw [← residue_ne_zero_iff_isUnit, key, ← derivative_map]
      exact hder)
  exact ⟨y, hy⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRootStatement
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]), f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 → ∃ y : S, f.eval y = 0 := by
  first | exact @GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | exact GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | (intros; apply GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLe
open TensorProduct

namespace GlobalTheory

theorem exists_span_eq_top_of_card_hom_residueField_le
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  set k := IsLocalRing.ResidueField Λ
  let V := k ⊗[Λ] A
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V

  have hsurj : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)

  have hspan : Submodule.span Λ (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b (fun i => hf i)

  let Φ : (V →ₗ[k] k) → (A →ₗ[Λ] k) := fun g =>
    (g.restrictScalars Λ).comp (TensorProduct.mk Λ k A 1)
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    have h' := LinearMap.congr_fun h y
    simp only [Φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply] at h'
    have e : x ⊗ₜ[Λ] y = x • ((1 : k) ⊗ₜ[Λ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul]
    exact congrArg (x • ·) h'

  have : Finite (A →ₗ[Λ] k) := by
    refine Finite.of_injective (fun g : A →ₗ[Λ] k => fun i => g (f i)) ?_
    intro g₁ g₂ h
    exact LinearMap.ext_on_range hspan (fun i => congr_fun h i)
  have hcard : Nat.card (V →ₗ[k] k) = Nat.card k ^ d := by
    rw [← Nat.card_congr (b.constr k).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
      Fintype.card_fin]
  have hle : Nat.card k ^ d ≤ Nat.card k ^ a := by
    rw [← hcard]; exact (Nat.card_le_card_of_injective Φ hΦ).trans h
  have hk : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hda : d ≤ a := (Nat.pow_le_pow_iff_right hk).mp hle

  refine ⟨fun i => if hi : (i : ℕ) < d then f ⟨i, hi⟩ else 0, ?_⟩
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hda⟩, by simp⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_of_card_hom_residueField_le : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  first | exact @GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | exact GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | (intros; apply GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingIdempotentTensor
open TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_embedding_idempotent_tensor (F K L : Type) [Field F] [CharZero F] [Field K]
    [Field L] [Algebra F K] [Algebra F L] [FiniteDimensional F K] (τ : K →ₐ[F] L) :
    ∃ (m : ℕ) (c : Fin m → L) (k : Fin m → K), ∑ j, c j * τ (k j) = 1 ∧
      ∀ y : K, ∑ j, c j ⊗ₜ[F] (y * k j) = ∑ j, (τ y * c j) ⊗ₜ[F] k j := by
  classical
  have hB : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  have hsymm : (Algebra.traceForm F K).IsSymm := Algebra.traceForm_isSymm F
  let b := Module.finBasis F K
  let d := (Algebra.traceForm F K).dualBasis hB b
  have hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j
  set s : K := ∑ j, b j * d j with hs
  have hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x := by
    intro x
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hbd]
  have hs0 : s ≠ 0 := by
    intro h
    have htr : Algebra.trace F K s = (Module.finrank F K : F) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, map_sum]
      simp [hbd]
    rw [h, map_zero] at htr
    exact (Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp htr.symm)
  refine ⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩
  · calc ∑ j, τ (s⁻¹ * b j) * τ (d j) = τ (s⁻¹ * s) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]
      _ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]
  · have lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) =
        ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← hd (y * d j)]
      rw [TensorProduct.tmul_sum]
      simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i =
        ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, mul_left_comm]
      conv_lhs => rw [← hb (y * b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.mul_sum, map_sum, TensorProduct.sum_tmul]
      simp_rw [mul_smul_comm, map_smul]
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_right_comm y (d j) (b i)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
namespace GlobalTheory

theorem finite_quotient_of_complete_nakayama : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  intro R _ ϖ hR T Z _ _ _ _ hT hZ d N hdN s hs
  classical
  choose A C X hACX using hs
  choose limR hlimR using hR
  choose limT hlimT using hT
  have key : ∀ c : Z, ∀ n : ℕ, c = ∑ i ∈ s, (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) • i
      + ϖ ^ n • C^[n] c + d (∑ j ∈ Finset.range n, ϖ ^ j • X (C^[j] c)) := by
    intro c n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      simp only [Finset.sum_range_succ]
      set e := C^[n] c with he
      conv_lhs => rw [hACX e]
      simp only [add_smul, Finset.sum_add_distrib, smul_add, map_add (f := _), map_smul, Finset.smul_sum,
        mul_smul, pow_succ]
      abel
  have hfin : ∀ c : Z, c - (∑ i ∈ s, limR (fun j => A (C^[j] c) i) • i
      + d (limT (fun j => X (C^[j] c)))) = 0 := by
    intro c
    apply hZ
    intro n
    have hk := key c n
    choose b hb using fun i => hlimR (fun j => A (C^[j] c) i) n
    obtain ⟨z, hz⟩ := hlimT (fun j => X (C^[j] c)) n
    refine ⟨C^[n] c - ∑ i ∈ s, b i • i - d z, ?_⟩
    have hα : ∀ i, limR (fun j => A (C^[j] c) i)
        = (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) + ϖ ^ n * b i :=
      fun i => sub_eq_iff_eq_add'.mp (hb i)
    have hY := sub_eq_iff_eq_add'.mp hz
    simp only [hα, hY]
    rw [sub_eq_iff_eq_add]
    refine hk.trans ?_
    simp only [add_smul, Finset.sum_add_distrib, smul_sub, map_add (f := _), map_smul, Finset.smul_sum,
      mul_smul]
    abel
  have h0 : ∀ y : T, N.mkQ (d y) = 0 := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdN ⟨y, rfl⟩
  refine ⟨⟨s.image N.mkQ, ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨c, rfl⟩ := N.mkQ_surjective q
  have hc := sub_eq_zero.mp (hfin c)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_add (f := _), h0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayamaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  first | exact @GlobalTheory.finite_quotient_of_complete_nakayama | exact GlobalTheory.finite_quotient_of_complete_nakayama | (intros; apply GlobalTheory.finite_quotient_of_complete_nakayama <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
open IsLocalRing Matrix

namespace GlobalTheory.BurnsideMonoid

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isIrreducible {G K V : Type} [Monoid G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_matrix_eq_top_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Monoid Γ] (σ : Γ →* Matrix ι ι K)
    (h : ∀ W : Submodule K (ι → K), (∀ g, ∀ w ∈ W, σ g *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Submodule.span K (Set.range σ) = ⊤ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
  let τ : Representation K Γ (ι → K) :=
    { toFun := fun g => Matrix.toLin' (σ g)
      map_one' := by simp; rfl
      map_mul' := fun g g' => by simp [Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => ?_⟩
      have h1 : (⊥ : Submodule K (ι → K)) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
      exact bot_ne_top h1
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isIrreducible τ hirr
  have hm : Set.range σ =
      (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

end GlobalTheory.BurnsideMonoid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
namespace GlobalTheory.CommuteInvLeft

theorem commute_inv_left : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  have h' : x * y = y * x := h
  show xi * y = y * xi
  calc xi * y = xi * y * (x * xi) := by rw [h1, mul_one]
    _ = xi * (y * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * y) * xi := by rw [h']
    _ = (xi * x) * y * xi := by simp only [mul_assoc]
    _ = y * xi := by rw [h2, one_mul]

end GlobalTheory.CommuteInvLeft
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddMulInvMem
universe u_1

namespace GlobalTheory.AddMulInvMembership

theorem add_mul_inv_mem :
    (let d1 : {K : Type u_1} → [inst : Field K] → Subring K → K → K → Prop :=
      @(fun {K : Type u_1} [Field K] (S : Subring K) (π a : K) ↦ a * π⁻¹ ∈ S);
    ∀ {K : Type u_1} [inst : Field K] [StarRing K] {S : Subring K} {π a b : K},
      d1 S π a → d1 S π b → d1 S π (a + b)) := by
  intro d1 K _ _ S π a b ha hb
  show (a + b) * π⁻¹ ∈ S
  rw [add_mul]
  exact S.add_mem ha hb

end GlobalTheory.AddMulInvMembership
end
