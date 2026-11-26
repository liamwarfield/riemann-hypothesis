module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.UnramSimpleGen

theorem not_mem_sq_of_derivative : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  intro E E' _ _ _ _ _ p P β f _ hβ hadj hPp hder c hc

  have hmem := aeval_derivative_mem_differentIdeal (𝓞 E) E E' β hadj
  have hint : IsIntegral (𝓞 E) β := Algebra.IsIntegral.isIntegral β
  have hdvd : minpoly (𝓞 E) β ∣ f.map (algebraMap ℤ (𝓞 E)) :=
    minpoly.isIntegrallyClosed_dvd hint (by rw [aeval_map_algebraMap]; exact hβ)
  obtain ⟨k, hk⟩ := hdvd
  have hfd : aeval β (derivative f) = aeval β (derivative (minpoly (𝓞 E) β)) * aeval β k := by
    have h := congrArg (fun q => aeval β (derivative q)) hk
    simp only [derivative_mul, map_add (f := _), map_mul, minpoly.aeval, zero_mul, add_zero] at h
    rw [← h, derivative_map, aeval_map_algebraMap]
  have hnd : ¬ P.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 E') := by
    intro h
    apply hder
    rw [hfd]
    exact Ideal.mul_mem_right _ _ ((Ideal.dvd_iff_le.1 h) hmem)

  haveI := p.isMaximal
  have hnle : ¬ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) ≤ P.asIdeal ^ 2 := by
    intro hle
    have h := pow_sub_one_dvd_differentIdeal (𝓞 E) (p := p.asIdeal) P.asIdeal 2 p.ne_bot
      (Ideal.dvd_iff_le.2 hle)
    exact hnd (by simpa using h)

  by_cases hcp : c ∈ p.asIdeal
  swap
  · intro h
    exact hcp ((hPp c).1 (Ideal.pow_le_self two_ne_zero h))

  obtain ⟨J, hJ⟩ : p.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hcp)
  have hJp : ¬ J ≤ p.asIdeal := by
    intro h
    apply hc
    have h1 : Ideal.span {c} ≤ p.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h1 (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := Set.not_subset.1 hJp
  have hps : p.asIdeal * Ideal.span {s} ≤ Ideal.span {c} := by
    rw [hJ]; exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hsJ)
  intro hcP
  apply hnle
  have hs' : algebraMap (𝓞 E) (𝓞 E') s ∉ P.asIdeal := fun h => hsp ((hPp s).1 h)
  have hcop : IsCoprime P.asIdeal (Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine P.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hs' ?_)
    rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hdiv : P.asIdeal ^ 2 ∣ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) *
      Ideal.span {algebraMap (𝓞 E) (𝓞 E') s} := by
    rw [Ideal.dvd_iff_le]
    calc p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) * Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}
        = (p.asIdeal * Ideal.span {s}).map (algebraMap (𝓞 E) (𝓞 E')) := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
      _ ≤ (Ideal.span {c}).map (algebraMap (𝓞 E) (𝓞 E')) := Ideal.map_mono hps
      _ = Ideal.span {algebraMap (𝓞 E) (𝓞 E') c} := by rw [Ideal.map_span, Set.image_singleton]
      _ ≤ P.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).2 hcP
  exact Ideal.dvd_iff_le.1 ((hcop.pow_left).dvd_of_dvd_mul_right hdiv)

end GlobalTheory.UnramSimpleGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivativeStatement
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | exact GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | (intros; apply GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubset
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
namespace GlobalTheory.ParahoricTranslate

theorem isUnit_det_one_add_nonunit_smul {O : Type} [CommRing O] [IsLocalRing O] {r : ℕ} (ϖ : O)
    (hϖ : ¬ IsUnit ϖ) (Z : Matrix (Fin r) (Fin r) O) :
    IsUnit (1 + ϖ • Z).det := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  set f := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have h0 : f (1 + ϖ • Z).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hf : f ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ))
  have h1 : f.mapMatrix (1 + ϖ • Z) = 1 := by
    rw [map_add (f := _), map_one]
    ext i j
    simp [hf]
  rw [RingHom.map_det, h1, Matrix.det_one] at h0
  exact one_ne_zero h0

theorem toRows_left_mul_matrix_eq {K : Type} [CommRing K] {r t : ℕ}
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : Matrix (Fin r) (Fin r) K) :
    Matrix.toRows₁ (x * g) = Matrix.toRows₁ x * g := by
  ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hirr x g g' z z' hx hx' y w hy
  set φ := algebraMap O K
  set e := Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)
  set Z := Matrix.toRows₁ z
  set Z' := Matrix.toRows₁ z'
  set P : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z
  set P' : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z'
  set A := Matrix.toRows₁ x
  have hP : IsUnit P.det := isUnit_det_one_add_nonunit_smul ϖ hirr.not_isUnit Z
  have hA : A * (g : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P := by
    have := congrArg Matrix.toRows₁ hx
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z)).map φ = (1 + ϖ • Z).map φ
    congr 1
  have hA' : A * (g' : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P' := by
    have := congrArg Matrix.toRows₁ hx'
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z')).map φ = (1 + ϖ • Z').map φ
    congr 1
  have hPK : IsUnit (φ.mapMatrix P).det := by
    rw [← RingHom.map_det]; exact hP.map φ
  have hAu : IsUnit A.det := by
    rw [← hA, Matrix.det_mul] at hPK
    exact isUnit_of_mul_isUnit_left hPK
  set c : Matrix (Fin r) (Fin r) O := P⁻¹ * P'
  have hgc : (g' : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c := by
    have h2 : A * (g' : Matrix (Fin r) (Fin r) K) = A * ((g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c) := by
      rw [hA', ← Matrix.mul_assoc, hA, map_mul, ← Matrix.mul_assoc, ← map_mul,
        Matrix.mul_nonsing_inv _ hP, map_one, Matrix.one_mul]
    have h3 := congrArg (fun M => A⁻¹ * M) h2
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hAu] using h3
  refine ⟨Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c, ?_⟩
  have hc : c = 1 + ϖ • (P⁻¹ * (Z' - Z)) := by
    have : P' = P + ϖ • (Z' - Z) := by
      simp only [P, P', smul_sub]; abel
    simp only [c, this, Matrix.mul_add, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hP]
  have key : (e + ϖ • w) * c = e + ϖ • (Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c) := by
    rw [Matrix.add_mul, Matrix.smul_mul]
    have he : e * c = Matrix.fromRows c (0 : Matrix (Fin t) (Fin r) O) := by
      simp [e, Matrix.fromRows_mul]
    rw [he]
    nth_rewrite 1 [hc]
    ext (i | i) j <;> simp [e, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, smul_add, add_assoc]
  rw [hgc, ← Matrix.mul_assoc, hy, RingHom.mapMatrix_apply, ← Matrix.map_mul, key]

end GlobalTheory.ParahoricTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubsetStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  first | exact @GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | exact GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset | (intros; apply GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrime
open Polynomial

namespace GlobalTheory

theorem padicComplex_norm_prime (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    PadicAlgCl.norm_extends, Padic.norm_p]

theorem lift_hasSum_zero : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  intro l _ X ι η τ S hS x hx hxb
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := padicComplex_norm_prime l
  have hp : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; positivity
  have hllt : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hp
  have hl0 : (l : ℂ_[l]) ≠ 0 := norm_pos_iff.mp hlpos
  let T := {t : ι → ℂ_[l] // ∀ i, ‖t i‖ ≤ τ i}
  have hg : ∀ t : T, ∃ y ∈ S, ∀ i, ‖η y i + t.1 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t
    obtain ⟨y, hyS, hy⟩ := hS (-t.1) (fun i => by simpa using t.2 i)
    exact ⟨y, hyS, fun i => by simpa [sub_eq_add_neg] using hy i⟩
  choose g hgS hgb using hg
  have hdiv : ∀ z : ℂ_[l], ∀ i, ‖z‖ ≤ ‖(l : ℂ_[l])‖ * τ i → ‖z / l‖ ≤ τ i := by
    intro z i hz
    rw [norm_div, div_le_iff₀ hlpos]; linarith [mul_comm (‖(l : ℂ_[l])‖) (τ i)]
  let step : T → T := fun t => ⟨fun i => (t.1 i + η (g t) i) / l,
    fun i => hdiv _ i (by rw [add_comm]; exact hgb t i)⟩
  let t0 : T := ⟨fun i => η x i / l, fun i => hdiv _ i (hxb i)⟩
  let ts : ℕ → T := fun k => step^[k] t0
  let y : ℕ → X := fun k => Nat.casesOn k x (fun k => g (ts k))
  have hy0 : y 0 = x := rfl
  have hysucc : ∀ k, y (k+1) = g (ts k) := fun k => rfl
  have htsucc : ∀ k, ts (k+1) = step (ts k) := fun k => Function.iterate_succ_apply' step k t0
  refine ⟨y, hy0, ?_, ?_⟩
  · intro k; cases k with
    | zero => exact hx
    | succ k => exact hgS _
  intro i

  have hinv : ∀ k, ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i = (l : ℂ_[l]) ^ (k+1) * (ts k).1 i := by
    intro k
    induction k with
    | zero => simp [hy0, ts, t0]; field_simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hysucc, htsucc]
      simp only [step]
      field_simp
      ring

  have hτ : ∀ k, 0 ≤ τ i := fun k => le_trans (norm_nonneg _) ((ts k).2 i)
  have hbd : ∀ k, ‖η (y k) i‖ ≤ τ i := by
    intro k; cases k with
    | zero => exact le_trans (hxb i) (by nlinarith [hτ 0])
    | succ k =>
      rw [hysucc]
      have h1 := hgb (ts k) i
      have h2 := (ts k).2 i
      have : η (g (ts k)) i = (η (g (ts k)) i + (ts k).1 i) - (ts k).1 i := by ring
      rw [this]
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (by rw [norm_neg]; exact h2))
      exact le_trans h1 (by nlinarith [hτ 0])
  have hterm : ∀ k, ‖(l : ℂ_[l]) ^ k * η (y k) i‖ ≤ τ i * ‖(l : ℂ_[l])‖ ^ k := by
    intro k; rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd k) (pow_nonneg (norm_nonneg _) _)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hllt).mul_left (τ i)) hterm
  rw [hsum.hasSum_iff_tendsto_nat]
  have hlim : Filter.Tendsto (fun k : ℕ => (l : ℂ_[l]) ^ (k+1) * (ts k).1 i) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (g := fun k : ℕ => ‖(l : ℂ_[l])‖ ^ (k+1) * τ i) ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left ((ts k).2 i) (pow_nonneg (norm_nonneg _) _)
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hllt).comp (Filter.tendsto_add_atTop_nat 1)
      simpa using this.mul_const (τ i)
  have hlim2 : Filter.Tendsto (fun k : ℕ => ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i) Filter.atTop (nhds 0) := by
    simpa only [hinv] using hlim
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrimeStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  first | exact @GlobalTheory.lift_hasSum_zero | exact GlobalTheory.lift_hasSum_zero | (intros; apply GlobalTheory.lift_hasSum_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCorestrictionCocycle
namespace GlobalTheory

open scoped BigOperators

theorem corCoc_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have := QuotientGroup.eq.mp h
  simpa [mul_assoc] using this

theorem exists_corestriction_cocycle : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → (∀ x, Continuous fun g => ρ g x) → ∀ f : G → X, ContinuousOn f H → (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + ρ g (f h)) → ∃ F : G → X, Continuous F ∧ (∀ g h, F (g * h) = F g + ρ g (F h)) ∧ (∃ x, ∀ h ∈ H, F h = (∑ᶠ q : G ⧸ H, ρ q.out (f (q.out⁻¹ * h * q.out))) + (ρ h x - x)) ∧ ∀ (Y : Submodule R X), (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → ∀ (f₀ : G → X) (x : X), (∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ Y) → (∀ h ∈ H, f h - f₀ h - (ρ h x - x) ∈ Y) → ∃ x', ∀ g, F g - H.index • f₀ g - (ρ g x' - x') ∈ Y := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x
    rw [map_mul]; rfl
  refine ⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)), ?_, ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun q _ => ?_
    rw [continuous_iff_continuousAt]
    intro g₀
    have hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out := by fun_prop
    have hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H :=
      hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))
    have h1 : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
      refine (hρ _).continuousAt.comp ?_
      exact ContinuousAt.comp (g := f) (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q)))
        hk.continuousAt
    refine h1.congr ?_
    filter_upwards [hn] with g hg
    have : g • q = g₀ • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)
    rw [this]
  · intro g h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply, mul_smul]
    have e : (g • h • q).out⁻¹ * (g * h) * q.out =
        ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out) := by group
    rw [e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add (f := _), hmul, hmul]
    congr 3
    group
  · refine ⟨0, fun h hh => ?_⟩
    rw [finsum_eq_sum_of_fintype]
    simp only [map_zero, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : h • q = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)
      refine QuotientGroup.eq.mpr ?_
      have := Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out
      simpa [mul_assoc] using this
    rw [this]
  · intro Y hY f₀ x h₀ hx
    refine ⟨∑ q : G ⧸ H, (f₀ q.out + ρ q.out x), fun g => ?_⟩
    have hidx : H.index • f₀ g = ∑ _q : G ⧸ H, f₀ g := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    have hre : ∑ q : G ⧸ H, (f₀ q.out + ρ q.out x) =
        ∑ q : G ⧸ H, (f₀ (g • q).out + ρ (g • q).out x) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f₀ q.out + ρ q.out x)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hidx, map_sum, hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Y.sum_mem fun q _ => ?_
    set s' := (g • q).out
    set s := q.out
    have e : s' * (s'⁻¹ * g * s) = g * s := by group
    have a1 := hY s' _ (hx _ (corCoc_mem H g q))
    have a2 := h₀ s' (s'⁻¹ * g * s)
    have a3 := h₀ g s
    rw [e] at a2
    change ρ s' (f (s'⁻¹ * g * s) - f₀ (s'⁻¹ * g * s) - (ρ (s'⁻¹ * g * s) x - x)) ∈ Y at a1
    rw [map_sub, map_sub, map_sub, hmul, e] at a1
    have := Y.add_mem (Y.sub_mem a1 a2) a3
    convert this using 1
    rw [map_add (f := _), hmul]
    abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
open MeasureTheory

namespace GlobalTheory

theorem norm_mul_cexp_le_of_abs_le_on_support {s : ℂ} {f t : ℝ} {R : ℝ} (hf : 0 ≤ f) (hR : f ≠ 0 → |t| ≤ R) :
    ‖(f : ℂ) * Complex.exp (s * t)‖ ≤ f * Real.exp (‖s‖ * R) := by
  by_cases h0 : f = 0
  · simp [h0]
  have ht := hR h0
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  apply Real.exp_le_exp.mpr
  have h1 : (s * (t : ℂ)).re = s.re * t := by simp
  rw [h1]
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ ‖s‖ * R := mul_le_mul (Complex.abs_re_le_norm s) ht (abs_nonneg _) (norm_nonneg _)

theorem exp_integral_entire_real_pos {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ)
    (hfm : Measurable f) (htm : Measurable t) (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f ν) (hR : ∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) :
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  obtain ⟨R, hR⟩ := hR
  have hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y) := by
    intro s; fun_prop
  have hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν := by
    intro s
    refine Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable
      (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))
  refine ⟨?_, ?_⟩
  · intro s₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
      (F := fun s y => (f y : ℂ) * Complex.exp (s * t y))
      (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y))
      (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R))
      (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s₀)
      (by fun_prop : Measurable fun y => (f y : ℂ) * (Complex.exp (s₀ * t y) * t y)).aestronglyMeasurable
      (ae_of_all _ fun y s hs => ?_)
      ((hfi.mul_const R).mul_const _)
      (ae_of_all _ fun y s _ => ?_)
    · exact key.2.differentiableAt
    · by_cases h0 : f y = 0
      · simp [h0]
      have ht := hR y h0
      have hR0 : 0 ≤ R := (abs_nonneg _).trans ht
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have e1 := norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(f y : ℂ) * Complex.exp (s * t y)‖ * |t y|
          ≤ (f y * Real.exp (‖s‖ * R)) * R := mul_le_mul e1 ht (abs_nonneg _) (mul_nonneg (hf0 y) (Real.exp_pos _).le)
        _ ≤ f y * R * Real.exp ((‖s₀‖ + 1) * R) := by
          have : Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)
          nlinarith [this]
    · have := ((hasDerivAt_id s).mul_const (t y : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul (f y : ℂ)
  · intro r
    have hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ) := by
      intro y; push_cast; ring_nf
    simp_rw [hre]
    rw [integral_complex_ofReal]
    refine ⟨Complex.ofReal_im _, fun hpos => ?_⟩
    rw [Complex.ofReal_re]
    have gint : Integrable (fun y => f y * Real.exp (r * t y)) ν := by
      have := hint (r : ℂ)
      simp_rw [hre] at this
      exact this.re
    have hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y) := by
      intro y
      by_cases h0 : f y = 0
      · simp [h0]
      apply mul_le_mul_of_nonneg_left _ (hf0 y)
      apply Real.exp_le_exp.mpr
      have ht := hR y h0
      have : |r * t y| ≤ |r| * R := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      linarith [neg_abs_le (r * t y)]
    calc 0 < (∫ y, f y ∂ν) * Real.exp (-(|r| * R)) := mul_pos hpos (Real.exp_pos _)
      _ = ∫ y, f y * Real.exp (-(|r| * R)) ∂ν := (integral_mul_const _ _).symm
      _ ≤ ∫ y, f y * Real.exp (r * t y) ∂ν := integral_mono (hfi.mul_const _) gint hle

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPosStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
namespace GlobalTheory

open Polynomial in
private lemma norm_le_one_of_monic_root_lemma {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : K[X]} (hp : p.Monic) (hc : ∀ i, ‖p.coeff i‖ ≤ 1) {x : K} (hx : p.eval x = 0) :
    ‖x‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [hp.as_sum] at hx
  simp only [eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum, eval_mul, eval_C] at hx
  set n := p.natDegree
  have hxn : x ^ n = -∑ i ∈ Finset.range n, p.coeff i * x ^ i := eq_neg_of_add_eq_zero_left hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hxn
    simp at hxn
  have hle : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by
    rw [hxn, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖p.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) := by
          gcongr
          · exact hc i
          · exact h.le
      _ = ‖x‖ ^ (n - 1) := one_mul _
  rw [norm_pow] at hle
  have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith


open Polynomial in
theorem _root_.GlobalTheory.padicAlgCl_embedding_bounded_continuous (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O))
    (ι : O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  set g : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hg : ι.comp (algebraMap ℤ_[l] O) = g := by
    ext z
    exact hι z
  have h1 : ∀ a, ‖ι a‖ ≤ 1 := by
    intro a
    obtain ⟨p, hpm, hpa⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a
    have hroot : (p.map g).eval (ι a) = 0 := by
      rw [eval_map, ← hg, ← hom_eval₂]
      rw [hpa, map_zero]
    refine norm_le_one_of_monic_root_lemma (hpm.map g) (fun i => ?_) hroot
    rw [coeff_map]
    change ‖algebraMap ℚ_[l] (PadicAlgCl l) ((p.coeff i : ℤ_[l]) : ℚ_[l])‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact PadicInt.norm_le_one _
  have hunit : ∀ u : Oˣ, ‖ι u‖ = 1 := by
    intro u
    have hprod : ‖ι u‖ * ‖ι ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have ha := h1 u
    have hb := h1 ↑u⁻¹
    have ha0 := norm_nonneg (ι u)
    have hb0 := norm_nonneg (ι ↑u⁻¹)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖlt : ‖ι ϖ‖ < 1 := by
    refine lt_of_le_of_ne (h1 ϖ) fun heq => ?_
    set x := algebraMap ℤ_[l] O (l : ℤ_[l])
    have hx : ‖ι x‖ = ‖(l : ℚ_[l])‖ := by
      rw [hι, PadicAlgCl.norm_extends]
      push_cast
      rfl
    have hlt : ‖ι x‖ < 1 := hx ▸ Padic.norm_p_lt_one
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero, norm_zero] at hx
      have : (0 : ℝ) < ‖(l : ℚ_[l])‖ := by
        rw [Padic.norm_p]
        have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      linarith
    obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [hxu, map_mul, norm_mul, map_pow, norm_pow, heq, one_pow, mul_one, hunit] at hlt
    exact lt_irrefl _ hlt
  have hpow : ∀ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal O ^ n, ‖ι a‖ ≤ ‖ι ϖ‖ ^ n := by
    intro n a ha
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖ι b‖ * ‖ι ϖ‖ ^ n ≤ 1 * ‖ι ϖ‖ ^ n := by gcongr; exact h1 b
      _ = ‖ι ϖ‖ ^ n := one_mul _
  refine ⟨h1, fun a ha => ?_, ?_⟩
  · have := hpow 1 a (by rwa [pow_one])
    rw [pow_one] at this
    exact this.trans_lt hϖlt
  · refine continuous_of_continuousAt_zero ι ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
    have hopen := (isAdic_iff.mp hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
    rw [dist_zero_right]
    exact (hpow n a ha).trans_lt hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicI
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicI
open PowerSeries

namespace GlobalTheory

theorem padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (δ : ℤ_[l]) {n : ℕ} (hn : n ≠ 0) (hδ : δ ^ n = 1) (h1 : PadicInt.toZMod δ = 1) : δ = 1 := by
  have key : ∀ p : ℕ, p.Prime → ∀ ε : ℤ_[l], ε ^ p = 1 → PadicInt.toZMod ε = 1 → ε = 1 := by
    intro p hp ε hε he1
    by_contra hne
    have hsum : ∑ i ∈ Finset.range p, ε ^ i = 0 := by
      have := geom_sum_mul ε p
      rw [hε, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have hp0 : (p : ZMod l) = 0 := by
      have := congrArg PadicInt.toZMod hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_pow, he1] using this
    have hpl : l = p := (Nat.prime_dvd_prime_iff_eq hl.out hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp hp0)
    subst hpl
    have hmem : ∀ z : ℤ_[l], (l : ℤ_[l]) ∣ z ↔ PadicInt.toZMod z = 0 := by
      intro z
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
    have h := emultiplicity_geom_sum₂_eq_one (p := l) (x := ε) (y := 1) PadicInt.prime_p
      (hl.out.odd_of_ne_two h2) ((hmem _).mpr (by simp [he1])) (by rw [hmem, he1]; exact one_ne_zero)
    simp [hsum] at h
  induction n using Nat.recOnMul generalizing δ with
  | zero => exact absurd rfl hn
  | one => simpa using hδ
  | prime p hp => exact key p hp δ hδ h1
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hn
    have hb : b ≠ 0 := right_ne_zero_of_mul hn
    refine iha δ ha (ihb (δ ^ a) hb (by rw [← pow_mul, hδ]) (by rw [map_pow, h1, one_pow])) h1

theorem exists_coset_representatives_of_finite_subgroup_padicInt_units {l : ℕ} [hl : Fact l.Prime]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (h2 : l ≠ 2) :
    ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧
      (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧
      ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ,
        x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  classical
  let g : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype
  have hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) := fun _ => rfl
  have hs : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by rw [← hg, hd]; rfl
    have hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1 := by
      have : d ^ Nat.card Δ = 1 := pow_card_eq_one'
      have := congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    exact Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))
  let H : Subgroup (ZMod l)ˣ := g.range
  have hH : Nat.card H = Nat.card Δ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H := by
    intro x hx
    have hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker := by
      intro y hy
      have : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hH] at this
      simpa using congrArg Subtype.val this
    have hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H := by
      rw [IsCyclic.card_powMonoidHom_ker, hH]
      exact Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    simpa using hx
  let φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H)) := Finite.equivFin _
  let r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ := fun τ => (φ.symm τ).out
  have hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ := fun τ => Quotient.out_eq _
  have hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ := fun τ => ZMod.natCast_zmod_val _
  have hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ' := by
    intro τ τ' h
    have := QuotientGroup.eq.mpr h
    rw [hr, hr] at this
    exact φ.symm.injective this
  refine ⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
      ZMod.card_units]
  · intro τ h
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hcast] at this
    exact (r τ).ne_zero this
  · intro τ τ' hne h
    simp only [hcast] at h
    have h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ := Units.ext (by simpa using h)
    exact hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))
  · intro x hx
    let u : (ZMod l)ˣ := Units.mk0 x hx
    have hu : (r (φ u))⁻¹ * u ∈ H := by
      rw [← QuotientGroup.eq, hr, Equiv.symm_apply_apply]
    obtain ⟨d, hd⟩ := hu
    have hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ,
        x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔
          u = r p.1 * g p.2 := by
      intro p
      rw [hcast, ← hg, Units.ext_iff]
      rfl
    have hd' : u = r (φ u) * g d := by rw [hd, mul_inv_cancel_left]
    refine ⟨(φ u, d), (hform _).mpr hd', ?_⟩
    rintro ⟨τ, d'⟩ hp
    have hp' : u = r τ * g d' := (hform _).mp hp
    have hτ : τ = φ u := by
      apply hreq
      refine ⟨d' * d⁻¹, ?_⟩
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]
      exact hd'
    rw [hτ] at hp'
    have : g d' = g d := mul_left_cancel (hp'.symm.trans hd')
    rw [hτ, hinj this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicIStatement
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ], l ≠ 2 → ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧ (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧ ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ, x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | exact GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | (intros; apply GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
namespace GlobalTheory

theorem isSquare_one_add_of_pow_two_pow_eq_zero {A : Type} [CommRing A] (c : A)
    (hc : 2 * c = 1) : ∀ (m : ℕ) (n : A), n ^ (2 ^ m) = 0 → IsSquare (1 + n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    simp only [pow_zero, pow_one] at hn
    exact ⟨1, by rw [hn]; ring⟩
  | succ m ih =>
    intro n hn
    have hnil : IsNilpotent (c * n) := ⟨2 ^ (m + 1), by rw [mul_pow, hn, mul_zero]⟩
    obtain ⟨v, hv⟩ := (hnil.isUnit_one_add).exists_right_inv
    have hn' : (-(c ^ 2 * n ^ 2 * v ^ 2)) ^ (2 ^ m) = 0 := by
      have : -(c ^ 2 * n ^ 2 * v ^ 2) = n ^ 2 * (-(c ^ 2 * v ^ 2)) := by ring
      rw [this, mul_pow, ← pow_mul, ← pow_succ', hn, zero_mul]
    obtain ⟨z, hz⟩ := ih _ hn'
    refine ⟨(1 + c * n) * z, ?_⟩
    linear_combination (1 + c * n) ^ 2 * hz + (c ^ 2 * n ^ 2 * ((1 + c * n) * v + 1)) * hv
      + (-n) * hc

theorem isSquare_one_add_of_isNilpotent {A : Type} [CommRing A] (c : A) (hc : 2 * c = 1)
    {n : A} (hn : IsNilpotent n) : IsSquare (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  exact isSquare_one_add_of_pow_two_pow_eq_zero c hc N n
    (pow_eq_zero_of_le (Nat.lt_two_pow_self).le hN)

theorem units_modSq_finite_of_fields : ∀ (k : Type) [Field k] [CharZero k],
    (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L],
      Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) →
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
      Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  intro k _ _ hL A _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hc : (2 : A) * algebraMap k A (1 / 2) = 1 := by
    have h2 : (2 : A) * algebraMap k A (1 / 2) = algebraMap k A (2 * (1 / 2)) := by
      rw [map_mul, map_ofNat]
    rw [h2]
    norm_num
  let Q : MaximalSpectrum A → Type := fun I =>
    (A ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range
  haveI hQ : ∀ I, Finite (Q I) := by
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact hL (A ⧸ I.asIdeal)
  let φ : Aˣ →* ((I : MaximalSpectrum A) → Q I) := MonoidHom.pi fun I =>
    (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have key : ∀ (I : MaximalSpectrum A) (u : Aˣ), φ u I = 1 ↔
      Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u ∈
        (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range :=
    fun I u => QuotientGroup.eq_one_iff _
  have hS : (powMonoidHom 2 : Aˣ →* Aˣ).range ≤ φ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext I
    rw [Pi.one_apply, key]
    exact ⟨Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom y, by simp⟩
  have hk : ∀ x : Aˣ, φ x = 1 → x ∈ (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    intro x hx
    have hloc : ∀ I : MaximalSpectrum A, ∃ w : (A ⧸ I.asIdeal)ˣ,
        (w : A ⧸ I.asIdeal) ^ 2 = Ideal.Quotient.mk I.asIdeal x := by
      intro I
      have h1 := (key I x).1 (congrFun hx I)
      obtain ⟨w, hw⟩ := h1
      refine ⟨w, ?_⟩
      have := congrArg (fun u : (A ⧸ I.asIdeal)ˣ => (u : A ⧸ I.asIdeal)) hw
      simpa using this
    choose w hw using hloc
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun I : MaximalSpectrum A => I.asIdeal)
      (fun I J h => MaximalSpectrum.isCoprime_of_ne h) (fun I => (w I : A ⧸ I.asIdeal))
    have hmem : ∀ I : MaximalSpectrum A, (x : A) - a ^ 2 ∈ I.asIdeal := by
      intro I
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      rw [ha I, hw I, sub_self]
    have hjac : (x : A) - a ^ 2 ∈ (⊥ : Ideal A).jacobson := by
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    have hnil : IsNilpotent ((x : A) - a ^ 2) := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      refine ⟨N, ?_⟩
      have := Ideal.pow_mem_pow hjac N
      rw [hN] at this
      simpa using this
    set m := (x : A) - a ^ 2 with hm
    have ha2 : IsUnit (a ^ 2) := by
      have : a ^ 2 = (x : A) + (-m) := by rw [hm]; ring
      rw [this]
      exact hnil.neg.isUnit_add_left_of_commute x.isUnit (Commute.all _ _)
    have hau : IsUnit a := (isUnit_pow_iff (by norm_num)).1 ha2
    obtain ⟨b, hb⟩ := hau
    have hn2 : IsNilpotent (((b⁻¹ : Aˣ) : A) ^ 2 * m) :=
      (Commute.all _ _).isNilpotent_mul_left hnil
    obtain ⟨z, hz⟩ := isSquare_one_add_of_isNilpotent _ hc hn2
    have hzu : IsUnit z := by
      have hu : IsUnit (1 + ((b⁻¹ : Aˣ) : A) ^ 2 * m) := hn2.isUnit_one_add
      rw [hz] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine ⟨b * hzu.unit, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec]
    have hbb : (b : A) * ((b⁻¹ : Aˣ) : A) = 1 := by simp
    have hxm : (x : A) = a ^ 2 + m := by rw [hm]; ring
    rw [hxm, ← hb]
    linear_combination (b : A) ^ 2 * hz.symm + (m * ((b : A) * ((b⁻¹ : Aˣ) : A) + 1)) * hbb
  let ψ := QuotientGroup.lift _ φ hS
  have hinj : Function.Injective ψ := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H x =>
    induction q using QuotientGroup.induction_on with
    | H y =>
    rw [QuotientGroup.eq]
    apply hk
    have h1 : φ x = φ y := hpq
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact Finite.of_injective ψ hinj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFieldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
end
end
