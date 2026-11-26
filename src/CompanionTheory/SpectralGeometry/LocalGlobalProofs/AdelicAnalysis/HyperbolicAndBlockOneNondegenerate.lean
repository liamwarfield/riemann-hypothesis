module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BlockForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    exact blockOne_succ_succ t A i j
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blockOne_zero_zero, blockOne_zero_succ, h0]

theorem hypJ_zero_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 0 = 0 := rfl

theorem hypJ_zero_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 1 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_zero_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 0 j.succ.succ = 0 := rfl

theorem hypJ_one_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 0 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 1 j.succ.succ = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 0 = 0 := rfl

theorem hypJ_succ_succ_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_succ_succ {K : Type} [Zero K] [One K] {M : ℕ}
    (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) : hypJ A i.succ.succ j.succ.succ = A i j := rfl

theorem det_hypJ {K : Type} [CommRing K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    (hypJ A).det = -A.det := by
  have h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A := by
    rw [← Fin.succ_zero_eq_one]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypJ (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (hypJ J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [hypJ_zero_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_one]
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
          · rw [hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]
            exact hJ.1 i j
  · rw [det_hypJ]
    exact neg_ne_zero.mpr hJ.2

theorem isHermND_blockOne (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {t : F} (ht : t ≠ 0) : IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · rw [blockOne_succ_succ, blockOne_succ_succ]
      exact hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2

theorem blockForms_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧
      ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) :=
  fun _ _ _ _ _ _ _ σ _ _ _ hJ => ⟨isHermND_hypJ σ hJ, fun _ ht => isHermND_blockOne σ hJ ht⟩

end GlobalTheory.CompanionTheory.SW.BlockForm
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerateStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_and_block_one_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧ ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | exact GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | (intros; apply GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem repr_ofF {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) (u : Fin 1) (i : Fin M) (k : Fin d) :
    b.repr (ofF b x u i) k = x (i, k) := by
  have h : ofF b x u i = b.equivFun.symm (fun k => x (i, k)) := by
    simp [ofF, Module.Basis.equivFun_symm_apply]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem ofF_bijective {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) := by
  constructor
  · intro x y hxy
    funext p
    obtain ⟨i, k⟩ := p
    rw [← repr_ofF b x 0 i k, ← repr_ofF b y 0 i k, hxy]
  · intro Y
    refine ⟨fun p => b.repr (Y 0 p.1) p.2, ?_⟩
    funext u i
    obtain rfl : u = 0 := Subsingleton.elim _ _
    exact b.sum_repr (Y 0 i)

theorem ofF_zero {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    ofF b (0 : Fin M × Fin d → F) = 0 := by
  funext u i
  simp [ofF]

theorem exists_algebraMap_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {σ : E →ₐ[F] E} (hne : σ ≠ AlgHom.id F E) {h : E}
    (hh : σ h = h) : ∃ c : F, h = algebraMap F E c := by
  by_contra hcon
  push Not at hcon
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), h] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hcon (-(s / t))
      have h1 : algebraMap F E t * h = -algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    subst ht
    simpa using hst
  have hspan : Submodule.span F (Set.range ![(1 : E), h]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h2])
  apply hne
  have hlin : σ.toLinearMap = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simp
    · simpa using hh
  ext y
  exact congrArg (fun f : E →ₗ[F] E => f y) hlin

theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro hσ
  have := h.2.1
  have hc := IsTotallyComplex.complexEmbedding_not_isReal τ
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa using this.symm

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigma_hE_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (y : Fin M → E) :
    σ (hE σ J y y) = hE σ J y y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (σ : E →+* E) (y j) = σ (y j) := rfl
  have h2 : (σ : E →+* E) (y i) = σ (y i) := rfl
  rw [h1, h2, sigma_sigma hσ, hJ.1 i j]
  ring

theorem ofF_gram_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧
    (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧
    ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F),
      (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) =
        (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ
          (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) →
      ∀ (β : F) (x : Fin M × Fin d → F),
        gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔
          (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  refine ⟨ofF_bijective b, ?_, ?_⟩
  · intro x
    rw [not_iff_not]
    constructor
    · intro h
      exact (ofF_bijective b).1 (h.trans (ofF_zero b).symm)
    · rintro rfl
      exact ofF_zero b
  · intro B hB β x
    obtain ⟨c, hc⟩ := exists_algebraMap_of_fixed hσ.2.2.1 (sigma_ne_id hσ)
      (sigma_hE_self hσ hJ (ofF b x 0))
    have hco : (fun p : Fin M × Fin d => b.repr (ofF b x 0 p.1) p.2) = x := by
      funext p
      exact repr_ofF b x 0 p.1 p.2
    have htr := hB (ofF b x 0)
    rw [hco, hc, Algebra.trace_algebraMap, hσ.2.2.1] at htr
    have hgram : gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ c = β := by
      constructor
      · intro h
        have h0 := congrFun (congrFun h 0) 0
        have h1 : hE σ J (ofF b x 0) (ofF b x 0) = algebraMap F E β := h0
        rw [hc] at h1
        exact (algebraMap F E).injective h1
      · rintro rfl
        funext u v
        obtain rfl : u = 0 := Subsingleton.elim _ _
        obtain rfl : v = 0 := Subsingleton.elim _ _
        exact hc
    rw [hgram, ← htr, nsmul_eq_mul]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e : (1 / 2 : F) * (((2 : ℕ) : F) * c) = c := by
      push_cast
      field_simp
    rw [e]

end GlobalTheory.CompanionTheory.SW.BB.RatCoord
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceFormStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_bijection_trace_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧ (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧ ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (β : F) (x : Fin M × Fin d → F), gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | exact GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianContinuousRapidDecay
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianContinuousRapidDecay
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem exists_lower_sup {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  have hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx
  have hcont : Continuous fun x : n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : n → ℝ) 1, c ≤ u ⬝ᵥ (P *ᵥ u) := by
    rcases (Metric.sphere (0 : n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨u, hu, hm⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos u ?_, fun v hv => hm hv⟩
      rintro rfl
      simp at hu
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hmin _ hu
  have h2 : (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x)) := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sq, mul_assoc]
  rw [h2] at h1
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  calc c * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = x ⬝ᵥ (P *ᵥ x) := by field_simp

theorem posdef_quadratic_lower_bound_l1 {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  obtain ⟨c, hc, h⟩ := exists_lower_sup hP
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨c / (N ^ 2 + 1), by positivity, fun x => (?_ : _ ≤ _).trans (h x)⟩
  have h1 : ∑ p, |x p| ≤ N * ‖x‖ := by
    calc ∑ p, |x p| ≤ ∑ _p : n, ‖x‖ := Finset.sum_le_sum fun p _ => norm_le_pi_norm x p
      _ = N * ‖x‖ := by simp [N]
  have h0 : 0 ≤ ∑ p, |x p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (∑ p, |x p|) ^ 2 ≤ (N ^ 2 + 1) * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ‖x‖]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem exists_lower_family {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
  choose c hc h using fun i => posdef_quadratic_lower_bound_l1 (hP i)
  obtain ⟨c0, hc0, hle⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ c i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min c
      exact ⟨c i, hc i, hi⟩
  set W : ℝ := (Fintype.card ι : ℝ)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  refine ⟨c0 / (W + 1), by positivity, fun y => ?_⟩
  have h1 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ W * ∑ i, (∑ p, |y i p|) ^ 2 := by
    simpa [W] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ∑ p, |y i p|)
  have hS : 0 ≤ ∑ i, (∑ p, |y i p|) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c0 * ∑ i, (∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)).trans (h i (y i))
  refine le_trans ?_ h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ (W + 1) * ∑ i, (∑ p, |y i p|) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]

theorem exp_mul_pow_le {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp ((N : ℝ) * s) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc Real.exp (-q) * (1 + s) ^ N ≤ Real.exp (-q) * Real.exp ((N : ℝ) * s) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-q + (N : ℝ) * s) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h2 : (N : ℝ) * s ≤ a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) := by
        have : 0 ≤ (2 * a * s - N) ^ 2 / (4 * a) := by positivity
        have e : (2 * a * s - N) ^ 2 / (4 * a) = a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) - N * s := by
          field_simp
          ring
        linarith
      linarith

end GlobalTheory.CompanionTheory.SW.BB.GaussReg

namespace GlobalTheory.CompanionTheory.SW.BB

open GaussReg

theorem sizeTup_eq_sum_xw {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem gaussQ_continuous_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  intro F E _ _ _ _ _ σ hCM M d b e hom he Pm
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  refine ⟨?_, fun hP N => ?_⟩
  · unfold gaussQ
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
    exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))
  · obtain ⟨c, hc, hlow⟩ := exists_lower_family hP
    refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * (Real.pi * c))), fun X => ?_⟩
    have hs := sizeTup_eq_sum_xw b e he X
    have hs0 : 0 ≤ sizeTup b X := by
      rw [hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq := hlow fun w => xw e b X w
    rw [← hs] at hq
    have hn : ‖((gaussQ e b Pm X : ℝ) : ℂ)‖ = gaussQ e b Pm X := by
      rw [Complex.norm_real, gaussQ, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn]
    have key := exp_mul_pow_le (a := Real.pi * c) (mul_pos Real.pi_pos hc) N hs0
      (q := Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq Real.pi_pos.le)
    simpa [gaussQ, neg_mul] using key

end GlobalTheory.CompanionTheory.SW.BB
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianContinuousRapidDecayStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_continuous_rapid_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay | exact GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay | (intros; apply GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CoordMat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_one_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def traceGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

def coordL (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin M × Fin d → R) :=
  (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis R b).equivFun).trans
    (LinearEquiv.curry R R (Fin M) (Fin d)).symm

theorem coordL_apply (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    coordL R M b x p = (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := rfl

theorem trace_expand [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * inclR R e * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  have hx : ∀ z : R ⊗[F] E, z = ∑ k, (Algebra.TensorProduct.basis R b).repr z k • ((1 : R) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hs : ∀ (r : R) (w : R ⊗[F] E), sigR R σ (r • w) = r • sigR R σ w := by
    intro r w
    exact map_smul (Algebra.TensorProduct.map (AlgHom.id R R) (σ : E →ₐ[F] E)) r w
  generalize hcu : (Algebra.TensorProduct.basis R b).repr u = cu
  generalize hcv : (Algebra.TensorProduct.basis R b).repr v = cv
  have hu : u = ∑ k, cu k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcu]; exact hx u
  have hv : v = ∑ k, cv k • ((1 : R) ⊗ₜ[F] b k) := by rw [← hcv]; exact hx v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu, hv, map_sum, Finset.sum_mul, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : sigR R σ ((1 : R) ⊗ₜ[F] b k) = (1 : R) ⊗ₜ[F] σ (b k) := by simp [sigR]
  have h2 : inclR R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [hs, h1, h2, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    trace_one_tmul, smul_eq_mul, smul_eq_mul]
  ring

theorem trace_hR [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      coordL R M b x ⬝ᵥ (traceGram σ J b).map (algebraMap F R) *ᵥ coordL R M b y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, JR, Matrix.map_apply, trace_expand R σ b]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, coordL_apply, traceGram, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hform_mulVec {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J g : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  have h : ∀ (K : Matrix (Fin M) (Fin M) A) (u v : Fin M → A), hform s K u v = (s ∘ u) ⬝ᵥ (K *ᵥ v) := by
    intro K u v
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : s ∘ (g *ᵥ x) = (g.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [h, h, hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  simp only [cT, Matrix.mul_assoc]

theorem matrix_ext_dot {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A] (P Q : Matrix ι ι A)
    (h : ∀ u v : ι → A, u ⬝ᵥ P *ᵥ v = u ⬝ᵥ Q *ᵥ v) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

theorem dot_conj {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by
  rw [← Matrix.vecMul_transpose g u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem traceGram_isSymm [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  refine Matrix.IsSymm.ext fun p q => ?_
  simp only [traceGram]
  have hm : e (σ (b q.2) * J q.1 p.1 * b p.2) = σ (b p.2) * J p.1 q.1 * b q.2 := by
    change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
    rw [map_mul, map_mul, hσ, hJ]
    ring
  exact (Algebra.trace_eq_of_algEquiv e _).symm.trans (congrArg _ hm)

theorem traceGram_det_ne_zero [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (b : Module.Basis (Fin d) F E) : (traceGram σ J b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  let y : Fin M → E := fun j => ∑ l, v (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, traceGram, Pi.zero_apply] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have h2 : ∀ i z, Algebra.trace F E (z * (J *ᵥ y) i) = 0 := by
    intro i z
    have hz : z = ∑ k, b.repr (σ z) k • σ (b k) := by
      have h := congrArg σ (b.sum_repr (σ z))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hσ, map_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun k _ => map_smul σ _ _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, h1, smul_zero]
  have h3 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact h2 i z
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hJ h3
  funext p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun l => v (p.1, l)) (congrFun h4 p.1) p.2

theorem hR_mat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hm : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
  rw [hR, hform_mulVec, hm, hR]

end Alg

theorem coord_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (h : HA R σ J), ∃ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ X : Fin 1 → Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2 := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  refine ⟨traceGram σ J b, traceGram_isSymm σ hσ J hJ.1 b, traceGram_det_ne_zero σ hσ J hJ.2 b,
    fun R _ _ h => ?_⟩
  let c := coordL (F := F) (E := E) R M b
  let T : (Fin M → R ⊗[F] E) →ₗ[R] (Fin M → R ⊗[F] E) :=
    (Matrix.mulVecLin (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))).restrictScalars R
  let g : Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
    LinearMap.toMatrix' (c.toLinearMap ∘ₗ T ∘ₗ c.symm.toLinearMap)
  have hg : ∀ x, g *ᵥ c x = c ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) := by
    intro x
    simp [g, T, LinearMap.toMatrix'_mulVec]
  refine ⟨g, ?_, fun X => (hg (X 0)).symm⟩
  refine matrix_ext_dot _ _ fun u v => ?_
  obtain ⟨x, rfl⟩ := c.surjective u
  obtain ⟨y, rfl⟩ := c.surjective v
  rw [dot_conj, hg, hg]
  have hx := trace_hR R σ J b x y
  have hy := trace_hR R σ J b ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
  rw [hR_mat] at hy
  exact hy.symm.trans hx

end GlobalTheory.CompanionTheory.SW.CoordMat
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormInvarianceUnderUnitary
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormInvarianceUnderUnitary
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isometry_map_ringHom {ι R S K : Type} [Fintype ι] [CommRing R] [CommRing S] [CommRing K]
    (φ : R →+* S) (α : K →+* R) (ψ : K →+* S) (hφ : ∀ x, φ (α x) = ψ x)
    (A : Matrix ι ι R) (B : Matrix ι ι K)
    (h : Aᵀ * B.map α * A = B.map α) :
    (A.map φ)ᵀ * B.map ψ * A.map φ = B.map ψ := by
  have hB : B.map ψ = (B.map α).map φ := by
    ext i j
    simp [hφ]
  have := congrArg (fun X => X.map φ) h
  simp only [Matrix.map_mul] at this
  rw [hB, ← Matrix.transpose_map]
  simpa using this

theorem ginf_gfin_isometry (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (hB : ∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) *
      gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) :
    (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧
      ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω =
        B.map (algebraMap F (Af F)) := by
  refine ⟨fun ω w => ?_, fun ω => ?_⟩
  · exact isometry_map_ringHom
      ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F)))
      (algebraMap F (AF F)) (ρ w)
      (fun x => by
        have h1 : fstA F (algebraMap F (AF F) x) = algebraMap F (Ainf F) x :=
          (fstA F).commutes x
        simpa [h1] using he x w)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)
  · exact isometry_map_ringHom (sndA F : AF F →+* Af F)
      (algebraMap F (AF F)) (algebraMap F (Af F))
      (fun x => (sndA F).commutes x)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormInvarianceUnderUnitaryStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_invariance_under_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) * gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) → (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧ ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω = B.map (algebraMap F (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRoot
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRoot
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRootStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_continuous_square_root : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ, ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧ (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnits
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnits
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem continuous_tmul_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (fun a : AF F => a ⊗ₜ[F] (1 : E)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  let φ : AF F →ₗ[AF F] AF F ⊗[F] E :=
    (TensorProduct.AlgebraTensorModule.mk F (AF F) (AF F) E).flip (1 : E)
  exact IsModuleTopology.continuous_of_linearMap φ

theorem exists_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨θ, hθ⟩ := (GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles F hCM.1).1
  let g : ℝ → AF F ⊗[F] E := fun x => pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)
  have g0 : g 0 = 1 := by
    simp only [g, Real.exp_zero, map_one]
    rfl
  have gadd : ∀ x y, g (x + y) = g x * g y := by
    intro x y
    have h : pairA F (θ (Real.exp x) * θ (Real.exp y)) 1 =
        pairA F (θ (Real.exp x)) 1 * pairA F (θ (Real.exp y)) 1 :=
      Prod.ext rfl (mul_one (1 : Af F)).symm
    simp only [g, Real.exp_add, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h]
  have gc : Continuous g := by
    refine (continuous_tmul_one F E).comp ?_
    show Continuous fun x : ℝ => ((θ (Real.exp x), 1) : AF F)
    exact (hθ.comp Real.continuous_exp).prodMk continuous_const
  let f : Multiplicative ℝ →* AF F ⊗[F] E :=
    { toFun := fun x => g x.toAdd
      map_one' := g0
      map_mul' := fun x y => gadd x.toAdd y.toAdd }
  refine ⟨f.toHomUnits, ?_, θ, hθ, fun x => rfl⟩
  rw [Units.continuous_iff]
  constructor
  · exact gc.comp continuous_toAdd
  · have : (fun x : Multiplicative ℝ => (((f.toHomUnits x)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
        fun x => g (-x.toAdd) := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact gc.comp (continuous_neg.comp continuous_toAdd)

end GlobalTheory.CompanionTheory.SW.Flow
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnitsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_flow_adelic_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Flow.exists_flow | exact GlobalTheory.CompanionTheory.SW.Flow.exists_flow | (intros; apply GlobalTheory.CompanionTheory.SW.Flow.exists_flow <;> assumption)
end
end
