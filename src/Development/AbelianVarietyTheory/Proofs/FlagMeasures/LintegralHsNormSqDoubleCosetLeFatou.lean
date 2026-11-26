module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalTwoSided
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqIintLeLiminf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFolnerOverlapAverageTendstoForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOne
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem folner_single_translate : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r))
    (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S,
    Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  intro k r S μ Om h p hp
  obtain ⟨_, hC⟩ := h
  obtain ⟨Oc, hOc, hlim⟩ := hC {p} isCompact_singleton (Set.singleton_subset_iff.2 hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · refine ENNReal.div_le_div_right (measure_mono fun x hx => ?_) _
    exact ⟨(hOc j).2.1 hx, (hOc j).2.2 p rfl x hx⟩
  · exact (ENNReal.div_le_div_right (measure_mono fun x (hx : x ∈ {s | s ∈ Om j ∧ lmulM p s ∈ Om j}) => hx.1) _).trans ENNReal.div_self_le_one

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOneStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.folner_single_translate_proportion_tendsto_one : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S, Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.SgInf.folner_single_translate | exact GlobalTheory.SgInf.folner_single_translate | (intros; apply GlobalTheory.SgInf.folner_single_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFolnerOverlapAverageTendstoForm
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLimit

theorem mul_mem_GG {k r : ℕ} {g g' : Mat k r} (hg : g ∈ GG k r) (hg' : g' ∈ GG k r) : g * g' ∈ GG k r := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : g'ᴴ * Hpk k r * g' = Hpk k r := hg'
  show (g * g')ᴴ * Hpk k r * (g * g') = Hpk k r
  calc (g * g')ᴴ * Hpk k r * (g * g') = g'ᴴ * (gᴴ * Hpk k r * g) * g' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

theorem DD_stable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  have hv' : v ∈ DD σ w := hv
  show σ g v ∈ DD σ w
  unfold DD at hv'
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', hg', rfl⟩ := hx
    have := hσ.1.2 g hg g' hg'
    have h2 : σ g (σ g' w) = σ (g * g') w := by rw [this]; rfl
    rw [h2]
    exact mem_DD σ w (mul_mem_GG hg hg')
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add (f := _)]; exact (DD σ w).add_mem (ihx hx) (ihy hy)
  | smul c x hx ih => rw [map_smul]; exact (DD σ w).smul_mem c (ih hx)

theorem measurable_overlap {k r : ℕ} (μ : Measure (Mt k r)) [SFinite μ] {Ω : Set (Mt k r)}
    (hΩ : MeasurableSet Ω) :
    Measurable fun p : Mt k r => μ {s | s ∈ Ω ∧ lmulM (Matrix.of p) s ∈ Ω} := by
  have hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2 :=
    Continuous.matrix_mul (A := fun q : Mt k r × Mt k r => (Matrix.of q.1 : Mat k r))
      (B := fun q : Mt k r × Mt k r => (Matrix.of q.2 : Mat k r)) continuous_fst continuous_snd
  have hm : MeasurableSet {q : Mt k r × Mt k r | q.2 ∈ Ω ∧ lmulM (Matrix.of q.1) q.2 ∈ Ω} :=
    (measurable_snd hΩ).inter (hc.measurable hΩ)
  exact measurable_measure_prodMk_left hm

theorem tendsto_of_integrable {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {Om : ℕ → Set (Mt k r)} (hO : IsFolner S μ Om) {f : Mt k r → ℂ} (hf : Integrable f μ) :
    Filter.Tendsto (fun j => (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ)) Filter.atTop (nhds (∫ p, f p ∂μ)) := by
  haveI : SigmaFinite μ := hμ.1
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have heq : ∀ j, (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ) =
      ∫ p, (((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j)).toReal : ℝ) : ℂ) * f p ∂μ := by
    intro j
    rw [← integral_div]
    congr 1
    funext p
    rw [ENNReal.toReal_div]
    push_cast
    ring
  simp only [heq]
  refine tendsto_integral_of_dominated_convergence (fun p => ‖f p‖) (fun j => ?_) hf.norm (fun j => ?_) ?_
  · refine AEStronglyMeasurable.mul ?_ hf.1
    have := ((measurable_overlap μ (hO.1 j).1).div_const (μ (Om j))).ennreal_toReal
    exact (Complex.measurable_ofReal.comp this).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have h1 : μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j) ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono fun s hs => hs.1)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  · filter_upwards [hae] with p hp
    have h1 := GlobalTheory.T.folner_single_translate_proportion_tendsto_one k r S μ Om hO _ hp
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
    have h4 := h3.mul_const (f p)
    simpa [Function.comp_def] using h4

theorem folner_limit : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide Om hO y hy ξ
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w)
    (DD_stable hStd.2.1 w) hStd.2.2.2.2.2.2.2.1 y hy y hy).1
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪ξ, T ξ⟫_ℂ := fun T => rfl
  have hfun : (fun p : Mt k r => L (coef σ y y (Matrix.of p) • PiS (psiGen k r z c) π (Matrix.of p)⁻¹)) =
      fun p => coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ := by
    funext p
    rw [map_smul, hL, smul_eq_mul]
  have hf := L.integrable_comp hint
  have hI := L.integral_comp_comm hint
  rw [hfun] at hf hI
  have := tendsto_of_integrable hSide.2.2.2.1 hO hf
  rw [hI] at this
  exact this

end GlobalTheory.SgInf.FolnerLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFolnerOverlapAverageTendstoFormStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFolner_overlap_average_tendsto_form : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  first | exact @GlobalTheory.SgInf.FolnerLimit.folner_limit | exact GlobalTheory.SgInf.FolnerLimit.folner_limit | (intros; apply GlobalTheory.SgInf.FolnerLimit.folner_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotent
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.Dilation

variable {k r : ℕ}

def dd (k r : ℕ) (τ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then ((r - i.val : ℕ) : ℤ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℤ)

theorem dil_eq (τ : ℝ) : dil k r τ = Matrix.diagonal (dd k r τ) := rfl

theorem dd_eq_zpow {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i = (τ : ℂ) ^ wt k r i := by
  unfold dd wt
  split_ifs
  · rw [_root_.zpow_natCast]
  · rw [_root_.zpow_zero]
  · rw [_root_.zpow_neg, _root_.zpow_natCast]

theorem dd_inv_mul {τ : ℝ} (hτ : τ ≠ 0) (i j : Fin (2 * r + k + 1)) :
    dd k r τ⁻¹ i * dd k r τ j = (τ : ℂ) ^ (wt k r j - wt k r i) := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow (inv_ne_zero hτ), dd_eq_zpow hτ, Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    neg_add_eq_sub]

theorem dd_mul_inv {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i * dd k r τ⁻¹ i = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow hτ, dd_eq_zpow (inv_ne_zero hτ), Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    add_neg_cancel, _root_.zpow_zero]

theorem star_dd (τ : ℝ) (i : Fin (2 * r + k + 1)) : star (dd k r τ i) = dd k r τ i := by
  unfold dd
  split_ifs <;> simp

theorem dd_pair {τ : ℝ} (hτ : τ ≠ 0) {i j : Fin (2 * r + k + 1)} (h : i.val < r ∨ j.val < r)
    (hs : i.val + j.val = 2 * r + k) : dd k r τ i * dd k r τ j = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have hw : wt k r i + wt k r j = 0 := by
    have := i.isLt
    have := j.isLt
    unfold wt
    split_ifs <;> omega
  rw [dd_eq_zpow hτ, dd_eq_zpow hτ, ← _root_.zpow_add₀ h0, hw, _root_.zpow_zero]

theorem dd_middle (τ : ℝ) {i : Fin (2 * r + k + 1)} (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    dd k r τ i = 1 := by
  unfold dd
  rw [if_neg (by omega), if_pos h2]

theorem dil_entry (a b : ℝ) (m : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (dil k r a * m * dil k r b) i j = dd k r a i * m i j * dd k r b j := by
  rw [dil_eq, dil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dil_mul_inv {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ * dil k r τ⁻¹ = 1 := by
  rw [dil_eq, dil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dd_mul_inv hτ i

theorem dil_inv {τ : ℝ} (hτ : τ ≠ 0) : (dil k r τ)⁻¹ = dil k r τ⁻¹ := by
  exact Matrix.inv_eq_right_inv (dil_mul_inv hτ)

theorem uh_mul {g h : Mat k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem dil_mem {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ ∈ UH (Hpk k r) := by
  show (dil k r τ)ᴴ * Hpk k r * dil k r τ = Hpk k r
  ext i j
  rw [dil_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, star_dd]
  by_cases h1 : (i.val < r ∨ j.val < r) ∧ i.val + j.val = 2 * r + k
  · rw [mul_right_comm, dd_pair hτ h1.1 h1.2, one_mul]
  · by_cases h2 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
    · obtain ⟨hr, hk, rfl⟩ := h2
      rw [dd_middle τ hr hk, one_mul, mul_one]
    · have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (fun hc => h1 ⟨Or.inl hc.1, hc.2⟩), if_neg (fun hc => h1 ⟨Or.inr hc.1, hc.2⟩),
          if_neg h2]
      rw [h0, mul_zero, zero_mul]

theorem Hpk_row {i p t : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val)
    (hs : i.val + p.val = 2 * r + k) : Hpk k r p t = if t = i then 1 else 0 := by
  have hpo : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
  simp only [Hpk]
  rcases eq_or_ne t i with rfl | hti
  · rw [if_pos rfl]
    rcases h with h | h
    · rw [if_neg (by omega), if_pos ⟨h, by omega⟩]
    · rw [if_pos ⟨by omega, by omega⟩]
  · have hv : t.val ≠ i.val := fun e => hti (Fin.ext e)
    rw [if_neg hti, if_neg (by omega), if_neg (by omega), if_neg (fun hc => hpo ⟨hc.1, hc.2.1⟩)]

theorem uw_col {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1)} (hp : p.val < r ∨ r + k < p.val) (s : Fin (2 * r + k + 1)) :
    h s p = if s = p then 1 else 0 := by
  have hcol : ∀ q : Fin (2 * r + k + 1), h *ᵥ bvec q = bvec q → h s q = if s = q then 1 else 0 := by
    intro q hq
    have e := congrFun hq s
    simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using e
  have hpl := p.isLt
  rcases hp with hp | hp
  · have hq : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have := (hh.2.1 ⟨p.val, hp⟩).1
    rw [hq] at this
    exact hcol p this
  · have hq : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have := (hh.2.1 ⟨2 * r + k - p.val, by omega⟩).2
    rw [hq] at this
    exact hcol p this

theorem uw_zero {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    h i j = 0 := by
  have hil := i.isLt
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  let p : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hpv : p.val = 2 * r + k - i.val := rfl
  have hpo : p.val < r ∨ r + k < p.val := by omega
  have hip : i.val + p.val = 2 * r + k := by omega
  have hcol := uw_col hh hpo
  have hrow : ∀ t, Hpk k r p t = if t = i then 1 else 0 := fun t => Hpk_row hi hip
  have hleft : ∀ t, (hᴴ * Hpk k r) p t = Hpk k r p t := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [Matrix.conjTranspose_apply, hcol]
    · intro s _ hs
      simp [Matrix.conjTranspose_apply, hcol, hs]
    · simp
  have e := congrFun (congrFun hU p) j
  rw [Matrix.mul_apply] at e
  simp only [hleft, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  have hji : j ≠ i := fun hc => by subst hc; omega
  rw [if_neg hji] at e
  exact e

theorem dil_comm {z : Fin (2 * r + k + 1) → ℂ} (τ : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    dil k r τ * h = h * dil k r τ := by
  ext i j
  rw [dil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [uw_col hh hj i]
    split_ifs with e
    · subst e
      rw [one_mul, mul_one]
    · rw [mul_zero, zero_mul]
  · have hj' : r ≤ j.val ∧ j.val ≤ r + k := by omega
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_zero hh hi hj'.1 hj'.2, mul_zero, zero_mul]
    · rw [dd_middle τ (by omega) (by omega), dd_middle τ hj'.1 hj'.2, one_mul, mul_one]

private theorem conj_mem_lemma {τ : ℝ} (hτ : τ ≠ 0) (m : Mat k r) (i j : Fin (2 * r + k + 1))
    (h : m i j = if i = j then 1 else 0) :
    (dil k r τ * m * dil k r τ⁻¹) i j = if i = j then 1 else 0 := by
  rw [dil_entry, h]
  split_ifs with e
  · subst e
    rw [mul_one, dd_mul_inv hτ]
  · rw [mul_zero, zero_mul]

theorem conj_mem {τ : ℝ} (hτ : τ ≠ 0) {m : Mat k r} (hm : m ∈ Nset k r) :
    dil k r τ * m * dil k r τ⁻¹ ∈ Nset k r := by
  have hU : m ∈ UH (Hpk k r) := hm.1
  have hc : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      m i (eI k r a) = if i = eI k r a then 1 else 0 := hm.2.1
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  refine ⟨uh_mul (uh_mul (dil_mem hτ) hU) (dil_mem (inv_ne_zero hτ)), ?_, ?_⟩
  · intro a i hai
    exact conj_mem_lemma hτ m i _ (hc a i hai)
  · intro i j h1 h2 h3
    exact conj_mem_lemma hτ m i j (hb i j h1 h2 h3)

theorem wt_lt {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hn : ¬ (r ≤ i.val ∧ j.val ≤ r + k)) :
    wt k r j + 1 ≤ wt k r i := by
  unfold wt
  split_ifs <;> omega

private theorem apply_self_eq_one_of_mem_Nset {m : Mat k r} (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1)) :
    m i i = if i = i then 1 else 0 :=
  Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i i le_rfl

theorem contract {τ : ℝ} (hτ : 1 ≤ τ) {m : Mat k r} (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) :
    ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖ := by
  have hpos : 0 < τ := by linarith
  have hτ0 : τ ≠ 0 := hpos.ne'
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  rw [dil_inv hτ0, Matrix.sub_apply, Matrix.sub_apply, dil_entry, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hij' : i.val < j.val := hij
    rw [if_neg hij.ne, sub_zero, sub_zero]
    by_cases hmid : r ≤ i.val ∧ j.val ≤ r + k
    · have h0 : m i j = 0 := by
        have e := hb i j (by omega) hmid.2 hmid.1
        rwa [if_neg hij.ne] at e
      rw [h0]
      simp
    · have hw := wt_lt (k := k) (r := r) hij' hmid
      rw [mul_right_comm, dd_inv_mul hτ0, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← _root_.zpow_neg_one]
      exact _root_.zpow_le_zpow_right₀ hτ (by omega)
  · have h1 : m i i = 1 := by simpa using apply_self_eq_one_of_mem_Nset hm i
    rw [h1, if_pos rfl, mul_one, dd_inv_mul hτ0, sub_self, _root_.zpow_zero]
    simp
  · have h0 : m i j = 0 := by
      have e := Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i j hij.le
      rwa [if_neg hij.ne'] at e
    rw [if_neg hij.ne', h0]
    simp

theorem main : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  intro k r z _
  refine ⟨fun τ hτ => ⟨dil_mem hτ.ne', fun h hh => dil_comm τ hh, fun m hm => ⟨?_, ?_⟩⟩,
    fun τ hτ m hm i j => contract hτ hm i j⟩
  · rw [dil_inv hτ.ne']
    exact conj_mem hτ.ne' hm
  · have e := conj_mem (inv_ne_zero hτ.ne') hm
    rwa [inv_inv, ← dil_inv hτ.ne'] at e

end GlobalTheory.SgInf.Dilation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotentStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselRootDilation_normalizes_contracts_unipotent : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  first | exact @GlobalTheory.SgInf.Dilation.main | exact GlobalTheory.SgInf.Dilation.main | (intros; apply GlobalTheory.SgInf.Dilation.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerSets

variable {k r : ℕ}

def sn (a : Mat k r) : ℝ := @norm (Mt k r) _ a

theorem sn_nonneg (a : Mat k r) : 0 ≤ sn a := @norm_nonneg (Mt k r) _ a

theorem entry_le (a : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖a i j‖ ≤ sn a :=
  (norm_le_pi_norm (a i) j).trans (norm_le_pi_norm (show Mt k r from a) i)

theorem sn_le {a : Mat k r} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖a i j‖ ≤ c) : sn a ≤ c :=
  (pi_norm_le_iff_of_nonneg (x := (show Mt k r from a)) hc).2 fun i =>
    (pi_norm_le_iff_of_nonneg hc).2 fun j => h i j

theorem sn_add_le (a b : Mat k r) : sn (a + b) ≤ sn a + sn b := @norm_add_le (Mt k r) _ a b

theorem sn_sub_le (a b : Mat k r) : sn (a - b) ≤ sn a + sn b := @norm_sub_le (Mt k r) _ a b

theorem sn_one_le : sn (1 : Mat k r) ≤ 1 := sn_le zero_le_one fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem continuous_sn : Continuous (sn : Mat k r → ℝ) := @continuous_norm (Mt k r) _

def dd (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

theorem dd_nonneg : 0 ≤ dd k r := Nat.cast_nonneg _

theorem sn_mul_le {a b : Mat k r} {A B : ℝ} (ha : sn a ≤ A) (hb : sn b ≤ B) :
    sn (a * b) ≤ dd k r * A * B := by
  have hA : 0 ≤ A := (sn_nonneg a).trans ha
  have hB : 0 ≤ B := (sn_nonneg b).trans hb
  refine sn_le (mul_nonneg (mul_nonneg dd_nonneg hA) hB) fun i j => ?_
  rw [Matrix.mul_apply]
  calc ‖∑ l, a i l * b l j‖ ≤ ∑ l, ‖a i l * b l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), A * B := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul ((entry_le a i l).trans ha) ((entry_le b l j).trans hb) (norm_nonneg _) hA
    _ = dd k r * A * B := by simp [dd, mul_assoc]

theorem exists_bound {C : Set (Mat k r)} (hC : IsCompact C) : ∃ M, 0 ≤ M ∧ ∀ a ∈ C, sn a ≤ M := by
  obtain ⟨M, hM⟩ := (hC.image continuous_sn).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun a ha => (hM ⟨a, ha, rfl⟩).trans (le_max_left _ _)⟩

theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc gᴴ, h, hH]
  exact Matrix.isUnit_det_of_left_inverse this

def cj (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) : Mt k r ≃ₜ Mt k r where
  toFun x := b * Matrix.of x * a
  invFun x := a * Matrix.of x * b
  left_inv x := by
    show a * (b * Matrix.of x * a) * b = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, hab, one_mul, mul_assoc, hab, mul_one]
  right_inv x := by
    show b * (a * Matrix.of x * b) * a = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, hba, one_mul, mul_assoc, hba, mul_one]
  continuous_toFun := (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem of_cj (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) (x : Mt k r) :
    (Matrix.of (cj a b hab hba x) : Mat k r) = b * Matrix.of x * a := rfl

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem of_lmulM (a : Mat k r) (x : Mt k r) : (Matrix.of (lmulM a x) : Mat k r) = a * Matrix.of x := rfl

theorem mem_iff_cj {S : Set (Mat k r)} {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1)
    (h1 : ∀ s ∈ S, a * s * b ∈ S) (h2 : ∀ s ∈ S, b * s * a ∈ S) (x : Mt k r) :
    Matrix.of (cj a b hab hba x) ∈ S ↔ Matrix.of x ∈ S := by
  refine ⟨fun h => ?_, fun h => h2 _ h⟩
  have := h1 _ h
  rwa [of_cj, ← mul_assoc, ← mul_assoc, hab, one_mul, mul_assoc, hab, mul_one] at this

theorem isHaarOn_map_cj {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1)
    (h1 : ∀ s ∈ S, a * s * b ∈ S) (h2 : ∀ s ∈ S, b * s * a ∈ S) :
    IsHaarOn S (μ.map (cj a b hab hba)) := by
  obtain ⟨hσ, hne, hc, hinv⟩ := hμ
  have hm : Measurable (cj a b hab hba) := (cj a b hab hba).continuous.measurable
  refine ⟨(cj a b hab hba).toMeasurableEquiv.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 hne
  · have hop : IsOpen {x : Mt k r | Matrix.of x ∉ S} := hS.isOpen_compl
    rw [Measure.map_apply hm hop.measurableSet, ← hc]
    congr 1
    ext x
    exact not_congr (mem_iff_cj hab hba h1 h2 x)
  · rw [Measure.map_map (continuous_lmulM s).measurable hm]
    have : lmulM s ∘ cj a b hab hba = cj a b hab hba ∘ lmulM (a * s * b) := by
      funext x
      show s * (b * Matrix.of x * a) = b * (a * s * b * Matrix.of x) * a
      simp only [← mul_assoc, hba, one_mul]
    rw [this, ← Measure.map_map hm (continuous_lmulM _).measurable, hinv _ (h1 s hs)]

def AA (S H : Set (Mat k r)) (t : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ S} ∩ {x | ∃ h ∈ H, sn (h * Matrix.of x) < t}

theorem isOpen_U (H : Set (Mat k r)) (t : ℝ) :
    IsOpen {x : Mt k r | ∃ h ∈ H, sn (h * Matrix.of x) < t} := by
  have : {x : Mt k r | ∃ h ∈ H, sn (h * Matrix.of x) < t} =
      ⋃ h ∈ H, {x : Mt k r | sn (lmulM h x) < t} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]; rfl
  rw [this]
  exact isOpen_biUnion fun h _ => isOpen_lt (continuous_sn.comp (continuous_lmulM h)) continuous_const

theorem measurableSet_AA {S : Set (Mat k r)} (hS : IsClosed S) (H : Set (Mat k r)) (t : ℝ) :
    MeasurableSet (AA S H t) := by
  have hc : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  exact hc.measurableSet.inter (isOpen_U H t).measurableSet

theorem AA_mono (S H : Set (Mat k r)) {t t' : ℝ} (h : t ≤ t') : AA S H t ⊆ AA S H t' :=
  fun _ ⟨h1, g, hg, h2⟩ => ⟨h1, g, hg, h2.trans_le h⟩

theorem AA_bound {S H : Set (Mat k r)} (hH : IsClosedSub k r H) {M : ℝ} (hM : ∀ h ∈ H, sn h ≤ M) {t : ℝ}
    {x : Mt k r} (hx : x ∈ AA S H t) : sn (Matrix.of x) ≤ dd k r * M * t := by
  obtain ⟨-, h, hh, hlt⟩ := hx
  have : (Matrix.of x : Mat k r) = h⁻¹ * (h * Matrix.of x) := by
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh)), one_mul]
  rw [this]
  exact sn_mul_le (hM _ (hH.2.2.2.2 _ hh)) hlt.le

theorem lmulM_mem_AA {S H : Set (Mat k r)} (hS : IsClosedSub k r S) (hH : IsClosedSub k r H) {M : ℝ}
    (hM : ∀ h ∈ H, sn h ≤ M) {t ε : ℝ} {x : Mt k r} (hx : x ∈ AA S H t) {h₀ m : Mat k r} (h0 : h₀ ∈ H)
    (hm : sn (m - 1) ≤ ε) (hc : h₀ * m ∈ S) :
    lmulM (h₀ * m) x ∈ AA S H (t * (1 + dd k r * (dd k r * (dd k r * M * ε) * M))) := by
  obtain ⟨hxS, h, hh, hlt⟩ := hx
  refine ⟨hS.2.2.2.1 _ hc _ hxS, h * h₀⁻¹, hH.2.2.2.1 _ hh _ (hH.2.2.2.2 _ h0), ?_⟩
  have e0 := Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 h0))
  have e1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh))
  have : h * h₀⁻¹ * Matrix.of (lmulM (h₀ * m) x) =
      h * Matrix.of x + (h * (m - 1) * h⁻¹) * (h * Matrix.of x) := by
    rw [of_lmulM]
    calc h * h₀⁻¹ * (h₀ * m * Matrix.of x) = h * (h₀⁻¹ * h₀) * m * Matrix.of x := by
          simp only [mul_assoc]
      _ = h * Matrix.of x + h * (m - 1) * (h⁻¹ * h) * Matrix.of x := by
          rw [e0, e1]; noncomm_ring
      _ = _ := by simp only [mul_assoc]
  rw [this]
  have b1 := sn_mul_le (sn_mul_le (hM _ hh) hm) (hM _ (hH.2.2.2.2 _ hh))
  have b2 := sn_mul_le b1 (le_refl (sn (h * Matrix.of x)))
  have b3 : 0 ≤ dd k r * (dd k r * (dd k r * M * ε) * M) :=
    mul_nonneg dd_nonneg ((sn_nonneg _).trans b1)
  calc _ ≤ _ := sn_add_le _ _
    _ ≤ sn (h * Matrix.of x) * (1 + dd k r * (dd k r * (dd k r * M * ε) * M)) := by linarith
    _ < _ := mul_lt_mul_of_pos_right hlt (by linarith)

theorem tendsto_AA (S H : Set (Mat k r)) (μ : Measure (Mt k r)) {L : ℝ} (hL : 0 ≤ L) :
    Filter.Tendsto (fun j : ℕ => μ (AA S H (2 / (1 + L * ((j : ℝ) + 1)⁻¹)))) Filter.atTop
      (nhds (μ (AA S H 2))) := by
  have hlim : Filter.Tendsto (fun j : ℕ => 2 / (1 + L * ((j : ℝ) + 1)⁻¹)) Filter.atTop (nhds 2) := by
    have h0 : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := (tendsto_const_nhds (x := (2 : ℝ))).div ((h0.const_mul L).const_add 1) (by simp)
    rw [mul_zero, add_zero, div_one] at this
    exact this
  have hU : AA S H 2 = ⋃ j : ℕ, AA S H (2 / (1 + L * ((j : ℝ) + 1)⁻¹)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨h1, h, hh, hlt⟩
      obtain ⟨j, hj⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
      exact Set.mem_iUnion.2 ⟨j, h1, h, hh, hj⟩
    · refine Set.iUnion_subset fun j => AA_mono S H ?_
      have : 0 ≤ L * ((j : ℝ) + 1)⁻¹ := by positivity
      exact div_le_self (by norm_num) (by linarith)
  rw [hU]
  refine tendsto_measure_iUnion_atTop fun i j hij => AA_mono S H ?_
  have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  gcongr

theorem exists_isFolner : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  intro k r z μ hz hT hμ
  obtain ⟨-, hN, hH, hS, hHc⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.besselRootDilation_normalizes_contracts_unipotent k r z hz
  obtain ⟨hfin, hpos⟩ := GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r _ μ hS hμ
  obtain ⟨M, hM0, hM⟩ := exists_bound hHc
  set a : ℕ → Mat k r := fun j => dil k r ((j : ℝ) + 1) with ha
  have hτ : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hu : ∀ j, IsUnit (a j).det := fun j => isUnit_det_of_mem (hd1 _ (hτ j)).1
  have hab : ∀ j, a j * (a j)⁻¹ = 1 := fun j => Matrix.mul_nonsing_inv _ (hu j)
  have hba : ∀ j, (a j)⁻¹ * a j = 1 := fun j => Matrix.nonsing_inv_mul _ (hu j)
  have hc1 : ∀ j, ∀ h ∈ UWset k r z, a j * h = h * a j := fun j => (hd1 _ (hτ j)).2.1
  have hc2 : ∀ j, ∀ h ∈ UWset k r z, (a j)⁻¹ * h = h * (a j)⁻¹ := fun j h hh => by
    calc (a j)⁻¹ * h = (a j)⁻¹ * (h * a j) * (a j)⁻¹ := by simp only [mul_assoc, hab, mul_one]
      _ = _ := by rw [← hc1 j h hh, ← mul_assoc, hba, one_mul]
  have e1 : ∀ j, ∀ h ∈ UWset k r z, ∀ m, a j * (h * m) * (a j)⁻¹ = h * (a j * m * (a j)⁻¹) :=
    fun j h hh m => by rw [← mul_assoc, hc1 j h hh]; simp only [mul_assoc]
  have e2 : ∀ j, ∀ h ∈ UWset k r z, ∀ m, (a j)⁻¹ * (h * m) * a j = h * ((a j)⁻¹ * m * a j) :=
    fun j h hh m => by rw [← mul_assoc, hc2 j h hh]; simp only [mul_assoc]
  have h1 : ∀ j, ∀ s ∈ Sset k r z, a j * s * (a j)⁻¹ ∈ Sset k r z := by
    rintro j s ⟨h, hh, m, hm, rfl⟩
    exact ⟨h, hh, _, ((hd1 _ (hτ j)).2.2 m hm).1, e1 j h hh m⟩
  have h2 : ∀ j, ∀ s ∈ Sset k r z, (a j)⁻¹ * s * a j ∈ Sset k r z := by
    rintro j s ⟨h, hh, m, hm, rfl⟩
    exact ⟨h, hh, _, ((hd1 _ (hτ j)).2.2 m hm).2, e2 j h hh m⟩
  set ψ : ℕ → Mt k r ≃ₜ Mt k r := fun j => cj (a j) (a j)⁻¹ (hab j) (hba j) with hψ
  have hψm : ∀ j, Measurable (ψ j) := fun j => (ψ j).continuous.measurable
  choose c hc0 hct hc using fun j => GlobalTheory.T.closedSubgroupBesselUnitary_haar_unique k r _ μ _ hS hμ
    (isHaarOn_map_cj hS.2.1 hμ (hab j) (hba j) (h1 j) (h2 j))
  have hmeas : ∀ j t, μ (ψ j ⁻¹' AA (Sset k r z) (UWset k r z) t) =
      c j * μ (AA (Sset k r z) (UWset k r z) t) := fun j t => by
    rw [← Measure.map_apply (hψm j) (measurableSet_AA hS.2.1 _ t), hc j]; rfl
  have hA0 : 0 < μ (AA (Sset k r z) (UWset k r z) 2) := by
    have hU := hpos _ (isOpen_U (UWset k r z) 2) ⟨(1 : Mat k r), ⟨1, hH.2.2.1, by
      show sn ((1 : Mat k r) * 1) < 2
      rw [one_mul]; linarith [sn_one_le (k := k) (r := r)]⟩, hS.2.2.1⟩
    rw [AA, Set.inter_comm, measure_inter_conull' ]
    · exact hU
    · exact measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have hAt : μ (AA (Sset k r z) (UWset k r z) 2) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun x hx => ?_)
      (hfin _ (isCompact_closedBall (0 : Mt k r) (dd k r * M * 2)))
    exact mem_closedBall_zero_iff.2 (AA_bound hH hM hx)
  refine ⟨fun j => ψ j ⁻¹' AA (Sset k r z) (UWset k r z) 2, fun j => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hψm j (measurableSet_AA hS.2.1 _ _)
  · exact fun x hx => (mem_iff_cj (hab j) (hba j) (h1 j) (h2 j) x).1 hx.1
  · refine isBounded_iff_forall_norm_le.2
      ⟨dd k r * (dd k r * sn (a j) * (dd k r * M * 2)) * sn (a j)⁻¹, fun x hx => ?_⟩
    have hb := sn_mul_le (sn_mul_le (le_refl (sn (a j))) (AA_bound hH hM hx)) (le_refl (sn (a j)⁻¹))
    have : a j * Matrix.of (ψ j x) * (a j)⁻¹ = Matrix.of x := (ψ j).left_inv x
    rw [this] at hb
    exact hb
  · rw [hmeas]; exact ENNReal.mul_pos (hc0 j).ne' hA0.ne'
  · rw [hmeas]; exact ENNReal.mul_lt_top (hct j) hAt
  intro C hC hCS
  obtain ⟨K, hK0, hK⟩ := exists_bound hC
  have hd := dd_nonneg (k := k) (r := r)
  set L : ℝ := dd k r * (dd k r * (dd k r * M * (dd k r * M * K + 1)) * M) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨fun j => ψ j ⁻¹' AA (Sset k r z) (UWset k r z) (2 / (1 + L * ((j : ℝ) + 1)⁻¹)),
    fun j => ⟨hψm j (measurableSet_AA hS.2.1 _ _), ?_, ?_⟩, ?_⟩
  · refine Set.preimage_mono (AA_mono _ _ ?_)
    have : 0 ≤ L * ((j : ℝ) + 1)⁻¹ := by positivity
    exact div_le_self (by norm_num) (by linarith)
  · intro s hs x hx
    obtain ⟨h, hh, m, hm, rfl⟩ := hCS hs
    have hmb : sn (m - 1) ≤ dd k r * M * K + 1 := by
      have : m = h⁻¹ * (h * m) := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh)), one_mul]
      have hb := sn_mul_le (hM _ (hH.2.2.2.2 _ hh)) (hK _ hs)
      rw [← this] at hb
      linarith [sn_sub_le m 1, sn_one_le (k := k) (r := r)]
    have hm' : sn ((a j)⁻¹ * m * a j - 1) ≤ ((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1) := by
      refine sn_le (by positivity) fun p q => (hd2 _ (by simp) m hm p q).trans ?_
      exact mul_le_mul_of_nonneg_left ((entry_le _ p q).trans hmb) (by positivity)
    have hmem := lmulM_mem_AA hS hH hM hx hh hm' (e2 j h hh m ▸ h2 j _ (hCS hs))
    have e : ψ j (lmulM (h * m) x) = lmulM (h * ((a j)⁻¹ * m * a j)) (ψ j x) := by
      rw [← e2 j h hh m]
      show (a j)⁻¹ * (h * m * Matrix.of x) * a j =
        (a j)⁻¹ * (h * m) * a j * ((a j)⁻¹ * Matrix.of x * a j)
      simp only [mul_assoc]
      rw [← mul_assoc (a j) (a j)⁻¹, hab, one_mul]
    have et : 2 / (1 + L * ((j : ℝ) + 1)⁻¹) * (1 + dd k r * (dd k r * (dd k r * M *
        (((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1))) * M)) = 2 := by
      have : dd k r * (dd k r * (dd k r * M * (((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1))) * M) =
          L * ((j : ℝ) + 1)⁻¹ := by rw [hL]; ring
      rw [this]
      exact div_mul_cancel₀ _ (by positivity)
    rw [et, ← e] at hmem
    exact hmem
  · have := ENNReal.Tendsto.div_const (tendsto_AA (Sset k r z) (UWset k r z) μ hL0)
      (b := μ (AA (Sset k r z) (UWset k r z) 2)) (Or.inr hA0.ne')
    rw [ENNReal.div_self hA0.ne' hAt.ne] at this
    refine this.congr fun j => ?_
    rw [hmeas, hmeas, ENNReal.mul_div_mul_left _ _ (hc0 j).ne' (hct j).ne]

end GlobalTheory.SgInf.FolnerSets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBesselStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFolnerSequenceBessel : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  first | exact @GlobalTheory.SgInf.FolnerSets.exists_isFolner | exact GlobalTheory.SgInf.FolnerSets.exists_isFolner | (intros; apply GlobalTheory.SgInf.FolnerSets.exists_isFolner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatou
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FatouI

theorem lintegral_le_of_liminf {X : Type*} [MeasurableSpace X] (ν : Measure X) (F : X → ENNReal)
    (g : ℕ → X → ENNReal) (hg : ∀ j, Measurable (g j))
    (hF : ∀ᵐ γ ∂ν, F γ ≤ Filter.liminf (fun j => g j γ) Filter.atTop) (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ j, ∫⁻ γ, g j γ ∂ν = ENNReal.ofReal (b j))
    (hL : Filter.Tendsto b Filter.atTop (nhds L)) : ∫⁻ γ, F γ ∂ν ≤ ENNReal.ofReal L := by
  refine (lintegral_mono_ae hF).trans ((lintegral_liminf_le hg).trans ?_)
  simp_rw [hb]
  exact (ENNReal.tendsto_ofReal hL).liminf_eq.le

variable {k r : ℕ}

theorem measurable_besselTwoSidedAction_joint :
    Measurable fun q : Mt k r × (Mt k r × Mt k r) => act2 (Matrix.of q.1) q.2 := by
  let m : Mt k r × Mt k r → Mt k r := fun q => lmulM (Matrix.of q.1) q.2
  have hmul : Continuous m :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hm : Measurable m := hmul.measurable
  have h1 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (q.2.1, q.1) :=
    hm.comp (measurable_snd.fst.prodMk measurable_fst)
  have h2 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => invM q.2.2 :=
    measurable_invM.comp measurable_snd.snd
  have h3 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (m (q.2.1, q.1), invM q.2.2) :=
    hm.comp (h1.prodMk h2)
  exact h3

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem DD_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : IsURepOn (GG k r) σ) (hG : IsClosedSub k r (GG k r)) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, rfl⟩ := hv
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact (DD σ w).add_mem hu hv
  | smul a v _ hv => rw [map_smul]; exact (DD σ w).smul_mem a hv

theorem integrable_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) {S : Set (Mat k r)} (hS : IsClosedSub k r S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {a C : ℝ} (hfin : normInt μ a < ⊤) (u v : H)
    (hC : ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)) :
    Integrable (fun p : Mt k r => coef σ u v (Matrix.of p)) μ := by
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have hSm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
    IsClosed.measurableSet (α := Mt k r) hS.2.1
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun p : Mt k r => coef σ u v (Matrix.of p))
        {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
      ContinuousOn.inner (𝕜 := ℂ) continuousOn_const ((hσ.2.2 u).mono hS.1)
    have := hc.aestronglyMeasurable (μ := μ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p : Mt k r | (Matrix.of p : Mat k r) ∈ S}) hae] at this
  · refine lt_of_le_of_lt (b := ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (opn (Matrix.of x) ^ (-a)) ∂μ)
      (lintegral_mono_ae ?_) ?_
    · filter_upwards [hae] with p hp
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (opn_nonneg _) _), ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC _ (hS.1 hp))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem dis_of_continuousOn {Ω S S' : Set (Mat k r)} {μG μS μS' ν : Measure (Mt k r)}
    (hG : IsClosedSub k r (GG k r)) (hS : IsClosedSub k r S) (hS' : IsClosedSub k r S')
    (hμG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn S μS) (hμ' : IsHaarOn S' μS') (hΩ : Ω ⊆ GG k r)
    (hν : IsDis Ω μG μS μS' ν) (f : Mat k r → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf : ContinuousOn f (GG k r))
    (hfi : Integrable (fun g : Mt k r => f (Matrix.of g)) μG) :
    ∃ g : Mt k r → ENNReal, Measurable g ∧
      (∀ γ : Mt k r, Matrix.of γ ∈ Ω →
        g γ = ∫⁻ p, ENNReal.ofReal (f (Matrix.of (act2 (Matrix.of γ) p))) ∂(μS.prod μS')) ∧
      ∫⁻ γ, g γ ∂ν = ENNReal.ofReal (∫ g, f (Matrix.of g) ∂μG) := by
  classical
  haveI := hμ.1
  haveI := hμ'.1
  have hGm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) hG.2.1
  let f0 : Mt k r → ℝ := {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r}.piecewise
    (fun p => f (Matrix.of p)) (fun _ => 0)
  have hf0m : Measurable f0 :=
    ContinuousOn.measurable_piecewise (f := fun p : Mt k r => f (Matrix.of p)) hf continuousOn_const hGm
  have hf0e : ∀ p : Mt k r, Matrix.of p ∈ GG k r → f0 p = f (Matrix.of p) := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ hp
  have hF : Measurable fun p => ENNReal.ofReal (f0 p) := hf0m.ennreal_ofReal
  refine ⟨fun γ => ∫⁻ p, ENNReal.ofReal (f0 (act2 (Matrix.of γ) p)) ∂(μS.prod μS'), ?_, ?_, ?_⟩
  · exact (hF.comp measurable_besselTwoSidedAction_joint).lintegral_prod_right'
  · intro γ hγ
    have h1 : ∀ᵐ p ∂μS, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
    have h2 : ∀ᵐ p ∂μS', (Matrix.of p : Mat k r) ∈ S' := hμ'.2.2.1
    have h1' := Measure.quasiMeasurePreserving_fst (μ := μS) (ν := μS') |>.ae h1
    have h2' := Measure.quasiMeasurePreserving_snd (μ := μS) (ν := μS') |>.ae h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1', h2'] with p hp hp'
    rw [hf0e]
    exact hG.2.2.2.1 _ (hG.2.2.2.1 _ (hS.1 hp) _ (hΩ hγ)) _ (hG.2.2.2.2 _ (hS'.1 hp'))
  · rw [← hν.2.2 _ hF, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun g => hf0 _)]
    have h1 : ∀ᵐ p ∂μG, (Matrix.of p : Mat k r) ∈ GG k r := hμG.2.2.1
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with p hp
    rw [hf0e p hp]

end GlobalTheory.SgInf.FatouI


open GlobalTheory.SgInf.FatouI in
theorem GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' ν hν x hx y hy ξ ξ'
  obtain ⟨hG, -, -, hS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSd.1 hSd.2.1
  obtain ⟨-, -, -, hS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hSd'.1 hSd'.2.1
  obtain ⟨Om, hOm⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z μS hSd.1 hSd.2.1 hSd.2.2.2.1
  obtain ⟨Om', hOm'⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z' μS' hSd'.1 hSd'.2.1 hSd'.2.2.2.1
  have hdec := hStd.2.2.2.2.2.2.2.1
  have ha : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    have h1 : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
      have := hStd.1
      exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    have := hStd.2.2.2.2.2.2.1
    linarith
  have hiy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS := by
    obtain ⟨C, hC⟩ := hdec y hy y hy
    exact integrable_coef σ hStd.2.1 hS hSd.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS a hS hSd.2.2.2.1 ha) y y hC
  have hix : Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' := by
    obtain ⟨C, hC⟩ := hdec x hx x hx
    exact integrable_coef σ hStd.2.1 hS' hSd'.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS' a hS' hSd'.2.2.2.1 ha) x x hC
  have h62 := fun j => GlobalTheory.T.bessel_functional_two_sided k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' x y ξ ξ' (Om j) (Om' j)
    (hOm.1 j).1 (hOm'.1 j).1 (hOm.1 j).2.2.2.2 (hOm'.1 j).2.2.2.2 hiy hix
  have h63 := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z c π μS hStd hSd Om hOm y hy ξ
  have h63' := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z' c' π' μS' hStd hSd' Om' hOm' x hx ξ'
  have h64 := GlobalTheory.T.hsNormSq_Iint_le_liminf_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' Om Om' hOm hOm' x hx y hy ξ ξ'
  have hadj := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSd (DD σ w) (DD_stable σ w hStd.2.1 hG) hdec
    y hy y hy).2.2.1
  have him : (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hadj]
  have hcont : Continuous (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) := by
    have : (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 :=
      funext hsNormSq_eq_sum
    rw [this]
    fun_prop
  have hnn : ∀ A : Wq →L[ℂ] Wp, 0 ≤ hsNormSq A := fun A => by
    rw [hsNormSq_eq_sum]; positivity
  have hdis := fun j => dis_of_continuousOn hG hS hS' hStd.2.2.2.2.1 hSd.2.2.2.1 hSd'.2.2.2.1
    (Greg_subset z z') hν (fun g => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' g)) (fun g => hnn _)
      (hcont.comp_continuousOn (h62 j).1) (h62 j).2.1
  choose g hgm hge hgi using hdis
  have hpos : ∀ j, 0 < (μS (Om j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm.1 j).2.2.2.1.ne' (hOm.1 j).2.2.2.2.ne
  have hpos' : ∀ j, 0 < (μS' (Om' j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm'.1 j).2.2.2.1.ne' (hOm'.1 j).2.2.2.2.ne
  refine lintegral_le_of_liminf ν _ (fun j γ => g j γ / (μS (Om j) * μS' (Om' j)))
    (fun j => (hgm j).div_const _) ?_
    (fun j => (∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of g)) ∂μG) /
        ((μS (Om j)).toReal * (μS' (Om' j)).toReal)) _ ?_ ?_
  · have h1 : ∀ᵐ γ ∂ν, (Matrix.of γ : Mat k r) ∈ Greg k r z z' := hν.2.1
    filter_upwards [h1] with γ hγ
    simp_rw [fun j => hge j γ hγ]
    exact h64 _ hγ
  · intro j
    simp_rw [div_eq_mul_inv (g j _)]
    rw [lintegral_mul_const _ (hgm j), hgi j, ENNReal.ofReal_div_of_pos (mul_pos (hpos j) (hpos' j)),
      ENNReal.ofReal_mul (hpos j).le, ENNReal.ofReal_toReal (hOm.1 j).2.2.2.2.ne,
      ENNReal.ofReal_toReal (hOm'.1 j).2.2.2.2.ne, div_eq_mul_inv]
  · have hT := (Complex.continuous_re.tendsto _).comp ((h63.const_mul ((d : ℂ)⁻¹)).mul h63')
    convert hT using 2 with j
    · have e := (h62 j).2.2
      rw [Function.comp_apply, ← mul_div_assoc (d : ℂ)⁻¹, div_mul_div_comm, ← e]
      norm_cast
    · rw [← Complex.ofReal_inv, mul_assoc (_ : ℂ), Complex.re_ofReal_mul, Complex.mul_re, him]
      ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatouStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  first | exact @GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | exact GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | (intros; apply GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le <;> assumption)
end
