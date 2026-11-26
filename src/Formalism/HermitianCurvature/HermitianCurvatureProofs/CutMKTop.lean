module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopBump
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopBump

theorem bump_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f g : E → ℂ) (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x, (b x : ℂ) * f x ∂μ) ≠ 0 ∧
      (∫ x, (b x : ℂ) * g x ∂μ) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (1 / 2 : ℝ) (by norm_num)
  obtain ⟨δ', hδ', hδg⟩ := Metric.continuousAt_iff.1 hg.continuousAt (1 / 2 : ℝ) (by norm_num)
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  let B : ContDiffBump (0 : E) := ⟨min δ δ' / 4, min δ δ' / 2, by positivity, by linarith⟩
  set b : E → ℝ := fun x => B x with hbdef
  have hbd : ContDiff ℝ ∞ b := B.contDiff
  have hbc : HasCompactSupport b := B.hasCompactSupport
  have hbnn : ∀ x, 0 ≤ b x := fun x => B.nonneg
  have hbcont : Continuous b := B.continuous
  have hbint : 0 < ∫ x, b x ∂μ := B.integral_pos
  have hbs : tsupport b ⊆ Metric.ball (0 : E) (min δ δ') := by
    rw [show tsupport b = Metric.closedBall (0 : E) (min δ δ' / 2) from B.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  have aux : ∀ h : E → ℂ, Continuous h →
      (∀ x, dist x 0 < min δ δ' → ‖h x - 1‖ < 1 / 2) → (∫ x, (b x : ℂ) * h x ∂μ) ≠ 0 := by
    intro h hh hs
    have hbC : Continuous (fun x => (b x : ℂ)) := Complex.continuous_ofReal.comp hbcont
    have hbcC : HasCompactSupport (fun x => (b x : ℂ)) := hbc.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun x => (b x : ℂ)) μ := hbC.integrable_of_hasCompactSupport hbcC
    have hi2 : Integrable (fun x => (b x : ℂ) * (h x - 1)) μ :=
      (hbC.mul (hh.sub continuous_const)).integrable_of_hasCompactSupport (hbcC.mul_right)
    have hi3 : Integrable (fun x => b x * (1 / 2 : ℝ)) μ :=
      (hbcont.integrable_of_hasCompactSupport hbc).mul_const _
    have split : (∫ x, (b x : ℂ) * h x ∂μ) = (∫ x, (b x : ℂ) ∂μ) + ∫ x, (b x : ℂ) * (h x - 1) ∂μ := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext x
      ring
    have hbound : ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ ≤ ∫ x, b x * (1 / 2 : ℝ) ∂μ := by
      refine norm_integral_le_of_norm_le hi3 (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn x)]
      by_cases hbx : b x = 0
      · rw [hbx]; simp
      · have hx : x ∈ Metric.ball (0 : E) (min δ δ') := hbs (subset_tsupport _ hbx)
        exact mul_le_mul_of_nonneg_left (hs x hx).le (hbnn x)
    have hreal : (∫ x, (b x : ℂ) ∂μ) = ((∫ x, b x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [integral_mul_const] at hbound
    intro h0
    rw [split, hreal] at h0
    have e1 : ((∫ x, b x ∂μ : ℝ) : ℂ) = -∫ x, (b x : ℂ) * (h x - 1) ∂μ := eq_neg_of_add_eq_zero_left h0
    have e2 : ‖((∫ x, b x ∂μ : ℝ) : ℂ)‖ = ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ := by rw [e1, norm_neg]
    rw [Complex.norm_real, Real.norm_of_nonneg hbint.le] at e2
    linarith
  refine ⟨b, hbd, hbc, aux f hf fun x hx => ?_, aux g hg fun x hx => ?_⟩
  · have := hδf (lt_of_lt_of_le hx (min_le_left _ _))
    rwa [hf0, dist_eq_norm] at this
  · have := hδg (lt_of_lt_of_le hx (min_le_right _ _))
    rwa [hg0, dist_eq_norm] at this

local instance bsS {p : ℕ} : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC {k p ρ : ℕ} : BorelSpace (U.RC k p ρ) := Prod.borelSpace

theorem piHaar {n p : ℕ} : (volume : Measure (Fin n → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

theorem rcHaar {k p ρ : ℕ} : (volume : Measure (U.RC k p ρ)).IsAddHaarMeasure := by
  have := @piHaar (2 * ρ + k + 1) p
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem bump_exists {k p ρ : ℕ} (z z' : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (hz' : inWb k ρ z') :
    ∃ b : U.RC k p ρ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)) ≠ 0 ∧
      (∫ x, (b x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)) ≠ 0 := by
  have hc : Continuous (fun x : U.RC k p ρ => psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x)) :=
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)
  have hc' : Continuous (fun x : U.RC k p ρ => star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x))) :=
    ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)).star
  have h0 : psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ 0) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero]
    exact Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz) _
  have h0' : star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ 0)) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz') _, star_one]
  have := @rcHaar k p ρ
  unfold U.muRC
  exact bump_two volume _ _ hc hc' h0 h0'

end Formalism.FourierDecayAlt.P.CutEX.MkTopBump
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTC
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTB
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTA
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopCut
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

def MkTopCut : Prop :=
  ∀ r : ℕ, ∃ β : (Fin r → Fin r → ℂ) → ℝ,
    ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
    (∀ Z : Fin r → Fin r → ℂ, (Matrix.of Z).det ≠ 0 →
      Integrable (fun v : G.UT r → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) ∧
        ∫ v : G.UT r → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1) ∧
    ∀ (X : Type) [TopologicalSpace X] (K : Set ((Fin r → Fin r → ℂ) × X)), IsCompact K →
      (∀ q ∈ K, (Matrix.of q.1).det ≠ 0) →
      ∃ K' : Set ((Fin r → Fin r → ℂ) × X), IsCompact K' ∧
        (∀ q ∈ K', (Matrix.of q.1).det ≠ 0 ∧ ∃ q₀ ∈ K, q.2 = q₀.2) ∧
        ∀ q : (Fin r → Fin r → ℂ) × X, (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
          (∃ u : Matrix (Fin r) (Fin r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
          q ∈ K'

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem sum_lt_castLE {j : ℕ} (hj : j ≤ n) (f : Fin n → ℂ) :
    ∑ i : Fin n, (if i.val < j then f i else 0) = ∑ b : Fin j, f (Fin.castLE hj b) := by
  rw [← Finset.sum_filter]
  have e : (Finset.univ.filter fun i : Fin n => i.val < j) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩; simp
  rw [e, Finset.sum_map]
  rfl

def gram (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Zᴴ * Z

def blkJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => A (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)

def colJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Fin j → ℂ := fun a => A (Fin.castLE j.isLt.le a) j

def Wm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  if h : i.val < j.val then -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) ⟨i.val, h⟩) else if i = j then 1 else 0

theorem Wm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [Wm, Matrix.of_apply]
    rw [dif_neg (by have : j.val < i.val := h; omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h)]
  · simp [Wm]

theorem mul_col_split (A V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ C2.UTset n) (l j : Fin n) :
    (A * V) l j = ∑ b : Fin j, A l (Fin.castLE j.isLt.le b) * V (Fin.castLE j.isLt.le b) j + A l j := by
  rw [Matrix.mul_apply, ← sum_lt_castLE j.isLt.le (fun i => A l i * V i j)]
  have hsplit : ∀ i : Fin n, A l i * V i j = (if i.val < j.val then A l i * V i j else 0) +
      (if i = j then A l j else 0) := by
    intro i
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [if_pos h, if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), add_zero]
    · have e : i = j := Fin.ext h
      subst e
      rw [if_neg (lt_irrefl _), if_pos rfl, hV.2, mul_one, zero_add]
    · rw [if_neg (by omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), hV.1 i j h, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem blk_gram_eq (Z : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blkJ (gram Z) j = (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b))ᴴ *
      Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b) := by
  ext a b
  simp [blkJ, gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem blk_det_ne {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (j : Fin n) : (blkJ (gram Z) j).det ≠ 0 := by
  rw [blk_gram_eq]
  refine (Matrix.PosDef.det_pos (Matrix.PosDef.conjTranspose_mul_self _ ?_)).ne'
  intro x y hxy
  set ex : (Fin j → ℂ) → Fin n → ℂ := fun x l => if h : l.val < j.val then x ⟨l.val, h⟩ else 0 with hex
  have hm : ∀ x : Fin j → ℂ, (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b)) *ᵥ x = Z *ᵥ ex x := by
    intro x
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    set f : Fin n → ℂ := fun l => Z a l * ex x l with hf
    calc ∑ b : Fin j, Z a (Fin.castLE j.isLt.le b) * x b = ∑ b : Fin j, f (Fin.castLE j.isLt.le b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hf, hex, Fin.val_castLE, dif_pos b.isLt]
      _ = ∑ l : Fin n, (if l.val < j.val then f l else 0) := (sum_lt_castLE _ f).symm
      _ = ∑ l : Fin n, f l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases h : l.val < j.val
          · rw [if_pos h]
          · rw [if_neg h]; simp only [hf, hex, dif_neg h, mul_zero]
  rw [hm, hm] at hxy
  have hinj : Function.Injective (Z *ᵥ ·) := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr hZ))
  have := hinj hxy
  funext a
  have h2 := congrFun this (Fin.castLE j.isLt.le a)
  simp only [hex, Fin.val_castLE, dif_pos a.isLt] at h2
  exact h2

theorem Wm_spec {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (l j : Fin n) (hlj : l.val < j.val) :
    (gram Z * Wm Z) l j = 0 := by
  rw [mul_col_split _ _ (Wm_ut Z)]
  have hBc : blkJ (gram Z) j *ᵥ ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) = colJ (gram Z) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)), Matrix.one_mulVec]
  have hrow := congrFun hBc ⟨l.val, hlj⟩
  simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply] at hrow
  have hl : Fin.castLE j.isLt.le ⟨l.val, hlj⟩ = l := Fin.ext rfl
  rw [hl] at hrow
  have hW : ∀ b : Fin j, Wm Z (Fin.castLE j.isLt.le b) j =
      -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) b) := by
    intro b
    simp only [Wm, Matrix.of_apply, Fin.val_castLE, dif_pos b.isLt, Fin.eta]
  simp only [hW, mul_neg, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin j, gram Z l (Fin.castLE j.isLt.le x) * ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) x =
      gram Z l j from hrow]
  ring

theorem Wm_unique {Z V : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hV : V ∈ C2.UTset n)
    (hlow : ∀ l j : Fin n, l.val < j.val → (gram Z * V) l j = 0) : V = Wm Z := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hu : IsUnit (blkJ (gram Z) j).det := isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)
    set x : Fin j → ℂ := fun b => V (Fin.castLE j.isLt.le b) j with hx
    have hB : blkJ (gram Z) j *ᵥ x = -colJ (gram Z) j := by
      ext a
      have h0 := hlow (Fin.castLE j.isLt.le a) j (by simp [a.isLt])
      rw [mul_col_split _ _ hV] at h0
      simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply, hx, Pi.neg_apply]
      linear_combination h0
    have hx' : x = -((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) := by
      have e : x = (blkJ (gram Z) j)⁻¹ *ᵥ (blkJ (gram Z) j *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      rw [e, hB, Matrix.mulVec_neg]
    have h1 := congrFun hx' ⟨i.val, h⟩
    simp only [hx, Pi.neg_apply] at h1
    rw [show Fin.castLE j.isLt.le ⟨i.val, h⟩ = i from Fin.ext rfl] at h1
    rw [h1]
    simp only [Wm, Matrix.of_apply, dif_pos h]
  · have e : i = j := Fin.ext h
    subst e
    rw [hV.2, (Wm_ut Z).2]
  · rw [hV.1 i j h, (Wm_ut Z).1 i j h]

theorem gram_mul (Z u : Matrix (Fin n) (Fin n) ℂ) : gram (Z * u) = uᴴ * gram Z * u := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem Wm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Wm (Z * u) = u⁻¹ * Wm Z := by
  have hZu : (Z * u).det ≠ 0 := by rw [Matrix.det_mul, C2x2.ut_det hu, mul_one]; exact hZ
  refine (Wm_unique hZu (C2x2.ut_mul (C2x2.ut_inv hu) (Wm_ut Z)) ?_).symm
  intro l j hlj
  rw [gram_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ l.val
  · rw [Wm_spec hZ i j (by omega), mul_zero]
  · rw [Matrix.conjTranspose_apply, hu.1 i l (by show l.val < i.val; omega), star_zero, zero_mul]

def Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Wm Z).adjugate

theorem Sm_eq_inv (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z = (Wm Z)⁻¹ := by
  rw [Sm, Matrix.inv_def, C2x2.ut_det (Wm_ut Z), Ring.inverse_one, one_smul]

theorem Sm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z ∈ C2.UTset n := by
  rw [Sm_eq_inv]; exact C2x2.ut_inv (Wm_ut Z)

theorem Sm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Sm (Z * u) = Sm Z * u := by
  rw [Sm_eq_inv, Sm_eq_inv, Wm_mul hZ hu, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (C2x2.ut_unit hu)]

theorem Wm_mul_Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z * Sm Z = 1 := by
  rw [Sm_eq_inv]; exact Matrix.mul_nonsing_inv _ (C2x2.ut_unit (Wm_ut Z))

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

noncomputable section

open Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

section cd

variable {m : ℕ}

theorem cd_det : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => by fun_prop

theorem cd_adj (i j : Fin m) : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) := by
  have h : (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) =
      (fun N : Fin m → Fin m → ℂ => (Matrix.of N).det) ∘
        (fun M : Fin m → Fin m → ℂ => fun a b => (Matrix.of M).updateRow j (Pi.single i 1) a b) := by
    funext M
    rw [Matrix.adjugate_apply]
    rfl
  rw [h]
  refine cd_det.comp ?_
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.updateRow_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem cd_inv (i j : Fin m) :
    ContDiffOn ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M)⁻¹ i j) {M | (Matrix.of M).det ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞
      (fun M : Fin m → Fin m → ℂ => ((Matrix.of M).det)⁻¹ * (Matrix.of M).adjugate i j)
      {M | (Matrix.of M).det ≠ 0} :=
    (cd_det.contDiffOn.inv fun M hM => hM).mul (cd_adj i j).contDiffOn
  refine h1.congr fun M _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]

end cd

section wm

variable {n : ℕ}

theorem cd_gram (a b : Fin n) : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => gram (Matrix.of Z) a b) := by
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ (by fun_prop)
  exact Complex.conjCLE.contDiff.comp
    (by fun_prop : ContDiff ℝ ∞ fun Z : Fin n → Fin n → ℂ => Z k a)

private lemma det_gram_castLE_ne_zero_of_det_ne_zero (Z : Fin n → Fin n → ℂ) (hZ : (Matrix.of Z).det ≠ 0) (k : ℕ)
    (hk : k ≤ n) :
    (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)).det ≠ 0 := by
  set E : Matrix (Fin n) (Fin k) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hk) with hE
  set A : Matrix (Fin n) (Fin k) ℂ := Matrix.of Z * E with hA
  have hA' : ∀ r a, A r a = Z r (Fin.castLE hk a) := by
    intro r a
    simp [hA, hE, Matrix.mul_apply, Matrix.one_apply]
  have hB : (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)) =
      Aᴴ * A := by
    ext a b
    simp only [Matrix.of_apply, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, hA']
  rw [hB]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : A *ᵥ v = 0 := by
    open scoped ComplexOrder in
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero A v).1 hv
  have h2 : E *ᵥ v = 0 := by
    by_contra hne
    apply hZ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨E *ᵥ v, hne, ?_⟩
    rw [Matrix.mulVec_mulVec, ← hA, h1]
  apply hv0
  funext a
  have := congrFun h2 (Fin.castLE hk a)
  simpa [hE, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.castLE_inj] using this

theorem cd_Wm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Wm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  simp only [Wm, blkJ, colJ, Matrix.of_apply]
  by_cases hij : (i : ℕ) < j
  · simp only [dif_pos hij, Matrix.mulVec, dotProduct, Pi.neg_apply]
    have hg : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b : Fin j =>
        gram (Matrix.of Z) (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_gram _ _
    refine ContDiffOn.neg (ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ (cd_gram _ _).contDiffOn)
    exact (cd_inv (m := j) ⟨i, hij⟩ c).comp hg.contDiffOn fun Z hZ => det_gram_castLE_ne_zero_of_det_ne_zero Z hZ j j.isLt.le
  · simp only [dif_neg hij]
    split_ifs <;> exact contDiffOn_const

theorem cd_Sm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Sm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  have hW : ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b => Wm (Matrix.of Z) a b)
      {Z | (Matrix.of Z).det ≠ 0} :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => cd_Wm a b
  exact (cd_adj i j).comp_contDiffOn hW

end wm

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem upper_utc {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ∈ C2.UTset n) : G.upper (StabilizerDisintegration.utc M) = M := by
  ext i j
  simp only [G.upper, G.strictUpper, StabilizerDisintegration.utc, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dite_eq_left h, if_neg (ne_of_lt h), zero_add]
  · rw [dite_eq_right (lt_irrefl _), if_pos rfl, hM.2, add_zero]
  · rw [dite_eq_right (not_lt.2 h.le), if_neg (ne_of_gt h), hM.1 i j h, add_zero]

theorem upper_ut (v : G.UT n → ℂ) : G.upper v ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [G.upper, G.strictUpper, not_lt.2 h.le, ne_of_gt h]
  · simp [G.upper, G.strictUpper]

section gam

variable {r : ℕ} {X : Type}

def Gam (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) : (Fin r → Fin r → ℂ) × X :=
  (Matrix.of.symm (Matrix.of p.1.1 * Wm (Matrix.of p.1.1) * G.upper p.2), p.1.2)

theorem Gam_det (p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)) :
    (Matrix.of (Gam p).1).det = (Matrix.of p.1.1).det := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Matrix.det_mul, Matrix.det_mul, C2x2.ut_det (Wm_ut _), C2x2.ut_det (upper_ut p.2), mul_one, mul_one]

theorem Gam_eq (q : (Fin r → Fin r → ℂ) × X) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (Matrix.of q.1).det ≠ 0)
    (hu : u ∈ C2.UTset r) : Gam ((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))) = q := by
  simp only [Gam, Equiv.apply_symm_apply]
  rw [Wm_mul hdet hu, upper_utc (Sm_ut _), Matrix.mul_assoc (Matrix.of q.1) u,
    Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc, Wm_mul_Sm, Matrix.mul_one]
  rfl

theorem Gam_cont [TopologicalSpace X] (S : Set (((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ)))
    (hS : ∀ p ∈ S, (Matrix.of p.1.1).det ≠ 0) : ContinuousOn Gam S := by
  have hW : ∀ a b : Fin r, ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) => Wm (Matrix.of p.1.1) a b) S :=
    fun a b => (cd_Wm a b).continuousOn.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hS p hp
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_)
    (continuous_snd.comp continuous_fst).continuousOn
  have e : ∀ p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ),
      (Gam p).1 a b = ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b := by
    intro p
    simp only [Gam]
    rfl
  have key : ContinuousOn (fun p : ((Fin r → Fin r → ℂ) × X) × (G.UT r → ℂ) =>
      ∑ c : Fin r, (∑ d : Fin r, p.1.1 a d * Wm (Matrix.of p.1.1) d c) * G.upper p.2 c b) S := by
    refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul (continuousOn_finsetSum _ fun d _ => ?_) ?_
    · exact (((continuous_apply_apply a d).comp (continuous_fst.comp continuous_fst)).continuousOn).mul (hW d c)
    · exact ((continuous_apply_apply c b).comp (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)).continuousOn
  exact key.congr fun p _ => e p

end gam

theorem top_truncation_construction : MkTopCut := by
  intro r
  let φ : ContDiffBump (0 : G.UT r → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set β₀ : (G.UT r → ℂ) → ℝ := φ.normed volume with hβ₀
  have hcont : Continuous β₀ := φ.continuous_normed
  refine ⟨fun Z => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z))), ?_, ?_, ?_⟩
  · have hS : ContDiffOn ℝ ∞ (fun Z : Fin r → Fin r → ℂ => StabilizerDisintegration.utc (Sm (Matrix.of Z)))
        {Z | (Matrix.of Z).det ≠ 0} :=
      contDiffOn_pi.2 fun q => cd_Sm q.1.1 q.1.2
    exact (φ.contDiff_normed (n := ⊤)).comp_contDiffOn hS
  · intro Z hZ
    have hmp := Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (Sm_ut (Matrix.of Z))
    have hfun : (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) =
        fun v => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of Z) * G.upper v)) := by
      funext v
      simp only [Equiv.apply_symm_apply]
      rw [Sm_mul hZ (upper_ut v)]
    show Integrable (fun v : G.UT r → ℂ => β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v)))))) ∧
      ∫ v : G.UT r → ℂ, β₀ (StabilizerDisintegration.utc (Sm (Matrix.of (Matrix.of.symm (Matrix.of Z * G.upper v))))) = 1
    rw [hfun]
    constructor
    · have hi := (integrable_map_measure hcont.aestronglyMeasurable hmp.measurable.aemeasurable).1
        (by rw [hmp.map_eq]; exact φ.integrable_normed)
      exact hi
    · rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]
      exact φ.integral_normed
  · intro X _ K hK hKdet
    have hC₀ : IsCompact (tsupport β₀) := φ.hasCompactSupport_normed
    refine ⟨Gam '' (K ×ˢ tsupport β₀), (hK.prod hC₀).image_of_continuousOn (Gam_cont _ fun p hp => hKdet _ hp.1), ?_, ?_⟩
    · rintro q ⟨⟨q', c⟩, ⟨hq', -⟩, rfl⟩
      exact ⟨by rw [Gam_det]; exact hKdet q' hq', q', hq', rfl⟩
    · rintro q hdet hβ ⟨u, hu, hK'⟩
      have huT : u ∈ C2.UTset r := ⟨fun i j h => hu.1 h, hu.2⟩
      exact ⟨((Matrix.of.symm (Matrix.of q.1 * u), q.2), StabilizerDisintegration.utc (Sm (Matrix.of q.1))),
        ⟨hK', subset_tsupport _ hβ⟩, Gam_eq q u hdet huT⟩

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

theorem psi_cast {k a b : ℕ} (e : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV e v) c (D.castM e g) = psi k a v c g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem top_construction : TopMk := by
  intro hC Wp Wq _ _ _ _ _ _ P p
  have hT := p.hT
  have hr : P.r ≤ P.r := le_rfl
  have e0 : P.r + (P.r - P.r) = P.r := by omega
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  obtain ⟨b, hbs, hbc, hκL, hκR⟩ := Formalism.FourierDecayAlt.P.CutEX.MkTopBump.bump_exists (k := P.k) (p := P.r) (ρ := P.r - P.r)
    (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem
  obtain ⟨β, hβs, hβi, hβK⟩ := Formalism.FourierDecayAlt.P.CutEXMT.top_truncation_construction P.r
  refine ⟨b, b, β, kapL (p.T.bs P.r).z b * kapR (p.T.bs P.r).z' b, hbs, hbc, hbs, hbc, mul_ne_zero hκL hκR, hβs,
    ?_, ?_⟩
  · intro K hK hKU
    obtain ⟨K', hK', hK'1, hK'2⟩ := hβK (Mt P.k (P.r - P.r)) K hK (fun q hq => (hKU hq).1)
    refine ⟨K', hK', fun q hq => ?_, hK'2⟩
    obtain ⟨hd, q₀, hq₀, he⟩ := hK'1 q hq
    exact ⟨hd, he ▸ (hKU hq₀).2⟩
  · intro Φ hΦL hΦU Z y hZ hy
    have hyG : (Matrix.of y : B.Mat P.k (P.r - P.r)) ∈ B.GV P.k (P.r - P.r) :=
      (Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).1 hy
    have hz : p.T.base.z' = D.castV e0 (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') := (p.T.z'_lev P.r hr).symm
    have hpsi : ∀ u : G.UT P.r → ℂ, CutEX.psiU p (G.upper u) =
        psi P.k (P.r + (P.r - P.r)) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') cStd
          (U.muP P.k P.r (P.r - P.r) (G.upper u)) := by
      intro u
      unfold CutEX.psiU
      rw [hz]
      exact psi_cast e0 _ _ _
    have key := hC P.k P.r (P.r - P.r) P.r Wp Wq e0 hρ (p.T.bs P.r) p.T.base (p.T.z'_lev P.r hr)
      (p.T.π'_lev P.r hr) (hT P.r hr).1 (hT P.r hr).2.1 (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT P.r hr e0)
      (hT P.r hr).2.2 (hT 0 (Nat.zero_le _)).2.2 b b β Φ hbs.continuous hbc hbs.continuous hbc Z hZ
      (hβi Z hZ).1 (hβi Z hZ).2 y hyG (fun h1 hh1 h2 hh2 => hΦL Z y hy h1 hh1 h2 hh2)
      (fun u y' hy' => by
        rw [hΦU Z y' (G.upper u) hZ ((Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).2 hy')
          (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.upper_isUpUni u), hpsi u])
    exact key

theorem mkTop_of_avgs (hR : RightAvg) (hL : LeftAvg) : CutEX.MkTop := mkTop_of_leaves hR hL top_construction

end Formalism.FourierDecayAlt.P.CutMK
