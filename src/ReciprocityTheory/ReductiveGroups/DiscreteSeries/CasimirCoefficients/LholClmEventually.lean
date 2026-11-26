module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMLocal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasPsB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasLPsM
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem casL_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, DifferentiableOn ℂ (Lhol X (psM T μ)) U) ∧
      ∀ z ∈ U, casL (psM T μ) z = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
  have := compactSpace_KG ε
  have hh := psM_holo T μ
  rcases hh with ⟨U, hUo, hpos, hΩ, hdiff, hfd⟩
  refine ⟨U, hUo, hpos, hdiff, fun X => CasPsB.differentiableOn_lhol T μ hUo hΩ hfd X, fun z hz => ?_⟩
  have hint : ∀ a b : Fin n, Integrable (fun k =>
      CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z))) (muK ε) := fun a b =>
    (CasPsB.integrable_K (CasPsB.continuous_FY' T μ hUo hΩ hfd _ hz)).apply_continuousLinearMap _
  calc casL (psM T μ) z
      = ∑ a, ∑ b, ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          CasPsB.lhol_lhol_psM T μ hUo hΩ hfd _ _ hz
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ∑ a, ∑ b, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) := by
        rw [integral_finsetSum Finset.univ
          (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hint a b)), Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum Finset.univ (fun b _ => hint a b), Finset.smul_sum]
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ((casVal lam : ℝ) : ℂ) • (PhiM μ (toMK k⁻¹ * z * toMK k) •
            (T.op k * projW T * T.op k⁻¹)) ∂(muK ε) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
          CasPsB.sum_FY' T μ lam hμ k (hΩ z hz k))
    _ = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
        rw [integral_smul, smul_comm]
        rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChain
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainB
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma ccb_JJ (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * A) = A := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]

lemma ccb_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show (Z - Jm ε * Zᴴ * Jm ε) + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

lemma ccb_inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, smul_add, smul_sub, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg]
  abel

lemma ccb_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first
    | (simp [Complex.conj_I]; ring)
    | (rw [star_div', star_one, star_mul', Complex.star_def, Complex.conj_I]; field_simp; ring)
    | (apply Complex.ext <;> simp [Complex.div_re, Complex.div_im])
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, neg_smul, smul_add, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_add]
  abel

lemma ccb_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

lemma ccb_exp_inUJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left (show Xᴴ * Jm ε + Jm ε * X = 0 from hX)
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hs : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  have e2 : (t : ℂ) • -(Jm ε * X * Jm ε) = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hs, hXh, e2, Matrix.exp_conj _ _ hJu, hJinv]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [Matrix.mul_assoc (Jm ε * _) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc]
    _ = Jm ε := by rw [ccb_exp_neg_mul, Matrix.mul_one]

lemma ccb_inUJ_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hh : inUJ ε h) : inUJ ε (g * h) := by
  unfold inUJ at *
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

section Paths
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma ccb_path_right (X y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * y) (X * y) 0 :=
  (dga_exp X).mul_const y

lemma ccb_path_left (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  (dga_exp X).const_mul g

end Paths

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ccb_rdv (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X)))
      (-(fderiv ℂ F (g⁻¹ * m) (X * (g⁻¹ * m)))) 0 := by
  set y := g⁻¹ * m with hy
  have hyV : y ∈ V := (hWV g hg).2
  have hΦ : HasFDerivAt F (fderiv ℂ F y) y := (hF.differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
  have h0 : y = NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * y := by simp
  have h1 : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y))
      (fderiv ℂ F y (-X * y)) 0 :=
    (hΦ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (ccb_path_right (-X) y) h0
  have hcont : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (ccb_path_left g X).continuousAt
  have hW0 : W ∈ nhds ((fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) := by
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hW.mem_nhds hg
  have hev : ∀ᶠ t : ℝ in nhds 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ W :=
    hcont.preimage_mem_nhds hW0
  have hfin : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y) := by
    filter_upwards [hev] with t ht
    rw [hf _ ht (ccb_inUJ_mul ε hgu (ccb_exp_inUJ ε hX t)), Matrix.mul_inv_rev, smul_neg,
      Matrix.exp_neg, Matrix.mul_assoc]
  have h2 := h1.congr_of_eventuallyEq hfin
  rwa [Matrix.neg_mul, map_neg] at h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eabV_of_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W)
    (hgu : inUJ ε g) :
    EabV ε a b f g = -(Lhol (Matrix.single a b 1) F (g⁻¹ * m)) := by
  have h1 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart1 ε (Matrix.single a b 1)) hg hgu
  have h2 := ccb_rdv ε hV hF hW hWV hf (ccb_inG_cpart2 ε (Matrix.single a b 1)) hg hgu
  simp only [EabV, EcV, RdV, Lhol]
  rw [h1.deriv, h2.deriv]
  conv_rhs => rw [← ccb_cpart_sum ε (Matrix.single a b 1)]
  rw [add_mul, smul_mul_assoc, map_add (f := _), map_smul, smul_neg, neg_add]

theorem contDiffOn_of_local [CompleteSpace E] {F : Matrix (Fin n) (Fin n) ℂ → E} {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) : ContDiffOn ℝ ∞ (fun g => F (g⁻¹ * m)) W := by
  classical
  have hent : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) := by
    intro i j
    fun_prop
  have hdet : ∀ {G : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ},
      (∀ i j, ContDiff ℂ ∞ (fun A => G A i j)) → ContDiff ℂ ∞ (fun A => (G A).det) := by
    intro G hG
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    exact contDiff_prod fun i _ => hG _ _
  have hadj : ∀ i j : Fin n, ContDiff ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate i j) := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine hdet fun k l => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact hent k l
  have hinv : ContDiffOn ℂ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W := by
    intro g hg
    have hdg : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp (hWV g hg).1).ne_zero
    have hid : ContDiffAt ℂ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) g :=
      ((hdet fun i j => hent i j).contDiffAt).inv hdg
    refine ContDiffAt.contDiffWithinAt ?_
    refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
    simp only [Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact ContDiffAt.sum fun k _ => (hid.mul (hadj i k).contDiffAt).mul contDiffAt_const
  have hFc : ContDiffOn ℂ ∞ F V := cca_contDiffOn hV hF
  have hc : ContDiffOn ℂ ∞ (F ∘ fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * m) W :=
    hFc.comp hinv fun g hg => (hWV g hg).2
  exact hc.restrict_scalars ℝ

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CasG

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma lhol_clm (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ) {G : Matrix (Fin n) (Fin n) ℂ → E}
    {z : Matrix (Fin n) (Fin n) ℂ} (hG : DifferentiableAt ℂ G z) :
    Lhol X (fun w => L (G w)) z = L (Lhol X G z) := by
  unfold Lhol
  have h1 : (fun w => L (G w)) = L ∘ G := rfl
  rw [h1]
  have h2 := (L.hasFDerivAt.comp z hG.hasFDerivAt).fderiv
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E' => A (X * z)) h2

lemma lhol_neg (X : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) ℂ → E)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol X (fun w => -G w) z = -Lhol X G z := by
  unfold Lhol
  by_cases hG : DifferentiableAt ℂ G z
  · have h2 := hG.hasFDerivAt.neg.fderiv
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E => A (X * z)) h2
  · have h3 : ¬ DifferentiableAt ℂ (fun w => -G w) z := fun h => hG (differentiableAt_neg_iff.1 h)
    simp [fderiv_zero_of_not_differentiableAt hG, fderiv_zero_of_not_differentiableAt h3]

end CasG

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_smooth (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    SmoothOnGV ε (PsiM T μ) := by
  intro g₀ hg₀
  obtain ⟨U, hUo, hpU, hd, -, -⟩ := casL_psM T μ lam hμ
  obtain ⟨W, k₀, hWo, hgW, hWU, hloc⟩ := psiM_local T μ hμ U hUo hpU hg₀
  refine ⟨W, fun g => ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) (psM T μ (g⁻¹ * toMK k₀)),
    hWo, hgW, ?_, fun g hg hgu => by rw [hloc g hg hgu]; rfl⟩
  exact contDiffOn_of_local hUo
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).differentiable.comp_differentiableOn hd) hWo hWU

theorem psiM_continuousOn (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ContinuousOn (PsiM T μ) {g | inUJ ε g} := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hEq⟩ := psiM_smooth T μ hμ g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine (hFc.continuousWithinAt (s := {g | inUJ ε g})).congr_of_eventuallyEq ?_ (hEq g₀ hg₀U hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgJ
  exact hEq g hgU hgJ

theorem psiM_casimir (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : casimirV ε (PsiM T μ) g = ((casVal lam : ℝ) : ℂ) • PsiM T μ g := by
  obtain ⟨U, hUo, hpU, hd, hdL, hcas⟩ := casL_psM T μ lam hμ
  obtain ⟨W, k₀, hWo, hgW, hWU, hloc⟩ := psiM_local T μ hμ U hUo hpU hg
  set Lk := ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) with hLk
  have hf : ∀ g' ∈ W, inUJ ε g' → PsiM T μ g' = (Lk ∘ psM T μ) (g'⁻¹ * toMK k₀) :=
    fun g' hg' hgu' => by rw [hloc g' hg' hgu']; rfl
  have hd0 : DifferentiableOn ℂ (Lk ∘ psM T μ) U := Lk.differentiable.comp_differentiableOn hd
  have hinner : ∀ a b : Fin n, ∀ g' ∈ W, inUJ ε g' →
      EabV ε b a (PsiM T μ) g' =
        (fun z => -(Lk (Lhol (Matrix.single b a 1) (psM T μ) z))) (g'⁻¹ * toMK k₀) := by
    intro a b g' hg' hgu'
    rw [eabV_of_local ε hUo hd0 hWo hWU hf b a hg' hgu']
    have hz := (hWU g' hg').2
    rw [show (⇑Lk ∘ psM T μ) = fun w => Lk (psM T μ w) from rfl,
      CasG.lhol_clm Lk (Matrix.single b a 1) (G := psM T μ) (hd.differentiableAt (hUo.mem_nhds hz))]
  have hdi : ∀ a b : Fin n,
      DifferentiableOn ℂ (fun z => -(Lk (Lhol (Matrix.single b a 1) (psM T μ) z))) U :=
    fun a b => (Lk.differentiable.comp_differentiableOn (hdL _)).neg
  have hm := (hWU g hgW).2
  have hterm : ∀ a b : Fin n, EabV ε a b (EabV ε b a (PsiM T μ)) g =
      Lk (Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (psM T μ)) (g⁻¹ * toMK k₀)) := by
    intro a b
    rw [eabV_of_local ε hUo (hdi a b) hWo hWU (hinner a b) a b hgW hg, CasG.lhol_neg, neg_neg,
      CasG.lhol_clm Lk (Matrix.single a b 1) (G := Lhol (Matrix.single b a 1) (psM T μ))
        ((hdL _).differentiableAt (hUo.mem_nhds hm))]
  unfold casimirV
  simp only [hterm]
  calc ∑ a, ∑ b, Lk (Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (psM T μ)) (g⁻¹ * toMK k₀))
      = Lk (casL (psM T μ) (g⁻¹ * toMK k₀)) := by simp only [casL, map_sum]
    _ = ((casVal lam : ℝ) : ℂ) • PsiM T μ g := by
      rw [hcas _ hm, map_smul, hf g hgW hg]
      rfl

end ReciprocityTheory.ChartRestriction.DS.S7
