module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWords
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  intro n ε H _ _ _ σ h d L hL x hx
  have hd : ∀ (v : Fin d → H), (∀ a, Sm ε σ (v a)) → ∀ X ∈ lieSet ε, ∀ y ∈ UJset ε,
      HasDerivAt (fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X)) (v a)))
        (∑ a, L a (σ y (dRep σ X (v a)))) 0 := by
    intro v hv X hX y hy
    refine HasDerivAt.fun_sum fun a _ => ?_
    simpa using CoefLow.hasDerivAt_coef h (hL a) (hv a) hX hy 0
  have hw : ∀ (u : List (Ltr ε)) (a : Fin d), Sm ε σ (wordV σ u (x a)) := by
    intro u a
    induction u with
    | nil => exact hx a
    | cons z u ih =>
      rcases z with X | k
      · exact Sm.word h.1 ih (l := [X.1]) (by simpa using X.2)
      · exact Sm.translate h.1 ih (K_le_UJ k.2)
  refine ⟨⟨fun l y => ∑ a, L a (σ y (Dw σ l (x a))), fun _ _ => rfl, fun l hl X hX g hg => ?_, fun l hl => ?_⟩,
    fun u => ?_⟩
  · exact hd _ (fun a => Sm.word h.1 (hx a) hl) X hX g hg
  · exact continuousOn_finsetSum _ fun a _ => h.continuousOn_coef (hL a) (Sm.word h.1 (hx a) hl)
  · induction u with
    | nil => exact fun _ _ => rfl
    | cons z u ih =>
      intro y hy
      rcases z with X | k
      · have e : (fun t : ℝ => wordF u (fun y => ∑ a, L a (σ y (x a))) (y * NormedSpace.exp (t • X.1))) =
            fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X.1)) (wordV σ u (x a))) :=
          funext fun t => ih _ (mul_mem_UJ hy (exp_mem_UJ X.2 t))
        exact (congrArg (fun f => deriv f 0) e).trans (hd _ (hw u) X.1 X.2 y hy).deriv
      · refine (ih _ (mul_mem_UJ hy (K_le_UJ k.2))).trans (Finset.sum_congr rfl fun a _ => ?_)
        rw [sigma_mul h.1 hy (K_le_UJ k.2)]
        rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffSum_smooth_rightDerivWords : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  first | exact @GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | exact GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | (intros; apply GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimitStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimit
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped Topology ContDiff

namespace GlobalTheory.TypeSum.CoefClos

theorem integral_rder_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant] (c : ℝ → G) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (h h' : G → ℂ) (hh : Continuous h) (hh' : Continuous h')
    (hs : HasCompactSupport h) (hs' : HasCompactSupport h')
    (hd : ∀ x, HasDerivAt (fun t => h (x * c t)) (h' x) 0) : ∫ x, h' x ∂μ = 0 := by
  have i0 : Integrable h μ := hh.integrable_of_hasCompactSupport hs
  have i1 : Integrable h' μ := hh'.integrable_of_hasCompactSupport hs'
  have pt : ∀ x, ∫ t in Set.Ioc (0 : ℝ) 1, h' (x * c t) = h (x * c 1) - h x := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => h (x * c t))
      (f' := fun t => h' (x * c t)) (fun r _ => ?_)
      ((hh'.comp (continuous_const.mul hc)).intervalIntegrable 0 1)
    · simpa only [h0, mul_one] using this
    · have h1 : HasDerivAt (fun t => h (x * c r * c t)) (h' (x * c r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← hadd, add_sub_cancel]
  have hint : Integrable (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hcont : Continuous (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t)) :=
      hh'.comp (continuous_fst.mul (hc.comp continuous_snd))
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => i1.comp_mul_right (c t), ?_⟩
    simp only [Function.uncurry_apply_pair, fun t => integral_mul_right_eq_self (μ := μ) (fun x => ‖h' x‖) (c t)]
    exact integrable_const _
  have sw := integral_integral_swap hint
  simp only [pt, fun t => integral_mul_right_eq_self (μ := μ) h' (c t)] at sw
  rw [integral_sub (i0.comp_mul_right _) i0, integral_mul_right_eq_self h, sub_self] at sw
  simpa using sw.symm

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def mkU (g : Mx n) (hg : g ∈ UJset ε) : UJ ε :=
  ⟨(isUnit_of_UJ hg).unit, show inUJ ε _ from hg⟩

theorem umat_mkU (g : Mx n) (hg : g ∈ UJset ε) : umat (mkU g hg) = g := rfl

theorem umat_emb (ε : Fin n → Bool) : Topology.IsClosedEmbedding (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1

theorem CSm.continuous {f : Mx n → ℂ} (h : CSm ε f) : Continuous fun g : UJ ε => f (umat g) := by
  obtain ⟨F, h1, -, h3⟩ := h
  exact ((h3 [] (by simp)).congr fun g hg => (h1 g hg).symm).comp_continuous (umat_emb ε).continuous fun g => g.2

theorem cSm_of_contDiff (φ : Mx n → ℂ) (hφ : ContDiff ℝ ∞ (fun y : Fin n → Fin n → ℂ => φ (Matrix.of y))) :
    CSm ε φ := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hφ' : ContDiff ℝ ∞ φ := by
    let L : Mx n →L[ℝ] (Fin n → Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact hφ.comp L.contDiff
  let F : List (Mx n) → Mx n → ℂ := fun l => l.foldr (fun X f g => fderiv ℝ f g (g * X)) φ
  have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
    intro l
    induction l with
    | nil => exact hφ'
    | cons X l ih =>
      exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_id.mul contDiff_const)
  refine ⟨F, fun _ _ => rfl, fun l _ X _ g _ => ?_, fun l _ => (hF l).continuous.continuousOn⟩
  have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).const_mul g
  have h2 : HasFDerivAt (F l) (fderiv ℝ (F l) g) (g * NormedSpace.exp ((0 : ℝ) • X)) := by
    rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (((hF l).differentiable (by simp)) g).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
  exact h3

def IsTest (ε : Fin n → Bool) (φ : Mx n → ℂ) : Prop := CSm ε φ ∧ HasCompactSupport fun g : UJ ε => φ (umat g)

theorem IsTest.integrable {φ F : Mx n → ℂ} (hφ : IsTest ε φ) (hF : CSm ε F) :
    Integrable (fun g : UJ ε => φ (umat g) * F (umat g)) (muG ε) :=
  (hφ.1.continuous.mul hF.continuous).integrable_of_hasCompactSupport hφ.2.mul_right

theorem exists_adjoint_ltr (x : Ltr ε) {φ : Mx n → ℂ} (hφ : IsTest ε φ) : ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * ltrF x F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
  · let c : ℝ → UJ ε := fun t => mkU (NormedSpace.exp (t • X)) (exp_mem_UJ hX t)
    have hc : Continuous c := (umat_emb ε).isInducing.continuous_iff.2 (continuous_exp_smul X)
    have h0 : c 0 = 1 := (umat_emb ε).injective (by
      change NormedSpace.exp ((0 : ℝ) • X) = 1
      simp)
    have hadd : ∀ a b, c (a + b) = c a * c b := fun a b => (umat_emb ε).injective (exp_add_smul X a b)
    have ht : IsTest ε (rder X φ) := by
      refine ⟨hφ.1.rder hX, hφ.2.mono' fun g hg => ?_⟩
      by_contra hn
      apply hg
      have h1 := notMem_tsupport_iff_eventuallyEq.1 hn
      have h2 : Filter.Tendsto (fun t => g * c t) (𝓝 0) (𝓝 g) := by
        have h4 : Continuous fun t => g * c t := continuous_const.mul hc
        simpa only [h0, mul_one] using h4.tendsto 0
      have h3 : (fun t : ℝ => φ (umat g * NormedSpace.exp (t • X))) =ᶠ[𝓝 0] fun _ => 0 := h2.eventually h1
      show deriv _ 0 = 0
      rw [h3.deriv_eq, deriv_const]
    refine ⟨(-1 : ℂ) • rder X φ, ⟨ht.1.smul _, ht.2.mul_left⟩, fun F hF => ?_⟩
    have key := integral_rder_eq_zero (muG ε) c hc h0 hadd (fun g => φ (umat g) * F (umat g))
      (fun g => rder X φ (umat g) * F (umat g) + φ (umat g) * rder X F (umat g))
      (hφ.1.continuous.mul hF.continuous)
      ((ht.1.continuous.mul hF.continuous).add (hφ.1.continuous.mul (hF.rder hX).continuous))
      hφ.2.mul_right (ht.2.mul_right.add hφ.2.mul_right) (fun g => by
        have := (hφ.1.hasDerivAt hX g.2).fun_mul (hF.hasDerivAt hX g.2)
        simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this
        exact this)
    rw [integral_add (ht.integrable hF) (hφ.integrable (hF.rder hX))] at key
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, integral_neg]
    exact eq_neg_of_add_eq_zero_right key
  · have hkU := K_le_UJ hk
    have hk' : k⁻¹ ∈ Kset ε := by
      refine ((maximal_compact_facts n ε).2.2.2.2 _).2 ⟨inv_mem_UJ hkU, ?_⟩
      rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)]
      exact Unitary.star_mem hk.1
    refine ⟨fun g => φ (g * k⁻¹), ⟨hφ.1.rt hk', ?_⟩, fun F hF => ?_⟩
    · exact hφ.2.comp_homeomorph (Homeomorph.mulRight (mkU k⁻¹ (K_le_UJ hk')))
    · rw [← integral_mul_right_eq_self (fun g : UJ ε => φ (umat g * k⁻¹) * F (umat g)) (mkU k hkU)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show φ (umat g) * F (umat g * k) = φ (umat g * k * k⁻¹) * F (umat g * k)
      rw [Matrix.mul_assoc, mul_inv_UJ hkU, Matrix.mul_one]

theorem exists_adjoint_word (u : List (Ltr ε)) : ∀ {φ : Mx n → ℂ}, IsTest ε φ → ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * wordF u F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  induction u with
  | nil => exact fun hφ => ⟨_, hφ, fun _ _ => rfl⟩
  | cons x u ih =>
    intro φ hφ
    obtain ⟨ψ, h1, h2⟩ := exists_adjoint_ltr x hφ
    obtain ⟨χ, h3, h4⟩ := ih h1
    exact ⟨χ, h3, fun F hF => (h2 _ (hF.wordF u)).trans (h4 F hF)⟩

theorem eq_zero_of_test (H : UJ ε → ℂ) (hH : Continuous H)
    (h : ∀ φ, IsTest ε φ → ∫ g : UJ ε, φ (umat g) * H g ∂(muG ε) = 0) (y : UJ ε) : H y = 0 := by
  by_contra hy
  have hc : Continuous fun g => (star (H y) * H g).re := by fun_prop
  have hpos : 0 < (star (H y) * H y).re := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  have hU : {g | 0 < (star (H y) * H g).re} ∈ 𝓝 y := (isOpen_lt continuous_const hc).mem_nhds hpos
  have hemb : Topology.IsClosedEmbedding (fun g : UJ ε => (Matrix.of.symm (umat g) : Fin n → Fin n → ℂ)) :=
    umat_emb ε
  rw [hemb.isInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  have hψ : Continuous fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφd.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφc.comp_isClosedEmbedding hemb
  have ht : IsTest ε (fun g => (φ (Matrix.of.symm g) : ℂ)) :=
    ⟨cSm_of_contDiff _ (Complex.ofRealCLM.contDiff.comp hφd), hψc.comp_left Complex.ofReal_zero⟩
  have hi : Integrable (fun g : UJ ε => star (H y) * ((φ (Matrix.of.symm (umat g)) : ℂ) * H g)) (muG ε) :=
    ((ht.1.continuous.mul hH).integrable_of_hasCompactSupport ht.2.mul_right).const_mul _
  have h1 := integral_re hi
  rw [integral_const_mul, h _ ht] at h1
  have h2 : 0 < ∫ g : UJ ε, φ (Matrix.of.symm (umat g)) * (star (H y) * H g).re ∂(muG ε) := by
    refine (hψ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) hψc.mul_right (fun g => ?_) ?_
    · by_cases h0 : φ (Matrix.of.symm (umat g)) = 0
      · rw [h0, zero_mul]; exact le_rfl
      · exact mul_nonneg (hφr ⟨_, rfl⟩).1 (le_of_lt (hVU (hφs (subset_tsupport _ h0))))
    · rw [hφ1, one_mul]; exact hpos.ne'
  refine h2.ne' ?_
  simp only [mul_left_comm (star (H y)), RCLike.re_to_complex, Complex.re_ofReal_mul] at h1
  simpa using h1

end GlobalTheory.TypeSum.CoefClos
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Mx n → ℂ), CSm ε F → ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)),
    (∀ C : Set (Mx n), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ f : Mx n → ℂ, CSm ε f ∧
      (∀ y ∈ C, y ∈ UJset ε → ‖F y - f y‖ < δ) ∧ ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) f y = 0) →
    ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) F y = 0 := by
  intro n ε F hF m c u hlim y hy
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcont : Continuous fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact continuous_const.mul (CSm.continuous (CSm.wordF hF (u i)))
  have key : ∀ φ, IsTest ε φ →
      ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) = 0 := by
    intro φ hφ
    choose ψ hψ hadj using fun i => exists_adjoint_word (u i) hφ

    have expand : ∀ G, CSm ε G →
        ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) G (umat g) ∂(muG ε)
          = ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * G (umat g) ∂(muG ε) := by
      intro G hG
      have hfun : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) G (umat g))
          = fun g => ∑ i, c i * (φ (umat g) * wordF (u i) G (umat g)) := by
        funext g
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfun, MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_const_mul, hadj i G hG]
      · intro i _
        exact (IsTest.integrable hφ (CSm.wordF hG (u i))).const_mul (c i)
    have h1 : CSm ε (fun _ : Mx n => (1 : ℂ)) := cSm_of_contDiff _ contDiff_const
    have hint1 : ∀ i, MeasureTheory.Integrable (fun g : UJ ε => ‖ψ i (umat g)‖) (muG ε) := by
      intro i
      simpa using (IsTest.integrable (hψ i) h1).norm
    set A : Fin m → ℝ := fun i => ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε) with hA
    set B : ℝ := ∑ i, ‖c i‖ * A i with hB
    have hA0 : ∀ i, 0 ≤ A i := fun i => MeasureTheory.integral_nonneg (fun g => norm_nonneg _)
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA0 i))
    set X := ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) with hX

    have bound : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ δ * B := by
      intro δ hδ
      let K : Set (UJ ε) := ⋃ i, tsupport (fun g : UJ ε => ψ i (umat g))
      have hK : IsCompact K := isCompact_iUnion (fun i => (hψ i).2.isCompact)
      have hC : IsCompact ((fun g : UJ ε => umat g) '' K) := hK.image (umat_emb ε).continuous
      obtain ⟨f, hf, hclose, hzero⟩ := hlim _ hC δ hδ
      have e0 : ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε) = 0 := by
        rw [← expand f hf]
        have hz : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) f (umat g)) = fun _ => 0 := by
          funext g
          rw [hzero _ (hmem g), mul_zero]
        rw [hz, MeasureTheory.integral_zero]
      have hXf : X = ∑ i, c i * ((∫ g : UJ ε, ψ i (umat g) * F (umat g) ∂(muG ε))
          - ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε)) := by
        rw [hX, expand F hF]
        simp only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]
      rw [hXf]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => ?_ : ∀ i ∈ Finset.univ, _ ≤ ‖c i‖ * (δ * A i))).trans
        (le_of_eq ?_)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        show _ ≤ δ * ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε)
        rw [← MeasureTheory.integral_sub (IsTest.integrable (hψ i) hF) (IsTest.integrable (hψ i) hf),
          ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.norm_integral_le_of_norm_le ((hint1 i).const_mul δ)
          (Filter.Eventually.of_forall (fun g => ?_))
        rw [← mul_sub, norm_mul]
        by_cases hg : g ∈ tsupport (fun g : UJ ε => ψ i (umat g))
        · have hgC : umat g ∈ (fun g : UJ ε => umat g) '' K := ⟨g, Set.mem_iUnion.2 ⟨i, hg⟩, rfl⟩
          rw [mul_comm δ]
          exact mul_le_mul_of_nonneg_left (hclose _ hgC (hmem g)).le (norm_nonneg _)
        · have h0 : ψ i (umat g) = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun g : UJ ε => ψ i (umat g)) hg
          rw [h0]
          simp
      · rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    by_contra hne
    have hpos : 0 < ‖X‖ := norm_pos_iff.2 hne
    have hle := bound (‖X‖ / (B + 1)) (div_pos hpos (by linarith))
    have hlt : ‖X‖ / (B + 1) * B < ‖X‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have h := eq_zero_of_test (fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)) hcont key (mkU y hy)
  simpa [umat_mkU] using h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBound
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem wordF_fam {n : ℕ} {ε : Fin n → Bool} {N : ℕ} {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ}
    (h1 : ∀ g ∈ UJset ε, F [] g = f g) (h2 : IsDerFam ε F) (h3 : FamGrowth ε N F) (u : List (Ltr ε)) :
    ∃ G : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, G [] g = wordF u f g) ∧ IsDerFam ε G ∧ FamGrowth ε N G := by
  induction u with
  | nil => exact ⟨F, h1, h2, h3⟩
  | cons x u ih =>
    obtain ⟨G, k1, k2, k3⟩ := ih
    rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
    · refine ⟨fun l => G (l ++ [X]), fun g hg => (CSm.rder_eq k1 k2 hX hg).symm, fun l hl Y hY g hg => ?_,
        fun l hl => k3 _ ?_⟩
      · exact k2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
      · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)
    · have hkU := K_le_UJ hk
      have hmap : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
          ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
        intro l hl Z hZ
        obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
        exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
      refine ⟨fun l g => G (l.map fun Y => k⁻¹ * Y * k) (g * k),
        fun g hg => k1 _ (mul_mem_UJ hg hkU), fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
      · have hY' : k⁻¹ * Y * k ∈ lieSet ε := GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU hY
        have := k2 _ (hmap l hl) _ hY' (g * k) (mul_mem_UJ hg hkU)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show G _ (g * NormedSpace.exp (t • Y) * k) = G _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
        rw [← exp_conj_smul hkU Y t]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
      · obtain ⟨C, hC⟩ := k3 _ (hmap l hl)
        refine ⟨max C 0 * (1 + Formalism.REAL.hs k) ^ N, fun g hg => (hC _ (mul_mem_UJ hg hkU)).trans ?_⟩
        have h0 : 0 ≤ 1 + Formalism.REAL.hs (g * k) := by
          unfold Formalism.REAL.hs; positivity
        calc C * (1 + Formalism.REAL.hs (g * k)) ^ N ≤ max C 0 * (1 + Formalism.REAL.hs (g * k)) ^ N :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 N)
          _ ≤ max C 0 * ((1 + Formalism.REAL.hs g) * (1 + Formalism.REAL.hs k)) ^ N :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (one_add_hs_mul_le g k) N) (le_max_right _ _)
          _ = _ := by rw [mul_pow]; ring

theorem wordF_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  intro n ε N f F h1 h2 h3 u
  obtain ⟨G, k1, -, k3⟩ := wordF_fam h1 h2 h3 u
  obtain ⟨C, hC⟩ := k3 [] (by simp)
  exact ⟨C, fun g hg => k1 g hg ▸ hC g hg⟩

end GlobalTheory.TypeSum.CoefClos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffWord_moderateGrowth_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  first | exact @GlobalTheory.TypeSum.CoefClos.wordF_growth | exact GlobalTheory.TypeSum.CoefClos.wordF_growth | (intros; apply GlobalTheory.TypeSum.CoefClos.wordF_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnRightDerivativeFamilyModerateGrowthStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnRightDerivativeFamilyModerateGrowth
noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace GlobalTheory.TypeSum.DerFamCont

theorem exists_chart {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E)
    (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1) :
    ∃ (N : ℕ) (Y : Fin N → E) (Ψ : E → Fin N → ℝ), (∀ i, σ (Y i) = -Y i) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : E), σ a * a = 1 → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let S : Submodule ℝ E := LinearMap.ker (σ + LinearMap.id)
  have hS : ∀ X, X ∈ S ↔ σ X = -X := fun X => by simp [S, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ S
  let e : Fin (Module.finrank ℝ S) → E := fun i => b i
  have hli : LinearIndependent ℝ e := b.linearIndependent.map' S.subtype S.ker_subtype
  have he : ∀ i, σ (e i) = -e i := fun i => (hS _).1 (b i).2
  have hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e) := fun X hX => by
    have h := congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext n
    simp [hp]
  set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin _ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i =>
      ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i))
        (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i) 0).hasStrictFDerivAt)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin _ => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp
  have hΦ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) :
        (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΦ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΦ.localInverse_tendsto
  have p3 := hΦ.eventually_right_inverse
  simp only [hΦ0] at p1 p3
  set Ψ := hΦ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1) := by
    have := hD.continuousAt.tendsto.comp p1
    rw [h0] at this
    exact this.comp hPt
  refine ⟨_, e, fun a => Ψ (P a), he, p1.comp hPt, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_chart_UJ (ε : Fin n → Bool) :
    ∃ (N : ℕ) (Y : Fin N → Mx n) (Ψ : Mx n → Fin N → ℝ), (∀ i, Y i ∈ lieSet ε) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : Mx n), a ∈ UJset ε → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h2 := Jm_mul_self ε
  have hH : (Jm ε)ᴴ = Jm ε := by
    have h : (Jm ε)ᴴ * Jm ε = 1 := (maximal_compact_facts n ε).2.2.1.1.1
    rw [← Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv h2]
  set J := Jm ε with hJdef
  let s : Mx n →ₗ[ℝ] Mx n :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Mx n, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  refine ⟨N, Y, Ψ, fun i => ?_, hΨ, hE.mono fun g q hg => q ?_⟩
  · have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    show (Y i)ᴴ * J + J * Y i = 0
    rw [this, neg_add_cancel]
  · have hg' : gᴴ * J * g = J := hg
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]

theorem exists_step_bound {f f' : Mx n → ℂ} {X : Mx n} (hX : X ∈ lieSet ε) {C : ℝ} {N : ℕ}
    (hd : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0)
    (hb : ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∃ B : ℝ, ∀ a ∈ UJset ε, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖f (a * NormedSpace.exp (s • X)) - f a‖ ≤ |C| * ((1 + hs a) * B) ^ N * ‖s‖ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image
    (f := fun u : ℝ => 1 + hs (NormedSpace.exp (u • X)))
    (continuous_const.add (continuous_hs.comp (continuous_exp_smul X))).continuousOn
  refine ⟨B, fun a ha s hs1 => ?_⟩
  have := (convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => f (a * NormedSpace.exp (t • X))) (f' := fun t => f' (a * NormedSpace.exp (t • X)))
    (C := |C| * ((1 + hs a) * B) ^ N) (x := 0) (y := s) (fun t _ => ?_) (fun t ht => ?_)
    (Metric.mem_closedBall_self zero_le_one) hs1
  · simpa using this
  · have k := hd _ (mul_mem_UJ ha (exp_mem_UJ hX t))
    have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).hasDerivWithinAt
    beta_reduce
    rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]
  · refine (hb _ (mul_mem_UJ ha (exp_mem_UJ hX t))).trans ?_
    have h0 := hs_nonneg (a * NormedSpace.exp (t • X))
    have h1 := hs_nonneg a
    refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)
    exact (one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB ⟨t, ht, rfl⟩) (by positivity))

theorem tendsto_prod {f : Mx n → ℂ} {α : Type} {L : Filter α} {g₀ : Mx n} {c : ℂ} {N : ℕ}
    (hf : ∀ X ∈ lieSet ε, ∃ (f' : Mx n → ℂ) (C : ℝ),
      (∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0) ∧
      ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∀ (d : ℕ) (Y : Fin d → Mx n) (t : α → Fin d → ℝ) (a : α → Mx n), (∀ i, Y i ∈ lieSet ε) →
      (∀ i, Tendsto (fun p => t p i) L (𝓝 0)) → (∀ p, a p ∈ UJset ε) → Tendsto a L (𝓝 g₀) →
      Tendsto (fun p => f (a p)) L (𝓝 c) →
      Tendsto (fun p => f (a p * (List.ofFn fun i => NormedSpace.exp (t p i • Y i)).prod)) L (𝓝 c) := by
  intro d
  induction d with
  | zero => intro Y t a _ _ _ _ h; simpa using h
  | succ d ih =>
    intro Y t a hY ht ha hag hc
    simp only [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]
    refine ih (fun i => Y i.succ) (fun p i => t p i.succ) (fun p => a p * NormedSpace.exp (t p 0 • Y 0))
      (fun i => hY _) (fun i => ht _) (fun p => mul_mem_UJ (ha p) (exp_mem_UJ (hY 0) _)) ?_ ?_
    · have := hag.mul (((continuous_exp_smul (Y 0)).tendsto 0).comp (ht 0))
      simpa using this
    · obtain ⟨f', C, h1, h2⟩ := hf _ (hY 0)
      obtain ⟨B, hB⟩ := exists_step_bound (hY 0) h1 h2
      have h3 : Tendsto (fun p => f (a p * NormedSpace.exp (t p 0 • Y 0)) - f (a p)) L (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun p => |C| * ((1 + hs (a p)) * B) ^ N * ‖t p 0‖) ?_ ?_
        · filter_upwards [(ht 0).eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with p hp
          exact hB _ (ha p) _ hp
        · have := (((((continuous_hs.tendsto g₀).comp hag).const_add 1).mul_const B).pow N |>.const_mul |C|).mul
            (ht 0).norm
          simpa using this
      simpa using h3.add hc

theorem continuousOn_of_isDerFam : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ),
    IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  intro n ε N F hF hG l hl g₀ hg₀
  obtain ⟨d, Y, Ψ, hY, hΨ, hE⟩ := exists_chart_UJ ε
  have ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝[UJset ε] g₀) (𝓝 1) := by
    have := ((continuous_const (y := g₀⁻¹)).matrix_mul continuous_id).tendsto g₀
    rw [id, inv_mul_UJ hg₀] at this
    exact this.mono_left nhdsWithin_le_nhds
  have key := tendsto_prod (ε := ε) (f := F l) (L := 𝓝[UJset ε] g₀) (g₀ := g₀) (c := F l g₀) (N := N)
    (fun X hX => by
      obtain ⟨C, hC⟩ := hG (X :: l) (List.forall_mem_cons.2 ⟨hX, hl⟩)
      exact ⟨F (X :: l), C, hF l hl X hX, hC⟩)
    d Y (fun g => Ψ (g₀⁻¹ * g)) (fun _ => g₀) hY (fun i => tendsto_pi_nhds.1 (hΨ.comp ht) i) (fun _ => hg₀)
    tendsto_const_nhds tendsto_const_nhds
  refine key.congr' ?_
  filter_upwards [ht.eventually hE, self_mem_nhdsWithin] with g q hg
  rw [q (mul_mem_UJ (inv_mem_UJ hg₀) hg), ← Matrix.mul_assoc, mul_inv_UJ hg₀, Matrix.one_mul]

end GlobalTheory.TypeSum.DerFamCont

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_rightDerivativeFamily_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  first | exact @GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam | exact GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam | (intros; apply GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMap
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

open GlobalTheory.TypeSum.CoefLow GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.GrowthForm

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)} {N : ℕ} {T : H →ₗ[ℂ] (Mx n → ℂ)}

omit [CompleteSpace H] in
theorem deriv_at (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X)))
      (T (dRep σ X v) (g * NormedSpace.exp (s • X))) s := by
  have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
  have h1 := hd v hv X hX _ hs
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = T v _
  rw [mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem taylor (h : Std ε σ)
    (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g)
    (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    ∃ C, 0 ≤ C ∧ ∀ g ∈ UJset ε, ∀ t : ℝ, |t| ≤ 1 →
      ‖T v (g * NormedSpace.exp (t • X)) - T v g - t • T (dRep σ X v) g‖ ≤ C * wt N g * t ^ 2 := by
  have hv1 := isKFin_dRep n ε H σ h v hv X hX
  have hv2 := isKFin_dRep n ε H σ h _ hv1 X hX
  obtain ⟨C, hC⟩ := hb _ hv2
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
    ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
  refine ⟨|C| * |B|, by positivity, fun g hg t ht => ?_⟩
  have := taylor_two (deriv_at hd hv hX hg) (deriv_at hd hv1 hX hg)
    (K := |C| * |B| * wt N g) (fun s hs => by
      refine (hC _ (mul_mem_UJ hg (exp_mem_UJ hX s))).trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self C) (wt_pos _ _).le).trans ?_
      rw [mul_assoc, mul_comm |B|]
      refine mul_le_mul_of_nonneg_left ((wt_mul_le N g _).trans ?_) (abs_nonneg C)
      exact mul_le_mul_of_nonneg_left ((hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)) (wt_pos N g).le) ht
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using this

omit [CompleteSpace H] in
theorem exists_bdMap (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g) :
    ∃ T₀ : H →ₗ[ℂ] Bd (Unit × UJset ε), ∀ v, IsKFin ε σ v → ∀ i, T₀ v i = T v i.2.1 / wt N i.2.1 := by
  let f : kfin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun v => mkBd (fun i => T v i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hb v v.2
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [mkBd, add_div]; rfl
      map_smul' := fun c v => by ext i; simp [mkBd, mul_div_assoc] }
  obtain ⟨T₀, hT⟩ := LinearMap.exists_extend f
  refine ⟨T₀, fun v hv i => ?_⟩
  have : T₀ v = f ⟨v, hv⟩ := LinearMap.congr_fun hT ⟨v, hv⟩
  rw [this]
  rfl

theorem exists_form : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  intro hCW n ε H _ _ _ σ h N T hb hK hd
  change ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g at hb
  obtain ⟨T₀, hT₀⟩ := exists_bdMap hb
  have key : ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε, rt ε _ N y (T₀ v) i = T v (i.2.1 * y) / wt N i.2.1 := by
    intro v hv y hy i
    rw [rt_apply hy, hT₀ v hv]
    have := wt_ne N (i.2.1 * y)
    field_simp
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := casselmanWallach_banach hCW n ε H σ h _ _ (modRep_rt ε Unit N) T₀
    (fun k hk v hv => by
      ext i
      rw [key v hv k (K_le_UJ hk), hT₀ _ (isKFin_translate hv hk), hK v hv k hk _ i.2.2])
    (fun X hX v hv => by
      obtain ⟨C, hC, hb⟩ := taylor h hb hd hv hX
      refine hasDerivAt_of_sq (K := C) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X v)) i = t • T₀ (dRep σ X v) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key v hv _ (exp_mem_UJ hX _),
        key v hv _ (exp_mem_UJ hX _), hT₀ _ (isKFin_dRep n ε H σ h v hv X hX), zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _), mul_right_comm]
      exact hb _ i.2.2 t ht)
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx n) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun c x => by simp; ring }
  have hL : ∀ w, Sm ε σ w → ‖L w‖ ≤ wt N (1 : Mx n) * |C| * sobNorm σ S w := fun w hw => by
    change ‖(wt N (1 : Mx n) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  refine ⟨L, ⟨S, _, hS, hL⟩, fun v hv y hy => ?_⟩
  change _ = wt N (1 : Mx n) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
  rw [hT2 y hy v (h.2.2.1 v hv), hT1 v hv, key v hv y hy]
  have := wt_ne N (1 : Mx n)
  simp only [one_mul]
  field_simp

end GlobalTheory.TypeSum.GrowthForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GrowthForm.exists_form | exact GlobalTheory.TypeSum.GrowthForm.exists_form | (intros; apply GlobalTheory.TypeSum.GrowthForm.exists_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqMatrixCoeffOfLocallyUniformLimitKFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  intro hHC hCW n ε H _ _ _ σ hstd d w hw h hcont humg happ
  obtain ⟨N, Φ, hΦ0, hΦD, hΦG⟩ := humg
  have hCh : CSm ε h := ⟨Φ, hΦ0, hΦD, GlobalTheory.T.continuousOn_rightDerivativeFamily_moderateGrowth n ε N Φ hΦD hΦG⟩
  set h0 : Mx n → ℂ := (UJset ε).indicator h with hh0def
  have hh0 : ∀ g ∈ UJset ε, h g = h0 g := fun g hg => (Set.indicator_of_mem hg h).symm
  have hm0 : h0 ∈ Smo ε := ⟨fun g hg => Set.indicator_of_notMem hg h, hCh.congr hh0⟩
  have hwS : ∀ a, Sm ε σ (w a) := fun a => hstd.2.2.1 _ (hw a)
  have hrel : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε) = 0 := by
    intro m c u hcu
    have hA := GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit n ε h hCh m c u (fun C hC δ hδ => by
      obtain ⟨L, hL, hLa⟩ := happ C hC δ hδ
      obtain ⟨hB1, hB2⟩ := GlobalTheory.T.coeffSum_smooth_rightDerivWords n ε H σ hstd d L hL w hwS
      refine ⟨_, hB1, hLa, fun y hy => ?_⟩
      simp only [fun i => hB2 (u i) y hy]
      rw [← Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin d))) (f := fun a => L a (σ y (∑ i, c i • wordV σ (u i) (w a))))
        (fun a _ => by rw [hcu a, map_zero, map_zero])]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm)
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_wordE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Submodule.coe_zero, Pi.zero_apply]
    by_cases hg : g ∈ UJset ε
    · rw [← hA g hg]
      exact Finset.sum_congr rfl fun i _ => by rw [wordF_congr hh0 (u i) g hg]
    · refine Finset.sum_eq_zero fun i _ => ?_
      have := (wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε)).2.1 g hg
      rw [coe_wordE] at this
      rw [this, mul_zero]
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.T.exists_maps_of_relations_alt hHC n ε H σ hstd d w hw (Smo ε) ltrM ⟨h0, hm0⟩ hrel
  have hD : ∀ a, ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε,
      ((Smo ε).subtype ∘ₗ T a) v y = L (σ y v) := by
    intro a
    refine GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap hCW n ε H σ hstd N ((Smo ε).subtype ∘ₗ T a) (fun v hv => ?_) (fun v hv k hk g hg => ?_)
      (fun v hv X hX g hg => ?_)
    · obtain ⟨m, c, u, e⟩ := hT3 a v hv
      have hb := fun i => GlobalTheory.T.coeffWord_moderateGrowth_bound n ε N h Φ hΦ0 hΦD hΦG (u i)
      choose C hC using hb
      refine ⟨∑ i, ‖c i‖ * C i, fun g hg => ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, e, Submodule.coe_sum, Submodule.coe_smul, coe_wordE,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, mul_assoc, ← wordF_congr hh0 (u i) g hg]
      exact mul_le_mul_of_nonneg_left (hC i g hg) (norm_nonneg _)
    · have := hT1 a v hv (Sum.inr ⟨k, hk⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show σ k v = ltrV σ (Sum.inr ⟨k, hk⟩ : Ltr ε) v from rfl, this]
      rfl
    · have := hT1 a v hv (Sum.inl ⟨X, hX⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show dRep σ X v = ltrV σ (Sum.inl ⟨X, hX⟩ : Ltr ε) v from rfl, this]
      exact (T a v).2.2.hasDerivAt hX hg
  choose L hL1 hL2 using hD
  refine ⟨L, hL1, fun y hy => ?_⟩
  rw [hh0 y hy, show h0 = ((⟨h0, hm0⟩ : Smo ε) : Mx n → ℂ) from rfl, ← hT2, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => hL2 a (w a) (hw a) y hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqMatrixCoeffOfLocallyUniformLimitKFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_matrixCoeff_of_locallyUniform_limit_kFinite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  first | exact @GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure | exact GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure | (intros; apply GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure <;> assumption)
end
