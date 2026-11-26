module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Measure Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Gen

theorem hasCompactSupport_slice {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B] {F : A × B → ℂ}
    (hF : HasCompactSupport F) (a : A) : HasCompactSupport (fun b => F (a, b)) :=
  HasCompactSupport.intro (hF.isCompact.image continuous_snd) fun b hb =>
    image_eq_zero_of_notMem_tsupport fun h => hb ⟨(a, b), h, rfl⟩

theorem integral_tensor {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (mX : Measure X) (mY : Measure Y) (mZ : Measure Z) [SigmaFinite mX] [SigmaFinite mY]
    [SigmaFinite mZ] (p : X → ℂ) (q : Y → ℂ) (r : Z → ℂ) :
    ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ)) = (∫ x, p x ∂mX) * (∫ y, q y ∂mY) * ∫ w, r w ∂mZ := by
  calc ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ))
      = ∫ z, p z.1 * (fun w : Y × Z => q w.1 * r w.2) z.2 ∂(mX.prod (mY.prod mZ)) := by simp only [mul_assoc]
    _ = (∫ x, p x ∂mX) * ∫ w, q w.1 * r w.2 ∂(mY.prod mZ) :=
      integral_prod_mul (L := ℂ) (μ := mX) (ν := mY.prod mZ) p (fun w : Y × Z => q w.1 * r w.2)
    _ = _ := by rw [integral_prod_mul (L := ℂ) (μ := mY) (ν := mZ) q r, mul_assoc]

end Gen

section Abstract

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
variable {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]

omit [SecondCountableTopology X] in
theorem exists_bump (μ : Measure X) [IsHaarMeasure μ] :
    ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ∫ x, f x ∂μ ≠ 0 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : X)))
    isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, hfc.comp_left Complex.ofReal_zero, ?_⟩
  show ∫ x, ((f x : ℝ) : ℂ) ∂μ ≠ 0
  rw [show ∫ x, ((f x : ℝ) : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) from integral_ofReal, Complex.ofReal_ne_zero]
  exact (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hf01 x).1) (x := 1)
    (by simp [hf1 (Set.mem_singleton (1 : X))])).ne'

theorem exists_split (e : X × (Y × Z) ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ] (mX : Measure X) [IsHaarMeasure mX]
    (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z) [IsHaarMeasure mZ] :
    ∃ c : NNReal, 0 < c ∧ ∀ f : K → ℂ, ∫ g, f g ∂μ = c • ∫ z, f (e z) ∂(mX.prod (mY.prod mZ)) := by
  haveI : IsHaarMeasure (μ.map e.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  obtain ⟨c, hc0, h⟩ : ∃ c : NNReal, 0 < c ∧ μ.map e.symm = c • mX.prod (mY.prod mZ) :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, hc0, fun f => ?_⟩
  have he : ∫ z, f (e z) ∂(μ.map e.symm) = ∫ g, f g ∂μ := by
    have := integral_map_equiv (μ := μ) (e.toHomeomorph.toMeasurableEquiv.symm) (fun z => f (e z))
    refine this.trans ?_
    congr 1
    funext x
    exact congrArg f (e.apply_symm_apply x)
  rw [← he, h, integral_smul_nnreal_measure]

theorem integral_iter (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z)
    [IsHaarMeasure mZ] (f : X × (Y × Z) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ z, f z ∂(mX.prod (mY.prod mZ)) = ∫ x, ∫ y, ∫ w, f (x, (y, w)) ∂mZ ∂mY ∂mX := by
  rw [integral_prod _ (hf.integrable_of_hasCompactSupport hfc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod _ ((hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hfc x))

end Abstract

section Inst

theorem lc_G (n : ℕ) : LocallyCompactSpace (G n) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

variable (E : Type) [Field E] [NumberField E]

theorem lc_GLf (n : ℕ) : LocallyCompactSpace (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Af E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_GLf (n : ℕ) : SecondCountableTopology (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2_GL_finite_adeles (n : ℕ) : T2Space (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  Units.isEmbedding_embedProduct.t2Space

end Inst

attribute [local instance] lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem borelSpaceH : BorelSpace (H E a b) := ⟨rfl⟩

attribute [local instance] borelSpaceH

theorem haar_of_dom (D : Dom E a b) : IsHaarMeasure D.μ :=
  haveI := D.haar.2.2.2
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    toIsMulLeftInvariant := D.haar.1
    toIsOpenPosMeasure := D.haar.2.2.1 }

def tensH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (g : H E a b) : ℂ :=
  (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g)

theorem tensH_splitH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ)
    (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    tensH fa fb ψ (splitH a b z) = (∏ v, fa v (z.1 v)) * (∏ v, fb v (z.2.1 v)) * ψ z.2.2 := by
  simp only [tensH, gInf_splitH₁, gInf_splitH₂, hFin_splitH]

theorem integral_tensH_splitH [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb] (ν : Measure (Hf E a b)) [SigmaFinite ν]
    (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) :
    ∫ z, tensH fa fb ψ (splitH a b z) ∂((Measure.pi fun _ : InfinitePlace E => μa).prod
      ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)) =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν := by
  simp_rw [tensH_splitH]
  rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa v (y v))
    (fun y : InfinitePlace E → G b => ∏ v, fb v (y v)) ψ]
  beta_reduce
  rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]

set_option synthInstance.maxHeartbeats 400000 in
theorem compatFub : CompatFub := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ hC F hF hFc
  haveI := haar_of_dom D
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν
  have h1 := hC (fun _ => fa) (fun _ => fb) ψ (fun _ => ⟨hfa, hfac⟩) (fun _ => ⟨hfb, hfbc⟩) hψ hψc
  change ∫ g, tensH (fun _ => fa) (fun _ => fb) ψ g ∂D.μ = _ at h1
  rw [hc, integral_tensH_splitH] at h1
  have hc1 : c = 1 := by
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ h, ψ h ∂ν ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    rw [NNReal.smul_def, Complex.real_smul] at h1
    have h2 : ((c : ℝ) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
    exact_mod_cast h2
  rw [hc F, hc1, one_smul]
  exact integral_iter _ _ _ (fun z => F (splitH a b z)) (hF.comp (splitH a b).continuous)
    (hFc.comp_homeomorph (splitH a b).toHomeomorph)

theorem compatEx : CompatEx := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _
  haveI := haar_of_dom D
  haveI : D.μ.IsMulRightInvariant := D.haar.2.1
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  set ν₀ : Measure (Hf E a b) := Measure.haar
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν₀
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  have hR : ∀ h : Hf E a b, ν₀.map (· * h) = ν₀ := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k : NNReal, ν₀.map (· * h) = k • ν₀ := ⟨_, isMulLeftInvariant_eq_smul _ _⟩
    obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν₀
    have h1 := integral_mul_right_eq_self (μ := D.μ) (tensH (fun _ => fa) (fun _ => fb) ψ) (splitH a b (1, (1, h)))
    rw [hc, hc] at h1
    have e1 : ∀ z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b),
        tensH (fun _ => fa) (fun _ => fb) ψ (splitH a b z * splitH a b (1, (1, h))) =
          (∏ v, fa (z.1 v)) * (∏ v, fb (z.2.1 v)) * ψ (z.2.2 * h) := by
      intro z
      rw [← map_mul, tensH_splitH]
      simp
    simp_rw [e1] at h1
    rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa (y v))
      (fun y : InfinitePlace E → G b => ∏ v, fb (y v)) (fun w : Hf E a b => ψ (w * h)),
      integral_tensH_splitH] at h1
    beta_reduce at h1
    rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod] at h1
    have e2 : ∫ w, ψ (w * h) ∂ν₀ = k • ∫ w, ψ w ∂ν₀ := by
      rw [← integral_smul_nnreal_measure, ← hk, integral_map (measurable_mul_const h).aemeasurable
        hψ.aestronglyMeasurable]
    rw [e2] at h1
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀ ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    simp only [NNReal.smul_def, Complex.real_smul] at h1
    have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have h2 : ((k : ℝ) : ℂ) * (((c : ℝ) : ℂ) * ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) *
        (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) = 1 * (((c : ℝ) : ℂ) *
        ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) := by
      linear_combination h1
    have h3 : ((k : ℝ) : ℂ) = 1 := mul_right_cancel₀ (mul_ne_zero hc' hne) h2
    have hk1 : k = 1 := by exact_mod_cast h3
    rw [hk, hk1, one_smul]
  haveI : ν₀.IsMulRightInvariant := ⟨hR⟩
  refine ⟨c • ν₀, IsHaarMeasure.nnreal_smul _ hc0.ne', ⟨fun h => by
    rw [Measure.map_smul, hR]
    exact (measurable_mul_const h).aemeasurable⟩, ?_⟩
  intro fa' fb' ψ' hfa' hfb' hψ' hψc'
  change ∫ g, tensH fa' fb' ψ' g ∂D.μ = _
  rw [hc, integral_tensH_splitH, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  ring

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace PMul

section Loc

variable {n : ℕ}

theorem mem_GLs_val (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem entry_le_of_lg {y : G n} {R : ℝ} (h : lg y.val ≤ R) (p q : Fin n) :
    ‖y.val p q‖ ≤ Real.exp R ∧ ‖(y⁻¹ : G n).val p q‖ ≤ Real.exp R := by
  unfold lg at h
  set S := ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2) with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 + S ≤ Real.exp R := (Real.log_le_iff_le_exp (by linarith)).1 h
  have hterm : ‖y.val p q‖ ^ 2 + ‖(y.val)⁻¹ p q‖ ^ 2 ≤ S := by
    have e1 : ‖y.val p q‖ ^ 2 + ‖(y.val)⁻¹ p q‖ ^ 2 ≤ ∑ b, (‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ q)
    have e2 : ∑ b, (‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) ≤ S :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2)) (fun _ _ => by positivity)
        (Finset.mem_univ p)
    linarith
  have hinv : (y⁻¹ : G n).val = (y.val)⁻¹ := Matrix.coe_units_inv y
  rw [hinv]
  have a1 := norm_nonneg (y.val p q)
  have a2 := norm_nonneg ((y.val)⁻¹ p q)
  constructor <;> nlinarith [sq_nonneg (‖y.val p q‖ - 1), sq_nonneg (‖(y.val)⁻¹ p q‖ - 1)]

theorem isCompact_lg (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  set B : Set (Mat n) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.exp R)
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact (Units.embedProduct (Mat n) ⁻¹' (B ×ˢ (MulOpposite.op '' B))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  have hcl : IsClosed {y : G n | lg y.val ≤ R} := by
    refine isClosed_le ?_ continuous_const
    have hc : Continuous fun y : G n => (1 : ℝ) + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2) := by
      have hinv : (fun y : G n => (y.val)⁻¹) = fun y : G n => (y⁻¹ : G n).val := funext fun y => (Matrix.coe_units_inv y).symm
      have c1 : Continuous fun y : G n => (y.val)⁻¹ := by rw [hinv]; exact Units.continuous_val.comp continuous_inv
      have c0 : Continuous fun y : G n => y.val := Units.continuous_val
      refine continuous_const.add (continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_)
      exact (((continuous_apply q).comp ((continuous_apply p).comp c0)).norm.pow 2).add
        (((continuous_apply q).comp ((continuous_apply p).comp c1)).norm.pow 2)
    exact hc.log fun y => by positivity
  refine hK.of_isClosed_subset hcl fun y hy => ?_
  have h := fun p q => entry_le_of_lg (y := y) hy p q
  refine ⟨fun p _ q _ => ?_, ⟨(y⁻¹ : G n).val, fun p _ q _ => ?_, rfl⟩⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using (h p q).1
  · simpa [Metric.mem_closedBall, dist_zero_right] using (h p q).2

section Nrm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isMult_cts [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) :
    Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have hcont : ContinuousOn (fun x => ∑ i, c i • ks i x) (GLs n) :=
    continuousOn_finsetSum _ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)
  refine ⟨?_, ?_⟩
  · have e : (fun y : G n => k y.val) = fun y => ∑ i, c i • ks i y.val := funext fun y => hk _ (mem_GLs_val y)
    rw [e]
    exact hcont.comp_continuous Units.continuous_val mem_GLs_val
  · choose R hR using fun i => (hks i).2.2.1
    refine HasCompactSupport.intro (isCompact_lg (∑ i, |R i|)) fun y hy => ?_
    have hy' : ∑ i, |R i| < lg y.val := not_le.1 hy
    rw [hk _ (mem_GLs_val y)]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ i, |R i| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
    rw [hR i _ (mem_GLs_val y) (lt_of_le_of_lt hle hy'), smul_zero]

end Nrm

theorem ent_cont (M : KMod n) (i j : Ix M) : Continuous fun A : M.V →L[ℂ] M.V => ent M A i j := by
  unfold ent
  exact continuous_const.inner (continuous_id.clm_apply continuous_const)

theorem ent_mul (M : KMod n) (A B : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (A * B) i j = ∑ m, ent M A i m * ent M B m j := by
  unfold ent
  have hx : B (stdOrthonormalBasis ℂ M.V j) = ∑ m, inner ℂ (stdOrthonormalBasis ℂ M.V m)
      (B (stdOrthonormalBasis ℂ M.V j)) • stdOrthonormalBasis ℂ M.V m :=
    ((stdOrthonormalBasis ℂ M.V).sum_repr' _).symm
  rw [ContinuousLinearMap.mul_apply]
  conv_lhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

theorem loc_cts {M : KMod n} {k k' : Mat n → (M.V →L[ℂ] M.V)} (hk : Continuous fun y : G n => k y.val)
    (hks : HasCompactSupport fun y : G n => k y.val) (hk' : Continuous fun y : G n => k' y.val) (x : G n)
    (i m j : Ix M) :
    Continuous (fun y : G n => ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j) ∧
      HasCompactSupport (fun y : G n => ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j) := by
  refine ⟨((ent_cont M i m).comp hk).mul ((ent_cont M m j).comp (hk'.comp (continuous_inv.mul continuous_const))), ?_⟩
  exact HasCompactSupport.mul_right (hks.comp_left (g := fun A => ent M A i m) (ent_zero M i m))

theorem ent_conv [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (M : KMod n)
    {k k' : Mat n → (M.V →L[ℂ] M.V)} (hk : Continuous fun y : G n => k y.val)
    (hks : HasCompactSupport fun y : G n => k y.val) (hk' : Continuous fun y : G n => k' y.val) (x : G n)
    (i j : Ix M) :
    ent M (PositivityTheory.RgBcC.conv μ M k k' x.val) i j =
      ∑ m, ∫ y, ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j ∂μ := by
  have e : PositivityTheory.RgBcC.conv μ M k k' x.val = ∫ y, k y.val * k' (y⁻¹ * x).val ∂μ := by
    unfold PositivityTheory.RgBcC.conv
    simp only [Units.val_mul]
  have hFc : Continuous fun y : G n => k y.val * k' (y⁻¹ * x).val :=
    hk.mul (hk'.comp (continuous_inv.mul continuous_const))
  have hFs : HasCompactSupport fun y : G n => k y.val * k' (y⁻¹ * x).val := hks.mul_right
  have hFi := hFc.integrable_of_hasCompactSupport (μ := μ) hFs
  have h1 : ent M (∫ y, k y.val * k' (y⁻¹ * x).val ∂μ) i j =
      ∫ y, ent M (k y.val * k' (y⁻¹ * x).val) i j ∂μ := by
    unfold ent
    rw [ContinuousLinearMap.integral_apply hFi, ← integral_inner]
    exact (hFc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hFs.comp_left (g := fun A : M.V →L[ℂ] M.V => A (stdOrthonormalBasis ℂ M.V j)) (by simp))
  rw [e, h1]
  calc ∫ y, ent M (k y.val * k' (y⁻¹ * x).val) i j ∂μ
      = ∫ y, ∑ m, ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j ∂μ := by
        congr 1; funext y; exact ent_mul M _ _ i j
    _ = _ := integral_finsetSum _ fun m _ =>
        (loc_cts hk hks hk' x i m j).1.integrable_of_hasCompactSupport (loc_cts hk hks hk' x i m j).2

end Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def fA {M : Mods E n} (k k' : Kers M) (i j m : IxA M) (y : GA E n) (v : InfinitePlace E) (x : G n) : ℂ :=
  ent (M v) (k v x.val) (i v) (m v) * ent (M v) (k' v (x⁻¹ * gInf v y).val) (m v) (j v)

theorem fA_cts [MeasurableSpace (G n)] {μ μ' : Measure (G n)} {M : Mods E n} {k k' : Kers M} {val val' T T'}
    (hk : IsMults μ k val T) (hk' : IsMults μ' k' val' T') (i j m : IxA M) (y : GA E n) (v : InfinitePlace E) :
    Continuous (fA k k' i j m y v) ∧ HasCompactSupport (fA k k' i j m y v) :=
  loc_cts (isMult_cts (hk v)).1 (isMult_cts (hk v)).2 (isMult_cts (hk' v)).1 (gInf v y) (i v) (m v) (j v)

theorem entA_convK [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {μ' : Measure (G n)}
    {M : Mods E n} {k k' : Kers M} {val val' T T'} (hk : IsMults μ k val T) (hk' : IsMults μ' k' val' T')
    (i j : IxA M) (y : GA E n) :
    entA (convK μ k k') i j y = ∑ m : IxA M, ∏ v, ∫ x, fA k k' i j m y v x ∂μ := by
  unfold entA convK
  rw [Finset.prod_congr rfl fun v _ => ent_conv μ (M v) (isMult_cts (hk v)).1 (isMult_cts (hk v)).2
    (isMult_cts (hk' v)).1 (gInf v y) (i v) (j v)]
  rw [Fintype.prod_sum]
  rfl

theorem mulF_fin [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
    {κ : Type} [Fintype κ] {ψ ψ' : Matrix κ κ (Hf E a b → ℂ)} (hψ : IsFinM ψ) (hψ' : IsFinM ψ') : IsFinM (mulF ν ψ ψ') := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro x y
  refine ⟨continuous_finsetSum _ fun z _ => ?_, ?_⟩
  · have e : (fun g => ∫ h, ψ x z h * ψ' z y (h⁻¹ * g) ∂ν) =
        fun g => ∫ h in tsupport (ψ x z), ψ x z h * ψ' z y (h⁻¹ * g) ∂ν := by
      funext g
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
    rw [e]
    refine continuous_parametric_integral_of_continuous ?_ (hψ x z).2.isCompact
    exact ((hψ x z).1.comp continuous_snd).mul ((hψ' z y).1.comp (continuous_snd.inv.mul continuous_fst))
  · refine HasCompactSupport.intro (isCompact_iUnion fun z => (hψ x z).2.isCompact.mul (hψ' z y).2.isCompact)
      fun g hg => ?_
    refine Finset.sum_eq_zero fun z _ => ?_
    have : ∀ h, ψ x z h * ψ' z y (h⁻¹ * g) = 0 := by
      intro h
      by_cases h1 : h ∈ tsupport (ψ x z)
      · have h2 : h⁻¹ * g ∉ tsupport (ψ' z y) := fun h2 =>
          hg (Set.mem_iUnion.2 ⟨z, Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩⟩)
        rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
    simp [this]

theorem mulM_tens (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
    {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]
    {ka ka' : Kers Ma} {kb kb' : Kers Mb} {va va' vb vb'} {T T' : ℝ} {ψ ψ' : Matrix κ κ (Hf E a b → ℂ)}
    (hC : Compat D μa μb ν) (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hka' : IsMults μa ka' va' T')
    (hkb' : IsMults μb kb' vb' T') (hψ : IsFinM ψ) (hψ' : IsFinM ψ') :
    mulM D.μ (tens ka kb ψ) (tens ka' kb' ψ') = tens (convK μa ka ka') (convK μb kb kb') (mulF ν ψ ψ') := by
  funext i j y
  have step : ∀ k : Io Ma Mb κ, ∫ z, tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y) ∂D.μ =
      (∏ v, ∫ x, fA ka ka' i.1.1 j.1.1 k.1.1 y.1 v x ∂μa) * (∏ v, ∫ x, fA kb kb' i.1.2 j.1.2 k.1.2 y.2 v x ∂μb) *
        ∫ h, ψ i.2 k.2 h * ψ' k.2 j.2 (h⁻¹ * hFin y) ∂ν := by
    intro k
    have e : (fun z => tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y)) = fun z =>
        (∏ v, fA ka ka' i.1.1 j.1.1 k.1.1 y.1 v (gInf v z.1)) * (∏ v, fA kb kb' i.1.2 j.1.2 k.1.2 y.2 v (gInf v z.2)) *
          (fun h => ψ i.2 k.2 h * ψ' k.2 j.2 (h⁻¹ * hFin y)) (hFin z) := by
      funext z
      have hz : hFin (z⁻¹ * y) = (hFin z)⁻¹ * hFin y := by simp [hFin]
      simp only [tens, entA, fA, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, map_mul, map_inv, hz,
        Finset.prod_mul_distrib]
      ring
    rw [e]
    exact hC _ _ _ (fun v => fA_cts hka hka' _ _ _ _ v) (fun v => fA_cts hkb hkb' _ _ _ _ v)
      ((hψ i.2 k.2).1.mul ((hψ' k.2 j.2).1.comp (continuous_inv.mul continuous_const))) (hψ i.2 k.2).2.mul_right
  show ∑ k, ∫ z, tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y) ∂D.μ =
    entA (convK μa ka ka') i.1.1 j.1.1 y.1 * entA (convK μb kb kb') i.1.2 j.1.2 y.2 * mulF ν ψ ψ' i.2 j.2 (hFin y)
  rw [Finset.sum_congr rfl fun k _ => step k, entA_convK μa hka hka', entA_convK μb hkb hkb']
  unfold mulF
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

end PMul


open PMul in
theorem tensMul : TensMul := fun _ _ _ _ _ _ D _ _ _ _ _ _ μa _ μb _ ν _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hka hkb hka'
    hkb' hψ hψ' => ⟨mulF_fin ν hψ hψ', mulM_tens D μa μb ν hC hka hkb hka' hkb' hψ hψ'⟩

end PositivityTheory.Rg.BcB.CG
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical ComplexConjugate

namespace PositivityTheory.Rg.BcB.CG

theorem trace_mul_ent {n : ℕ} (M : KMod n) (A B : M.V →L[ℂ] M.V) :
    LinearMap.trace ℂ M.V ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) = ∑ i, ∑ j, ent M A i j * ent M B j i := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ M.V)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((A * B : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) (stdOrthonormalBasis ℂ M.V i) =
      A (∑ j, inner ℂ (stdOrthonormalBasis ℂ M.V j) (B (stdOrthonormalBasis ℂ M.V i)) • stdOrthonormalBasis ℂ M.V j) := by
    rw [(stdOrthonormalBasis ℂ M.V).sum_repr']; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, ent, ent, mul_comm]

theorem phiOf_eq {n : ℕ} (M : KMod n) (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) (y : G n) :
    phiOf M Tθ k y = ∑ p, ∑ q, ent M (k y.val) p q * ent M Tθ q p :=
  trace_mul_ent M _ _

theorem ent_adjoint {n : ℕ} (M : KMod n) [CompleteSpace M.V] (A : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (ContinuousLinearMap.adjoint A) i j = conj (ent M A j i) := by
  simp only [ent]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem sum_pair {α β : Type} [Fintype α] [Fintype β] (X : α → α → ℂ) (Y : β → β → ℂ) :
    ∑ i : α × β, ∑ j : α × β, X i.1 j.1 * Y i.2 j.2 = (∑ p, ∑ q, X p q) * ∑ p, ∑ q, Y p q := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_io {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] (A A' : α → α → ℂ) (B B' : β → β → ℂ)
    (C D : κ → κ → ℂ) :
    ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
        A i.1.1 j.1.1 * B i.1.2 j.1.2 * C i.2 j.2 * (A' j.1.1 i.1.1 * B' j.1.2 i.1.2 * D j.2 i.2) =
      (∑ p, ∑ q, A p q * A' q p) * (∑ p, ∑ q, B p q * B' q p) * ∑ x, ∑ y, C x y * D y x := by
  calc _ = ∑ i : (α × β) × κ, ∑ j : (α × β) × κ,
          (A i.1.1 j.1.1 * A' j.1.1 i.1.1 * (B i.1.2 j.1.2 * B' j.1.2 i.1.2)) * (C i.2 j.2 * D j.2 i.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ p : α × β, ∑ q : α × β, A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) * ∑ x, ∑ y, C x y * D y x :=
        sum_pair (fun p q : α × β => A p.1 q.1 * A' q.1 p.1 * (B p.2 q.2 * B' q.2 p.2)) (fun x y => C x y * D y x)
    _ = _ := by
        rw [sum_pair (fun p q => A p q * A' q p) (fun p q => B p q * B' q p)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem prod_sum_ent (M : Mods E n) (A B : Ops M) :
    ∏ v, (∑ p, ∑ q, ent (M v) (A v) p q * ent (M v) (B v) q p) =
      ∑ P : IxA M, ∑ Q : IxA M, (∏ v, ent (M v) (A v) (P v) (Q v)) * ∏ v, ent (M v) (B v) (Q v) (P v) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact Finset.prod_mul_distrib

theorem tensTr : TensTr := by
  intro E _ _ _ a b Ma Mb κ _ ka kb Ta Tb ψ N g
  have ha := prod_sum_ent Ma (fun v => ka v (gInf v g.1).val) Ta
  have hb := prod_sum_ent Mb (fun v => kb v (gInf v g.2).val) Tb
  simp only [F.trM, tens, opM, entA, phiOf_eq]
  rw [ha, hb]
  exact sum_io (α := IxA Ma) (β := IxA Mb) (κ := κ)
    (fun P Q : IxA Ma => ∏ v, ent (Ma v) (ka v (gInf v g.1).val) (P v) (Q v))
    (fun Q P : IxA Ma => ∏ v, ent (Ma v) (Ta v) (Q v) (P v))
    (fun P Q : IxA Mb => ∏ v, ent (Mb v) (kb v (gInf v g.2).val) (P v) (Q v))
    (fun Q P : IxA Mb => ∏ v, ent (Mb v) (Tb v) (Q v) (P v)) (fun x y : κ => ψ x y (hFin g)) (fun y x : κ => N y x)

theorem gInf_eq (v : InfinitePlace E) (g : GA E n) :
    gInf v g = GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v)
      (GeneralLinearGroup.map (pInf E) g) := rfl

theorem continuous_hFin : Continuous (hFin (E := E) (a := a) (b := b)) :=
  ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.1.comp continuous_fst).prodMk ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.1.comp continuous_snd)

theorem hFin_inv (g : H E a b) : hFin g⁻¹ = (hFin g)⁻¹ :=
  Prod.ext (map_inv (gFin (E := E) (n := a)) g.1) (map_inv (gFin (E := E) (n := b)) g.2)

def ofComps (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y)

theorem continuous_ofComps : Continuous (ofComps (E := E) (n := n)) := by
  have hc : Continuous fun x : InfinitePlace E → Mat n =>
      (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm x :=
    continuous_matrix fun i j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  exact (Continuous.units_map _ hc).comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E => Mat n)).symm.continuous

theorem ofComps_gInf (g : GA E n) : ofComps (fun v => gInf v g) = GeneralLinearGroup.map (pInf E) g :=
  Units.ext (Matrix.ext fun _ _ => funext fun _ => rfl)

theorem hasCompactSupport_of_section {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {F : X → ℂ}
    (p : X → Y) (s : Y → X) (hs : Continuous s) (hsp : ∀ x, s (p x) = x) {K : Set Y} (hK : IsCompact K)
    (hF : ∀ x, F x ≠ 0 → p x ∈ K) : HasCompactSupport F :=
  HasCompactSupport.intro (hK.image hs) fun x hx => by
    by_contra h
    exact hx ⟨p x, hF x h, hsp x⟩

def ofParts (y : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b) : H E a b :=
  (infGL E a (ofComps y.1.1) * finGL E a y.2.1, infGL E b (ofComps y.1.2) * finGL E b y.2.2)

theorem continuous_ofParts : Continuous (ofParts (E := E) (a := a) (b := b)) :=
  (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.1.comp (continuous_ofComps.comp (continuous_fst.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a).2.2.2.comp (continuous_fst.comp continuous_snd))).prodMk
    (((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.1.comp (continuous_ofComps.comp (continuous_snd.comp continuous_fst))).mul
      ((GlobalTheory.T.continuous_GL_adelic_projections_inclusions E b).2.2.2.comp (continuous_snd.comp continuous_snd)))

theorem ofParts_parts (g : H E a b) : ofParts ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g) = g := by
  refine Prod.ext ?_ ?_
  · show infGL E a (ofComps fun v => gInf v g.1) * finGL E a (gFin g.1) = g.1
    rw [ofComps_gInf]; exact infGL_mul_finGL g.1
  · show infGL E b (ofComps fun v => gInf v g.2) * finGL E b (gFin g.2) = g.2
    rw [ofComps_gInf]; exact infGL_mul_finGL g.2

theorem entA_adjK (M : Mods E n) (k : Kers M) (i j : IxA M) (g : GA E n) :
    entA (adjK k) i j g = conj (entA k j i g⁻¹) := by
  simp only [entA, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : (gInf v g⁻¹).val = (gInf v g).val⁻¹ := by rw [map_inv]; exact Matrix.coe_units_inv _
  rw [e]
  have := FiniteDimensional.complete ℂ (M v).V
  exact ent_adjoint (M v) _ (i v) (j v)

theorem tens_entry {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [MeasurableSpace (G a)] [MeasurableSpace (G b)]
    {μa : Measure (G a)} {μb : Measure (G b)} {ka : Kers Ma} {kb : Kers Mb} {va vb} {T : ℝ}
    {ψ : Matrix κ κ (Hf E a b → ℂ)} (hA : IsMults μa ka va T) (hB : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (i j : Io Ma Mb κ) : Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  set_option synthInstance.maxHeartbeats 200000 in
    have cA : ∀ v, Continuous fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v) := fun v =>
      (mult_ent (hA v) _ _).1
    have cB : ∀ v, Continuous fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v) := fun v =>
      (mult_ent (hB v) _ _).1
    refine ⟨?_, ?_⟩
    · exact ((continuous_finsetProd _ fun v _ => (cA v).comp ((continuous_gInf a v).comp continuous_fst)).mul
        (continuous_finsetProd _ fun v _ => (cB v).comp ((continuous_gInf b v).comp continuous_snd))).mul
        ((hψ i.2 j.2).1.comp continuous_hFin)
    · refine hasCompactSupport_of_section (fun g : H E a b => ((fun v => gInf v g.1, fun v => gInf v g.2), hFin g))
        ofParts continuous_ofParts ofParts_parts
        (K := (Set.univ.pi (fun v => tsupport fun y : G a => ent (Ma v) (ka v y.val) (i.1.1 v) (j.1.1 v)) ×ˢ
          Set.univ.pi (fun v => tsupport fun y : G b => ent (Mb v) (kb v y.val) (i.1.2 v) (j.1.2 v))) ×ˢ
          tsupport (ψ i.2 j.2))
        (((isCompact_univ_pi fun v => (mult_ent (hA v) _ _).2).prod
          (isCompact_univ_pi fun v => (mult_ent (hB v) _ _).2)).prod (hψ i.2 j.2).2) fun g hg => ?_
      have hg' : entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g) ≠ 0 := hg
      obtain ⟨⟨h1, h2⟩, h3⟩ := mul_ne_zero_iff.1 hg' |>.imp_left mul_ne_zero_iff.1
      refine ⟨⟨fun v _ => subset_tsupport _ ?_, fun v _ => subset_tsupport _ ?_⟩, subset_tsupport _ h3⟩
      · exact Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)
      · exact Finset.prod_ne_zero_iff.1 h2 v (Finset.mem_univ v)

theorem tensTest : TensTest := by
  intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb κ _ ka kb va vb T ψ hA hB hψ
  refine ⟨fun i j => tens_entry hA hB hψ i j, ?_⟩
  funext i j y
  show starRingEnd ℂ (tens ka kb ψ j i y⁻¹) = tens (adjK ka) (adjK kb) (adjF ψ) i j y
  simp only [tens, adjF, entA_adjK, map_mul, hFin_inv, Prod.fst_inv, Prod.snd_inv]

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def ValCont : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (k : Mat n → (M.V →L[ℂ] M.V))
  (val : Inf n → ℂ) (T : ℝ) (χ : ℕ → Inf n) (χ₀ : Inf n), IsMult μ M k val T →
  (∀ s m, Tendsto (fun j => GlobalTheory.Dec.gelfVal (χ j s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χ₀ s) m))) →
  Tendsto (fun j => val (χ j)) atTop (𝓝 (val χ₀))

def Pack : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (κ : Type) [Fintype κ]
    (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (g : ℝ → ℝ)
    (ka' : Bool → ℕ → Kers Ma) (kb' : Bool → ℕ → Kers Mb) (K₁ : Subgroup (GL (Fin a) (Af E)))
    (K₂ : Subgroup (GL (Fin b) (Af E))) (M : ℕ) (f : Io Ma Mb κ → H E a b → ℂ) (c : ℂ)
    (ca cb : InfinitePlace E → Bool → ℕ → ℂ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
    IsBump g T → (∀ v, IsKer μa (Ma v) [] g (ka v)) → (∀ v, IsKer μb (Mb v) [] g (kb v)) →
    (∀ s m v, IsKer μa (Ma v) [(s, m)] g (ka' s m v)) → (∀ s m v, IsKer μb (Mb v) [(s, m)] g (kb' s m v)) →
    IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
    (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) →
    (∀ i, Continuous (f i)) → f ≠ 0 → LeftInv f → WL2 D M f → c ≠ 0 →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v (ka' s m v)) kb ψ) f = ca v s m • f) →
    (∀ v s m, PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v (kb' s m v)) ψ) f = cb v s m • f) →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = ca v s m / c) ∧ (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = cb v s m / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

theorem pack_of (h1 : TensTest) (h2 : TypeOf) (h3 : SmoothOf) (h4 : GrowthOf) (h5 : GelOf) (h6 : InfEx) (h7 : AutOf) :
    Pack := by
  intro E _ _ _ a b Ma Mb
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := h2 E a b Ma Mb
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D _ _ _ _ _ _ μa _ μb _ ν _ κ _ ka kb va vb T ψ g ka' kb' K₁ K₂ M f c ca cb hC hka hkb hψ hg k0a k0b k1a k1b
    o₁ o₂ hlev hf hf0 hL hW2 hc he hea heb
  have hR : Repr D ka kb ψ f := ⟨hf, c, hc, he⟩
  have hty := hW D μa μb κ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hR
  obtain ⟨s₁, s₂⟩ := h3 E a b μa μb Ma Mb κ D ka kb va vb T ψ (K₁.prod K₂) f hka hkb hψ (o₁.prod o₂)
    (fun x y u hu h => hlev x y u.1 hu.1 u.2 hu.2 h) hR
  obtain ⟨C, N, hG⟩ := h4 E a b D _ _ M f c (h1 E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1 hf hL hW2 hc he
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hf0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hi₀
  have ga := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (ca v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).1
    _ (k0a v) (k1a s m v) (hea v s m)
  have gb := fun v s m => (h5 E a b D μa μb ν Ma Mb κ ka kb va vb T ψ f c (cb v s m) v g s m hC hka hkb hψ hg ⟨s₁, s₂⟩ hf hc he).2
    _ (k0b v) (k1b s m v) (heb v s m)
  have ea : ∀ v, ∃ χ : Inf a, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = ca v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₁ i₀ x₀.2
    refine h6 E a {φ} v (fun s m => ca v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.1
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact ga v s m i₀ y x₀.2 x hx
  have eb : ∀ v, ∃ χ : Inf b, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = cb v s m / c := fun v => by
    obtain ⟨φ, hφ⟩ := s₂ i₀ x₀.1
    refine h6 E b {φ} v (fun s m => cb v s m / c) ⟨φ, rfl, fun e => hx₀ ?_⟩ ?_
    · have := congrFun hφ x₀.2
      rw [e] at this
      exact this.symm
    · rintro _ rfl y s m x hx
      rw [hφ]
      exact gb v s m i₀ y x₀.1 x hx
  choose χa hχa using ea
  choose χb hχb using eb
  have hE : EigAll χa χb f :=
    ⟨fun i v y m₂ s m x hx => by rw [hχa]; exact ga v s m i y m₂ x hx,
      fun i v y m₁ s m x hx => by rw [hχb]; exact gb v s m i y m₁ x hx⟩
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h7 E a b _ f K₁ K₂ W₁ W₂ χa χb C N o₁ o₂ f₁ f₂ hL hty hG hE
  exact ⟨χa, χb, hχa, hχb, hE, hty, s₁, s₂, a₁, a₂, a₃, a₄⟩

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.FinHecke
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH HeckeM heckeAct)
open scoped Classical

namespace PositivityTheory.Rg.BcB.CG

theorem finH_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

theorem finHecke : FinHecke := by
  intro E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU

  set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK
  have hKc : IsCompact K := isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2

  let C : Hf E a b ⧸ U → Set (Hf E a b) := fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))
  have hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q := by
    intro q h
    show q.out⁻¹ * h ∈ U ↔ _
    rw [← QuotientGroup.eq]
    simp only [Quotient.out_eq]
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hUo.preimage (continuous_const.mul continuous_id)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hCo q).measurableSet
  have hCf : ∀ q, ν (C q) ≠ ⊤ := by
    intro q
    show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤
    rw [measure_preimage_mul]
    exact hUc.measure_lt_top.ne
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover C hCo (by
    intro h _
    exact Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)
  have hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t) := by
    intro h x y hne
    have hhK : h ∈ K := Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (ht hhK)
    obtain ⟨hqt, hq⟩ := Set.mem_iUnion.1 hq
    rwa [(hCmem q h).1 hq]
  refine ⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0,
    ?_, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · intro p q x y
    simp
  · intro f hf
    funext i X
    simp only [convF, heckeAct]
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single i.1 (fun p _ hp => by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (Ne.symm hp)]
      simp) (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [if_true]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ
    have hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h := by
      intro h u hu
      simp only [hΦ]
      rw [finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]
    have hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h := by
      intro h
      have h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U := (hCmem _ h).2 rfl
      calc Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out
          = Φ ((QuotientGroup.mk h : Hf E a b ⧸ U).out * ((QuotientGroup.mk h : Hf E a b ⧸ U).out⁻¹ * h)) :=
            (hΦU _ _ h1).symm
        _ = Φ h := by rw [mul_inv_cancel_left]
    have hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h := by
      funext h
      rw [Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]
      · rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hc
        exact hq ((hCmem q h).1 hc).symm
      · intro hmem
        rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
        by_contra hne
        apply hmem
        refine hin h i.2 z ?_
        intro h0
        apply hne
        simp only [hΦ, h0, zero_mul]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]
      simp only [hΦ, Complex.real_smul, Measure.real]
      ring
    · intro q _
      exact (integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))

end PositivityTheory.Rg.BcB.CG

end
end
