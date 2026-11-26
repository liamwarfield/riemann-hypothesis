module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEvaluationBijectiveSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEvaluationBijectiveSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.InvTame

open Filter
open scoped Classical

theorem isTame_inv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij A hA g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end GlobalTheory.InvTame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEvaluationBijectiveSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_model_evaluation_bijective_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  first | exact @GlobalTheory.InvTame.isTame_inv | exact GlobalTheory.InvTame.isTame_inv | (intros; apply GlobalTheory.InvTame.isTame_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportional
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem lintegral_sq_split {Z X Y : Type} [TopologicalSpace Z] [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X]
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : Z ≃ₜ X × Y) (he : ∀ a b, e (a + b) = e a + e b)
    (μ : Measure Z) [μ.IsAddHaarMeasure] (μX : Measure X) [μX.IsAddHaarMeasure]
    {f g : Z → ℂ} (hf : Continuous f) (hg : Continuous g) (c : ℝ≥0∞)
    (h : ∀ y, ∫⁻ x, ‖f (e.symm (x, y))‖ₑ ^ 2 ∂μX = c * ∫⁻ x, ‖g (e.symm (x, y))‖ₑ ^ 2 ∂μX) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = c * ∫⁻ z, ‖g z‖ₑ ^ 2 ∂μ := by
  let E : Z ≃ₜ+ X × Y :=
    { e.toEquiv with
      map_add' := he
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let eM : Z ≃ᵐ X × Y := e.toMeasurableEquiv
  let μY : Measure Y := Measure.addHaar
  haveI hν : (μ.map E).IsAddHaarMeasure := inferInstance
  have hE : (E : Z → X × Y) = eM := rfl
  set s := Measure.addHaarScalarFactor (μ.map E) (μX.prod μY)
  have hs : μ.map E = s • (μX.prod μY) := Measure.isAddLeftInvariant_eq_smul _ _
  have key : ∀ F : Z → ℂ, Continuous F →
      ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
    intro F hF
    have hm : Measurable fun p : X × Y => ‖F (e.symm p)‖ₑ ^ 2 :=
      ((hF.comp e.symm.continuous).measurable.enorm.pow_const 2)
    calc ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = ∫⁻ p, ‖F (e.symm p)‖ₑ ^ 2 ∂(μ.map E) := by
          rw [hE, lintegral_map_equiv]; simp [eM]
      _ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
          rw [hs, lintegral_smul_measure, lintegral_prod_symm _ hm.aemeasurable]; rfl
  rw [key f hf, key g hg]
  have hmg : Measurable fun p : X × Y => ‖g (e.symm p)‖ₑ ^ 2 :=
    ((hg.comp e.symm.continuous).measurable.enorm.pow_const 2)
  simp_rw [h]
  rw [lintegral_const_mul _ (hmg.lintegral_prod_left' )]
  ring

end GlobalTheory.DoublingEvaluationL2

namespace GlobalTheory.DoublingEvaluationL2

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  intro F _ _ κ κ' _ _ A hA hL2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  let μX : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc⟩ := hL2 μX inferInstance
  constructor
  · intro μ hμ
    letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
    haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_left F κ κ κ' A hA) Φ hΦ
    refine lintegral_sq_split (Homeomorph.sumPiEquivProdPi κ κ' (fun _ => AF F)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
  · intro μ hμ
    letI mZ : MeasurableSpace (κ' ⊕ κ → AF F) := borel _
    haveI : BorelSpace (κ' ⊕ κ → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_right F κ' κ κ A hA) Φ hΦ
    refine lintegral_sq_split ((Homeomorph.sumPiEquivProdPi κ' κ (fun _ => AF F)).trans
        (Homeomorph.prodComm _ _)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceR hΦ y)

end GlobalTheory.DoublingEvaluationL2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportionalStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_haar_norm_proportional : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.DoublingEvaluationL2.main | exact GlobalTheory.DoublingEvaluationL2.main | (intros; apply GlobalTheory.DoublingEvaluationL2.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblESymmToLinearMap
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem elim_dot' {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

section Coord

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) w w' = hTens c JA JB w.toCols₁ w'.toCols₁ - hTens c JA JB w.toCols₂ w'.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.toCols₁_apply, Matrix.toCols₂_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) w w' = symp c ξ JA JB w.toCols₁ w'.toCols₁ - symp c ξ JA JB w.toCols₂ w'.toCols₂ := by
  unfold symp
  rw [hTens_dbl, mul_sub, map_sub]

variable [Invertible (2 : R)] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

def dblCo (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun w => (Sum.elim (d.e w.toCols₁).1 (d.e w.toCols₂).1, Sum.elim (d.e w.toCols₁).2 (-(d.e w.toCols₂).2))
      map_add' := fun w w' => by
        have h1 : (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ := by ext; simp
        have h2 : (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ := by ext; simp
        rw [h1, h2, map_add (f := _), map_add (f := _)]
        ext k <;> cases k <;> simp [add_comm]
      map_smul' := fun a w => by
        have h1 : (a • w).toCols₁ = a • w.toCols₁ := by ext; simp
        have h2 : (a • w).toCols₂ = a • w.toCols₂ := by ext; simp
        rw [h1, h2, map_smul, map_smul]
        ext k <;> cases k <;> simp
      invFun := fun p => Matrix.fromCols (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      left_inv := fun w => by
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_neg, Prod.mk.eta, LinearEquiv.symm_apply_apply]
        exact Matrix.fromCols_toCols w
      right_inv := fun p => by
        simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply, neg_neg,
          Sum.elim_comp_inl_inr] }
  form w w' := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [symp_dbl, d.form, d.form, elim_dot', elim_dot', dotProduct_neg, dotProduct_neg]
    ring

theorem dblCo_isDblCoord (d : Darboux (symp c ξ JA JB) κ) : IsDblCoord c ξ JA JB d (dblCo c d) := fun w₁ w₂ => by
  simp [dblCo]

end Coord

section Equivs

variable {R : Type}

def conjE {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

theorem conjE_apply {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) (φ : X → ℂ) : conjE T φ = star (T (star φ)) := rfl

def partLE {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partRE {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblE {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partRE (conjE T)).trans (partLE T)

end Equivs

end GlobalTheory.DblInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesSchwartz
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem evDbl_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem hasDbl_of_tame {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E]
    (c : E →ₐ[AF F] E) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (hT : IsGoodInt (adeleClass F) ψ d d₁ T) (ht : IsTame F T.toLinearMap) (hti : IsTame F T.symm.toLinearMap) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hS : IsTame F (conjMap T.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht
  have hSi : IsTame F (conjMap T.symm.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht
  have hRi : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi
  have hLi : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti
  have hD : IsTame F (dblE T).toLinearMap := hR.comp hL
  have hDi : IsTame F (dblE T).symm.toLinearMap := hLi.comp hRi
  have hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ := fun φ hφ =>
    GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    rw [conjE_apply]
    constructor
    · intro h
      exact hstar _ ((hsp _).1 (hstar _ h))
    · intro h
      have h1 : T (star φ) ∈ schA F κ := by simpa using hstar _ h
      simpa using hstar _ ((hsp _).2 h1)
  have hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := hunit
  have hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨c₀, hc₀⟩ := hunit μ hμ
    refine ⟨c₀, fun φ hφ => ?_⟩
    have h := hc₀ (star φ) (hstar φ hφ)
    simp only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢
    exact h
  refine ⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁,
    ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩,
      fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hDi.mapsTo _ h
    rw [show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ] at this
    exact this
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩
    have e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2)) := by
      unfold Darboux.rho; rw [hdd]
    have e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2)) := by
      unfold Darboux.rho; rw [dblCo_isDblCoord]
    rw [e1, e2]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hDi.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨c₁, hc₁⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ
    obtain ⟨c₂, hc₂⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ
    refine ⟨c₁ * c₂, fun Φ hΦ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _
    rw [hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    GlobalTheory.T.good_model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti

end GlobalTheory.DblInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_evaluation_preserves_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  first | exact @GlobalTheory.DblInt.main | exact GlobalTheory.DblInt.main | (intros; apply GlobalTheory.DblInt.main <;> assumption)
end
