module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorus
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem sigmaFinite_comap_of_measurable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y)
    (hf : Measurable f) (μ : Measure Y) [SigmaFinite μ] : SigmaFinite (μ.comap f) := by
  by_cases h : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · refine ⟨⟨⟨fun n => f ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.comap_apply₀ f μ h.1 h.2 ((measurableSet_spanningSets μ n).preimage hf).nullMeasurableSet]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  · rw [Measure.comap, dite_eq_right h]; infer_instance

theorem fubini_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  intro F E _ _ _ _ _ A r τ p hG M μK hμK α Φ hΦ hαlc hαcs hα0 c h1
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  obtain ⟨hBor, hHaar, -⟩ := GlobalTheory.JR.LinDesc.unitsMeas_isHaar F E A μK hμK
  haveI := hBor
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) F) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin r) F) := Units.isEmbedding_embedProduct.t2Space
  have e := (LinDesc.bas A hG).equivFun
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  haveI : SecondCountableTopology A.K := (Homeomorph.mk e.toEquiv he1 he2).secondCountableTopology
  haveI : SigmaFinite μK := inferInstance
  haveI : SigmaFinite (LinDesc.unitsMeas A μK) := by
    unfold LinDesc.unitsMeas
    haveI : SigmaFinite (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹) :=
      SigmaFinite.withDensity_ofReal _
    exact sigmaFinite_comap_of_measurable _ (measurable_iff_comap_le.2 le_rfl) _
  have htm : Continuous (LinDesc.tm A hG) := Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (LinDesc.bas A hG)).toLinearMap)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hαc : Continuous α := hαlc.continuous
  have hC : IsCompact (tsupport Φ) := hΦ.2
  have hz : ∀ g, g ∉ tsupport Φ → Φ g = 0 := fun g hg => image_eq_zero_of_notMem_tsupport hg
  haveI : IsFiniteMeasure (M.μG.restrict (tsupport Φ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  set ν := LinDesc.unitsMeas A μK with hν
  set f : A.Kˣ → GL (Fin r) F → ℂ := fun s g => Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) with hf
  have hfc : Continuous (Function.uncurry f) := by
    refine (hΦc.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hαc.comp ?_))
    exact (continuous_snd.mul continuous_const).mul (htm.comp continuous_fst)
  have hin : ∀ g, Integrable (fun s => f s g) ν := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · have hi : Integrable (fun s => α (g * c * LinDesc.tm A hG s)) ν :=
        Integrable.of_integral_ne_zero (by rw [h1 g hg]; exact one_ne_zero)
      exact hi.ofReal.const_mul (Φ g)
  have hnorm : ∀ g, ∫ s, ‖f s g‖ ∂ν = ‖Φ g‖ := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · simp only [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hα0 _)]
      rw [integral_const_mul, h1 g hg, mul_one]
  have hint : Integrable (Function.uncurry f) (ν.prod (M.μG.restrict (tsupport Φ))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hin, ?_⟩
    exact (hΦc.norm.continuousOn.integrableOn_compact hC).congr (Eventually.of_forall fun g => (hnorm g).symm)
  have eL : ∀ s, ∫ g, f s g ∂M.μG = ∫ g in tsupport Φ, f s g ∂M.μG := fun s =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => by simp [hf, hz g hg]).symm
  have eR : ∫ g, Φ g ∂M.μG = ∫ g in tsupport Φ, Φ g ∂M.μG :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hz g hg).symm
  show ∫ s, ∫ g, f s g ∂M.μG ∂ν = ∫ g, Φ g ∂M.μG
  simp_rw [eL, eR]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : Φ g = 0
  · simp [hf, hg]
  · simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal, h1 g hg, Complex.ofReal_one, mul_one]

end GlobalTheory.JR.LinDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorusStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  first | exact @GlobalTheory.JR.LinDesc.fubini_cutoff | exact GlobalTheory.JR.LinDesc.fubini_cutoff | (intros; apply GlobalTheory.JR.LinDesc.fubini_cutoff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralLinearDescentCutoff
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem valuationParitySign_mul_self {F : Type} [NormedField F] (x : F) : eta x * eta x = 1 := by
  unfold eta; split_ifs <;> norm_num

theorem valuationParitySign_one {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta; rw [if_pos ⟨1, by simp⟩]

theorem desc_unit_eq {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F)
    (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (a s : A.Kˣ) :
    desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s =
      A.etaK a * (letI := M.mG; ∫ g, f' (act g (pt A hG lam 1 a)) * eta ((g : Matrix (Fin r) (Fin r) F).det) *
        (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG) := by
  letI := M.mG
  haveI := M.bG
  haveI : M.μG.IsMulRightInvariant := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  have hmul := (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1
  set Y := pt A hG lam 1 (a : A.K) with hY
  set u : A.Kˣ := a * s⁻¹ with hu
  have hpt : pt A hG lam ((a : A.K) * Ring.inverse (s : A.K)) (s : A.K) = act (tm A hG u) Y := by
    rw [hY, act_tm, Ring.inverse_unit]
    congr 1
    · rw [hu, Units.val_mul, mul_one]
    · rw [hu, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have h1 : desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) =
      ∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG := by
    unfold desc
    simp only [hpt, act_mul]
  have h2 : (∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG) =
      ∫ g, f' (act g Y) * eta (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) *
        (α (g * (tm A hG u)⁻¹) : ℂ) ∂M.μG := by
    have := integral_mul_right_eq_self (μ := M.μG) (fun h : GL (Fin r) F => f' (act h Y) *
      eta (((h * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) * (α (h * (tm A hG u)⁻¹) : ℂ)) (tm A hG u)
    simp only [mul_inv_cancel_right] at this
    exact this
  rw [h1, h2, ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hui : (tm A hG u)⁻¹ = tm A hG a⁻¹ * tm A hG s := by
    rw [← map_inv, ← map_mul, hu, _root_.mul_inv_rev, inv_inv, mul_comm]
  have hdg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hN : ∀ t : A.Kˣ, Algebra.norm F (t : A.K) ≠ 0 := fun t =>
    (IsUnit.map (Algebra.norm F) (Units.isUnit t)).ne_zero
  have hdet : (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) =
      (g : Matrix (Fin r) (Fin r) F).det * (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K) * Algebra.norm F (s : A.K)) := by
    rw [hui, Units.val_mul, Matrix.det_mul, ← map_mul, det_tm, Units.val_mul, map_mul]
  have h12 : eta (Algebra.norm F (a : A.K)) * eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K)) = 1 := by
    rw [← hmul _ _ (hN a) (hN a⁻¹), ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, valuationParitySign_one]
  have h11 := valuationParitySign_mul_self (Algebra.norm F (a : A.K))
  have h33 := valuationParitySign_mul_self (Algebra.norm F (s : A.K))
  simp only []
  rw [hdet, hmul _ _ hdg (mul_ne_zero (hN _) (hN _)), hmul _ _ (hN _) (hN _), hui, ← _root_.mul_assoc g (tm A hG a⁻¹) (tm A hG s)]
  unfold Et.etaK
  set e1 := eta (Algebra.norm F (a : A.K))
  set e2 := eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K))
  set e3 := eta (Algebra.norm F (s : A.K))
  set d := eta ((g : Matrix (Fin r) (Fin r) F).det)
  set fv := f' (act g Y)
  set al : ℂ := (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ)
  linear_combination (fv * d * al * e2) * h33 - (fv * d * al * e2) * h11 + (fv * d * al * e1) * h12

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem orb_descent_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  intro F E _ _ _ _ _ A r τ p hG lam M μK hμK α f' hf' hαlc hαcs hα0 hcut κ₀ hκ a ha
  obtain ⟨a, rfl⟩ := ha
  letI := M.mG
  set Y := pt A hG lam 1 (a : A.K) with hY
  have hconv := (GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure F E A μK hμK).2.2
    (fun t => desc A M hG lam α f' ((a : A.K) * Ring.inverse t, t) * A.etaK t)
  have hO : A.orbK μK (desc A M hG lam α f') (a : A.K) =
      ∫ s, desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s ∂(unitsMeas A μK) := by
    rw [hconv]; rfl
  set Φ : GL (Fin r) F → ℂ := fun g => f' (act g Y) * omega (act g Y) with hΦ
  have hΔ : Delta (inv Y) ≠ 0 := by
    rw [hY, pt_one, GlobalTheory.JR.NormalFormL.inv_sec']
    exact ((GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).2 (a : A.K)).2.2 (Units.isUnit a)
  have hΦt : IsTest Φ := (GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M).1 f' hf' Y hΔ
  have hinner : ∀ s : A.Kˣ, κ₀ * (desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s) =
      ∫ g, Φ g * (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG := by
    intro s
    rw [desc_unit_eq, ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hΦ]
    rw [hκ (a : A.K) (Units.isUnit a) g]
    ring
  have hc : ∀ g, Φ g ≠ 0 → ∫ s, α (g * tm A hG a⁻¹ * tm A hG s) ∂(unitsMeas A μK) = 1 := by
    intro g hg
    refine hcut g ⟨(act g Y).2.1, (act g Y).2.2.1, ?_⟩ a⁻¹
    intro h0
    apply hg
    have h1 : f' (act g Y) = 0 := h0
    simp only [hΦ, h1, zero_mul]
  rw [hO, ← integral_const_mul]
  simp_rw [hinner]
  exact ((GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus) F E A r τ p hG M μK hμK α Φ hΦt hαlc hαcs hα0 (tm A hG a⁻¹) hc).symm

end GlobalTheory.JR.LinDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralLinearDescentCutoffStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_linearDescent_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  first | exact @GlobalTheory.JR.LinDesc.orb_descent_unit | exact GlobalTheory.JR.LinDesc.orb_descent_unit | (intros; apply GlobalTheory.JR.LinDesc.orb_descent_unit <;> assumption)
end
