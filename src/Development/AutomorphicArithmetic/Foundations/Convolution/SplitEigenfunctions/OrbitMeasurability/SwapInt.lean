module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DiagInvVal
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ContInfPart

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.GaloisBaseChangeSchemeActionCompSnd
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.AbsUnf
noncomputable section

open MeasureTheory Measure Set
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem invInvariant {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.IsInvInvariant := by
  constructor
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν.inv = c • ν :=
    ⟨haarScalarFactor ν.inv ν, by
      have := isMulLeftInvariant_eq_smul ν.inv ν
      rwa [ENNReal.smul_def] at this⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have hpos : ν K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hfin : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hsq : ν = (c * c) • ν := by
    conv_lhs => rw [← Measure.inv_inv ν, hc]
    rw [Measure.inv_def (c • ν), Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, hc, smul_smul]
  have h1 : c * c = 1 := by
    have : (c * c) * ν K = 1 * ν K := by
      rw [one_mul]; conv_rhs => rw [hsq]
      simp
    exact (ENNReal.mul_left_inj hpos hfin).1 this
  have h2 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exact absurd h1 (ne_of_lt (by
        calc c * c ≤ c * 1 := by gcongr
          _ < 1 := by simpa using h))
    · exact h
    · exact absurd h1 (ne_of_gt (by
        calc 1 < c := h
          _ = 1 * c := by simp
          _ ≤ c * c := by gcongr))
  rw [hc, h2, one_smul]

private theorem unf {G H ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    [Countable ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (μ : Measure G) (ν : Measure H)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (Γ' : Subgroup G) (Γ : Subgroup H)
    [Countable Γ'] [Countable Γ] (DG : Set G) (DH : Set H) (r : ι → G) (hj : Continuous j)
    (hinj : Function.Injective j) (hDG : IsFundamentalDomain Γ' DG μ) (hDH : IsFundamentalDomain Γ DH ν)
    (hr : ∀ i, r i ∈ Γ') (hjΓ : ∀ δ ∈ Γ, j δ ∈ Γ') (hdec : ∀ γ ∈ Γ', ∃! i, ∃ δ ∈ Γ, γ = r i * j δ)
    (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) :
    ∫⁻ p : G × ι, ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν ∂((μ.restrict DG).prod Measure.count) =
      ∫⁻ y, ∫⁻ g in DH, f (j g * y, y) ∂ν ∂μ := by
  haveI := invInvariant ν
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  let e : ι × Γ → Γ' := fun q => ⟨r q.1 * j q.2, Γ'.mul_mem (hr _) (hjΓ _ q.2.2)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨i, δ⟩ ⟨i', δ'⟩ h
      have h' : r i * j δ = r i' * j δ' := congrArg Subtype.val h
      have hi : i = i' := (hdec _ (Γ'.mul_mem (hr i) (hjΓ _ δ.2))).unique ⟨δ, δ.2, rfl⟩ ⟨δ', δ'.2, h'⟩
      subst hi
      have : δ = δ' := Subtype.ext (hinj (mul_left_cancel h'))
      rw [this]
    · rintro ⟨γ, hγ⟩
      obtain ⟨i, ⟨δ, hδ, h⟩, -⟩ := hdec γ hγ
      exact ⟨(i, ⟨δ, hδ⟩), Subtype.ext h.symm⟩

  let K : G → ℝ≥0∞ := fun x => ∫⁻ g in DH, f (x, (j g)⁻¹ * x) ∂ν
  have hK : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun q : G × H => f (q.1, (j q.2)⁻¹ * q.1)) ?_
    exact hf.comp (by fun_prop)
  have h1 : ∀ x i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν =
      ∑' δ : Γ, ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e (i, δ) : Γ') : G)⁻¹ * x)) ∂ν := by
    intro x i
    rw [← lintegral_inv_eq_self (μ := ν) (fun g => f (x, j g * ((r i)⁻¹ * x))), hDH.lintegral_eq_tsum'']
    refine tsum_congr fun δ => lintegral_congr fun g => ?_
    simp [e, Subgroup.smul_def, mul_assoc]
  have h2 : ∀ x, ∑' i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν = ∑' γ : Γ', K ((γ : G)⁻¹ * x) := by
    intro x
    simp_rw [h1]
    rw [← ENNReal.tsum_prod' (f := fun q : ι × Γ => ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x)) ∂ν),
      ← (Equiv.ofBijective e he).tsum_eq (fun γ : Γ' => K ((γ : G)⁻¹ * x))]
    refine tsum_congr fun q => lintegral_congr fun g => ?_
    have := hinv _ (Γ'.inv_mem (e q).2) x ((j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x))
    simpa [K] using this.symm
  have hmeasL : Measurable fun q : (G × ι) × H => f (q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1)) :=
    hf.comp (by fun_prop)
  have hmeasR : Measurable fun p : G × ι => ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν :=
    hmeasL.lintegral_prod_right'
  rw [lintegral_prod _ hmeasR.aemeasurable]
  simp_rw [lintegral_count]
  simp_rw [h2]
  rw [lintegral_tsum (f := fun (γ : Γ') x => K ((γ : G)⁻¹ * x))
    fun γ => (hK.comp (measurable_const_mul _)).aemeasurable]
  have h3 : ∫⁻ x, K x ∂μ = ∑' γ : Γ', ∫⁻ x in DG, K ((γ : G)⁻¹ * x) ∂μ := by
    rw [hDG.lintegral_eq_tsum' K]
    refine tsum_congr fun γ => lintegral_congr fun x => ?_
    simp [Subgroup.smul_def]
  rw [← h3]
  have hF : Measurable (Function.uncurry fun (x : G) (g : H) => f (x, (j g)⁻¹ * x)) :=
    hf.comp (by fun_prop)
  have hF' : Measurable (Function.uncurry fun (y : G) (g : H) => f (j g * y, y)) :=
    hf.comp (by fun_prop)
  rw [show ∫⁻ x, K x ∂μ = ∫⁻ g in DH, ∫⁻ x, f (x, (j g)⁻¹ * x) ∂μ ∂ν from
      lintegral_lintegral_swap hF.aemeasurable,
    lintegral_lintegral_swap hF'.aemeasurable]
  refine lintegral_congr fun g => ?_
  rw [← lintegral_mul_left_eq_self (fun x => f (x, (j g)⁻¹ * x)) (j g)]
  simp

theorem absUnf : AbsUnf := by
  intro G H ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ _ j Γ' Γ _ _ DG DH r φ c hj hinj hDG hDH hfin hr hjΓ hdec
    hφ hφinv hbd hc hci
  obtain ⟨B₀, hB₀⟩ := hbd
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  have U := fun (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) =>
    unf μ ν j Γ' Γ DG DH r hj hinj hDG hDH hr hjΓ hdec f hf hinv
  refine ⟨fun B hB => ?_, ?_⟩
  · have hBe : ∀ x, ‖φ x‖ₑ ≤ ENNReal.ofReal B := fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB x)
    calc ∫⁻ p : G × ι, ‖(∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1‖ₑ ∂((μ.restrict DG).prod Measure.count)
        ≤ ∫⁻ p : G × ι, ∫⁻ g, ‖c (j g * ((r p.2)⁻¹ * p.1)) * φ p.1‖ₑ ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine lintegral_mono fun p => ?_
          rw [← integral_mul_const]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ∫⁻ g in DH, ‖c y * φ (j g * y)‖ₑ ∂ν ∂μ :=
          U (fun q => ‖c q.2 * φ q.1‖ₑ) (by fun_prop) (fun γ hγ x y => by simp only [hφinv γ hγ x])
      _ ≤ ∫⁻ y, ∫⁻ g in DH, ‖c y‖ₑ * ENNReal.ofReal B ∂ν ∂μ := by
          refine lintegral_mono fun y => lintegral_mono fun g => ?_
          rw [enorm_mul]
          gcongr
          exact hBe _
      _ = ENNReal.ofReal B * ν DH * ∫⁻ y, ‖c y‖ₑ ∂μ := by
          simp_rw [setLIntegral_const, mul_assoc]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne), mul_comm, mul_assoc]
  · let P₁ : Measure ((G × ι) × H) := ((μ.restrict DG).prod Measure.count).prod ν
    let P₂ : Measure (G × H) := μ.prod (ν.restrict DH)
    let T₁ : (G × ι) × H → ℂ × G := fun q => (φ q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1))
    let T₂ : G × H → ℂ × G := fun q => (φ (j q.2 * q.1), q.1)
    have hT₁ : Measurable T₁ := by fun_prop
    have hT₂ : Measurable T₂ := by fun_prop
    have hmap : P₁.map T₁ = P₂.map T₂ := by
      ext S hS
      rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, lintegral_map (measurable_one.indicator hS) hT₁,
        lintegral_map (measurable_one.indicator hS) hT₂]
      have hm : Measurable (S.indicator (1 : ℂ × G → ℝ≥0∞)) := measurable_one.indicator hS
      have hu := U (fun q => S.indicator (1 : ℂ × G → ℝ≥0∞) (φ q.1, q.2)) (hm.comp (by fun_prop))
        (fun γ hγ x y => by simp only [hφinv γ hγ x])
      have e₁ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ a) ∂P₁ =
          ∫⁻ p, ∫⁻ g, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ (p, g)) ∂ν ∂((μ.restrict DG).prod Measure.count) :=
        lintegral_prod _ (hm.comp hT₁).aemeasurable
      have e₂ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ a) ∂P₂ =
          ∫⁻ y, ∫⁻ g in DH, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ (y, g)) ∂ν ∂μ :=
        lintegral_prod _ (hm.comp hT₂).aemeasurable
      rw [e₁, e₂]
      exact hu
    let h : ℂ × G → ℂ := fun w => c w.2 * w.1
    have hh : Measurable h := by fun_prop
    haveI : IsFiniteMeasure (ν.restrict DH) := ⟨by simpa using hfin⟩
    have hI₂ : Integrable (h ∘ T₂) P₂ := by
      refine ((hci.comp_fst (ν.restrict DH)).norm.mul_const B₀).mono' (hh.comp hT₂).aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      simp only [h, T₂, Function.comp, norm_mul, norm_norm]
      gcongr
      exact hB₀ _
    have hI : Integrable h (P₂.map T₂) :=
      (integrable_map_measure hh.aestronglyMeasurable hT₂.aemeasurable).2 hI₂
    have hI₁ : Integrable (h ∘ T₁) P₁ :=
      (integrable_map_measure hh.aestronglyMeasurable hT₁.aemeasurable).1 (hmap ▸ hI)
    calc ∫ p : G × ι, (∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1 ∂((μ.restrict DG).prod Measure.count)
        = ∫ p : G × ι, ∫ g, (h ∘ T₁) (p, g) ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          simp only [h, T₁, Function.comp]
          rw [integral_mul_const]
      _ = ∫ q, (h ∘ T₁) q ∂P₁ := (integral_prod _ hI₁).symm
      _ = ∫ w, h w ∂(P₁.map T₁) := (integral_map hT₁.aemeasurable hh.aestronglyMeasurable).symm
      _ = ∫ w, h w ∂(P₂.map T₂) := by rw [hmap]
      _ = ∫ q, (h ∘ T₂) q ∂P₂ := integral_map hT₂.aemeasurable hh.aestronglyMeasurable
      _ = ∫ y, ∫ g in DH, (h ∘ T₂) (y, g) ∂ν ∂μ := integral_prod _ hI₂
      _ = ∫ y, c y * ∫ g in DH, φ (j g * y) ∂ν ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [h, T₂, Function.comp]
          rw [integral_const_mul]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private noncomputable def hoD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : G1 F ≃ₜ G1 F :=
  ⟨⟨cD t, cD t⁻¹, fun g => by rw [← cD_mul_left, inv_mul_cancel, cD_one_left],
      fun g => by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]⟩,
    M.continuous_cD t, M.continuous_cD t⁻¹⟩

private theorem emb_cD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : MeasurableEmbedding (cD t : G1 F → G1 F) :=
  (hoD t).measurableEmbedding

private noncomputable def tau {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : (A E)ˣ) : (A E)ˣ :=
  Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) (ideleNorm ℚ E z)

private theorem em_dM {E : Type} [Field E] [NumberField E] (t : (A ℚ)ˣ) :
    em E (dM t) = dM (Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [em, dM, Matrix.GeneralLinearGroup.map]

private theorem gl_scalarCenter_commute {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (u : G1 E) :
    gl u * sZ D z = sZ D z * gl (cD (tau z) u) := by
  obtain ⟨-, -, -, -, -, -, -, -, hsc, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have e : em E (dM (ideleNorm ℚ E z)⁻¹) = (dM (tau z))⁻¹ := by
    rw [em_dM, map_inv, dM_inv]; rfl
  rw [hsc, e, gl_cD]
  rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm z (gl u)]
  group

private theorem cD_j {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ)
    (j : G1 ℚ →* G1 E) (hj : ∀ g, gl (j g) = em E (gl g)) (g : G1 ℚ) :
    cD (tau z) (j (cD (ideleNorm ℚ E z)⁻¹ g)) = j g := by
  obtain ⟨-, -, -, -, -, -, -, hc, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  apply gl_injective
  have h1 := gl_scalarCenter_commute D z (j (cD (ideleNorm ℚ E z)⁻¹ g))
  rw [hj, ← hc, ← hj] at h1
  exact (mul_left_cancel h1).symm

private theorem galoisBaseChangeSchemeAction_comp_snd {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (h u r : G1 E)
    (huh : h = r * u) :
    D.act (gl h * sZ D z)⁻¹ (D.act (gl r) (rp X0)) = D.act (gl (cD (tau z) u))⁻¹ (rp X0) := by
  obtain ⟨-, -, -, -, ha, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have h0 : D.act (sZ D z)⁻¹ (rp X0) = rp X0 := by
    conv_lhs => rw [← ha z]
    exact D.act_inv_act _ _
  subst huh
  rw [← D.act_mul, gl_mul, mul_assoc, gl_scalarCenter_commute D z u]
  have : (gl r * (sZ D z * gl (cD (tau z) u)))⁻¹ * gl r = (gl (cD (tau z) u))⁻¹ * (sZ D z)⁻¹ := by group
  rw [this, D.act_mul, h0]

private theorem pY_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    pY D (z, p) = D.act (gl p.1 * sZ D (z : IdeleGroup E))⁻¹ (rp p.2.1) := rfl

private theorem el_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    el D (z, p) = gl p.1 * sZ D (z : IdeleGroup E) := rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zOne :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZOne := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ z
  obtain ⟨j', r, hj', hjc, hji, hr, hjΓ, hu⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps E D
  have hjj : j' = j := MonoidHom.ext fun g => gl_injective ((hj' g).trans (hj g).symm)
  subst hjj
  haveI := N.haar
  haveI := N.right
  haveI := M.haar
  haveI := M.right
  haveI : DiscreteMeasurableSpace (Orb D.δ) := ⟨fun _ => trivial⟩
  haveI : Countable (Orb D.δ) := inferInstance
  obtain ⟨hcont, hleft⟩ := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1
  simp only [pY_eq, el_eq]
  generalize ((z : IdeleGroup E) : (A E)ˣ) = zz
  have hmpE : MeasurePreserving (cD (tau zz)) N.μ N.μ := (UpperTheory.ConvolutionTheory.RankTwoDescent.invE E N).1 _
  have hmpQ : MeasurePreserving (cD (ideleNorm ℚ E zz)⁻¹ : G1 ℚ → G1 ℚ) M.μ M.μ := UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _
  have hq : ∀ F : G1 ℚ → ℂ, ∫ g, F (cD (ideleNorm ℚ E zz)⁻¹ g) ∂M.μ = ∫ g, F g ∂M.μ :=
    fun F => hmpQ.integral_comp (emb_cD _) F
  obtain ⟨cs, hcsd⟩ : ∃ cs : G1 E → ℂ, ∀ y, cs y = c (cD (tau zz) y) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : G1 E → ℂ, ∀ x, f x = φ.1 (gl x * sZ D zz) := ⟨_, fun _ => rfl⟩
  have hcsC : Continuous cs := by
    rw [show cs = c ∘ cD (tau zz) from funext hcsd]
    exact hc.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_cD _)
  have hfC : Continuous f := by
    rw [show f = fun x => φ.1 (gl x * sZ D zz) from funext hfd]
    exact hcont.comp (continuous_gl.mul continuous_const)
  have hcsS : HasCompactSupport cs := by
    rw [show cs = c ∘ hoD (tau zz) from funext hcsd]
    exact hcs.comp_homeomorph _
  have hΨ' : ∀ (h : G1 E) (ξ : Orb D.δ), Ψ (D.act (gl h * sZ D zz)⁻¹ (rp ξ.1)) = ∫ g, cs (j' g * ((r ξ)⁻¹ * h)) ∂M.μ := by
    intro h ξ
    have e1 : D.act (gl h * sZ D zz)⁻¹ (rp ξ.1) = D.act (gl (cD (tau zz) ((r ξ)⁻¹ * h)))⁻¹ (rp X0) := by
      rw [(hr ξ).2]
      exact galoisBaseChangeSchemeAction_comp_snd D zz h _ (r ξ) (by group)
    rw [e1, hΨ, ← hq fun g => cs (j' g * ((r ξ)⁻¹ * h))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hcsd]
    rw [UpperTheory.ConvolutionTheory.R2.cD_mul _ (j' _) _, cD_j D zz j' hj' g]
  have hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE E P φ hφ {sZ D zz} isCompact_singleton
    exact ⟨B, fun x => by rw [hfd]; exact hB x _ rfl⟩
  have hinv : ∀ γ ∈ Gam E, ∀ x, f (γ * x) = f x := by
    rintro _ ⟨γ, rfl⟩ x
    rw [hfd, hfd, gl_mul, gl_ratS, mul_assoc, hleft]
  obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.absUnf (G1 E) (G1 ℚ) (Orb D.δ) N.μ M.μ j' (Gam E) (Gam ℚ) N.D M.D r f cs hjc hji N.fund M.fund
    (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) (fun i => (hr i).1) hjΓ hu hfC.measurable hinv hB hcsC.measurable (hcsC.integrable_of_hasCompactSupport hcsS)
  have hL : ∀ p : G1 E × Orb D.δ, Ψ (D.act (gl p.1 * sZ D zz)⁻¹ (rp p.2.1)) * φ.1 (gl p.1 * sZ D zz) =
      (∫ g, cs (j' g * ((r p.2)⁻¹ * p.1)) ∂M.μ) * f p.1 := by
    rintro ⟨h, ξ⟩
    rw [hΨ', hfd]
  refine ⟨fun B hBB => ?_, ?_⟩
  · simp only [hL]
    refine (h1 B (fun h => by rw [hfd]; exact hBB h)).trans_eq ?_
    rw [show (∫⁻ y, ‖cs y‖ₑ ∂N.μ) = ∫⁻ y, ‖c y‖ₑ ∂N.μ by
      simp only [hcsd]; exact hmpE.lintegral_comp_emb (emb_cD _) fun y => ‖c y‖ₑ]
  · simp only [hL]
    rw [h2]
    have := hmpE.integral_comp (emb_cD (tau zz)) fun y => c y * SLP M fun x => φ.1 (x * sZ D zz * gl y)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hcsd, SLP]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hfd]
    rw [gl_mul, hj', mul_assoc, gl_scalarCenter_commute D zz y, mul_assoc]
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem int_prod {Z P : Type} [MeasurableSpace Z] [MeasurableSpace P] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure P) [SFinite n] {F : Z × P → ℂ} (hF : Measurable F) {K : ℝ≥0∞} (hK : K < ⊤)
    (h : ∀ᵐ z ∂m, ∫⁻ p, ‖F (z, p)‖ₑ ∂n ≤ K) : Integrable F (m.prod n) := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  refine (lintegral_mono_ae h).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hK (measure_lt_top _ _)

private theorem swap_int {Z X T : Type} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace T] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure X) [SFinite n] (l : Measure T) [IsFiniteMeasure l] {c : X → ℂ} (hcm : Measurable c) (hc : Integrable c n)
    {G : (Z × X) × T → ℂ} (hG : Measurable G) {S : Set Z} (hS : ∀ᵐ z ∂m, z ∈ S) {B : ℝ}
    (hB : ∀ z ∈ S, ∀ y, c y ≠ 0 → ∀ g, ‖G ((z, y), g)‖ ≤ B) :
    ∫ z, ∫ y, c y * ∫ g, G ((z, y), g) ∂l ∂n ∂m = ∫ y, c y * ∫ z, ∫ g, G ((z, y), g) ∂l ∂m ∂n := by
  have h1 : StronglyMeasurable fun p : Z × X => ∫ g, G (p, g) ∂l := hG.stronglyMeasurable.integral_prod_right'
  have h2 : Integrable (fun p : Z × X => B * l.real Set.univ * ‖c p.2‖) (m.prod n) :=
    (hc.norm.comp_snd m).const_mul _
  have h3 : ∀ᵐ p : Z × X ∂(m.prod n), p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hS
  rw [integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact integral_const_mul _ _
  · refine h2.mono' (((hcm.comp measurable_snd).mul h1.measurable).aestronglyMeasurable) ?_
    filter_upwards [h3] with p hp
    by_cases h0 : c p.2 = 0
    · simp [Function.uncurry, h0]
    · simp only [Function.uncurry, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB p.1 hp p.2 h0 g)) (norm_nonneg _)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zAll :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZAll := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ hΨc
  obtain ⟨hfin, hS, C, hC, hSC⟩ := zDom E
  obtain ⟨hm1, hm2, -⟩ := yInt E D W M N P φ hφ
  have hsZ : Continuous (sZ D) := (szLaws E D).2.1
  have hφc : Continuous φ.1 := (decE E P φ hφ).1.1
  have hone := zOne E D W M N P φ hφ j hj c hc hcs Ψ hΨc
  haveI := N.haar
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by simpa using hfin⟩
  haveI : Countable (Orb D.δ) := inferInstance
  have hci : Integrable c N.μ := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨B, hB⟩ := bddE E P φ hφ _ (hC.image hsZ)
  obtain ⟨B', hB'⟩ := bddE E P φ hφ _
    ((hC.prod hcs.isCompact).image (f := fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2)
      ((hsZ.comp continuous_fst).mul (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)))
  have hI : Integrable (fun y => Ψ (pY D y) * φ.1 (el D y)) (mY D.δ N) := by
    refine int_prod _ _ ((hΨ.comp hm1).mul hm2) (K := ENNReal.ofReal B * M.μ M.D * ∫⁻ y, ‖c y‖ₑ ∂N.μ) ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M)) hci.2
    · filter_upwards [ae_restrict_mem hS] with z hz
      exact (hone z).1 B fun h => hB h _ ⟨_, hSC z hz, rfl⟩
  refine ⟨hI, ?_⟩
  have hG : Continuous fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × G1 ℚ =>
      φ.1 (em E (gl p.2) * sZ D (p.1.1 : IdeleGroup E) * gl p.1.2) :=
    hφc.comp (((cont_em.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)).mul
      (hsZ.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)))).mul
      (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp (continuous_snd.comp continuous_fst)))
  have hsw := swap_int ((normOneMeasure E).restrict (normOneFundamentalDomain E)) N.μ (M.μ.restrict M.D) hc.measurable hci
    hG.measurable (ae_restrict_mem hS) (B := B') (fun z hz y hy g => by
      have h := hB' (j g) _ ⟨((z : IdeleGroup E), y), ⟨hSC z hz, subset_tsupport _ hy⟩, rfl⟩
      rwa [hj, ← mul_assoc] at h)
  unfold mY at hI ⊢
  rw [integral_prod _ hI]
  simp only [fun z => (hone z).2]
  exact hsw

end
