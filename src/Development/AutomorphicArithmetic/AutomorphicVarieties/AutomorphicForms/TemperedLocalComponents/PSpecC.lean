module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
public import GroundTheory.AutomorphicForms.L2LocalComponents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrRepHolds
theorem UpperTheory.V.KernelIndexFullLattice.brRep_holds :
    UpperTheory.V.KernelIndexFullLattice.BrRep := by
  intro E _ _ _ a π₀
  refine ⟨UpperTheory.V.Cm.ofRep π₀, ?_⟩
  change (π₀.carrier.map (UpperTheory.V.Cm.ofCusp E a)).map _ = _
  rw [← Submodule.map_comp]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.RangeLe
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem rangeLe_holds : RangeLe := by
  intro E _ _ _ a μ _ μ₁ _ hp v
  have hv : v ∈ ((centralCuspForms E a).map (cuspVecL μ₁)).topologicalClosure := by
    rw [topologicalClosure_map_centralCuspForms μ₁]
    exact Submodule.mem_top
  have hmap : Set.MapsTo (cmp hp) (↑((centralCuspForms E a).map (cuspVecL μ₁)) : Set (CuspL2 μ₁))
      (L2cusp μ : Set (L2 (latticeGL E a) μ)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hc : Continuous φ.1 := φ.2.1.continuous
    have hl : IsLeftInvariant φ.1 := φ.2.1.isLeftInvariant
    have hcont : φ.1 ∈ cuspCont E a := by
      refine mem_cuspCont.2 ⟨hc, fun γ g => hl γ g, ?_,
        UpperTheory.isCuspidal_of_constantTerm_eq_zero E a φ.1 hl hc φ.2.2⟩
      intro t g
      rw [splitCentre_comm, splitEq_holds E a t]
      exact apply_mul_centralSection_of_mem hφ _ _
    apply mem_L2cusp_of_ae_eq hcont
    have hrep :
        (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
          =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot hl := by
      rw [toLp_cuspVecL]
      exact coeFn_cuspToL2 μ₁ φ
    have hquot :
        (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
          =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hl ∘ quotMap E a :=
      (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hrep)
    filter_upwards [ae_quotMeasure_iff.1 hquot] with g hg
    calc
      lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
          cuspQuot hl (quotMap E a (mk (latticeGL E a) g)) := hg
      _ = φ.1 g := by
        rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
        exact apply_mul_centralSection_of_mem hφ _ _
  exact hmap.closure_left (cmp hp).continuous (isClosed_L2cusp μ) hv

end UpperTheory.V.KernelIndexFullLattice
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KFinTr
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem kFinTr_holds : KFinTr := by
  intro E _ _ _ a μ _ _ μ₁ _ hp v h
  have hi : Function.Injective (cmp hp) := (cmp hp).injective
  refine ⟨?_, ?_⟩
  · convert h.1 using 1
    ext k
    have e := cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, e, hi.eq_iff, Fb.finEmb_eq]
  · have := h.2
    have hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map
        (cmp hp).toLinearMap ≤ Submodule.span ℂ
        (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := (Cm.grpEq E a).surjective (k : archGroup E a)
      have hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := (Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)
      refine Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩
      have ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y := Units.ext rfl
      change R (latticeGL E a) μ (infGL E a (Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a)))
        (cmp hp v) = cmp hp (archRepT μ₁ (k : archGroup E a) v)
      rw [ey, cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v, ← Cm.infEmb_grpEq, hy, archRepT_apply,
        retract_infEmb]
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional

end UpperTheory.V.KernelIndexFullLattice
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotPres
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BandDom
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem retract_zpow_mul (n : ℤ) (g : GA E a) :
    retractOne (splitCentre E a 1 ^ n * g) = retractOne g := by
  rw [retractOne_mul, splitEq_holds E a 1, ← map_zpow, retractOne_centralSection, one_mul]

private theorem one_lt_mod (ha : 0 < a) : (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem coe_mul_mem_band (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, mem_normOneGL_iff_detModule.1 x.2, one_mul]

private theorem zpow_mul_mem_band (ha : 0 < a) (n : ℤ) (g : GA E a) :
    splitCentre E a 1 ^ n * g ∈ band E a ↔
      (detModule E a g : ℝ) ∈ Set.Ico ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n))
        ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n + 1)) := by
  have hy := one_lt_mod (E := E) ha
  have hy0 : (0 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := zero_lt_one.trans hy
  simp only [band, Set.mem_setOf_eq, map_mul, map_zpow, ha.ne', false_or, Set.mem_Ico]
  rw [← Subtype.coe_le_coe, ← Subtype.coe_lt_coe, Positive.val_mul, Positive.coe_zpow, Positive.val_one,
    zpow_add_one₀ hy0.ne', zpow_neg, ← one_div, div_le_iff₀' (zpow_pos hy0 n), one_div,
    lt_inv_mul_iff₀ (zpow_pos hy0 n)]

private theorem exists_zpow_mul_mem_band (g : GA E a) : ∃ n : ℤ, splitCentre E a 1 ^ n * g ∈ band E a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact ⟨0, Or.inl ha⟩
  · obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (detModule E a g).2 (one_lt_mod (E := E) ha)
    exact ⟨-n, (zpow_mul_mem_band ha _ g).2 (by rwa [neg_neg])⟩

private theorem zpow_eq_of_mem_band {g : GA E a} {m n : ℤ} (hm : splitCentre E a 1 ^ m * g ∈ band E a)
    (hn : splitCentre E a 1 ^ n * g ∈ band E a) : splitCentre E a 1 ^ m = splitCentre E a 1 ^ n := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  · have hy := one_lt_mod (E := E) ha
    rw [zpow_mul_mem_band ha] at hm hn
    have h1 := (zpow_lt_zpow_iff_right₀ hy).1 (hm.1.trans_lt hn.2)
    have h2 := (zpow_lt_zpow_iff_right₀ hy).1 (hn.1.trans_lt hm.2)
    rw [show m = n by omega]

end UpperTheory.V.KernelIndexFullLattice

open UpperTheory.V.KernelIndexFullLattice in
theorem UpperTheory.V.KernelIndexFullLattice.bandDom_holds :
    UpperTheory.V.KernelIndexFullLattice.BandDom := by
  intro E _ _ _ a D hD g
  obtain ⟨⟨x, hx⟩, hxD, huniq⟩ := hD (retractOne g)
  obtain ⟨n, hn⟩ := exists_zpow_mul_mem_band g
  obtain ⟨γ, hγ⟩ := id hx
  have hγ' : ratGL E a γ = (x : GA E a) := hγ
  refine ⟨⟨(x : GA E a) * splitCentre E a 1 ^ n, mem_latticeGL_iff.2 ⟨γ, n, by rw [hγ']⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · change retractOne ((x : GA E a) * splitCentre E a 1 ^ n * g) ∈ D
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul]
    exact hxD
  · change (x : GA E a) * splitCentre E a 1 ^ n * g ∈ band E a
    rw [mul_assoc, coe_mul_mem_band]
    exact hn
  · rintro ⟨l, hl⟩ ⟨h1, h2⟩
    obtain ⟨δ, m, rfl⟩ := mem_latticeGL_iff.1 hl
    let y : G1 E a := ⟨ratGL E a δ, rationalGL_le_normOneGL ⟨δ, rfl⟩⟩
    change retractOne ((y : GA E a) * splitCentre E a 1 ^ m * g) ∈ D at h1
    change (y : GA E a) * splitCentre E a 1 ^ m * g ∈ band E a at h2
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul] at h1
    rw [mul_assoc, coe_mul_mem_band] at h2
    have e : y = x := congrArg Subtype.val (huniq ⟨y, ⟨δ, rfl⟩⟩ h1)
    refine Subtype.ext ?_
    change (y : GA E a) * splitCentre E a 1 ^ m = (x : GA E a) * splitCentre E a 1 ^ n
    rw [e, zpow_eq_of_mem_band h2 hn]
end

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

private theorem measurableSet_band' (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    MeasurableSet (band E a) := by
  have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  have h := hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))
  exact (MeasurableSet.const (a = 0)).union h

theorem UpperTheory.V.KernelIndexFullLattice.quotPres_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotPres := by
  intro E _ _ _ a μ _
  have hr : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable
  have hD := RightCosetSpace.measurableSet_fundamentalDomain (Γ1 E a)
  have hmk : Measurable (RightCosetSpace.mk (Γ1 E a)) := RightCosetSpace.measurable_mk _
  have hcomp : quotMap E a ∘ mk (latticeGL E a) = RightCosetSpace.mk (Γ1 E a) ∘ retractOne :=
    funext fun g => quotMk_holds E a g
  have hq : Measurable (quotMap E a) := by
    refine measurable_from_quotient.2 ?_
    change Measurable (quotMap E a ∘ mk (latticeGL E a))
    rw [hcomp]
    exact hmk.comp hr
  have hF : IsFundamentalDomain (latticeGL E a)
      (retractOne ⁻¹' RightCosetSpace.fundamentalDomain (Γ1 E a) ∩ band E a) μ :=
    IsFundamentalDomain.mk' ((hr hD).inter (measurableSet_band' E a)).nullMeasurableSet
      (bandDom_holds E a _ (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (Γ1 E a)))
  refine ⟨hq, ?_⟩
  rw [quotMeasure_eq hF, Measure.map_map hq measurable_mk, hcomp, RightCosetSpace.quotientMeasure, muOne,
    Measure.restrict_map hr hD, Measure.restrict_restrict (hr hD), Measure.map_map hmk hr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.MuHaar
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem one_lt_top (ha : 0 < a) : 1 < detModule E a (splitCentre E a 1) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  change (1 : ℝ) < Real.exp _
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem band_zero : band E 0 = Set.univ := Set.eq_univ_of_forall fun _ => Or.inl rfl

private theorem band_pos (ha : 0 < a) :
    band E a = detModule E a ⁻¹' Set.Ico 1 (detModule E a (splitCentre E a 1)) := by
  ext g
  simp only [band, Set.mem_setOf_eq, ha.ne', false_or, Set.mem_preimage, Set.mem_Ico]

private theorem meas_retract : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable

private theorem muOne_apply (μ : Measure (GA E a)) {A : Set (G1 E a)} (hA : MeasurableSet A) :
    muOne μ A = μ (retractOne ⁻¹' A ∩ band E a) := by
  rw [muOne, Measure.map_apply meas_retract hA, Measure.restrict_apply (meas_retract hA)]

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem retract_mul_left (x : G1 E a) (g : GA E a) :
    retractOne ((x : GA E a) * g) = x * retractOne g := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul,
    mul_assoc]

private theorem band_mul_left (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul]

private theorem isCompact_posIcc (s t : {r : ℝ // 0 < r}) : IsCompact (Set.Icc s t) := by
  refine (Topology.IsInducing.subtypeVal (t := {r : ℝ | 0 < r})).isCompact_iff.2 ?_
  convert isCompact_Icc (a := (s : ℝ)) (b := (t : ℝ)) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, s.2.trans_le hx.1⟩, hx, rfl⟩

end

theorem UpperTheory.V.KernelIndexFullLattice.muHaar_holds :
    UpperTheory.V.KernelIndexFullLattice.MuHaar := by
  intro E _ _ _ a μ _
  have h1 : (muOne μ).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    have hm : Measurable fun y : G1 E a => x * y := measurable_const_mul x
    rw [Measure.map_apply hm hA, muOne_apply μ (hm hA), muOne_apply μ hA,
      ← measure_preimage_mul μ (x : GA E a) (retractOne ⁻¹' A ∩ band E a)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, retract_mul_left, band_mul_left]
  have h2 : IsFiniteMeasureOnCompacts (muOne μ) := by
    refine ⟨fun C hC => ?_⟩
    rw [muOne_apply μ hC.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      exact (Set.toFinite _).isCompact.measure_lt_top
    · have hc : Continuous fun p : G1 E a × {r : ℝ // 0 < r} => (p.1 : GA E a) * centralSection E a p.2 :=
        (continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd)
      refine lt_of_le_of_lt (measure_mono ?_)
        ((hC.prod (isCompact_posIcc 1 (detModule E a (splitCentre E a 1)))).image hc).measure_lt_top
      rintro g ⟨hg, hb⟩
      rw [band_pos ha] at hb
      refine ⟨(retractOne g, detModule E a g), ⟨hg, hb.1, hb.2.le⟩, ?_⟩
      change (retractOne g : GA E a) * centralSection E a (detModule E a g) = g
      rw [coe_retractOne, inv_mul_cancel_right]
  have h3 : (muOne μ).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨x, hx⟩ := hne
    have hO : IsOpen (retractOne ⁻¹' U : Set (GA E a)) := hU.preimage continuous_retractOne
    rw [muOne_apply μ hU.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      rw [band_zero, Set.inter_univ]
      refine hO.measure_ne_zero μ ⟨1, ?_⟩
      change retractOne _ ∈ U
      rwa [Subsingleton.elim (retractOne _) x]
    · obtain ⟨s, hs1, hs2⟩ : ∃ s : {r : ℝ // 0 < r}, 1 < s ∧ s < detModule E a (splitCentre E a 1) := by
        obtain ⟨s, h1, h2⟩ := exists_between (show (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) from one_lt_top ha)
        exact ⟨⟨s, one_pos.trans h1⟩, h1, h2⟩
      have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
        continuous_subtype_val.comp continuous_detModule
      have hI : IsOpen (detModule E a ⁻¹' Set.Ioo 1 (detModule E a (splitCentre E a 1)) : Set (GA E a)) :=
        (isOpen_Ioo (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ))).preimage hc
      have hd : detModule E a ((x : GA E a) * centralSection E a s) = s := by
        rw [map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection ha, one_mul]
      have hr : retractOne ((x : GA E a) * centralSection E a s) = x := by
        ext1
        rw [coe_retractOne, hd, mul_inv_cancel_right]
      have hp := (hO.inter hI).measure_ne_zero μ ⟨(x : GA E a) * centralSection E a s, by
        rw [Set.mem_preimage, hr]; exact hx, by rw [Set.mem_preimage, hd]; exact ⟨hs1, hs2⟩⟩
      intro h0
      refine hp (measure_mono_null ?_ h0)
      rw [band_pos ha]
      exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.Ioo_subset_Ico_self)
  exact {}
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.ContMem
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem contMem_holds : ContMem := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ h
  obtain ⟨hc, hl, hz, hcu⟩ := mem_cuspCont.1 hφ
  have hL : IsLeftInvariant φ := fun γ g => hl γ g
  have hcusp : AutomorphicForm.IsCuspidal φ := UpperTheory.constantTerm_eq_zero_of_isCuspidal E a φ hL hc hcu
  have hr : ∀ g : GA E a, φ (retractOne g : G1 E a) = φ g := fun g => by
    obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) splitEq_holds (Reduction.detModule E a g)
    have h1 := hz t (retractOne g : G1 E a)
    rw [← h1, splitCentre_comm, coe_retractOne, ← ht, inv_mul_cancel_right]
  have hΦ : cuspQuot hL ∘ quotMap E a = descend (latticeGL E a) φ := by
    funext q
    change cuspQuot hL (RightCosetSpace.mk (Γ1 E a) (retractOne q.out)) = φ q.out
    rw [cuspQuot_mk]
    exact hr q.out
  have hm : MemLp (cuspQuot hL) 2 (RightCosetSpace.quotientMeasure (Γ1 E a) μ₁) := by
    have hs := (continuous_cuspQuot hL hc).aestronglyMeasurable
      (μ := Measure.map (quotMap E a) (quotMeasure (latticeGL E a) μ))
    rw [← hp.map_eq, memLp_map_measure_iff hs hp.aemeasurable, hΦ]
    exact h.2
  have hv : hm.toLp _ ∈ cuspidalL2 μ₁ := by
    change IsCuspidalL2 μ₁ (hm.toLp _)
    intro r h0 h1
    filter_upwards [ae_ctFun_congr μ₁ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    simpa only [ctFun, cuspQuot_mk, Subgroup.coe_mul, coe_unipOne, constantTerm, Pi.zero_apply]
      using hcusp r h0 h1 y
  refine ⟨⟨hm.toLp _, hv⟩, Lp.ext ?_⟩
  have hQuot : (cmp hp ⟨hm.toLp _, hv⟩ : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hL ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans
      (hp.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm))
  rw [hΦ] at hQuot
  exact hQuot.trans h.coeFn_toL2.symm

end UpperTheory.V.KernelIndexFullLattice
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompact
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.AutMult GroundTheory.Automorphic

theorem UpperTheory.V.KernelIndexFullLattice.absCompact_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsCompact := by
  intro G G₁ H L _ _ _ _ _ _ _ _ _ _ _ _ _ π ν _ _ ρ W hW J r hr hρ hJ hcpt
  have hmem : ∀ h, J h ∈ W := by
    intro h
    rw [← hJ]
    exact ⟨h, rfl⟩
  let Φ : H →ₗᵢ[ℂ] W :=
    { toLinearMap := (J.toLinearMap).codRestrict W hmem
      norm_map' := fun h => J.norm_map h }
  have hΦsurj : Function.Surjective Φ := by
    intro w
    have hw : (w : L) ∈ J.range := by
      rw [hJ]
      exact w.2
    obtain ⟨h, hh⟩ := hw
    exact ⟨h, Subtype.ext hh⟩
  let Ψ : H ≃ₗᵢ[ℂ] W := LinearIsometryEquiv.ofSurjective Φ hΦsurj
  let Ψc : H →L[ℂ] W := (Ψ.toContinuousLinearEquiv : H →L[ℂ] W)
  let Ψi : W →L[ℂ] H := (Ψ.symm.toContinuousLinearEquiv : W →L[ℂ] H)
  have hΨc : ∀ h, Ψc h = Ψ h := fun h => rfl
  have hΨi : ∀ w, Ψi w = Ψ.symm w := fun w => rfl
  have hrep : ∀ g h, hW.rep g (Ψ h) = Ψ (π (r g) h) := by
    intro g h
    apply Subtype.ext
    exact hρ g h
  intro w hw0
  have hne : Ψ.symm w ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Ψ h0
  obtain ⟨f, hf⟩ := π.exists_integrated_ne_zero ν hne
  refine ⟨Ψc ∘L (π.integrated ν (UnitaryRep.ccToL1 ν f)) ∘L Ψi, ?_, ?_, ?_⟩
  · exact ((hcpt f).comp_clm Ψi).clm_comp Ψc
  · intro S hS x
    rw [mem_homIn_top] at hS
    let T : H →L[ℂ] H := Ψi ∘L S ∘L Ψc
    have hT : T ∈ π.intertwiners π := by
      intro g₁ h
      obtain ⟨g, rfl⟩ := hr g₁
      show Ψ.symm (S (Ψ (π (r g) h))) = π (r g) (Ψ.symm (S (Ψ h)))
      have e1 : S (Ψ h) = Ψ (Ψ.symm (S (Ψ h))) := (Ψ.apply_symm_apply _).symm
      calc Ψ.symm (S (Ψ (π (r g) h))) = Ψ.symm (S (hW.rep g (Ψ h))) := by rw [hrep]
        _ = Ψ.symm (hW.rep g (S (Ψ h))) := by rw [hS]
        _ = Ψ.symm (hW.rep g (Ψ (Ψ.symm (S (Ψ h))))) := by rw [← e1]
        _ = π (r g) (Ψ.symm (S (Ψ h))) := by rw [hrep, LinearIsometryEquiv.symm_apply_apply]
    have hc := UnitaryRep.comp_integrated_of_mem_intertwiners π ν hT (UnitaryRep.ccToL1 ν f)
    have hc' := congrArg (fun Q => Q (Ψ.symm x)) hc
    simp only [T, ContinuousLinearMap.comp_apply, hΨc, hΨi,
      LinearIsometryEquiv.apply_symm_apply] at hc' ⊢
    rw [← hc', LinearIsometryEquiv.apply_symm_apply]
  · simpa [hΨc, hΨi] using hf
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsIrr
theorem UpperTheory.V.KernelIndexFullLattice.absIrr_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsIrr := by
  intro G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX
  obtain ⟨⟨hXc, hXinv⟩, hXne, hXmin⟩ := hX
  have hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H) :=
    hXc.preimage J.continuous
  haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe
  have hinv : π.IsInvariant (Submodule.comap J.toLinearMap X) := by
    intro g₁ v hv
    obtain ⟨g, rfl⟩ := hr g₁
    show J (π (r g) v) ∈ X
    rw [← hρ]
    exact hXinv g _ hv
  refine ⟨hVcomp, hinv, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    obtain ⟨h, rfl⟩ := hXJ hx
    refine nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_
    intro e
    apply hx0
    have e' : h = 0 := congrArg Subtype.val e
    rw [e', map_zero]
  · intro U' hU'c hU'inv
    let V := Submodule.comap J.toLinearMap X
    let U : Submodule ℂ L := (U'.map V.subtype).map J.toLinearMap
    have hUX : U ≤ X := by
      rintro _ ⟨_, ⟨u, _, rfl⟩, rfl⟩
      exact u.2
    have hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H) := by
      rw [Submodule.map_coe]
      exact hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c
    have hUc : IsClosed (U : Set L) := by
      rw [Submodule.map_coe]
      exact J.isometry.isClosedEmbedding.isClosedMap _ hU'H
    have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
      rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩
      exact (hρ g u).symm
    rcases hXmin U hUX ⟨hUc, hUinv⟩ with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have hJu : J u ∈ U := ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hJu
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hn : ‖(u : H)‖ = 0 := by rw [← J.norm_map, hJu, norm_zero]
      simpa using hn
    · right
      rw [eq_top_iff]
      intro u _
      have hJu : J u ∈ U := by
        rw [h]
        exact u.2
      obtain ⟨_, ⟨u', hu', rfl⟩, he⟩ := hJu
      have : u' = u := Subtype.ext (J.injective he)
      rw [← this]
      exact hu'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KernelIndexFullLatticeNeBot
theorem UpperTheory.V.KernelIndexFullLattice.kernelIndexFullLattice_neBot :
    UpperTheory.V.KernelIndexFullLattice.NeBot :=
  @GroundTheory.Automorphic.CuspidalSpectrum.summandCuspForms_ne_bot
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KFinMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.PvFinHolds
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.HomFin
open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.homFin_comp {R B S : Type} [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    isotypicComponent R B S = ⊥ ∨ isotypicComponent R B S ∈ isotypicComponents R B := by
  by_cases h : isotypicComponent R B S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨m, ⟨e⟩, -⟩ : ∃ m ∈ {m : Submodule R B | Nonempty (m ≃ₗ[R] S)}, m ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact h (sSup_eq_bot.mpr hc)
    haveI : IsSimpleModule R m := IsSimpleModule.congr e
    exact ⟨m, inferInstance, e.isotypicComponent_eq.symm⟩

theorem UpperTheory.V.KernelIndexFullLattice.homFin_holds :
    UpperTheory.V.KernelIndexFullLattice.HomFin := by
  intro C M X _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ F hF
  have hτK : CompactRep.IsKFinite τ := ⟨fun _ => inferInstance, hτ⟩
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ C) τ.asModule := CompactRep.isSemisimpleModule_asModule hτK
  haveI : IsNoetherian ℂ τ.asModule := inferInstanceAs (IsNoetherian ℂ X)
  haveI hτT : IsScalarTower ℂ (MonoidAlgebra ℂ C) τ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show τ.asAlgebraHom (c • a) _ = c • τ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI hσT : IsScalarTower ℂ (MonoidAlgebra ℂ C) σ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show σ.asAlgebraHom (c • a) _ = c • σ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI : IsNoetherian (MonoidAlgebra ℂ C) τ.asModule := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨t, ht, htop⟩ := WellFoundedGT.isSupFiniteCompact (α := Submodule (MonoidAlgebra ℂ C) τ.asModule) {m | IsSimpleModule (MonoidAlgebra ℂ C) m}
  rw [IsSemisimpleModule.sSup_simples_eq_top] at htop
  let W : Submodule (MonoidAlgebra ℂ C) τ.asModule → Submodule ℂ M := fun m =>
    F ⊓ ((isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m).restrictScalars ℂ : Submodule ℂ σ.asModule)
  refine ⟨t.sup W, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ M => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro m hm
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      rcases UpperTheory.V.KernelIndexFullLattice.homFin_comp (R := MonoidAlgebra ℂ C) (B := σ.asModule) (S := m) with h | hc
      · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
        intro v hv
        have hv2 : (show σ.asModule from v) ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m := hv.2
        rw [h] at hv2
        have hv0 : (show σ.asModule from v) = 0 := (Submodule.mem_bot (MonoidAlgebra ℂ C)).1 hv2
        exact (Submodule.mem_bot ℂ).2 hv0
      · haveI := hF _ hc
        refine Submodule.finiteDimensional_of_le
          (S₂ := LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)) ?_
        intro v hv
        exact ⟨⟨v, hv.1⟩, (CompactRep.kProj_apply_eq_self_iff hσ hc).2 hv.2⟩
  · intro f hf hFf x
    let f' : τ.asModule →ₗ[ℂ] σ.asModule :=
      σ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ τ.asModuleEquiv.toLinearMap
    let g : τ.asModule →ₗ[MonoidAlgebra ℂ C] σ.asModule :=
      MonoidAlgebra.equivariantOfLinearOfComm f'
        (fun k v => by
          simp [f']
          exact hf k v)
    have hg : ∀ y : τ.asModule, g y = f y := fun y => rfl
    have one : ∀ m ∈ t, ∀ y ∈ m, g y ∈ t.sup W := by
      intro m hm y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      refine Finset.le_sup (f := W) hm ⟨?_, ?_⟩
      · rw [hg]
        exact hFf y
      show g y ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m
      rcases (g.domRestrict m).injective_or_eq_zero with hi | h0
      · have hle : LinearMap.range (g.domRestrict m) ≤ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m :=
          le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
        exact hle ⟨⟨y, hy⟩, rfl⟩
      · have h1 : g y = 0 := by simpa using LinearMap.congr_fun h0 ⟨y, hy⟩
        rw [h1]
        exact zero_mem _
    have key : ∀ s : Finset (Submodule (MonoidAlgebra ℂ C) τ.asModule), s ⊆ t →
        ∀ y ∈ s.sup id, g y ∈ t.sup W := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ y hy
        have hy0 : y = 0 := by simpa using hy
        rw [hy0, map_zero]
        exact zero_mem _
      | insert a s ha ih =>
        intro hs y hy
        rw [Finset.sup_insert] at hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _)]
        exact add_mem (one a (hs (Finset.mem_insert_self a s)) y1 hy1)
          (ih ((Finset.subset_insert a s).trans hs) y2 hy2)
    have hx : (show τ.asModule from x) ∈ t.sup id := htop ▸ Submodule.mem_top
    have := key t subset_rfl _ hx
    rw [hg] at this
    exact this
end

open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem UpperTheory.V.KernelIndexFullLattice.pvFin_abs {G E M : Type} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M]
    (C : Subgroup G) [IsTopologicalGroup C] [CompactSpace C] [T2Space C] (ρ : BanachRep G E)
    (σ : Representation ℂ C M) (hσ : CompactRep.IsKFinite σ) (j : M →ₗ[ℂ] E) (hj : Function.Injective j)
    (hjσ : ∀ (k : C) m, j (σ k m) = ρ k (j m)) (F : Submodule ℂ M)
    (hF : ∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)))
    (v : E) (hv : FiniteDimensional ℂ (ρ.kSpan C v)) :
    ∃ N : Submodule ℂ E, FiniteDimensional ℂ N ∧ ∀ P : E →L[ℂ] E,
      (∀ (k : C) x, P (ρ k x) = ρ k (P x)) → (∀ x ∈ ρ.kSpan C v, ∃ m ∈ F, j m = P x) → P v ∈ N := by
  let S : Subrepresentation (ρ.restrict C).toRepresentation :=
    ⟨ρ.kSpan C v, fun k _ hw => ρ.map_mem_kSpan_of_mem C hw k⟩
  have hc : Representation.HasContinuousCoeff (W := ρ.kSpan C v) S.toRepresentation := by
    intro φ w
    refine φ.continuous_of_finiteDimensional.comp ?_
    exact Continuous.subtype_mk ((ρ.continuous_orbit (w : E)).comp continuous_subtype_val) _
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.homFin_holds C M (ρ.kSpan C v) σ hσ S.toRepresentation hc F hF
  refine ⟨N.map j, inferInstance, fun P hP hPF => ?_⟩
  have hr : ∀ x : ρ.kSpan C v, ((P : E →ₗ[ℂ] E) ∘ₗ (ρ.kSpan C v).subtype) x ∈ LinearMap.range j := by
    intro x
    obtain ⟨m, -, hm⟩ := hPF x x.2
    exact ⟨m, hm⟩
  let f : ρ.kSpan C v →ₗ[ℂ] M := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range j) _ hr
  have hf : ∀ x, j (f x) = P x := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨_, hr x⟩)
  refine ⟨f ⟨v, ρ.mem_kSpan_self C v⟩, hN' f (fun k x => hj ?_) (fun x => ?_) _, hf _⟩
  · rw [hjσ, hf, hf, ← hP]
    rfl
  · obtain ⟨m, hm, e⟩ := hPF x x.2
    rwa [hj ((hf x).trans e.symm)]

theorem UpperTheory.V.KernelIndexFullLattice.pvFin_holds :
    UpperTheory.V.KernelIndexFullLattice.PvFin := by
  intro K _ _ n μ₁ _ π U hUc hUo v hv hfin
  let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun m hm => Subtype.ext ?_
    exact eq_zero_of_cuspVecL_eq_zero (μ := μ₁) (π.le_central m.2) hm
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_abs (archCompact K n) (archRepT μ₁) π.toModule.gk.σ
    π.toModule.gk.isKFinite j hj (fun k m => cuspToL2_sigma μ₁ k (π.le_central m.2))
    (fixedVectors π.toModule.τ U) (π.isAdmissible.2 U hUc hUo) v hfin
  refine ⟨N, hN, fun P hPk hPu hP => hN' P hPk fun x hx => ?_⟩
  have hxU : ∀ u ∈ U, cuspRepT μ₁ (retractOne (finEmb K n u)) x = x := by
    intro u hu
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [archRepT_apply]
      have hcomm : retractOne (finEmb K n u) * archP K n k = archP K n k * retractOne (finEmb K n u) := by
        rw [← retract_infEmb (k : archGroup K n), ← retractOne_mul, ← retractOne_mul,
          infEmb_mul_finEmb_comm (k : archGroup K n) u]
      have h1 := (cuspRepT μ₁).map_mul_apply (retractOne (finEmb K n u)) (archP K n k) v
      have h2 := (cuspRepT μ₁).map_mul_apply (archP K n k) (retractOne (finEmb K n u)) v
      rw [hv u hu, ← hcomm, h1] at h2
      exact h2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  obtain ⟨φ, hφ, e⟩ := hP x
  refine ⟨⟨φ, hφ⟩, fun u hu => hj ?_, e⟩
  have h := cuspToL2_finRepCusp μ₁ u (π.le_central hφ)
  rw [e, ← hPu u hu, hxU u hu, ← e] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsApprox
private theorem starProjection_apply_comm_of_invariant_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Y : Submodule ℂ H) [Y.HasOrthogonalProjection] (B C : H →L[ℂ] H)
    (hB : ∀ y ∈ Y, B y ∈ Y) (hC : ∀ y ∈ Y, C y ∈ Y)
    (hBC : ContinuousLinearMap.adjoint B = C) (x : H) :
    Y.starProjection (B x) = B (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal' (z := B (x - Y.starProjection x))
    (hB _ (Y.starProjection_apply_mem x))
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hBC]
    exact Submodule.inner_right_of_mem_orthogonal (hC y hy)
      (Submodule.sub_starProjection_mem_orthogonal (K := Y) x)
  · rw [← map_add (f := _), add_sub_cancel]

private theorem exists_finiteDimensional_invariant_le_of_fg {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ι → H →L[ℂ] H) (W M : Submodule ℂ H) (hM : M.FG) (hMW : M ≤ W)
    (hW : ∀ w ∈ W, ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ w ∈ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y) :
    ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ M ≤ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have key : ∀ t : Finset H, (↑t : Set H) ⊆ W → ∃ Y ≤ W, FiniteDimensional ℂ Y ∧
      (↑t : Set H) ⊆ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨⊥, bot_le, inferInstance, by simp, fun i y hy => ?_⟩
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact Submodule.zero_mem _
    | insert a t ha ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨Y1, h1W, h1f, h1t, h1A⟩ := ih hsub.2
      obtain ⟨Y2, h2W, h2f, h2a, h2A⟩ := hW a hsub.1
      haveI := h1f
      haveI := h2f
      refine ⟨Y1 ⊔ Y2, sup_le h1W h2W, inferInstance, ?_, ?_⟩
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨Submodule.mem_sup_right h2a, h1t.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩
      · intro i y hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h1A i y1 hy1) (h2A i y2 hy2)
  obtain ⟨Y, hYW, hYf, hsY, hYA⟩ := key s (Submodule.span_le.1 hMW)
  exact ⟨Y, hYW, hYf, Submodule.span_le.2 hsY, hYA⟩

theorem UpperTheory.V.KernelIndexFullLattice.absApprox_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsApprox := by
  intro ι H _ _ _ A hA W N hN hW v hv hP
  classical
  haveI := hN
  have hfg : (N ⊓ W).FG := by
    haveI : FiniteDimensional ℂ ↥(N ⊓ W) := Submodule.finiteDimensional_of_le inf_le_left
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  obtain ⟨Y0, hY0W, hY0f, hNY0, hY0A⟩ := exists_finiteDimensional_invariant_le_of_fg A W (N ⊓ W) hfg inf_le_right hW
  haveI := hY0f
  have hproj : ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y], Y ≤ W →
      (∀ i, ∀ y ∈ Y, A i y ∈ Y) → Y0 ≤ Y → Y0.starProjection v = Y.starProjection v := by
    intro Y _ hYW hYA hY0Y
    have h1 : Y.starProjection v ∈ N := by
      apply hP
      · intro i x
        obtain ⟨j, hj⟩ := hA i
        exact starProjection_apply_comm_of_invariant_adjoint Y (A i) (A j) (hYA i) (hYA j) hj x
      · intro x
        exact hYW (Y.starProjection_apply_mem x)
    have h2 : Y.starProjection v ∈ Y0 := hNY0 ⟨h1, hYW (Y.starProjection_apply_mem v)⟩
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero h2
    intro w hw
    exact Submodule.starProjection_inner_eq_zero v w (hY0Y hw)
  have horth : ∀ w ∈ W, inner ℂ w (v - Y0.starProjection v) = 0 := by
    intro w hw
    obtain ⟨Y1, h1W, h1f, hw1, h1A⟩ := hW w hw
    haveI := h1f
    have hY := hproj (Y0 ⊔ Y1) (sup_le hY0W h1W) (fun i y hy => by
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hY0A i y1 hy1) (h1A i y2 hy2)) le_sup_left
    rw [hY, inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero v w (Submodule.mem_sup_right hw1)
  have hcl : v - Y0.starProjection v ∈ W.topologicalClosure :=
    W.topologicalClosure.sub_mem hv
      (W.le_topologicalClosure (hY0W (Y0.starProjection_apply_mem v)))
  have hsub : closure (W : Set H) ⊆ {x | inner ℂ x (v - Y0.starProjection v) = 0} :=
    closure_minimal horth (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  have hzero : inner ℂ (v - Y0.starProjection v) (v - Y0.starProjection v) = 0 := by
    apply hsub
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  rw [inner_self_eq_zero, sub_eq_zero] at hzero
  rw [hzero]
  exact hY0W (Y0.starProjection_apply_mem v)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.StabFin
open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.orbit_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (v : V)
    (hv : IsOpen {g : G | τ g v = v}) (U : Set G) (hU : IsCompact U) :
    ((fun g => τ g v) '' U).Finite := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun g : G => (fun x : G => g⁻¹ * x) ⁻¹' {h : G | τ h v = v})
    (fun g => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine (t.finite_toSet.image (fun g => τ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (ht hx)
  have hs : τ (g⁻¹ * x) v = v := hxg
  refine ⟨g, hg, ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  show τ g v = τ x v
  rw [e, map_mul, Module.End.mul_apply, hs]

private theorem UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable {C G : Type*} [Group C] [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ C V) (τ : Representation ℂ G V)
    (hσ : ∀ v : V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => σ k v)))
    (hc : ∀ k g, σ k * τ g = τ g * σ k) (U : Subgroup G) (v : V)
    (hf : ((fun g => τ g v) '' (U : Set G)).Finite) :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ (∀ k, ∀ y ∈ Y, σ k y ∈ Y) ∧
      ∀ u ∈ U, ∀ y ∈ Y, τ u y ∈ Y := by
  classical
  let Y : Submodule ℂ V := hf.toFinset.sup (fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
  have mem : ∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, σ k w ∈ Y := by
    intro w hw k
    exact Finset.le_sup (f := fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
      (hf.mem_toFinset.2 hw) (Submodule.subset_span ⟨k, rfl⟩)
  have stab : ∀ φ : Module.End ℂ V,
      (∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, φ (σ k w) ∈ Y) → ∀ y ∈ Y, φ y ∈ Y := by
    intro φ hφ y hy
    have hle : Y ≤ Y.comap φ := by
      refine Finset.sup_le fun w hw => ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hφ w (hf.mem_toFinset.1 hw) k
    exact hle hy
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ V => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro w _
      exact hσ w
  · have h1 := mem v ⟨1, U.one_mem, by simp⟩ 1
    simpa using h1
  · intro k
    refine stab (σ k) ?_
    intro w hw k'
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem w hw _
  · intro u hu
    refine stab (τ u) ?_
    rintro _ ⟨g, hg, rfl⟩ k
    have e : τ u (σ k (τ g v)) = σ k (τ (u * g) v) := by
      rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ u) (σ k), ← hc k u,
        Module.End.mul_apply]
    rw [e]
    exact mem _ ⟨u * g, U.mul_mem hu hg, rfl⟩ k

theorem UpperTheory.V.KernelIndexFullLattice.stabFin_holds :
    UpperTheory.V.KernelIndexFullLattice.StabFin := by
  intro K _ _ n V _ _ M hM U hU v
  exact UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable M.gk.σ M.τ M.gk.locallyFinite M.comm_σ U v
    (UpperTheory.V.KernelIndexFullLattice.orbit_finite M.τ v (hM v) _ hU)
end

open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem kFinMem_holds : KFinMem := by
  intro K _ _ n μ₁ _ π v hv hop hfin
  have h1 : retractOne (1 : AdelicGLn.AdelicGL K n) = 1 := retractOne_coe (1 : G1 K n)
  let r : AdelicGLn.FiniteAdelicGL K n →* G1 K n :=
    { toFun := fun h => retractOne (finEmb K n h)
      map_one' := by rw [map_one (finEmb K n), h1]
      map_mul' := fun a b => by rw [map_mul (finEmb K n), retractOne_mul] }
  let S : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | cuspRepT μ₁ (r h) v = v}
      one_mem' := by
        show cuspRepT μ₁ (r 1) v = v
        rw [map_one r]
        simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        have hb' : cuspRepT μ₁ (r b) v = v := hb
        show cuspRepT μ₁ (r (a * b)) v = v
        rw [map_mul r, UnitaryRep.map_mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        show cuspRepT μ₁ (r a⁻¹) v = v
        have h := (cuspRepT μ₁).map_mul_apply (r a⁻¹) (r a) v
        rw [ha', ← map_mul r, inv_mul_cancel, map_one r] at h
        rw [← h]
        simp }
  have hSo : IsOpen (S : Set (AdelicGLn.FiniteAdelicGL K n)) := hop
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) := S ⊓ AdelicGLn.integralFiniteGL K n
  have hUo : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := hSo.inter (AdelicGLn.isOpen_integralFiniteGL K n)
  have hUc : IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
  obtain ⟨N, hN, hN'⟩ := pvFin_holds K n μ₁ π U hUc hUo v (fun u hu => hu.1) hfin
  let A : archCompact K n ⊕ U → CuspL2 μ₁ →L[ℂ] CuspL2 μ₁ :=
    Sum.elim (fun k => cuspRepT μ₁ (archP K n k)) fun u => cuspRepT μ₁ (r u)
  refine absApprox_holds (archCompact K n ⊕ U) (CuspL2 μ₁) A ?_ _ N hN ?_ v hv
    fun P hP hPW => hN' P (fun k x => hP (.inl k) x) (fun u hu x => hP (.inr ⟨u, hu⟩) x) hPW
  · rintro (k | u)
    · refine ⟨.inl k⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (archP K n k)) = cuspRepT μ₁ (archP K n (k : archGroup K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv (archP K n)]
    · refine ⟨.inr u⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (r u)) =
        cuspRepT μ₁ (r (u : AdelicGLn.FiniteAdelicGL K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv r]
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨Y, hY, hφY, hk, hu⟩ :=
      stabFin_holds K n π.carrier π.toModule π.isAdmissible.1 U hUc ⟨φ, hφ⟩
    let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
    refine ⟨Y.map j, ?_, inferInstance, ⟨_, hφY, rfl⟩, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro (k | u) _ ⟨y, hy, rfl⟩
      · exact ⟨_, hk k y hy, cuspToL2_sigma μ₁ k (π.le_central y.2)⟩
      · exact ⟨_, hu u u.2 y hy, cuspToL2_finRepCusp μ₁ u (π.le_central y.2)⟩

end UpperTheory.V.KernelIndexFullLattice
end

open UpperTheory.V.KernelIndexFullLattice in
theorem UpperTheory.V.Af.cuspSpectrumGL :
    GlobalTheory.Published.CuspidalSpectrumGL :=
  ⟨partA muHaar_holds quotPres_holds cmpEquiv_holds rangeLe_holds contMem_holds absCompact_holds,
    partB splitEq_holds muHaar_holds quotPres_holds cmpEquiv_holds cmpForm_holds rangeLe_holds contMem_holds
      absIrr_holds kernelIndexFullLattice_neBot kFinTr_holds kFinMem_holds brRep_holds,
    partC splitEq_holds brCusp_holds⟩
