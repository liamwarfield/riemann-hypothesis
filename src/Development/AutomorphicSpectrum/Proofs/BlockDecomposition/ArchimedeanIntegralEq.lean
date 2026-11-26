module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionRegularOnNonvanishingChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BadProjectionLocusNull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheet
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem log_eq_of_frame {a ρ F G Pa Pb φ h : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hF : 0 < F) (hG : 0 < G)
    (hPa : 0 < Pa) (hPb : 0 < Pb) (hh : h = Pa / Pb * a * Real.exp (φ / 2))
    (e : a * ρ * (G / Pb) = F / Pa) : Real.log ρ - φ / 2 = Real.log (F / G / h) := by
  have hE := Real.exp_pos (φ / 2)
  have key : F / G / h = ρ / Real.exp (φ / 2) := by
    have hF' : F = a * ρ * (G / Pb) * Pa := by
      rw [e]
      field_simp
    rw [hh, hF']
    field_simp
  rw [key, Real.log_div hρ.ne' hE.ne', Real.log_exp]

theorem value_of_ne_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  intro m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0
  obtain ⟨α, β, hf, hg, -, -, hdeg⟩ := hfg
  obtain ⟨u, hu, hcl⟩ := hrat
  obtain ⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y := ⟨_, rfl⟩
  have hz' : IsUnder w z := hw ▸ hz
  have hwb := mem_pick (M.φ σ₀).isLB w
  obtain ⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w := ⟨_, rfl⟩
  rw [← hb] at hwb
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k := ⟨_, rfl⟩
  have hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)
  have hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hwb, hwc⟩
  have pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V) := by
    intro V hV
    subst hw
    exact CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)
  have hyc := pre _ hwc
  have hybc := pre _ hwbc
  have hyb := pre _ hwb
  have hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem (CxPts.mem_ptsIn.1 hyc)
  have hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem (CxPts.mem_ptsIn.1 hybc)
  have e := hcl b c hgc hgb
  have hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
  have val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k := by
    intro s a hs
    refine (ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
    exact ev_dehomog_of_isUnder m n c s a hs w z hz' hwc
  have unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s) := by
    intro s a hs h0
    refine (unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))
    rw [← ratVal_fnOf hyc hgc]
    change ratVal (fnAt i c hgc s) y ≠ 0
    rw [val s a hs]
    exact div_ne_zero h0 (hne a)
  have hF := unit f α hf hf0
  have hG := unit g β hg hg0
  have hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val)) := by
    obtain ⟨v, hv⟩ := (u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom
    have hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val := hv
    rw [← hv']
    exact unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v
  have hR : UnitAt (under y) (r fun _ => b : X.functionField) := by
    have e' : (r fun _ => b : X.functionField) =
        fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹ := by
      rw [← e]
      have h1 := hU.ne_zero
      have h2 := hG.ne_zero
      field_simp
    rw [e']
    exact hF.mul (hU.mul hG).inv
  have hxb : under y ∈ (M.restr i).B.U (fun _ => b) := by
    refine Set.mem_iInter.2 fun _ => ?_
    subst hw
    exact CxPts.mem_ptsIn.1 hwb
  have hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b)) := CxPts.mem_ptsIn.2 hxb
  have ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) :=
    mem_offSupp.2 fun hs =>
      ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR
  refine ⟨ho, ?_⟩
  have hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w := by
    rw [hw]
    exact GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y
  have hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w := by
    refine (ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
  have ev' := congrArg (ratVal · y) e
  simp only at ev'
  rw [ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf] at ev'
  have hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := fun a => by
    have := norm_pos_iff.2 (hne a)
    simpa only [norm_prod, norm_pow] using this
  have hh := hu.2.2 b c w z hz' hwbc
  have hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 : ‖z ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
    rw [← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]
  rw [hzp] at hh
  rw [logNorm_eq _ hr ho hyb', hφ, logNormRat]
  have evn := congrArg norm ev'
  simp only [norm_mul, norm_div, norm_prod, norm_pow] at evn
  exact log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR))
    (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheetStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_log_norm_on_sheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZero
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem chernPart_null_of_chart_null : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  intro k _ X q σ D B φ ε Z hZ hc
  have hchart : ∀ (c : GlobalTheory.AlgChart q σ D) (ρ : GlobalTheory.CxPts q σ → ENNReal),
      GlobalTheory.ChartGlue.chartMeas c.e ρ Z = 0 := by
    intro c ρ
    unfold GlobalTheory.ChartGlue.chartMeas
    have hf : AEMeasurable c.e.symm ((volume.restrict c.e.target).withDensity (ρ ∘ c.e.symm)) :=
      (c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable hf hZ]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' c.e.open_target.measurableSet, Set.inter_comm]
    exact hc c
  have hle : ∀ ρ : GlobalTheory.AlgChart q σ D → GlobalTheory.CxPts q σ → ENNReal,
      GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ ≤
        (GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ).restrict Zᶜ := by
    intro ρ
    unfold GlobalTheory.ChartGlue.glueMeas
    refine iSup_le fun c => ?_
    have hae : ∀ᵐ y ∂(GlobalTheory.ChartGlue.chartMeas c.e (ρ c)), y ∈ Zᶜ := by
      rw [ae_iff]
      simpa using hchart c (ρ c)
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact Measure.restrict_mono subset_rfl
      (le_iSup (fun c : GlobalTheory.AlgChart q σ D => GlobalTheory.ChartGlue.chartMeas c.e (ρ c)) c)
  have h3 : φ.chernPart D ε Z ≤ (φ.chernPart D ε).restrict Zᶜ Z :=
    Measure.le_iff'.mp (hle fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Z
  rw [Measure.restrict_apply hZ, Set.inter_compl_self, measure_empty] at h3
  exact nonpos_iff_eq_zero.mp h3

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZeroStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_null_set_zero : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null | exact GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null | (intros; apply GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormula
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem onePiece {Y : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (m : Measure Y) (e : OpenPartialHomeomorph Y (Fin D → ℂ)) (r : (Fin D → ℂ) → ℝ)
    (hr : ContinuousOn r e.target)
    (hm : m.restrict e.source = ((volume.restrict e.target).withDensity fun v =>
      ENNReal.ofReal (r v)).map e.symm)
    (S : Set Y) (hS : MeasurableSet S) (hSs : S ⊆ e.source) (K : Y → ℝ)
    (hK : IntegrableOn K S m) :
    Integrable ((e '' S).indicator fun v => K (e.symm v) * max (r v) 0) ∧
      ∫ y in S, K y ∂m = ∫ v, (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) v := by
  classical
  set ν0 : Measure (Fin D → ℂ) := volume.restrict e.target with hν0
  set d : (Fin D → ℂ) → ENNReal := fun v => ENNReal.ofReal (r v) with hd
  have htm : MeasurableSet e.target := e.open_target.measurableSet
  have hsm : MeasurableSet e.source := e.open_source.measurableSet
  have hdm : AEMeasurable d ν0 :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hr.aemeasurable htm)
  have hdlt : ∀ᵐ v ∂ν0, d v < ⊤ := Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top
  have hsy0 : AEMeasurable e.symm ν0 := e.continuousOn_symm.aemeasurable htm
  have hsy : AEMeasurable e.symm (ν0.withDensity d) :=
    hsy0.mono_ac (withDensity_absolutelyContinuous _ _)
  set K' : Y → ℝ := S.indicator K with hK'
  have hK1 : Integrable K' m := (integrable_indicator_iff hS).2 hK
  have hK2 : Integrable K' ((ν0.withDensity d).map e.symm) := by
    rw [← hm]; exact hK1.restrict
  have hK3 : Integrable (K' ∘ e.symm) (ν0.withDensity d) :=
    (integrable_map_measure hK2.aestronglyMeasurable hsy).1 hK2
  have hK4 : Integrable (fun v => (d v).toReal • (K' ∘ e.symm) v) ν0 :=
    (integrable_withDensity_iff_integrable_smul₀' hdm hdlt).1 hK3
  have hfun : (e '' S).indicator (fun v => K (e.symm v) * max (r v) 0) =
      e.target.indicator (fun v => (d v).toReal • (K' ∘ e.symm) v) := by
    funext v
    by_cases hv : v ∈ e '' S
    · obtain ⟨y, hy, rfl⟩ := hv
      have hyt : e y ∈ e.target := e.map_source (hSs hy)
      have hinv : e.symm (e y) = y := e.left_inv (hSs hy)
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), Set.indicator_of_mem hyt]
      simp [hinv, hK', hy, hd, ENNReal.toReal_ofReal', mul_comm]
    · rw [Set.indicator_of_notMem hv]
      by_cases hvt : v ∈ e.target
      · have hns : e.symm v ∉ S := fun h => hv ⟨_, h, e.right_inv hvt⟩
        rw [Set.indicator_of_mem hvt]; simp [hK', hns]
      · rw [Set.indicator_of_notMem hvt]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_indicator_iff htm).2 hK4
  · rw [hfun, integral_indicator htm]
    calc ∫ y in S, K y ∂m = ∫ y, K' y ∂m := (integral_indicator hS).symm
      _ = ∫ y in e.source, K' y ∂m := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
          intro y hy
          exact Set.indicator_of_notMem (fun h => hy (hSs h)) _
      _ = ∫ y, K' y ∂((ν0.withDensity d).map e.symm) := by rw [hm]
      _ = ∫ v, (K' ∘ e.symm) v ∂(ν0.withDensity d) :=
          integral_map hsy hK2.aestronglyMeasurable
      _ = ∫ v, (d v).toReal • (K' ∘ e.symm) v ∂ν0 :=
          integral_withDensity_eq_integral_toReal_smul₀ hdm hdlt _

theorem exists_partition {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Countable ι] (U : ι → Set Y) (hU : ∀ l, IsOpen (U l)) (G : Set Y) (hG : MeasurableSet G)
    (hGs : G ⊆ ⋃ l, U l) :
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ U l) ∧
      Pairwise (Function.onFun Disjoint S) ∧ ⋃ l, S l = G := by
  classical
  haveI := Encodable.ofCountable ι
  refine ⟨fun l => (G ∩ U l) \ ⋃ (k : ι) (_ : Encodable.encode k < Encodable.encode l), U k,
    fun l => ?_, fun l y hy => hy.1.2, ?_, ?_⟩
  · exact (hG.inter (hU l).measurableSet).diff
      (isOpen_iUnion fun k => isOpen_iUnion fun _ => hU k).measurableSet
  · have key : ∀ l k : ι, Encodable.encode k < Encodable.encode l →
        Disjoint ((G ∩ U k) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode k), U j)
          ((G ∩ U l) \ ⋃ (j : ι) (_ : Encodable.encode j < Encodable.encode l), U j) := by
      intro l k hlt
      refine Set.disjoint_left.2 fun y hyk hyl => hyl.2 ?_
      exact Set.mem_iUnion₂.2 ⟨k, hlt, hyk.1.2⟩
    intro l k hne
    rcases lt_trichotomy (Encodable.encode l) (Encodable.encode k) with h | h | h
    · exact key k l h
    · exact absurd (Encodable.encode_injective h) hne
    · exact (key l k h).symm
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun l y hy => hy.1.1
    · intro y hy
      have hex : ∃ n, ∃ l : ι, Encodable.encode l = n ∧ y ∈ U l := by
        obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hGs hy)
        exact ⟨_, l, rfl, hl⟩
      obtain ⟨l, hl, hyl⟩ := Nat.find_spec hex
      refine Set.mem_iUnion.2 ⟨l, ⟨hy, hyl⟩, fun hmem => ?_⟩
      obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 hmem
      exact Nat.find_min hex (hl ▸ hk) ⟨k, rfl, hyk⟩

theorem abs_eq_max_add_max (a : ℝ) : |a| = max a 0 + max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

theorem integral_pieces : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  intro Y ι D _ _ _ _ μ e ρ hρ hμ G hG hGs F hF
  obtain ⟨S, hSm, hSs, hSd, hSu⟩ := exists_partition (fun l => (e l).source)
    (fun l => (e l).open_source) G hG hGs
  refine ⟨S, hSm, hSs, hSd, hSu, ?_⟩
  have hSG : ∀ l, S l ⊆ G := fun l => hSu ▸ Set.subset_iUnion S l
  have piece : ∀ (l : ι) (ε : ℤˣ) (K : Y → ℝ), IntegrableOn K (S l) (μ ε) →
      Integrable ((e l '' S l).indicator fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) ∧
      ∫ y in S l, K y ∂μ ε =
        ∫ v, (e l '' S l).indicator (fun v => K ((e l).symm v) * max (((ε : ℤ) : ℝ) * ρ l v) 0) v :=
    fun l ε K hK => onePiece (μ ε) (e l) (fun v => ((ε : ℤ) : ℝ) * ρ l v)
      (continuousOn_const.mul (hρ l)) (hμ l ε) (S l) (hSm l) (hSs l) K hK
  set Φ : ι → (Fin D → ℂ) → ℝ := fun l =>
    (e l '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) with hΦ
  have hΦsub : ∀ l, Φ l =
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) -
      (e l '' S l).indicator (fun v => F ((e l).symm v) * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) := by
    intro l
    funext v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Pi.sub_apply, Set.indicator_of_mem hv]
      have h := max_zero_sub_max_neg_zero_eq_self (ρ l v)
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [← mul_sub, h]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hΦnorm : ∀ l v, ‖Φ l v‖ =
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v +
      (e l '' S l).indicator (fun v => ‖F ((e l).symm v)‖ * max ((((-1 : ℤˣ) : ℤ) : ℝ) * ρ l v) 0) v := by
    intro l v
    by_cases hv : v ∈ e l '' S l
    · simp only [hΦ, Set.indicator_of_mem hv]
      simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
      rw [norm_mul, ← mul_add, Real.norm_eq_abs (ρ l v), abs_eq_max_add_max]
    · simp [hΦ, Set.indicator_of_notMem hv]
  have hFS : ∀ l ε, IntegrableOn F (S l) (μ ε) := fun l ε => (hF ε).mono_set (hSG l)
  have hFnS : ∀ l ε, IntegrableOn (fun y => ‖F y‖) (S l) (μ ε) := fun l ε => (hFS l ε).norm
  have hΦint : ∀ l, Integrable (Φ l) := by
    intro l
    rw [hΦsub l]
    exact (piece l 1 F (hFS l 1)).1.sub (piece l (-1) F (hFS l (-1))).1
  have hΦval : ∀ l, ∫ v, Φ l v = ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1) := by
    intro l
    rw [hΦsub l, (piece l 1 F (hFS l 1)).2, (piece l (-1) F (hFS l (-1))).2]
    exact integral_sub (piece l 1 F (hFS l 1)).1 (piece l (-1) F (hFS l (-1))).1
  have hΦnval : ∀ l, ∫ v, ‖Φ l v‖ =
      ∫ y in S l, ‖F y‖ ∂μ 1 + ∫ y in S l, ‖F y‖ ∂μ (-1) := by
    intro l
    simp only [hΦnorm l]
    rw [(piece l 1 _ (hFnS l 1)).2, (piece l (-1) _ (hFnS l (-1))).2]
    exact integral_add (piece l 1 _ (hFnS l 1)).1 (piece l (-1) _ (hFnS l (-1))).1
  have hU : ∀ ε, IntegrableOn F (⋃ l, S l) (μ ε) := fun ε => by rw [hSu]; exact hF ε
  have hsumN : ∀ ε, Summable fun l => ∫ y in S l, ‖F y‖ ∂μ ε := fun ε =>
    (hasSum_integral_iUnion hSm hSd (hU ε).norm).summable
  have h1 : HasSum (fun l => ∫ v, Φ l v) (∫ v, ∑' l, Φ l v) :=
    hasSum_integral_of_summable_integral_norm hΦint
      (by simp only [hΦnval]; exact (hsumN 1).add (hsumN (-1)))
  have h2 : HasSum (fun l => ∫ y in S l, F y ∂μ 1 - ∫ y in S l, F y ∂μ (-1))
      (∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1)) := by
    have a := hasSum_integral_iUnion hSm hSd (hU 1)
    have b := hasSum_integral_iUnion hSm hSd (hU (-1))
    rw [hSu] at a b
    exact a.sub b
  simp only [hΦval] at h1
  exact h2.unique h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityChartIntegralFormulaStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_chart_integral_formula : ∀ {Y ι : Type} {D : ℕ} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι]
    (μ : ℤˣ → Measure Y) (e : ι → OpenPartialHomeomorph Y (Fin D → ℂ)) (ρ : ι → (Fin D → ℂ) → ℝ),
    (∀ l, ContinuousOn (ρ l) (e l).target) →
    (∀ l (ε : ℤˣ), (μ ε).restrict (e l).source = ((volume.restrict (e l).target).withDensity fun v =>
      ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ l v)).map (e l).symm) →
    ∀ (G : Set Y), MeasurableSet G → G ⊆ ⋃ l, (e l).source → ∀ F : Y → ℝ, (∀ ε, IntegrableOn F G (μ ε)) →
    ∃ S : ι → Set Y, (∀ l, MeasurableSet (S l)) ∧ (∀ l, S l ⊆ (e l).source) ∧ Pairwise (Function.onFun Disjoint S) ∧
      ⋃ l, S l = G ∧ ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) =
        ∫ v, ∑' l, ((e l) '' S l).indicator (fun v => F ((e l).symm v) * ρ l v) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.integral_pieces <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyGenericallyEtaleCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyGenericallyEtaleCoordinates
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.GenericCoords

theorem exists_etale_coords_int : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), GlobalTheory.IsArithVar p D →
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x).Etale :=
  fun _ _ _ _ h => GlobalTheory.GenericEtale.exists_etale_coords h

end GlobalTheory.CompanionTheory.MixZ.GenericCoords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyGenericallyEtaleCoordinatesStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_generically_etale_coordinates : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), GlobalTheory.IsArithVar p D →
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x).Etale := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int | exact GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int | (intros; apply GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointsSecondCountable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointsSecondCountable
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section
namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open Topology
open scoped CommRingCat.HomTopology

theorem secondCountable_hom_of_finiteType (A : CommRingCat.{0}) [Algebra.FiniteType ℤ A] :
    SecondCountableTopology (A ⟶ CommRingCat.of ℂ) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ A)
  choose q hq using hf
  have h := CommRingCat.HomTopology.isEmbedding_hom (CommRingCat.of ℂ) A
  have hcoord : Continuous fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i)) :=
    continuous_pi fun i => (continuous_apply (f (MvPolynomial.X i))).comp h.continuous
  have hemb : IsEmbedding fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i)) := by
    refine IsEmbedding.of_comp (g := fun (z : Fin n → ℂ) (u : A) => MvPolynomial.aeval z (q u))
      hcoord (continuous_pi fun u => ?_) ?_
    · simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      fun_prop
    · convert h using 1
      ext φ u
      simp only [Function.comp_apply]
      have e : (φ.hom.toIntAlgHom.comp f) = MvPolynomial.aeval fun i => φ.hom (f (MvPolynomial.X i)) := by
        ext i
        simp
      have := congrArg (fun g => g (q u)) e
      simp only [AlgHom.comp_apply, hq] at this
      exact this.symm
  exact hemb.secondCountableTopology

theorem finiteType_of_isAffineOpen {X : Scheme.{0}} (p : X ⟶ Sp ℤ) [LocallyOfFiniteType p] {U : X.Opens}
    (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have h := p.finiteType_appLE (isAffineOpen_top _) hU (fun _ _ => trivial)
  have h2 : ((p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
    h.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm.surjective)
  rw [← RingHom.finiteType_algebraMap]
  convert h2 using 1
  exact RingHom.ext_int _ _

theorem secondCountable_points {X : Scheme.{0}} (p : X ⟶ Sp ℤ) [LocallyOfFiniteType p] [CompactSpace X] :
    SecondCountableTopology (Sp ℂ ⟶ X) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have hsc : ∀ i : t, SecondCountableTopology
      ({x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1} : Set (Sp ℂ ⟶ X)) := fun i => by
    have := finiteType_of_isAffineOpen p i.1.2
    have := secondCountable_hom_of_finiteType Γ(X, i.1.1)
    exact (affineHomeomorph (C := ℂ) i.1.2).isEmbedding.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (U := fun i : t => {x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1})
    (fun i => isOpen_setOf_le_preimage _) (Set.eq_univ_of_forall fun x => ?_)
  have hx := ht (Set.mem_univ (x (IsLocalRing.closedPoint ℂ)))
  simp only [Set.mem_iUnion] at hx
  obtain ⟨U, hU, hxU⟩ := hx
  exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, (le_preimage_iff x _).2 hxU⟩

theorem secondCountable_cxPts (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ) (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := by
  obtain ⟨N, j, hj, e⟩ := hX.isProjOver
  have hN : IsProper (PSpace.str ℤ N) := isProper_str ℤ N
  have hp : IsProper (i ≫ mpStr ℤ m n) := by
    rw [← e]
    infer_instance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (i ≫ mpStr ℤ m n)
  have := secondCountable_points (i ≫ mpStr ℤ m n)
  exact IsEmbedding.subtypeVal.secondCountableTopology

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointsSecondCountableStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_second_countable : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormula
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

section Torus

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_torus_of_homog {s : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

private theorem ratio_cancel {a b F G H : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * F / (b * G) / (a / b * H) = F / G / H := by
  by_cases hG : G = 0
  · simp [hG]
  by_cases hH : H = 0
  · simp [hH]
  field_simp

theorem logNormRat_torus {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {A : HermLine ι} {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : IsRatSectionOn P A f g) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNormRat A f g (fun p => c p.1 * z p) = logNormRat A f g z := by
  obtain ⟨α, β, hf, hg, -, -, hd⟩ := h
  have hne : ∀ (a : K → ℕ), ‖∏ k, c k ^ a k‖ ≠ 0 := fun a =>
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  have hab : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ α k‖ / ‖∏ k, c k ^ β k‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), norm_pow, norm_pow, zpow_natCast, zpow_natCast]
  unfold logNormRat
  rw [eval_torus_of_homog hf, eval_torus_of_homog hg, A.smul c z hc, norm_mul, norm_mul, hab,
    ratio_cancel (hne α) (hne β)]

end Torus

theorem sheetDensity_eq_of_isSheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  intro m n P D Ψ B A f g hP hΨ hB hA
  let A' : HermLine (Bk n) := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine 1
  have hA1 : ∀ z, ReciprocityTheory.ChartRestriction.G.Geo.logNorm A' 1 z = 1 := fun z => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A' := contDiffOn_const
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P A' 1 := by
    refine ⟨0, fun k => by simp [A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight], fun d hd k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  filter_upwards [ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep (Fin (m + 1)) (Bk n) P D Ψ (fun _ => B) A' 1 hP hΨ (fun _ => hB) hAs hs]
    with v hind w γ hγ
  have hex : ∃ γ, IsSheet P Ψ v w γ := ⟨γ, hγ⟩
  have hc := hex.choose_spec
  have h1 := hind w _ γ hc hγ
  simp only [hA1, one_mul] at h1
  have hval : logNormRat A f g (hex.choose v) = logNormRat A f g (γ v) := by
    obtain ⟨c, hcne, hcz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre hγ.2.self_of_nhds.2.1.1 1 one_ne_zero
      (by rw [one_smul, hc.1, hγ.1])
    rw [hcz]
    exact logNormRat_torus hA hcne _
  unfold sheetDensity
  rw [dite_eq_left hex, hval]
  exact congrArg (logNormRat A f g (γ v) * ·) h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetDensityLogNormFormulaStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_density_log_norm_formula : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet <;> assumption)
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section
namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

theorem ae_cover {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1)) (Ψ : LinProj n D)
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) (N : Pol n) (a : Fin (m + 1) → ℕ) (hN : IsMultiHomog N a)
    (hNP : N ∉ ptIdeal (i (genericPoint X)))
    (hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source) :
    ∀ᵐ v : Fin D → ℂ, ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ pieceSet i Ψ N := by
  classical
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D => c.e.source) (fun c => c.e.open_source)
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.projB_null (J := Ideal.span {N}) Ψ hP hΨ
    ⟨{N}, by rintro f rfl; exact ⟨a, hN⟩, rfl⟩ (fun h => hNP (h (Ideal.subset_span rfl)))
  have h2 : volume (⋃ c ∈ T, projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y}) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun c _ => GlobalTheory.T.irregular_projection_image_null m n X i D Ψ c
  have h3 := measure_union_null h1 h2
  refine ae_iff.2 (measure_mono_null ?_ h3)
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨z, hz, hzv, hno⟩ := hv
  by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
  · refine Or.inl ⟨z, hz, ⟨hz.1, fun g hg => ?_⟩, hzv⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp [hNz]
  · obtain ⟨y, hy⟩ := GlobalTheory.T.multicone_point_descends_to_subvariety m n X i z hz
    obtain ⟨c₀, hc₀⟩ := hcov y z hy hNz
    have hyU : y ∈ ⋃ c ∈ T, c.e.source := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨c₀, hc₀⟩
    obtain ⟨c, hcT, hyc⟩ := Set.mem_iUnion₂.1 hyU
    have h0 : Ψ (segre z) 0 ≠ 0 := by simp [hzv]
    by_cases hreg : IsRegAt i Ψ c y
    · exact absurd ⟨y, hy, GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N a hN c y z hyc hy hNz h0 hreg⟩ hno
    · refine Or.inr (Set.mem_iUnion₂.2 ⟨c, hcT, y, ⟨hyc, ⟨z, hy, h0⟩, hreg⟩, ?_⟩)
      have hl : Over i y (liftOf i y) := by
        have hex : ∃ z, Over i y z := ⟨z, hy⟩
        simp only [liftOf, dif_pos hex]
        exact hex.choose_spec
      have ho : SameOrbit (liftOf i y) z := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i y y _ _ hl hy).1 rfl
      rw [projCoord, ratios_eq_of_sameOrbit Ψ ho h0, ratios_of_proj Ψ hzv]

theorem exists_form_chart {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧ j ∉ ptIdeal (i (genericPoint X)) ∧
      ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 →
        ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.T.arithmetic_variety_generically_etale_coordinates X (i ≫ mpStr ℤ m n) D hX
  obtain ⟨j, a, hj, hjP, hjU⟩ := GlobalTheory.T.exists_form_nonvanishing_on_chart m n X i U hg
  refine ⟨j, a, hj, hjP, fun y z hyz hz => ?_⟩
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale hU x hx (hjU y z hyz hz)
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq

namespace GlobalTheory.CompanionTheory.MixZ


open ArchEq in
theorem archIntEq_of_integrable : ArchIntegrableOn → ArchIntEq := by
  intro hI m n Nh M B A hB hA X _ i _ D hX sB sA r hr f g hfg hrat
  classical
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  have hPp : (ptIdeal (i (genericPoint X))).IsPrime := hP.2.1.1
  have hex : ∃ Ψ : LinProj n D, IsGoodProj (ptIdeal (i (genericPoint X))) Ψ :=
    ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists _ _ _ D hP
  haveI hsc : SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := GlobalTheory.T.complex_points_second_countable m n X i D hX
  unfold ptsIntegral
  rw [dif_pos hex]
  set Ψ : LinProj n D := hex.choose with hΨdef
  have hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ := hex.choose_spec
  obtain ⟨j, aj, hj, hjP, hjc⟩ := exists_form_chart i hX
  have hfg' := hfg
  obtain ⟨α, β, hα, hβ, hfP, hgP, -⟩ := hfg'
  set N : Pol n := j * f * g with hNdef
  have hNh : IsMultiHomog N (aj + α + β) := homog_mul (homog_mul hj hα) hβ
  have hNP : N ∉ ptIdeal (i (genericPoint X)) := fun h => by
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hjP h
      · exact hfP h
    · exact hgP h
  have hNe : ∀ z : (Σ k, Bk n k) → ℂ, eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      eval z (map (Int.castRingHom ℂ) j) ≠ 0 ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0 := fun z h => by
    simp only [hNdef, map_mul, mul_ne_zero_iff] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := fun y z h h' => hjc y z h (hNe z h').1

  have hL : (Nh.restr i).archInt (M.restr i) D hr =
      ((Nh.restr i).φ σ₀).chernInt D (offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr))
        (GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r) :=
    finsum_eq_single _ σ₀ fun σ hσ => absurd (Subsingleton.elim σ σ₀) hσ
  rw [hL]
  set S₀ := offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) with hS₀
  set F := GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r with hF
  set μ : ℤˣ → Measure (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := fun ε => ((Nh.restr i).φ σ₀).chernPart D ε with hμ
  set G := pieceSet i Ψ N with hG
  have hGo : IsOpen G := isOpen_pieceSet i Ψ N
  have hGS : G ⊆ S₀ := by
    rintro y ⟨e, Γ, hp, hy⟩
    have hv := hp.2.2 (e y) (e.map_source hy)
    rw [e.left_inv hy] at hv
    exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat y _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).1
  have hnull : ∀ ε, μ ε Gᶜ = 0 := fun ε => by
    refine GlobalTheory.T.chern_part_null_set_zero _ ε _ hGo.measurableSet.compl fun c => ?_
    have hsub : c.e.target ∩ c.e.symm ⁻¹' Gᶜ ⊆
        (c.e.target ∩ c.e.symm ⁻¹' {y | (∃ z, Over i y z ∧ Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0) ∨ ¬ IsRegAt i Ψ c y}) ∪
        (c.e.target ∩ c.e.symm ⁻¹' {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) N) = 0}) := by
      rintro v ⟨hv, hvG⟩
      obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i (c.e.symm v)
      by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
      · exact Or.inr ⟨hv, z, hz, hNz⟩
      · refine Or.inl ⟨hv, ?_⟩
        by_cases h0 : Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0
        · exact Or.inl ⟨z, hz, h0⟩
        · exact Or.inr fun hreg => hvG (GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N _ hNh c _ z (c.e.map_target hv) hz hNz h0 hreg)
    exact measure_mono_null hsub (measure_union_null (GlobalTheory.T.bad_projection_locus_null m n X i D hX Ψ hΨ c)
      ((GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D N _ hNh hNP).2 c))

  let J := {p : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) ×
    ((Fin D → ℂ) → (Σ k, Bk n k) → ℂ) // IsPiece i Ψ N p.1 p.2}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p : J => p.1.1.source)
    (fun p => p.1.1.open_source)
  haveI : Countable T := hTc.to_subtype
  let e : T → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) := fun l => l.1.1.1
  let Γ : T → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ := fun l => l.1.1.2
  have hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l) := fun l => l.1.2
  let ρ : T → (Fin D → ℂ) → ℝ := fun l => maDensity (fun _ y' => Real.log (B.h (Γ l y')))
  have hd := fun l => GlobalTheory.T.local_chart_sheet_decomposition m n Nh B hB sB X i D Ψ N (e l) (Γ l) (hpc l)
  have hcovG : G ⊆ ⋃ l, (e l).source := by
    rintro y ⟨e', Γ', hp, hy⟩
    have hmem : y ∈ ⋃ p : J, p.1.1.source := Set.mem_iUnion.2 ⟨⟨(e', Γ'), hp⟩, hy⟩
    rw [← hTU] at hmem
    obtain ⟨p, hp, hy⟩ := Set.mem_iUnion₂.1 hmem
    exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hy⟩
  have hIS := hI m n Nh M X i D hX r hr σ₀
  have hIG : ∀ ε, IntegrableOn F G (μ ε) := fun ε => by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact hIS.1.mono_set hGS
    · exact hIS.2.mono_set hGS
  obtain ⟨S, hSm, hSs, hSd, hSU, hSI⟩ := GlobalTheory.T.density_chart_integral_formula μ e ρ (fun l => (hd l).1) (fun l ε => (hd l).2 ε) G
    hGo.measurableSet hcovG F hIG
  have hae : ∀ ε, S₀ =ᵐ[μ ε] G := fun ε => by
    refine (ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy.2) (hnull ε), ?_⟩)
    rw [Set.diff_eq_empty.2 hGS, measure_empty]
  have hchern : ((Nh.restr i).φ σ₀).chernInt D S₀ F = ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) := by
    rw [GlobalTheory.Weight.chernInt, setIntegral_congr_set (hae 1), setIntegral_congr_set (hae (-1))]
  rw [hchern, hSI, ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt]
  refine integral_congr_ae ?_
  filter_upwards [ae_cover i hP Ψ hΨ N _ hNh hNP hcov, GlobalTheory.T.sheet_density_log_norm_formula m n _ D Ψ B A f g hP hΨ sB hfg] with v h1 h2
  have h3 : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ ⋃ l, S l := fun z hz hzv => by
    rw [hSU]
    exact h1 z hz hzv
  have h4 := GlobalTheory.T.sheet_integral_projection_formula m n X i D Ψ N hP hΨ e Γ S hpc hSs hSd v h3
    (fun w => sheetDensity (ptIdeal (i (genericPoint X))) Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w)
    (fun l => F ((e l).symm v) * ρ l v) (fun l hl => by
      obtain ⟨y, hyS, rfl⟩ := hl
      have hvt := (e l).map_source (hSs l hyS)
      have hv := (hpc l).2.2 _ hvt
      have hs : IsSheet (ptIdeal (i (genericPoint X))) Ψ (e l y) (ReciprocityTheory.ChartRestriction.G.Geo.segre (Γ l (e l y))) (Γ l) := by
        refine ⟨rfl, ?_⟩
        filter_upwards [(e l).open_target.mem_nhds hvt] with v' hv'
        have hv2 := (hpc l).2.2 v' hv'
        exact ⟨(hpc l).2.1.differentiableAt ((e l).open_target.mem_nhds hv'), hv2.2.1, hv2.2.2.1⟩
      rw [h2 _ _ hs]
      congr 1
      exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat _ _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).2.symm)
  exact h4.symm

end GlobalTheory.CompanionTheory.MixZ
