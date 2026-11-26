module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

section GenInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem allWt_eq_zero_of_generic (h : GenFrEx Xo c) {e : Ix Dw → ℤ} {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) (h0 : ∀ Z, evC h Z g = 0) : g = 0 := by
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨hL, -, -, hA'⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    have hA := hA' h
    have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
      intro L _ _ w
      obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
      obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
      have h1 : evR Xo c g C.yg = 0 := by
        rw [GlobalTheory.FlagTan.evR_frBor hg C.bor]
        have := h0 C.Z
        unfold evC at this
        rw [this, mul_zero]
      have h2 : χ (g q y₀) = 0 := by
        rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
        exact Subtype.ext h1
      have h3 : evR Xo c g z = 0 := by
        rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply, h2, map_zero]
      rw [GlobalTheory.FlagTan.evR_frBor hg hb, h3, mul_zero]
    funext p y
    have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
    show g p y = 0
    refine IsNilpotent.eq_zero ?_
    rw [nilpotent_iff_mem_prime]
    intro P hP
    let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
    obtain ⟨w, hw⟩ := hL.bc _ _ φ y
    have h4 := hfield _ w
    rw [GlobalTheory.FlagTan.evR_eq hg.1 hw] at h4
    exact Ideal.algebraMap_residueField_eq_zero.1 h4

theorem mem_allWt_of_secZ {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) :
    f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem mem_secZ_of_allWt {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a)) :
    f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem exZ_add (a b : WZ E) :
    GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (a + b) = GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a + GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw b := by
  funext i
  cases i <;> simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]

theorem secZ_eq_zero_of_generic (h : GenFrEx Xo c) {a : WZ E} {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (h0 : ∀ Z, evC h Z f = 0) : f = 0 :=
  allWt_eq_zero_of_generic h (mem_allWt_of_secZ hf) h0

theorem secZ_mul {a b : WZ E} {f g : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c b) : f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (a + b) := by
  apply mem_secZ_of_allWt
  rw [exZ_add]
  exact GlobalTheory.AllWt.mul_mem_secZ (mem_allWt_of_secZ hf) (mem_allWt_of_secZ hg)

theorem one_mem_secZ_zero : (1 : Rul Xo c) ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) :=
  ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]⟩

theorem evC_mul_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f * g) = evC h Z f * evC h Z g := by
  unfold evC evR evalAt
  rw [dite_eq_left (hT Z), dite_eq_left (hT Z), dite_eq_left (hT Z)]
  exact map_mul _ _ _

theorem evC_one_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) :
    evC h Z (1 : Rul Xo c) = 1 := by
  unfold evC evR evalAt
  rw [dite_eq_left (hT Z)]
  exact map_one _

end GenInj

theorem sections_generic_indicators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ a, ∀ f ∈ secZ Xo c a, (∀ Z, evC h Z f = 0) → f = 0) ∧ (∀ a Z, ∀ f ∈ cuspOn U h a Z, evC h Z f = 0 → f = 0) ∧ (∀ a b, ∀ f ∈ secZ Xo c a, ∀ g ∈ secZ Xo c b, f * g ∈ secZ Xo c (a + b)) ∧ (∀ Z, e Z * e Z = e Z) ∧ (∀ Z Z', Z ≠ Z' → e Z * e Z' = 0) ∧ ∑ᶠ Z, e Z = 1 := by
  intro E _ _ _ H Dw l Xo c r U h e hC
  have hT := hC.genT
  have hz : ∀ Z, e Z ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := fun Z => by
    have h1 := hC.e_sec Z
    rw [← GlobalTheory.CompanionTheory.Ar.Rec.secZ_nat] at h1
    have h2 : (fun x => ((((0 : (E →+* ℂ) × ℕ → ℕ)) x : ℕ) : ℤ)) = (0 : WZ E) := by
      funext x
      simp
    rwa [h2] at h1
  have hmul : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := by
    intro f g hf hg
    have := secZ_mul hf hg
    rwa [add_zero] at this
  have heq : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → (∀ Z, evC h Z f = evC h Z g) → f = g := by
    intro f g hf hg hv
    refine sub_eq_zero.1 (secZ_eq_zero_of_generic h (Submodule.sub_mem _ hf hg) fun Z => ?_)
    rw [← evL_apply, map_sub, evL_apply, evL_apply, hv Z, sub_self]
  have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  classical
  refine ⟨fun a f hf h0 => secZ_eq_zero_of_generic h hf h0, fun a Z f hf h0 => ?_,
    fun a b f hf g hg => secZ_mul hf hg, fun Z => ?_, fun Z Z' hne => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    refine secZ_eq_zero_of_generic h (Submodule.mem_inf.1 h1).1 fun Z' => ?_
    by_cases hZ : Z' = Z
    · rw [hZ]
      exact h0
    · have h3 := Submodule.mem_iInf _ |>.1 h2 Z'
      have h4 := Submodule.mem_iInf _ |>.1 h3 hZ
      exact h4
  · refine heq (hmul (hz Z) (hz Z)) (hz Z) fun Z' => ?_
    rw [evC_mul_of_test hT]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [(hC.e_val Z').1, one_mul]
    · rw [(hC.e_val Z).2 Z' hZ, zero_mul]
  · refine heq (hmul (hz Z) (hz Z')) (Submodule.zero_mem _) fun Y => ?_
    have hzero : evC h Y (0 : Rul Xo c) = 0 := by
      rw [← evL_apply, map_zero]
    rw [evC_mul_of_test hT, hzero]
    by_cases hY : Y = Z
    · subst hY
      rw [(hC.e_val Z').2 Y hne, mul_zero]
    · rw [(hC.e_val Z).2 Y hY, zero_mul]
  · rw [finsum_eq_sum_of_fintype]
    refine heq (Submodule.sum_mem _ fun Z _ => hz Z) one_mem_secZ_zero fun Y => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [evC_one_of_test hT, ← evL_apply, map_sum, Finset.sum_eq_single Y]
    · rw [evL_apply]
      exact (hC.e_val Y).1
    · intro Z _ hZ
      rw [evL_apply]
      exact (hC.e_val Z).2 Y (Ne.symm hZ)
    · intro hY
      exact absurd (Finset.mem_univ Y) hY

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.CompanionTheory.Ar.AVExp

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem compactSpace_points (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace _ (PointsCompact.pointTopology A) := by
  have h1 := @valAt'_rules
  have h2 := @existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov
      fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

theorem surjective_mulA (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (r : ℕ) (hr : 1 ≤ r) :
    Surjective (Out.mulA A r).left := by
  obtain ⟨hfin, hflat⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation ((Out.mulA A r).left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (Out.mulA A r).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  have hcl : IsClosed (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isOpenMap.isOpen_range
  have hne : (Set.range (Out.mulA A r).left).Nonempty := Set.range_nonempty _
  exact ⟨Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)⟩

theorem exists_div (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ A) (r : ℕ) (hr : 1 ≤ r) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = a₀ := by
  obtain ⟨hfin, -⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have hsurj := surjective_mulA A hA r hr
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (Out.mulA A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ (Out.mulA A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ A.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (Out.mulA A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = b ≫ Out.mulA A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

theorem exists_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  intro A _ L g hA hL hdim
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := hA.comm
  have := htop A
  have := compactSpace_points A L hL
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hdim 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hex0 : (hφ.exp 0).toMul = 1 := by rw [map_zero]; rfl
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x =>
    exists_div A hA x.toMul n (Nat.one_le_iff_ne_zero.mpr hn)

  obtain ⟨W', large₂, hW', h0', hL', hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (large₂ : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ large₂ W' ∧
      Set.MapsTo large₂ W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (large₂ v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩, U, t, hU, ?_, ?_, hφ.hasFDerivAt_chart_exp⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (large₂ (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL' hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add (f := _), add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    simp
  · show ⊤ ≤ (hφ.exp 0).toMul.left ⁻¹ᵁ U
    rwa [hex0]
  · show ∀ D : Γ(A.left, U) →+ ℂ, _ → (∀ f f', D (f * f') =
      valAt' (hφ.exp 0).toMul.left U f * D f' + valAt' (hφ.exp 0).toMul.left U f' * D f) → _
    rwa [hex0]

end GlobalTheory.CompanionTheory.Ar.AVExp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exp_chart_coordinates : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | exact GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | (intros; apply GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif <;> assumption)
end
end
