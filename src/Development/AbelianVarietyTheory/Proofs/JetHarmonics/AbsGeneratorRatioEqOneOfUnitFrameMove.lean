module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open GlobalTheory.UnitFrameGen MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.LevelCusp

theorem cabs_gen_eq_one_of_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hmv hb hx hx'
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨P, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨P', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  clear hA hA' hP
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : (U.un k' x').x = (U.un k x).x ≫ ρ := hb.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  generalize ik k = i at *
  generalize ik k' = i' at *
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_sabMap F ν hp hp'
    ((congrArg (· ≫ ρ) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F.ex i P z).left ≫ ν.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex i P z).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = ((U.un k x).x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F.ex i P 0).left = ((U.un k x).x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F.ex i P z).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0, hxρ]
        exact o4 _ _ _ _ hz0 hz)
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x y'.x
      (U.un k' x').s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2)⁻¹ *
        (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.LevelCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMoveStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_generatorRatio_eq_one_of_unitFrame_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) = 1 := by
  first | exact @GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move | exact GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move | (intros; apply GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionField
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem evI_eq_thExpr_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ) (xx : Fin n → Dw.La) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x)), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) → ∀ f, IsThRule Xo c nab xx Pp f → algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y F _ _ φ hφ yF hm a n xx Pp hP Fs hFs f hf
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hyT := y.2.1
  unfold evI evR evalAt
  rw [dite_eq_left hyT]
  have hm0 := hyT.choose_spec.choose_spec.choose_spec
  have hv0 := hf hyT.choose hyT.choose_spec.choose_spec.choose
  have hvF : ThValAt Xo c nab yF xx Pp (thExpr Xo c nab yF Pp Fs) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id c.F F, yF, Fs, ?_, GlobalTheory.FramedBaseChange.refl yF, hFs, rfl⟩
  · have key := GlobalTheory.ThetaField.thetaValue_natural_field E H Dw l Xo c nab hnab _ F (φ.comp _) _ yF
      (GlobalTheory.FramedBaseChange.trans _ φ hm0 hm) a n xx Pp hP _ _ hv0 hvF
    refine Eq.trans ?_ key
    exact (congrArg (fun g : T.Fr →+* F => g _) hφ).symm
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id

end GlobalTheory.PtTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ) (xx : Fin n → Dw.La) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x)), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) → ∀ f, IsThRule Xo c nab xx Pp f → algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
  first | exact @GlobalTheory.PtTie.evI_eq_thExpr_ext | exact GlobalTheory.PtTie.evI_eq_thExpr_ext | (intros; apply GlobalTheory.PtTie.evI_eq_thExpr_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OneColumnTranslateSectionRootOfUnityMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.OneColTranslate

theorem pow_eq_one_of_act {S : Scheme.{0}} {O : Type} [CommRing O] {G T : Over S} [GrpObj G]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (b : T ⟶ G) (α β : O) (N : ℕ) (h : α * β = (N : O))
    (hb : b ≫ a.act β = 1) : b ^ N = 1 := by
  have h0 : a.act 0 = 1 := by
    have h1 := a.add 0 0
    rw [add_zero] at h1
    exact (mul_eq_left.mp h1.symm)
  have hn : ∀ n : ℕ, b ≫ a.act (n : O) = b ^ n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]
  haveI := a.hom α
  rw [← hn, ← h, mul_comm, a.mul, ← Category.assoc, hb, MonObj.one_comp]

theorem oneColumn_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∃ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ ∧ PullAl P.D F P.oD α 1 N θ₁ θα₁ ∧ ∀ (p : QkPt P.D.toPre F (1 * N)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ P.A.A) (r₀ r : Fam P.D.toPre F (1 * N)) (σ : P.U.toUnifPre.SecGF F N), w.IsGen → FinOrd P.D F (1 * N) p w ζ → P.ToA F (1 * N) p x → x ≫ P.oA.act (star α) = 1 → PhiRel P.D.toPre F (1 * N) p w θα₁ r₀ → Fam.IsSmul P.D.toPre F ζ r₀ r → P.U.toUnifPre.ExpandsG F N σ (PowGerm.famCast (Dp := P.D.toPre) (F := F) (one_mul N) r) → ∃ (u : F) (b : ptO Xo yF.x ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo yF.x))) (σ₀ : P.U.toUnifPre.SecGF F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ b ≫ Xo.univ.t.act.act (star α) = 1 ∧ IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N yF.s b hh ∧ SecTieF I P F yF.x N σ₀ hh ∧ ∀ jj, σ.f jj = resTop ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (R := T.V) (G := I.G.G) F) (fun _ => (N : ℤ))).U jj) (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ₀.f jj := by
  intro E _ _ _ H Dw l Xo c T io y I P ϖ hϖ F _ _ _ φ hφ yF hyF α N hN hα
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hN1 : 1 ≤ N := hN.pos
  have hx : yF.x = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := by
    have h1 := hyF.1
    rw [hφ] at h1
    exact h1
  have hbij := GlobalTheory.expandsG_bijective_of_dvr hL hLL.2.1 hLL.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 T.V P.D P.A I.G.G P.U F
  have hsec := GlobalTheory.T.powPullbackSec_modelUniversal_bijective E H Dw l Xo c T io y I P F yF.x hx
  obtain ⟨σs, hσs, -⟩ := (hsec 1).2.1 yF.s
  obtain ⟨θ₁, hθ₁, -⟩ := (hbij 1 le_rfl).1 σs
  obtain ⟨π, -, hπ⟩ := GlobalTheory.PullLin.exists_pull_linearMap hL T.V P.D F (𝓞 E) P.oD H.w0 P.w0 α N 1 hN1 le_rfl hα
  have hpull : PullAl P.D F P.oD α 1 N θ₁ (π θ₁) := (hπ _ _).2 rfl
  refine ⟨θ₁, π θ₁, GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y I P ϖ hϖ F φ hφ yF hyF σs θ₁ hσs hθ₁, hpull, ?_⟩
  intro p w ζ x r₀ r σ hw hfin hto hxk hphi hsm hσ
  obtain ⟨e, he, hea⟩ := GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal E H Dw l Xo c T io y I P F yF.x hx
  have hb : e x ≫ Xo.univ.t.act.act (star α) = 1 := by rw [← hea, hxk, map_one]
  have hbN : e x ^ N = 1 := pow_eq_one_of_act _ _ α (star α) N hα hb
  obtain ⟨hh, hhh⟩ := GlobalTheory.T.exists_translated_normalisedPullback_section E H Dw l Xo c F yF.x α N hN hα yF.s (e x) hbN
  obtain ⟨h₁, hnp, hsym⟩ := id hhh
  obtain ⟨σ₁, hσ₁, -⟩ := (hsec N).2.1 h₁
  obtain ⟨σ₀, hσ₀, -⟩ := (hsec N).2.1 hh
  have hex₁ := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y I P F yF.x hx α N 1 N (_root_.one_mul N) hα hN1 (Or.inl rfl)
    σs yF.s θ₁ σ₁ h₁ (π θ₁) hσs hθ₁ hnp hσ₁ hpull
  have key : ∀ (q : ℕ) (eq : q = N) (θ : Fam P.D.toPre F q) (p : QkPt P.D.toPre F q)
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q)))
      (r₀ r : Fam P.D.toPre F q),
      P.U.toUnifPre.ExpandsG F N σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq θ) →
      w.IsGen → FinOrd P.D F q p w ζ → P.ToA F q p x → PhiRel P.D.toPre F q p w θ r₀ →
      Fam.IsSmul P.D.toPre F ζ r₀ r →
      ∃ (u : F) (t' : Fam P.D.toPre F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧
        Fam.IsSmul P.D.toPre F u (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq r) t' ∧
        P.U.toUnifPre.ExpandsG F N σ₀ t' := by
    intro q eq
    obtain rfl : N = q := eq.symm
    intro θ p w r₀ r hθ hw hfin hto hphi hsm
    exact GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y I P F yF.x hx N hN1 σ₁ σ₀ h₁ hh θ r₀ r x (e x) p w ζ hσ₁ hσ₀ hθ hsym
      ((he _ _).2 rfl) hto hw hfin hphi hsm
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, hex₀⟩ := key (1 * N) (one_mul N) (π θ₁) p w r₀ r hex₁ hw hfin hto hphi hsm
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hum
    exact zero_ne_one hum
  rw [isSmul_iff] at hut
  let σ' : P.U.toUnifPre.SecGF F N := SecOps.secScale
    (Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u⁻¹) σ₀
  have hex' := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V P.D P.A I.G.G P.U F N 1 (fun _ => u⁻¹) (fun _ => σ₀)
    (fun _ => t') σ' (fun _ => hex₀) (fun jj => by rw [Fin.sum_univ_one]; rfl)
  rw [Fin.sum_univ_one, hut, smul_smul, inv_mul_cancel₀ hu, one_smul] at hex'
  have hσσ : σ = σ' := ((hbij N hN1).2 _).unique hσ hex'
  refine ⟨u⁻¹, e x, hh, σ₀, ⟨m, hm, by rw [inv_pow, hum, inv_one]⟩, hb, hhh, hσ₀, fun jj => ?_⟩
  rw [hσσ]
  rfl

end GlobalTheory.OneColTranslate
end
