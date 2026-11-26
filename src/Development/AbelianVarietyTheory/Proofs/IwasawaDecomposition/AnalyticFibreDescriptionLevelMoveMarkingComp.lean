module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Dict.Lift

namespace GlobalTheory.Dict.FibreMove

theorem exists_frame_push {X Y : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : LB X}
    {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen)
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L'.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L'.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L'.U j ⊓ L'.U j') →
      fr j z = valAt' (e z) (L'.U j ⊓ L'.U j') (L'.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j}) ∧
      (∀ j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j → fr' j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j') →
        fr' j z = valAt' (e z ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * fr' j' z) ∧
      ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr' a z = wv w (e z) a j * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L' hL'
  have key : ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j →
      wv w (e z) a (ch z) * fr (ch z) z = wv w (e z) a j * fr j z := by
    intro a j z ha hj
    have h0 := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have h2 := valAt'_unit_ne_zero (e z) h0 (L'.g (ch z) j)
    rw [wv_change hw ha ha (hch z) hj, val_g_self _ L hL a ha, fr_g (ch z) j z h0]
    field_simp
  refine ⟨fun a z => wv w (e z) a (ch z) * fr (ch z) z, fun a z₀ hz₀ => ?_, fun a z ha => ?_,
    fun a a' z h => ?_, key⟩
  · have hN := (hol ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) (w.s (fun _ => a, ch z₀)).val)
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, mem_both hz₀ (hch z₀)⟩
    have hsub : ∀ z, ⊤ ≤ e z ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) →
        ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a ∧ ⊤ ≤ e z ⁻¹ᵁ L'.U (ch z₀) := fun z hz =>
      ⟨(mem_wchart (e z) L _ _).1 ((top_le_preimage_inf _ _ _).1 hz).1 ⟨⟩, ((top_le_preimage_inf _ _ _).1 hz).2⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => (hsub z hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => wv w (e z) a (ch z₀)) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key a (ch z₀) z (hsub z hz.2).1 (hsub z hz.2).2
  · exact mul_ne_zero (wv_ne w ha (hch z)) (fr_ne _ z (hch z))
  · obtain ⟨ha, ha'⟩ := (top_le_preimage_inf _ _ _).1 h
    simp only []
    rw [wv_change hw ha ha' (hch z) (hch z), val_g_self _ L' hL' _ (hch z)]
    ring

theorem anFib_levR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c ℂ} (h : levR (gM, gA) y y')
    (A : AnFib X bas idx e x L y) :
    ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧
      ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  obtain ⟨ρ, ν, -, hν, hmv⟩ := h
  obtain ⟨hb, hu, pm, w, hf, hs, hcub, hc⟩ := MoveCalc.frMove_iff_carry.1 hmv
  obtain ⟨hw, hrig, -⟩ := hcub
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_frame_push Xo.univ.t.PP.isLB Xo.univ.t.PP.isLB hw
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hadd : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => by
    simp only [ex, A.ex_add, map_mul]
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := hadd
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := (funext hex).symm ▸ PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        have h1 := FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
        rw [hu]
        exact (funext hex).symm ▸ h1
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun a ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch 0
        have h1 := key a j 0 ha hj
        have h2 := A.fr_0 j hj
        have h3 := val_rig ν.cm Xo.univ.t.PP Xo.univ.t.PP w hrig y.x a j (hex0 ▸ ha) (hex0 ▸ hj)
        have h4 : y.x ≫ ν.cm.e = y'.x := by rw [ν.base]; exact hb.symm
        erw [h4, ← h2, ← hex0] at h3
        exact h1.trans h3.symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv a z ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch z
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h1 := key a j z ha hj
        have h2 := key a j (z + pv X idx x v) (hz ▸ ha) (hz ▸ hj)
        have h3 := A.fr_per v hv j z hj
        simp only [hz] at h2
        rw [h1, h2, h3]
        ring }
  refine ⟨A', fun θ hθ a z pt' hp1 hp2 ha => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have ha' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U a := hex z ▸ ha
    let pt : Sp ℂ ⟶ Gx y.x := pullback.lift (𝟙 _) (A.ex z).left (by
      rw [Category.id_comp]; exact (Over.w (A.ex z)).symm)
    have e₁ : pt ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (A.ex z).left := pullback.lift_snd _ _ _
    have e₂ : pt ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ := pullback.lift_fst _ _ _
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact hp2.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · refine (hp1.trans (hex z)).trans ?_
        rw [← e₁]
        exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm
    have h1 := hθ j z pt e₁ e₂ hj
    have h2 := MoveValues.val_carry hs hc pt (i := a) (j := j)
      (by rw [e₁]; exact (MoveValues.mem_iff ((A.ex z).left ≫ ν.φ) _).2 ha')
      (by rw [e₁]; exact (MoveValues.mem_iff _ _).2 hj)
    refine h2.trans ?_
    rw [e₁]
    refine (congrArg (wv w (A.ex z).left a j * ·) h1).trans ?_
    change _ = θ z * fr a z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key a j z ha' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x ((l.M : E)⁻¹ • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hν.2.1, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.Dict.FibreMove

theorem GlobalTheory.Dict.FibreMove.anFib_levR_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h A => GlobalTheory.Dict.FibreMove.anFib_levR h A
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingCompStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFibre_description_levelMove_marking_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  first | exact @GlobalTheory.Dict.FibreMove.anFib_levR_id | exact GlobalTheory.Dict.FibreMove.anFib_levR_id | (intros; apply GlobalTheory.Dict.FibreMove.anFib_levR_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagLiftGenericPointSpecializesResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagLiftGenericPointSpecializesResidue
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_valuation_point {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (y : M.Z) :
    ∃ (V : ValuationSubring Ω) (v : Sp V ⟶ M.Z), spMap (algebraMap V Ω) ≫ v = M.pt ∧
      v (IsLocalRing.closedPoint V) = y := by
  haveI : IsLocalRing (M.O y).toSubring := inferInstanceAs (IsLocalRing (M.O y))
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk (M.O y).toSubring).exists_le_valuationSubring
  let ψ : M.Z.presheaf.stalk y →+* V :=
    (M.stalkHom y).codRestrict V (fun a => hle (M.stalkEquiv y a).2)
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    have h1 : IsUnit (Subring.inclusion hle (M.stalkEquiv y a)) := ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv y)).1 (hloc.map_nonunit _ h1)⟩
  refine ⟨V, spMap ψ ≫ M.Z.fromSpecStalk y, ?_, ?_⟩
  · have hs := M.pt_specializes (IsLocalRing.closedPoint Ω) y
    have hc : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω) =
        M.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
      ext a
      rfl
    calc spMap (algebraMap V Ω) ≫ spMap ψ ≫ M.Z.fromSpecStalk y
        = Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V Ω)) ≫ M.Z.fromSpecStalk y := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) ≫
            Spec.map (M.Z.presheaf.stalkSpecializes hs) ≫ M.Z.fromSpecStalk y := by
          rw [hc, Spec.map_comp, Category.assoc]
      _ = M.pt := by
          rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have ec : spMap ψ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint ψ
    show M.Z.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint V)) = y
    rw [ec]
    exact Scheme.fromSpecStalk_closedPoint

theorem exists_valuation_point_var {F : Type} [Field F] (Y : Var F) (y : Y.X) :
    ∃ (V : ValuationSubring Y.Fn) (v : Sp V ⟶ Y.X), spMap (algebraMap V Y.Fn) ≫ v = (ratOf Y).pt ∧
      v (IsLocalRing.closedPoint V) = y :=
  exists_valuation_point (ratOf Y) y

theorem lift_specializes_genericPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hco y hy
  obtain ⟨V, v, hvg, hvc⟩ := exists_valuation_point_var Y₁ y
  have hs : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
  haveI : IsProper (f₂ ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f₂ := UniversallyClosed.of_comp_of_isSeparated f₂ X.str
  have hE : ValuativeCriterion.Existence f₂ :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f₂) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f₂).1
  have hsq : q ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    exact hq.trans ((congrArg (· ≫ f₁) hvg.symm).trans (Category.assoc _ _ _))
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := Y₁.Fn, i₁ := q, i₂ := v ≫ f₁, commSq := ⟨hsq⟩ }
  have hl₁ : spMap (algebraMap V Y₁.Fn) ≫ l.l = q := l.fac_left
  have hl₂ : l.l ≫ f₂ = v ≫ f₁ := l.fac_right
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v l.l hl₂.symm
    (by
      have e : spMap (algebraMap V Y₁.Fn) ≫ v ≫ f₁ = (ratOf Y₁).pt ≫ f₁ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hvg)
      have key : ∀ (x x' : Sp Y₁.Fn ⟶ X.X) (p p' : Sp Y₁.Fn ⟶ Y₁.X) (r r' : Sp Y₁.Fn ⟶ Y₂.X), x = x' → p = p' →
          r = r' → CoBear Eb S₁ φ₁ S₂ φ₂ x p r → CoBear Eb S₁ φ₁ S₂ φ₂ x' p' r' := by
        rintro _ _ _ _ _ _ rfl rfl rfl h
        exact h
      exact key _ _ _ _ _ _ e.symm hvg.symm hl₁.symm hco)
  have ec : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
      IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
  have hp' := hy (IsLocalRing.ResidueField V) (spMap (IsLocalRing.residue V) ≫ v)
    (spMap (IsLocalRing.residue V) ≫ l.l)
    (by
      show v (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = y
      rw [ec]
      exact hvc)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hl₂.symm).trans
      (Category.assoc _ _ _).symm))
    (by convert hinc using 1; exact Category.assoc _ _ _)
  have e2 : l.l (IsLocalRing.closedPoint V) = genericPoint Y₂.X := by
    change l.l (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint _)) = _ at hp'
    rwa [ec] at hp'
  have e1 : q (IsLocalRing.closedPoint Y₁.Fn) =
      l.l (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn)) := by
    have := congrArg (fun g : Sp Y₁.Fn ⟶ Y₂.X => g (IsLocalRing.closedPoint Y₁.Fn)) hl₁
    exact this.symm
  have h2 := (IsLocalRing.specializes_closedPoint
    (spMap (algebraMap V Y₁.Fn) (IsLocalRing.closedPoint Y₁.Fn))).map l.l.continuous
  convert h2 using 1
  exact e2.symm

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagLiftGenericPointSpecializesResidueStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagLift_genericPoint_specializes_residue : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  first | exact @GlobalTheory.FlagBundle.lift_specializes_genericPoint | exact GlobalTheory.FlagBundle.lift_specializes_genericPoint | (intros; apply GlobalTheory.FlagBundle.lift_specializes_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundlePointAtGenericLiftImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundlePointAtGenericLiftImage
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagBundle

theorem exists_spMap_fromSpecResidueField {Z : Scheme.{0}} (y : Z) {K : Type} [Field K] (p : Sp K ⟶ Z)
    (hp : p (IsLocalRing.closedPoint K) = y) :
    ∃ σ : Z.residueField y →+* K, spMap σ ≫ Z.fromSpecResidueField y = p := by
  subst hp
  exact ⟨(Z.descResidueField (Scheme.stalkClosedPointTo p)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z p⟩

theorem coBear_swap {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
    {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}
    {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ : Sp K ⟶ Y₁.X} {p₂ : Sp K ⟶ Y₂.X}
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) (hx : x = x') : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂ p₁ := by
  subst hx
  obtain ⟨A, hA, g, hg, h₁, h₂⟩ := h
  exact ⟨A, hA, g, hg, h₂, h₁⟩

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.conclusion : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ r hr hrc K _ p p' hp hpp' hc
  set y₁ := r (IsLocalRing.closedPoint Y₂.Fn)
  let c : Sp (Y₁.X.residueField y₁) ⟶ Y₁.X := Y₁.X.fromSpecResidueField y₁
  obtain ⟨τ, hτ⟩ := exists_spMap_fromSpecResidueField y₁ r rfl
  obtain ⟨σ, hσ⟩ := exists_spMap_fromSpecResidueField y₁ p hp
  obtain ⟨A, hA, g, hg, hb₁⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ hR₁ _ c
  obtain ⟨s, ⟨hs, hb₂⟩, -⟩ := hR₂.2.2 _ (c ≫ f₁) A hA g hg
  have hcs : CoBear Eb S₁ φ₁ S₂ φ₂ (c ≫ f₁) c s := ⟨A, hA, g, hg, hb₁, hb₂⟩
  have hτc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ τ _ _ _ hcs
  have hσc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ σ _ _ _ hcs
  have hτ' : spMap τ ≫ c = r := hτ
  have hσ' : spMap σ ≫ c = p := hσ
  rw [hτ'] at hτc
  rw [hσ'] at hσc
  have e₁ : (spMap τ ≫ s) ≫ f₂ = r ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hτ']
  have e₂ : (spMap σ ≫ s) ≫ f₂ = p ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hσ']
  have k₁ : spMap τ ≫ s = (ratOf Y₂).pt :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ r e₁ hr.symm
      (coBear_swap hτc (by rw [Category.assoc, hs])) (coBear_swap hrc hr)
  have k₂ : p' = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ p hpp'.symm e₂
      (coBear_swap hc hpp') (coBear_swap hσc (by rw [Category.assoc, hs]))
  have hgen : s (IsLocalRing.closedPoint _) = genericPoint Y₂.X := by
    have e : (spMap τ ≫ s) (IsLocalRing.closedPoint Y₂.Fn) = s (IsLocalRing.closedPoint _) := by
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
    rw [← e, k₁]
    exact Scheme.fromSpecStalk_closedPoint
  rw [k₂, ← hgen]
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundlePointAtGenericLiftImageStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_point_at_genericLift_image : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  first | exact @GlobalTheory.FlagBundle.conclusion | exact GlobalTheory.FlagBundle.conclusion | (intros; apply GlobalTheory.FlagBundle.conclusion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

theorem GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ)
    (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) : ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧
      CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ Y₁.Fn (ratOf Y₁).pt
  obtain ⟨q, ⟨hq, hqb⟩, -⟩ := h₂.2.2 Y₁.Fn ((ratOf Y₁).pt ≫ f₁) A hA h hh
  have hcq : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q := ⟨A, hA, h, hh, hb, hqb⟩
  obtain ⟨B, hB, g, hg, hgb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ h₂ Y₂.Fn (ratOf Y₂).pt
  obtain ⟨r, ⟨hr, hrb⟩, -⟩ := h₁.2.2 Y₂.Fn ((ratOf Y₂).pt ≫ f₂) B hB g hg
  have hcr : CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt := ⟨B, hr ▸ hB, g, hg, hrb, hgb⟩
  have hsp := GlobalTheory.T.fullFlagLift_genericPoint_specializes_residue F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hcq (r (IsLocalRing.closedPoint _))
    (fun K _ p p' hp hpp hc => GlobalTheory.T.fullFlagBundle_point_at_genericLift_image F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ r hr hcr K p p' hp hpp hc)
  have hs : q ≫ Y₂.str = spMap (algebraMap F Y₁.Fn) := by
    have e1 : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
    have e2 : f₁ ≫ X.str = Y₁.str := h₁.1.inducedModelMorphism_comp_structureMap
    have e3 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ Y₁.str = spMap (algebraMap F Y₁.Fn) := (ratOf Y₁).pt_s
    calc q ≫ Y₂.str = q ≫ (f₂ ≫ X.str) := congrArg (q ≫ ·) e1.symm
    _ = (q ≫ f₂) ≫ X.str := (Category.assoc _ _ _).symm
    _ = ((ratOf Y₁).pt ≫ f₁) ≫ X.str := congrArg (· ≫ X.str) hq
    _ = (ratOf Y₁).pt ≫ (f₁ ≫ X.str) := Category.assoc _ _ _
    _ = (ratOf Y₁).pt ≫ Y₁.str := congrArg (((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ ·) e2
    _ = _ := e3
  obtain ⟨ψ, rfl⟩ := GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint F Y₂ Y₁.Fn q hsp hs
  refine ⟨ψ, ?_, hcq⟩
  have key : ∀ (σ : X.Fn →+* Y₁.Fn) (a : X.Fn), (ratOf X).val (spMap σ ≫ (ratOf X).pt) a = σ a := by
    intro σ a
    have hm : a ∈ (ratOf X).O (genericPoint (ratOf X).Z) :=
      (RatModel.O_genericPoint (ratOf X)).symm ▸ Algebra.mem_top
    have h1 := RatModel.val_spMap_comp σ (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    have h2 := RatModel.valLoc_eq_val (M := ratOf X) (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    exact h1.trans (congrArg σ (h2.trans (RatModel.val_pt (M := ratOf X) a)))
  have H1 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ f₁ = spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₁.1
  have H2 : ((ratOf Y₂).pt : Sp Y₂.Fn ⟶ Y₂.X) ≫ f₂ = spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₂.1
  have e : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) =
      spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := by
    have s1 : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)
        = spMap ψ.toRingHom ≫ (spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)) := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    exact s1.trans ((congrArg (spMap ψ.toRingHom ≫ ·) H2.symm).trans
      ((Category.assoc _ _ _).symm.trans (hq.trans H1)))
  ext a
  have := congrArg (fun y => (ratOf X).val y a) e
  simp only [key] at this
  exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPointStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

namespace ChernSpan

variable {R : Type} [CommRing R]

def blockSum {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin (M + N)) (Fin (M + N)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 b)

def kron {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin (M * N)) (Fin (M * N)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) a b)

abbrev Pair (M : ℕ) : Type := {p : Fin M × Fin M // p.1 < p.2}

abbrev pairCard (M : ℕ) : ℕ := Fintype.card (Pair M)

def pairEquiv (M : ℕ) : Fin (pairCard M) ≃ Pair M := (Fintype.equivFin (Pair M)).symm

def wedgeRaw {M : ℕ} (a : Matrix (Fin M) (Fin M) R) : Matrix (Pair M) (Pair M) R :=
  Matrix.of fun p q => a p.1.1 q.1.1 * a p.1.2 q.1.2 - a p.1.2 q.1.1 * a p.1.1 q.1.2

def wedge2 {M : ℕ} (a : Matrix (Fin M) (Fin M) R) : Matrix (Fin (pairCard M)) (Fin (pairCard M)) R :=
  Matrix.reindex (pairEquiv M).symm (pairEquiv M).symm (wedgeRaw a)

def wedgeLieRaw {M : ℕ} (L : Matrix (Fin M) (Fin M) R) : Matrix (Pair M) (Pair M) R :=
  Matrix.of fun p q =>
    L p.1.1 q.1.1 * (1 : Matrix (Fin M) (Fin M) R) p.1.2 q.1.2 +
      (1 : Matrix (Fin M) (Fin M) R) p.1.1 q.1.1 * L p.1.2 q.1.2 -
      L p.1.2 q.1.1 * (1 : Matrix (Fin M) (Fin M) R) p.1.1 q.1.2 -
      (1 : Matrix (Fin M) (Fin M) R) p.1.2 q.1.1 * L p.1.1 q.1.2

def wedge2Lie {M : ℕ} (L : Matrix (Fin M) (Fin M) R) : Matrix (Fin (pairCard M)) (Fin (pairCard M)) R :=
  Matrix.reindex (pairEquiv M).symm (pairEquiv M).symm (wedgeLieRaw L)

section Laws

variable {M N : ℕ}

theorem blockSum_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).map f = blockSum (a.map f) (b.map f) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem blockSum_one : blockSum (1 : Matrix (Fin M) (Fin M) R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [blockSum, Matrix.fromBlocks_one]

theorem blockSum_mul (a a' : Matrix (Fin M) (Fin M) R) (b b' : Matrix (Fin N) (Fin N) R) :
    blockSum (a * a') (b * b') = blockSum a b * blockSum a' b' := by
  simp [blockSum, Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv]

theorem blockSum_transpose (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    blockSum aᵀ bᵀ = (blockSum a b)ᵀ := by
  simp [blockSum, Matrix.fromBlocks_transpose, Matrix.transpose_submatrix]

theorem kron_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).map f = kron (a.map f) (b.map f) := by
  ext i j
  simp [kron]

theorem kron_one : kron (1 : Matrix (Fin M) (Fin M) R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [kron, Matrix.one_kronecker_one]

theorem kron_mul (a a' : Matrix (Fin M) (Fin M) R) (b b' : Matrix (Fin N) (Fin N) R) :
    kron (a * a') (b * b') = kron a b * kron a' b' := by
  simp [kron, Matrix.mul_kronecker_mul, Matrix.submatrix_mul_equiv]

theorem kron_transpose (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    kron aᵀ bᵀ = (kron a b)ᵀ := by
  ext i j
  simp [kron]

theorem sum_sum_eq_sum_pair (F : Fin M → Fin M → R) :
    ∑ x, ∑ y, F x y = ∑ r : Pair M, (F r.1.1 r.1.2 + F r.1.2 r.1.1) + ∑ x, F x x := by
  have key : ∀ G : Fin M → Fin M → R, ∑ r : Pair M, G r.1.1 r.1.2 = ∑ x, ∑ y, if x < y then G x y else 0 := by
    intro G
    rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin M × Fin M => p.1 < p.2) (fun x => by simp)
      (fun p => G p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
  have key' := key (fun x y => F y x)
  rw [Finset.sum_add_distrib, key, key']
  have h : ∀ x y, F x y = (if x < y then F x y else 0) + (if y < x then F x y else 0) + (if x = y then F x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  calc ∑ x, ∑ y, F x y
      = ∑ x, ∑ y, ((if x < y then F x y else 0) + (if y < x then F x y else 0) + (if x = y then F x y else 0)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h x y
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · congr 1
          rw [Finset.sum_comm]
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp [eq_comm]

theorem wedge2_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R) :
    (wedge2 a).map f = wedge2 (a.map f) := by
  ext p q
  simp [wedge2, wedgeRaw]

theorem wedgeRaw_one : wedgeRaw (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  simp only [wedgeRaw, Matrix.of_apply, Matrix.one_apply, Subtype.mk.injEq, Prod.mk.injEq]
  have h0 : (if j = k then (1 : R) else 0) * (if i = l then 1 else 0) = 0 := by
    by_cases h3 : j = k
    · by_cases h4 : i = l
      · subst h3; subst h4; exact absurd (hij.trans hkl) (lt_irrefl _)
      · simp [h4]
    · simp [h3]
  rw [h0, sub_zero]
  by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2]

theorem wedgeRaw_mul (a b : Matrix (Fin M) (Fin M) R) : wedgeRaw (a * b) = wedgeRaw a * wedgeRaw b := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  rw [Matrix.mul_apply]
  show (a * b) i k * (a * b) j l - (a * b) j k * (a * b) i l = ∑ r : Pair M,
    (a i r.1.1 * a j r.1.2 - a j r.1.1 * a i r.1.2) * (b r.1.1 k * b r.1.2 l - b r.1.2 k * b r.1.1 l)
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have e : ∀ x y, a i x * b x k * (a j y * b y l) - a j x * b x k * (a i y * b y l)
      = (a i x * a j y - a j x * a i y) * (b x k * b y l) := fun x y => by ring
  simp only [e]
  rw [sum_sum_eq_sum_pair]
  have hz : ∑ x, (a i x * a j x - a j x * a i x) * (b x k * b x l) = 0 :=
    Finset.sum_eq_zero fun x _ => by ring
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem wedgeRaw_transpose (a : Matrix (Fin M) (Fin M) R) : wedgeRaw aᵀ = (wedgeRaw a)ᵀ := by
  ext p q
  simp only [wedgeRaw, Matrix.of_apply, Matrix.transpose_apply]
  ring

theorem wedge2_one : wedge2 (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  simp [wedge2, wedgeRaw_one]

theorem wedge2_mul (a b : Matrix (Fin M) (Fin M) R) : wedge2 (a * b) = wedge2 a * wedge2 b := by
  simp [wedge2, wedgeRaw_mul, Matrix.submatrix_mul_equiv]

theorem wedge2_transpose (a : Matrix (Fin M) (Fin M) R) : wedge2 aᵀ = (wedge2 a)ᵀ := by
  simp [wedge2, wedgeRaw_transpose, Matrix.transpose_submatrix]

end Laws

end ChernSpan

namespace PolyRep

variable {ι : Type} {m : ι → ℕ}

open ChernSpan

theorem evEnt_blockSum {M N : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    (Q : Matrix (Fin N) (Fin N) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (blockSum P Q) A = blockSum (evEnt P A) (evEnt Q A) := by
  have h := blockSum_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P Q
  simpa [evEnt] using h

theorem evEnt_kron {M N : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    (Q : Matrix (Fin N) (Fin N) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (kron P Q) A = kron (evEnt P A) (evEnt Q A) := by
  have h := kron_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P Q
  simpa [evEnt] using h

theorem evEnt_wedge2 {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (ChernSpan.wedge2 P) A = ChernSpan.wedge2 (evEnt P A) := by
  have h := wedge2_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P
  simpa [evEnt] using h

def zero (m : ι → ℕ) : PolyRep m where
  M := 0
  ent := 0
  one R _ := by ext i; exact i.elim0
  mul R _ A B := by ext i; exact i.elim0
  transp R _ A := by ext i; exact i.elim0

def triv (m : ι → ℕ) : PolyRep m where
  M := 1
  ent := 1
  one R _ := by ext i j; simp [evEnt, Matrix.one_apply]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.one_apply]
  transp R _ A := by ext i j; simp [evEnt, Matrix.one_apply, eq_comm]

def sum (ρ σ : PolyRep m) : PolyRep m where
  M := ρ.M + σ.M
  ent := blockSum ρ.ent σ.ent
  one R _ := by rw [evEnt_blockSum, ρ.one R, σ.one R, blockSum_one]
  mul R _ A B := by rw [evEnt_blockSum, evEnt_blockSum, evEnt_blockSum, ρ.mul R, σ.mul R, blockSum_mul]
  transp R _ A := by rw [evEnt_blockSum, evEnt_blockSum, ρ.transp R, σ.transp R, blockSum_transpose]

def nsum (ρ : PolyRep m) (k : ℕ) : PolyRep m :=
  Nat.rec (zero m) (fun _ σ => σ.sum ρ) k

def tensor (ρ σ : PolyRep m) : PolyRep m where
  M := ρ.M * σ.M
  ent := kron ρ.ent σ.ent
  one R _ := by rw [evEnt_kron, ρ.one R, σ.one R, kron_one]
  mul R _ A B := by rw [evEnt_kron, evEnt_kron, evEnt_kron, ρ.mul R, σ.mul R, kron_mul]
  transp R _ A := by rw [evEnt_kron, evEnt_kron, ρ.transp R, σ.transp R, kron_transpose]

def wedge2 (ρ : PolyRep m) : PolyRep m where
  M := pairCard ρ.M
  ent := ChernSpan.wedge2 ρ.ent
  one R _ := by rw [evEnt_wedge2, ρ.one R, wedge2_one]
  mul R _ A B := by rw [evEnt_wedge2, evEnt_wedge2, evEnt_wedge2, ρ.mul R, wedge2_mul]
  transp R _ A := by rw [evEnt_wedge2, evEnt_wedge2, ρ.transp R, wedge2_transpose]

def ptr [Fintype ι] (ρ : PolyRep m) (i : ℕ) {S : Type} [CommRing S] (A : Mat m S) : S :=
  ((ρ.lie A) ^ i).trace

end PolyRep

namespace ChernSpan

variable {ι : Type}

def Reach [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] : Submodule ℝ (Mat m S → S) :=
  Submodule.span ℝ (Set.range fun ρ : PolyRep m => fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n)

def trProd {m : ι → ℕ} (l : List (ι × ℕ)) {S : Type} [CommRing S] (A : Mat m S) : S :=
  (l.map fun x => ((A x.1) ^ x.2).trace).prod

def TrSpan (m : ι → ℕ) (w : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] : Submodule ℝ (Mat m S → S) :=
  Submodule.span ℝ {f | ∃ l : List (ι × ℕ), (∀ x ∈ l, 1 ≤ x.2) ∧ (l.map Prod.snd).sum = w ∧ f = fun A => trProd l A}

end ChernSpan

end GlobalTheory.GoodMetric
end
end
