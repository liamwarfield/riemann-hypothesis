module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormNullValEqNormTheta
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusOfPeriodHermitian
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExpTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_base_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {O : Type} [CommRing O] {β : O →+* K} (hβ : ∀ x : O, la.valuation K (β x) ≤ 1)
    (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  have key : ∀ x : O, io (β x) ∈ (algebraMap T.V T.Fr).range := by
    intro x
    have h1 : valV T.V (io (β x)) ≤ 1 := by
      by_cases h0 : β x = 0
      · rw [h0, map_zero, map_zero]; exact zero_le_one
      have h2 := ho.2 (β x)
      have h3 : WithZero.log (la.valuation K (β x)) ≤ 0 := by
        have := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 (hβ x)
        simpa using this
      have h4 : 0 ≤ vV T.V (io (β x)) := by
        rw [h2]
        exact mul_nonneg (Nat.cast_nonneg e) (by unfold vLa; omega)
      have h5 : valV T.V (io (β x)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
      refine (WithZero.log_le_log h5 one_ne_zero).1 ?_
      unfold vV at h4
      rw [WithZero.log_one]; omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one h1
  have hinj : Function.Injective (algebraMap T.V T.Fr).rangeRestrict := fun a b h =>
    IsFractionRing.injective T.V T.Fr (congrArg Subtype.val h)
  let eq : T.V ≃+* (algebraMap T.V T.Fr).range :=
    RingEquiv.ofBijective _ ⟨hinj, (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp ((io.comp β).codRestrict _ key), RingHom.ext fun x => ?_⟩
  exact congrArg Subtype.val (eq.apply_symm_apply ⟨io (β x), key x⟩)

theorem point_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] (u v : Sp A ⟶ X)
    (h : spMap i ≫ u = spMap i ≫ v) (h' : u ≫ s = v ≫ s) : u = v := by
  have : IsDominant (spMap i) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2
      (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)
    exact this
  exact ext_of_isDominant_of_isSeparated s h' (spMap i) h

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem datAt_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  intro E _ _ _ H Dw l Xo c O _ β Y la hB T io e ho x s G I hxs T' φ G' mG U hU hT p C Pc eF f h1' h2' h3' h4'
  obtain ⟨b, hb⟩ := exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  let tP : SAB H (Sp T.V) := ⟨(Over.pullback yt).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩
  let mP' : SABMap tP Y.t yt := mP
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t I.t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast I.m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t I.t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP I.t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper I.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP I.t' hprop I.m2 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  let n' : SABMap G Y.t yt := PullbackSections.sabMapCast n (Category.id_comp yt)
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n' mG
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp (f.comp φ) = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, spMap_comp_spMap, h1']
  have halg : (f.comp φ).comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  have hfac : spMap f ≫ spMap φ ≫ yt = Pc.yt := by
    refine point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
    · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc (spMap f), spMap_comp_spMap, ← Category.assoc,
        spMap_comp_spMap, hr, ← spMap_comp_spMap, Category.assoc]
    · rw [Pc.yt_over, Category.assoc, Category.assoc, h2, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, halg]
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := h4'
      fac := hfac
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hT }
  exact ⟨A, LinearEquiv.refl _ _, fun _ _ => rfl⟩

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  first | exact @GlobalTheory.EtaVal.datAt_of_uniformisation | exact GlobalTheory.EtaVal.datAt_of_uniformisation | (intros; apply GlobalTheory.EtaVal.datAt_of_uniformisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsSmallCoeffRuleNeZero
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
open Formalism.L2.Pj hiding Unf GoodEmb relab toC
attribute [local instance] Over.cartesianMonoidalCategory

theorem nonzeroRule_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem exists_small_coeff_rule_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R : ℕ), Odd R → 1 < R → 2 ≤ r → ∃ (i : ℕ) (_ : Fintype (LatMod Dw R)) (x₀ : Fin r → Dw.La) (cf : (Fin r → LatMod Dw R) → ℤ) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Fintype.card (Fin r → LatMod Dw R) ≤ R ^ (2 * I2.PT.f E * r ^ 2) ∧ (∀ j, |cf j| ≤ (max 1 (Fintype.card U.Comp) * R ^ (8 * I2.PT.f E * r ^ 2) : ℕ)) ∧ Spans (shiftFam R x₀ : (Fin r → LatMod Dw R) → Fin r → LatMod Dw (R ^ 4)) ∧ IsEtaRule Xo c R cf (shiftFam R x₀) f ∧ ∀ k, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU hT R hR h1 h2
  have hr : r = Dw.p + Dw.q := hU.1
  subst hr
  obtain ⟨hfG, hfL, hcL, hcG, hdiv, ⟨x₀, hx₀⟩, hspan⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1
  obtain ⟨i, hi⟩ := hdiv hR h2
  letI hFin : Fintype (LatMod Dw R) := Fintype.ofFinite _
  have hf : FD.fdeg E = I2.PT.f E := rfl
  rw [hf] at hcL hcG
  choose xk hxk using fun k => nonzeroRule_dom_nonempty (U.X k)
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  let e := Fintype.equivFin U.Comp
  obtain ⟨cf, hcf, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR h1
    (Dw.p + Dw.q) x₀ (CAt σ) (Fintype.card U.Comp) (fun a => U.un (e.symm a) ⟨xk _, hxk _⟩)
  obtain ⟨f, hrule, -⟩ := (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR
    (Fin (Dw.p + Dw.q) → LatMod Dw R) (Dw.p + Dw.q) (fun j => (cf j : ℤ)) (shiftFam R x₀)).1
  refine ⟨i, hFin, x₀, fun j => (cf j : ℤ), f, ?_, hi, ?_, ?_, ?_, hrule, ?_⟩
  · have hpos : 0 < Nat.card (LevGrp Dw (R ^ 4)) := Nat.card_pos
    rw [hi] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  · rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcL, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  · intro j
    rw [Nat.abs_cast]
    exact_mod_cast (hcf j).trans (Nat.mul_le_mul (le_max_right _ _) hcG)
  · intro j
    exact hspan _ x₀ hx₀ j (LinearEquiv.refl _ _)
  · intro k
    obtain ⟨a, rfl⟩ := e.symm.surjective k
    refine ⟨xk _, hxk _, ?_⟩
    have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR _ _ _ _ f hrule (CAt σ) (U.un (e.symm a) ⟨xk _, hxk _⟩)
      (hT _ _)).1
    have h0 := hne a _ hv
    have e1 : rdU U f (e.symm a) (xk _) = toC (evR Xo c f (U.un (e.symm a) ⟨xk _, hxk _⟩)) := dif_pos (hxk _)
    rw [e1]
    exact h0

end GlobalTheory.EtaAn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
open Formalism.L2.Pj hiding Unf GoodEmb relab toC
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn.ArchPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem gen_mod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pm : D.La →+ (Fin g → ℂ)}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {T : I2.PT E} {ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim}
    (hP : IsPeriod D ty Pm) (hT : IsTorusOf D ty Pm Hm T ψ) (R : ℕ) {n : ℕ} (a : Fin n → D.La)
    (ha : ∀ u : D.La, ∃ (cf : Fin n → 𝓞 E) (v : D.La), u = ∑ b, cf b • a b + (R ^ 4) • v) :
    ∀ x ∈ T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (ψ (Pm (a b))) + (R : ℂ) • y := by
  obtain ⟨-, -, -, hL, hact, -⟩ := hT
  intro x hx
  obtain ⟨u, rfl⟩ := (hL x).1 hx
  obtain ⟨cf, v, rfl⟩ := ha u
  refine ⟨cf, ψ (Pm ((R ^ 3) • v)), (hL _).2 ⟨_, rfl⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hact]
    congr 1
    funext k
    exact hP.1 _ _ _
  · rw [Nat.cast_smul_eq_nsmul, ← map_nsmul ψ, ← map_nsmul Pm, smul_smul, ← pow_succ']

theorem evR_eq {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (hA : AllTest Xo c)
    {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ} {xs : J → Fin n → LatMod Dw (R ^ 4)}
    {f : Rul Xo c} (hf : IsEtaRule Xo c R cf xs f) (y : FrPt Xo c (CAt σ))
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → CAt σ)
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    evR Xo c f y = etaExpr (R ^ 4) cf xs w := by
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have h₁ := (GlobalTheory.T.etaProductRule_value_eq_productForm_of_testRing E H Dw l Xo c R hR J n cf xs f hf (CAt σ) y (hA _ y)).1
  have h₂ : EtaValAt Xo c R cf xs y (etaExpr (R ^ 4) cf xs w) :=
    ⟨CAt σ, inferInstance, inferInstance, AlgHom.id c.F _, y, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, GlobalTheory.FramedBaseChange.refl y, hev, hw, rfl⟩
  exact ((GlobalTheory.EtaForm.etaValAt_existsUnique_natural GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR J n cf xs).1 _ y).unique h₁ h₂

end GlobalTheory.EtaAn.ArchPt

namespace GlobalTheory.EtaAn

theorem norm_productForm_le_at_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R i N : ℕ), Odd R → 1 < R → Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i → 1 ≤ N → ∀ (J : Type) [Fintype J] (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) → (∀ j, |cf j| ≤ N) → Spans xs → IsEtaRule Xo c R cf xs f → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) → ‖rdU U f k x.1‖ ≤ Real.exp (-(i : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R N)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA R i N hR h1R hcard hN J _ cf xs f hJ hcf hsp hf DF q m R0 hrun hm k x hx
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (GlobalTheory.T.relabelling_goodEmbedding_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q (fun j => relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := GlobalTheory.T.exists_torus_of_period_hermitian E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := GlobalTheory.T.periodTorus_isTorusAt_frame E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact GlobalTheory.T.appellHumbert_section_entire_with_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := GlobalTheory.T.ahFrame_factor_eq_negOnePow_riemannForm E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := GlobalTheory.T.theta_function_torus_l2_norm E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) (U.un k x).x ev :=
    (GlobalTheory.fullLevel_cover_baseChange_torsor GlobalTheory.firstFiveLaws.1 E H Dw l Xo (R ^ 4) hR4).2.2.2 ℂ (U.un k x).x
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact GlobalTheory.T.norm_nullVal_eq_norm_theta_alt E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)
  haveI : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1R).1
  haveI := Fintype.ofFinite (LevGrp Dw (R ^ 4))
  have hval : rdU U f k x.1 = ∏ g : LevGrp Dw (R ^ 4), ∑ j, (cf j : ℂ) * ∏ b, toC (w (g (xs j b))) := by
    have e₁ : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e₁, ArchPt.evR_eq hA hR hf (U.un k x) ev w hev hw, etaExpr, finprod_eq_prod_of_fintype]
    rfl
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hspan : ∀ (g : LevGrp Dw (R ^ 4)) j, Submodule.span (𝓞 E) (Set.range fun b => g (xs j b)) = ⊤ := fun g j => by
    have : (Set.range fun b => g (xs j b)) = g.toLinearMap '' Set.range (xs j) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, hsp j, Submodule.map_top, LinearEquiv.range]
  have hgen' : ∀ (g : LevGrp Dw (R ^ 4)) j, ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (g (xs j b)))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact ArchPt.gen_mod hP hT R (fun b => a (g (xs j b))) (hgen r _ (hspan g j))
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : LevGrp Dw (R ^ 4) → J → Fin r → ℂ) (a : LevGrp Dw (R ^ 4) → J → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R N)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R i N h1R hN _ hsec hl2' (LevGrp Dw (R ^ 4)) J
      (by rw [← Nat.card_eq_fintype_card, hcard]) hJ' cf w' a' hcf
  exact key r hr hJ (fun g j b => toC (w (g (xs j b)))) (fun g j b => ψ (z (g (xs j b))))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)

end GlobalTheory.EtaAn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
open Formalism.L2.Pj hiding Unf GoodEmb relab toC
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_etaProductForm_le_at_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R i N : ℕ), Odd R → 1 < R → Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i → 1 ≤ N → ∀ (J : Type) [Fintype J] (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), Fintype.card J ≤ R ^ (2 * I2.PT.f E * r ^ 2) → (∀ j, |cf j| ≤ N) → Spans xs → IsEtaRule Xo c R cf xs f → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) → ‖rdU U f k x.1‖ ≤ Real.exp (-(i : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R N)) := by
  first | exact @GlobalTheory.EtaAn.norm_productForm_le_at_unit_frame | exact GlobalTheory.EtaAn.norm_productForm_le_at_unit_frame | (intros; apply GlobalTheory.EtaAn.norm_productForm_le_at_unit_frame <;> assumption)
end
end
