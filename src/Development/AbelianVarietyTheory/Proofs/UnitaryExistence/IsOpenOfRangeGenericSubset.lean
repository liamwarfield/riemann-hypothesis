module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifAfterExt

theorem exists_finite_split {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∃ S : SplitExt (Sp k'), S.IsGt ((Over.pullback (spMap (algebraMap k k'))).obj G) := by
  have := hG.smooth
  obtain ⟨k', hk, T⟩ := exists_finite_torusExtension k (AlgebraicClosure k) G
    inferInstance hG.quasiCompact hG.separated (hG.fibres _ _)
  have := hG.comm
  exact ⟨k', inferInstance, inferInstance, hk, exists_splitExt_isGt_of_torusExtension _ _ T⟩

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [Finite (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ Finite (ResidueField W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, hl, -, e, he⟩ := GlobalTheory.unramExt W k'
  have hfk : Finite k' := Module.finite_of_finite (ResidueField W)
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) E _ d)⟩

theorem exists_generic_square {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (hf : Function.Injective f) :
    ∃ g : Sp (FractionRing W) ⟶ Sp (FractionRing V), jK W ≫ spMap f = g ≫ jK V := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hf
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg : ∀ r, g (algebraMap _ _ r) = algebraMap W _ (f r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value g
  have e : spMap g ≫ jK V = jK W ≫ spMap f := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg))
  exact ⟨_, e.symm⟩

theorem isOpen_of_range_generic_subset (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (U : Set (Sp V)) (hU : Set.range (jK V) ⊆ U) : IsOpen U := by
  have hgen : ∀ x : Sp V, x ≠ closedPoint V → x ∈ U := fun x hx => by
    have h0 : x.asIdeal = ⊥ := by
      by_contra hne
      exact hx (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hne)))
    refine hU ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)), PrimeSpectrum.ext ?_⟩
    rw [h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  by_cases hc : (closedPoint V : Sp V) ∈ U
  · have : U = Set.univ := Set.eq_univ_of_forall fun x => by
      by_cases hx : x = closedPoint V
      · exact hx ▸ hc
      · exact hgen x hx
    rw [this]; exact isOpen_univ
  · have : U = {(closedPoint V : Sp V)}ᶜ := Set.ext fun x => ⟨fun hx h => hc (h ▸ hx), hgen x⟩
    rw [this]
    exact (IsLocalRing.isClosed_singleton_closedPoint V).isOpen_compl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_sabMap {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : RelAmple u.G u.PP.L)
    (hk : KTriv u.G u.PP.L) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K) (h : j' ≫ f = g ≫ j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K')) (p : Sp K' ⟶ S) (_ : p = g ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (g ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ h n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (g ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

theorem isOpen_and_uniformised (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [hz : CharZero W]
    (hc : IsAdicComplete (maximalIdeal W) W) (t : SAB H (Sp W)) (hp : GlobalTheory.LN.PolAt t (jK W))
    (hS : ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t.G)) :
    IsOpen (abLocus t.G) ∧ UniformisationConclusion t (abLocus t.G) := by
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, hc, hz⟩
  have hadm : GlobalTheory.LN.admitted W (maximalIdeal W) := by
    refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hc, hz, inferInstance, ?_⟩
    letI := Ideal.Quotient.field (maximalIdeal W)
    infer_instance
  have ho := isOpen_of_range_generic_subset W _ (abLocusOne _ _ t.semi _ _ hp.1)
  obtain ⟨A, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W t hp
  obtain ⟨P, -, -, hP⟩ := GlobalTheory.T.exists_pel_uniformisation_complete_dvr E H W hW t A gen hg hw hS
  exact ⟨ho, P, GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H W _ hadm t P hP ho, hP⟩

theorem exists_finite_ext_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr)) (_ : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap tK Xo.univ.t x), T.FinRes → ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)), Function.Injective φ ∧ φ.Finite ∧ T'.FinRes ∧ IsOpen (abLocus t'.G) ∧ UniformisationConclusion t' (abLocus t'.G) := by
  intro E _ _ _ H Dw l Xo T t tK mK x mx hT
  have : Finite (ResidueField T.V) := hT
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨ho, hN⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, hr, ho, hN⟩

end GlobalTheory.UnifAfterExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hA hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces E H D l Xo _ g ty F hD rfl hty hA c fun τ hτ => ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  exact GlobalTheory.T.permutes_periodSpaces_id_of_fixes_cm_curve_torsion E H D l Xo _ g ty F hD rfl hty hA hsig τ (hτ _ (c.le h1)) (hC τ hτ)

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefinedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffField_algClosed_functionField_of_torsionDefined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.fnAlgClosed_of_curveOver | exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver | (intros; apply GlobalTheory.CompRat.fnAlgClosed_of_curveOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
noncomputable section

namespace GlobalTheory.GalTw.CharSec

section General

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sec_eq_zero_of_complex (σ : c.F →+* ℂ) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}
    (hg : g ∈ sec Xo c a n) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c g y = 0) : g = 0 := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW := (GlobalTheory.Frames.algebraic_laws hS E H Dw l Xo c).2.2.1
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  letI : Algebra c.F ℂ := σ.toAlgebra
  refine GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := c.F) (Ω := ℂ) (g p y) ?_
  intro φ
  let φ' : p.R →ₐ[c.F] CAt σ := φ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) φ' y
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evR evalAt at h0
  rw [dite_eq_left hT, ← hW g hg.1 (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  exact h0

theorem conj_value (σ σ' : c.F →+* ℂ) (τ : ℂ ≃+* ℂ) (hσ : σ' = (τ : ℂ →+* ℂ).comp σ) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt σ'))
    (h : y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x) : toC (evR Xo c f y') = τ (toC (evR Xo c f y)) := by
  subst hσ
  exact GlobalTheory.T.weightZeroSection_value_conj_point E H Dw l Xo c σ τ f hf y y' h

theorem exists_conj_point (σ : c.F →+* ℂ) {ta : c.F ≃+* c.F} (hta : Fixes c ta) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a, τ (σ a) = σ (ta a)) (y : FrPt Xo c (CAt σ)) :
    ∃ y₀ : FrPt Xo c (CAt σ), y.x = spMap (τ : ℂ →+* ℂ) ≫ y₀.x ∧
      ∀ f ∈ sec Xo c 0 0, toC (evR Xo c (galRul hta f) y) = τ (toC (evR Xo c f y₀)) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let φ : CAt (σ.comp ta.toRingHom) →ₐ[c.F] CAt σ :=
    { toRingHom := (τ.symm : ℂ →+* ℂ)
      commutes' := fun a => by
        show τ.symm (σ (ta a)) = σ a
        rw [← hτ, RingEquiv.symm_apply_apply] }
  let y' : FrPt Xo c (CAt (σ.comp ta.toRingHom)) := twPt hta y
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φ y'
  have hx : y.x = spMap (τ : ℂ →+* ℂ) ≫ z.x := by
    have h1 : z.x = spMap (τ.symm : ℂ →+* ℂ) ≫ y.x := hz.1
    have h2 : spMap (τ : ℂ →+* ℂ) ≫ spMap (τ.symm : ℂ →+* ℂ) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      simp
    rw [h1]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) h2).trans (Category.id_comp _))).symm
  refine ⟨z, hx, fun f hf => ?_⟩
  have e1 := (((GlobalTheory.T.conjugateSection_values_semilinear E H Dw l Xo c ta hta).1 0 0 f hf).2 (CAt σ) y)
  have e2 := conj_value σ (σ.comp ta.toRingHom) τ (RingHom.ext fun a => (hτ a).symm) hf z y' hx
  rw [e1]
  exact e2

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat GlobalTheory.GalTw

end GlobalTheory.GalTw.CharSec
end
end
