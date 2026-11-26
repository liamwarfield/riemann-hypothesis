module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTautologicalMarking
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HomExtOfGeometric
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

namespace GlobalTheory.FrameFreeRule

theorem fnAt_comp {X Y : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (g : X ⟶ Y) (f : Γ(Y, ⊤)) :
    fnAt (y ≫ g) f = fnAt y (g.appTop.hom f) := by
  simp only [fnAt, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem fnAt_spMap_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (y : Sp S ⟶ X)
    (f : Γ(X, ⊤)) : fnAt (spMap φ ≫ y) f = φ (fnAt y f) := by
  rw [fnAt_comp]
  exact congrArg (fun q => q.hom (y.appTop.hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem fnAt_id {S : Type} [CommRing S] (a : S) :
    fnAt (𝟙 (Sp S)) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) = a := by
  simp [fnAt]

theorem eq_zero_of_geometric {P : Scheme.{0}} [IsReduced P] (s : Γ(P, ⊤))
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), fnAt y s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  let K := AlgebraicClosure (P.residueField x)
  let y : Sp K ⟶ P := spMap (algebraMap (P.residueField x) K) ≫ P.fromSpecResidueField x
  have h0 : y.appTop.hom s = 0 := by
    have := h K y
    unfold fnAt at this
    exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective).1 this
  have h1 : y ⁻¹ᵁ P.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen_top]
    erw [h0]
    exact Scheme.basicOpen_zero _ _
  have h2 : (default : Sp K) ∈ y ⁻¹ᵁ P.basicOpen s := by
    change y default ∈ P.basicOpen s
    have : y default = x := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rwa [this]
  rw [h1] at h2
  exact h2

theorem hom_ext_of_geometric {P Y : Scheme.{0}} [IsReduced P] [IsAffine Y] (u v : P ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), y ≫ u = y ≫ v) : u = v := by
  refine ext_of_isAffine ?_
  ext r
  rw [← sub_eq_zero]
  refine eq_zero_of_geometric _ fun K _ _ y => ?_
  have := congrArg (fun q => fnAt q r) (h K y)
  simp only [fnAt_comp] at this
  unfold fnAt at this ⊢
  rw [map_sub, map_sub, sub_eq_zero]
  exact this

theorem exists_glue {X : Scheme.{0}} [IsReduced X] {ι : Type} (A : ι → Type) [∀ i, CommRing (A i)]
    (j : ∀ i, Sp (A i) ⟶ X) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (a : ∀ i, A i)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (i i' : ι) (χ : A i →+* K) (χ' : A i' →+* K),
      spMap χ ≫ j i = spMap χ' ≫ j i' → χ (a i) = χ' (a i')) :
    ∃ f : Γ(X, ⊤), ∀ i, fnAt (j i) f = a i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => Sp (A i)) j
    (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩)
  let ev : ∀ i, Polynomial ℤ →+* A i := fun i => Polynomial.eval₂RingHom (Int.castRingHom _) (a i)
  let g : ∀ i, Sp (A i) ⟶ Sp (Polynomial ℤ) := fun i => spMap (ev i)
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    have : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    refine hom_ext_of_geometric _ _ fun K _ _ y => ?_
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (y ≫ pullback.fst (j i) (j i'))
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective (y ≫ pullback.snd (j i) (j i'))
    have e := h K i i' χ.hom χ'.hom (by
      change Spec.map χ ≫ _ = Spec.map χ' ≫ _
      rw [hχ, hχ', Category.assoc, Category.assoc, pullback.condition])
    rw [← Category.assoc, ← Category.assoc, ← hχ, ← hχ']
    change spMap χ.hom ≫ spMap (ev i) = spMap χ'.hom ≫ spMap (ev i')
    rw [GlobalTheory.LocalFrame.spMap_spMap, GlobalTheory.LocalFrame.spMap_spMap]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simpa [ev] using e
  let G : X ⟶ Sp (Polynomial ℤ) := 𝒰.glueMorphisms g hg
  refine ⟨G.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X), fun i => ?_⟩
  have hi : j i ≫ G = g i := 𝒰.ι_glueMorphisms g hg i
  rw [← fnAt_comp, hi, ← Category.comp_id (g i), fnAt_spMap_comp, fnAt_id]
  simp [ev]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem evR_eq_of_chart (s : Rul Xo c) (hs : s ∈ sec Xo c 0 0)
    (hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K),
      y'.x = y.x → evR Xo c s y' = evR Xo c s y)
    {A : Type} [CommRing A] [IsDomain A] [Algebra c.F A] (u : FrPt Xo c A)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (χ : A →ₐ[c.F] K) (y : FrPt Xo c K)
    (hy : y.x = spMap χ.toRingHom ≫ u.x) : evR Xo c s y = χ (evR Xo c s u) := by
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c A K χ u
  rw [hfree K z y (hy.trans hz.1.symm)]
  have hT1 := GlobalTheory.TransferCompare.allTest_framed Xo c A u
  have hT2 := GlobalTheory.TransferCompare.allTest_framed Xo c K z
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c s hs.1 K _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ _ u z hT1.choose_spec.choose_spec.choose_spec hz)

theorem exists_fn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (s : Rul Xo c), s ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c s y' = evR Xo c s y) → ∃ f : Γ(Xo.XF c, ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K), evR Xo c s y = GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.fnAt (GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.basePt y) f := by
  intro E _ _ _ H D l Xo c s hs hfree
  choose A iA dA aA j u hj hp hsn _ hu using
    GlobalTheory.LocalFrame.exists_integral_chart_frame GlobalTheory.abelianSchemeLaws_all.2.secTwist E H D l Xo c
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsReduced (Xo.XF c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd _ _)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (p : Xo.XF c) (χ : A p →+* K),
      spMap χ ≫ j p = basePt y → evR Xo c s y = χ (evR Xo c s (u p)) := by
    intro K _ _ _ y p χ hχ
    have h1 : χ.comp (algebraMap c.F (A p)) = algebraMap c.F K := by
      have h2 : spMap (χ.comp (algebraMap c.F (A p))) = spMap (algebraMap c.F K) := by
        rw [← GlobalTheory.LocalFrame.spMap_spMap, ← hsn, ← Category.assoc, hχ]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    refine evR_eq_of_chart s hs hfree (u p) ⟨χ, fun r => RingHom.congr_fun h1 r⟩ y ?_
    change y.x = spMap χ ≫ _
    rw [hu, ← Category.assoc, hχ]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨f, hf⟩ := exists_glue A j (fun x => ⟨x, hp x⟩) (fun p => evR Xo c s (u p)) (by
    intro K _ _ p p' χ χ' hχ
    letI : Algebra c.F K := (χ.comp (algebraMap c.F (A p))).toAlgebra
    have hsn' : (spMap χ ≫ j p) ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
      rw [Category.assoc, hsn, GlobalTheory.LocalFrame.spMap_spMap]
    have hx : ((spMap χ ≫ j p) ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsn', sOf, GlobalTheory.LocalFrame.spMap_spMap]
    obtain ⟨y, hy⟩ : ∃ y : FrPt Xo c K, y.x = (spMap χ ≫ j p) ≫ pullback.fst _ _ := by
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist ((spMap χ ≫ j p) ≫ pullback.fst _ _)
      exact ⟨⟨_, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
    have hb : spMap χ ≫ j p = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [← hy]; exact (pullback.lift_fst _ _ _).symm
      · rw [hsn']; exact (pullback.lift_snd _ _ _).symm
    exact (key K y p χ hb).symm.trans (key K y p' χ' (hχ.symm.trans hb)))
  refine ⟨f, fun K _ _ _ y => ?_⟩
  let p : Xo.XF c := basePt y default
  have hr : Set.range (basePt y) ⊆ Set.range (j p) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default]
    exact hp p
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (IsOpenImmersion.lift (j p) (basePt y) hr)
  have hb : spMap χ.hom ≫ j p = basePt y := by
    change Spec.map χ ≫ _ = _
    rw [hχ, IsOpenImmersion.lift_fac]
  rw [key K y p χ.hom hb, ← hb, fnAt_spMap_comp, hf]

end GlobalTheory.FrameFreeRule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.FiniteOrderConst

open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

theorem isHolTo_of_eqOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) : IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => and_congr_right fun hb => by rw [e b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [e b hb.1]⟩

theorem valAt'_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) : valAt' y ⊤ f = fnAt y f := by
  rw [valAt', dite_eq_left (show (⊤ : (Sp ℂ).Opens) ≤ y ⁻¹ᵁ ⊤ from le_rfl), valAt, fnAt]
  have : y.appLE ⊤ ⊤ le_rfl = y.appTop := Scheme.Hom.appLE_eq_app y
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (q.hom f)) this

theorem fnAt_eq_of_pow {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {a : V → (Sp ℂ ⟶ X)} (hB : IsPreconnected B) (h : IsHolTo B a) (f : Γ(X, ⊤)) {N : ℕ} (hN : 0 < N)
    (hp : ∀ b ∈ B, fnAt (a b) f ^ N = 1) {b b' : V} (hb : b ∈ B) (hb' : b' ∈ B) : fnAt (a b) f = fnAt (a b') f := by
  have hc : ContinuousOn (fun b => fnAt (a b) f) B := by
    have := (h ⊤ f).2.continuousOn
    simp only [valAt'_top] at this
    exact this.mono fun b hb => ⟨hb, le_rfl⟩
  have hfin : {z : ℂ | z ^ N = 1}.Finite :=
    (Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simpa [Polynomial.mem_nthRoots hN] using hz
  exact hB.constant_of_mapsTo hfin.isDiscrete hc hp hb hb'

theorem const_on_period_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  classical
  rintro E _ _ _ H Dw l Xo c σ f hf hfree ⟨N, hN, hp⟩ g ty F hty i P P' y y' hP hP' hy hy'
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.FrameFreeRule.exists_fn E H Dw l Xo c f hf hfree
  obtain ⟨m, B, Q, -, hB, hconv, h0, hQ0, hQ, hall⟩ := GlobalTheory.PeriodChart.period_chart E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) P hP
  obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := hall P' hP'
  have hbP : F.u i (Q b) = F.u i P' :=
    (F.fibre i (Q b) P' (hQ.1 b hb) hP').2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, hh⟩
  have hex : ∀ t, ∃ z : FrPt Xo c ℂ, t ∈ B → z.x = F.u i (Q t) := fun t => by
    by_cases ht : t ∈ B
    · have hx := F.over_σ i _ (hQ.1 t ht)
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist (F.u i (Q t))
      exact ⟨⟨F.u i (Q t), hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, fun _ => rfl⟩
    · exact ⟨y, fun h => absurd h ht⟩
  choose z hz using hex
  have hhol : IsHolTo B fun t => basePt (z t) :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (isHolTo_of_eqOn (F.hol i m B Q hB hQ).1 fun t ht => (pullback.lift_fst _ _ _).trans (hz t ht))
      (isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_const hB (spMap σ)) fun t _ => pullback.lift_snd _ _ _)
  have key := fnAt_eq_of_pow hconv.isPreconnected hhol f₀ hN
    (fun t _ => by rw [← hf₀ ℂ (z t)]; exact hp (z t)) h0 hb
  rw [← hf₀ ℂ, ← hf₀ ℂ] at key
  exact (hfree ℂ (z 0) y (hy.trans (by rw [hz 0 h0, hQ0]))).trans
    (key.trans (hfree ℂ y' (z b) ((hz b hb).trans (hbP.trans hy'.symm))))

end GlobalTheory.FiniteOrderConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpaceStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFree_finiteOrder_rule_const_periodSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  first | exact @GlobalTheory.FiniteOrderConst.const_on_period_space | exact GlobalTheory.FiniteOrderConst.const_on_period_space | (intros; apply GlobalTheory.FiniteOrderConst.const_on_period_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.CMObjBundlePull
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM

section Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (t : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ t)

def IsTan {G : Over S} [GrpObj G] (t : Sp R ⟶ S) (v : epsAt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left

def IsMultiple {G : Over S} {t : Sp R ⟶ S} (x : R) (v w : epsAt t ⟶ G) : Prop :=
  w.left = spMap (epsScaleR x) ≫ v.left

end Lie

section Line

variable {K : Type} [Field K] [NumberField K]

abbrev genPt (K : Type) [Field K] [NumberField K] : Sp K ⟶ Sp (𝓞 K) := spMap (algebraMap (𝓞 K) K)

end Line

section Pol

variable {K : Type} [Field K] [NumberField K]

end Pol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def psi (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}

def psiBar (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = -H.rt0}

structure CMObj (c : Coeff l) (p q : ℕ) : Type 1 where

  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [alg : Algebra c.F K]

  B : Out.PolAV (Sp (𝓞 K))

  AP : Out.PolAV (Sp (𝓞 K))

  AC : Out.PolAV (Sp (𝓞 K))
  ιB : Out.RingAct B.A (𝓞 E)
  ιP : Out.RingAct AP.A (𝓞 E)
  ιC : Out.RingAct AC.A (𝓞 E)

  φP : Fin p → (AP.A ⟶ B.A)
  φP_hom : ∀ j, IsMonHom (φP j)
  φP_lin : ∀ j a, ιP.act a ≫ φP j = φP j ≫ ιB.act a

  φC : Fin q → (AC.A ⟶ B.A)
  φC_hom : ∀ j, IsMonHom (φC j)
  φC_lin : ∀ j a, ιC.act a ≫ φC j = φC j ≫ ιB.act a

  hP : Fin p → 𝓞 E

  hC : Fin q → 𝓞 E

  ηP : psi H → (epsAt (genPt K) ⟶ AP.A)

  ηC : psiBar H → (epsAt (genPt K) ⟶ AC.A)

  ℓP : psi H → MLine K

  ℓC : psiBar H → MLine K

attribute [instance] CMObj.field CMObj.numberField CMObj.alg

namespace CMObj

variable {c : Coeff l} {p q : ℕ} (o : CMObj c p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.LamCM Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

namespace GlobalTheory.CMClaims

theorem laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
theorem secTwist : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
theorem homExt : CM.HomExtDvr := fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ =>
  GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ

section Vec

variable {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {G : Over (Sp R)} {G' : Over (Sp R')} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

variable (h : IsGrpPullback G' G (spMap f) φ)

variable [IsCommMonObj G'] {n : ℕ} {v : Fin n → (epsR R' ⟶ G')} (hv : IsLieBasis v)

end Vec

section Pair

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E}

end Pair

section Isog

theorem card_torsion_eq {M N : Type} [CommGroup M] [CommGroup N] (F : M →* N) (hF : Function.Surjective F) (m : ℕ)
    (hm : ∀ x, F x = 1 → x ^ (m + 1) = 1) :
    Nat.card {x : M // x ^ (m + 2) = 1} = Nat.card {y : N // y ^ (m + 2) = 1} := by
  refine Nat.card_eq_of_bijective (fun x => ⟨F x.1, by rw [← map_pow, x.2, map_one]⟩) ⟨fun a b e => ?_, fun y => ?_⟩
  · have e₁ : F (a.1 / b.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val e
    have e₂ : (a.1 / b.1) ^ (m + 2) = 1 := by rw [div_pow, a.2, b.2, div_one]
    rw [pow_succ, hm _ e₁, _root_.one_mul, div_eq_one] at e₂
    exact Subtype.ext e₂
  · obtain ⟨x, hx⟩ := hF y.1
    have e₁ : (x ^ (m + 2)) ^ (m + 1) = 1 := hm _ (by rw [map_pow, hx, y.2])
    refine ⟨⟨x ^ ((m + 1) * (m + 1)), ?_⟩, Subtype.ext ?_⟩
    · rw [← pow_mul, show (m + 1) * (m + 1) * (m + 2) = (m + 2) * (m + 1) * (m + 1) by ring, pow_mul, pow_mul, e₁, one_pow]
    · change F _ = y.1
      rw [map_pow, hx, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring, pow_succ, pow_mul, y.2, one_pow, _root_.one_mul]

variable {K : Type} [Field K] [NumberField K]

theorem onto_points {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {P Q : Over (Sp R)} (Φ : P ⟶ Q)
    [IsFinite Φ.left] [Surjective Φ.left] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ Q) : ∃ x : Over.mk t ⟶ P, y = x ≫ Φ := by
  obtain ⟨p, hp⟩ := GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end Isog

section Sum

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l} {p q : ℕ}

end Sum

section Types

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

variable {E : Type} [Field E] [NumberField E]

end Types

section Lines

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

end Lines

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable [StarRing (𝓞 E)] {l : Level H} {c : Coeff l} {p q : ℕ}

def Readable (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg ∧ abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g ∧
    (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
    (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
    ∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a

variable (hs : ∀ a : 𝓞 E, star a = H.bar a) (o : abelian₂.LamObj c p q) (h : Readable o)

end Main

end GlobalTheory.CMClaims
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

end GlobalTheory.LeafCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PosAtOfCptCoefOfThmPActualCpt
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialBetaPosOfXiExists
open MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.WeightedFormPos


open Formalism.FourierDecayAlt.P.JCx2 in
theorem radialBetaPos_of_xiExists (hXi : B.XiExists) : JC.RadialBetaPos := by
  intro Wp Wq _ _ _ _ _ _ P0 T j μ hμ
  obtain ⟨C1, hC1, hpair⟩ := rb_pairAt (T.bs j) μ hμ
  refine ⟨C1⁻¹, inv_pos.2 hC1, fun n x x' Φ Φ' ε _ hx hx' hΦ hΦ' => ?_⟩
  have h : P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta (T.bs j) (x a) (x' a) := by
    refine (rb_form_eq (k := P0.k) (r := P0.r - j) μ Φ Φ').trans ?_
    let f : Wd.Ix (Fin n) → (Fin (P0.r - j) → ℂ) × ℂ → ℂ := fun a q =>
      (bcWeight P0.k (P0.r - j) (Tz P0.k (P0.r - j) (T.bs j).z) (Tz P0.k (P0.r - j) (T.bs j).z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF (T.bs j) (x' a) (B.gq (T.bs j) q))) (B.hsVec (B.JF (T.bs j) (x a) (B.gq (T.bs j) q)))
    have hint : ∀ a, Integrable (f a) := fun a =>
      betaIntegrand_integrable_of_xiExists hXi P0.k (P0.r - j) Wp Wq (T.bs j) _ (x a) (x' a) le_rfl
        ((hx a).2.1 _ 5) ((hx' a).2.1 _ 5)
    have hae : (fun c : Fin (P0.r - j) → ℂ => ((∏ a : Fin (P0.r - j), ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ b, P5.pairAt (k := P0.k) (r := P0.r - j) μ (Φ b) (Φ' b) c)
        =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
      filter_upwards [rb_ae_OmX] with c hc
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [rb_weight hc]
      rfl
    refine (integral_congr_ae hae).trans ?_
    rw [integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, ← integral_prod _ (hint b)]
    rfl
  rw [h]
  have hC : (C1 : ℂ) ≠ 0 := by exact_mod_cast hC1.ne'
  push_cast
  field_simp

theorem radialModuleForm_of_xiExists (hXi : B.XiExists) : JC.RadialModuleForm :=
  radial_module_form_of_parts (radialBetaPos_of_xiExists hXi) radial_module_action bessel_function_finite_class
    bessel_module module_regularity

end GlobalTheory.WeightedFormPos
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory.WeightedFormPos


open Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q in
theorem form_nonneg_of_cptCoef (hXi : B.XiExists) (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hc : KB.CutWord P p.l0 w) (x : Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hxc : ∀ e, KB.CptCoef (p.T.bs j) (x e)) : 0 ≤ p.form j hj w x x := by
  obtain ⟨ε, hε, hx⟩ := PBL.nv_of_cv (Bs := p.T.bs j) (x := x) hxc
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := radialModuleForm_of_xiExists hXi Wp Wq P p.T jF X μ L st p.l0 hD
  have hpic := fun a => (hxc a).2.1.elim fun R hR =>
    PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJ hε (hx a) (R := R) hR
  choose Φ hΦK hΦ using hpic
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hx hx hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

theorem posAt_of_cptCoef_of_xiExists (hXi : B.XiExists) : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), (∀ y, 0 ≤ nn y) → KB.CptCoef p.T.base F → TBB.PosAt p nn F Y N := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N hnn hF
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p F j hj w h h hh hh]
    have h0 := form_nonneg_of_cptCoef hXi hA P p j hj w hw.1 _
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e)
    exact (Complex.nonneg_iff.1 h0).1
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_right (fun h1 => hh h1.1)]
    simp

theorem formPosCpt_of_xiExists (hXi : B.XiExists) : PBL.FormPosCpt :=
  fun hP _ _ _ _ _ _ _ _ P p j hj w hc x hx => form_nonneg_of_cptCoef hXi hP P p j hj w hc x hx

end GlobalTheory.WeightedFormPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstIffSecondAndResiduals
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RepCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_actLat (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (v' : Fin n → E) :
    v' ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v' := by
  simp [UnitaryAdjointCongruence.actLat]






theorem mul_adj {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) : γ * UnitaryAdjointCongruence.adjM γ = 1 :=
  mul_eq_one_comm.1 h

theorem form_adj (γ : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * γ.mulVec w j =
      ∑ j, IsCMField.complexConj E ((UnitaryAdjointCongruence.adjM γ).mulVec v j) * w j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, UnitaryAdjointCongruence.adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (UnitaryAdjointCongruence.actLat γ Λ).Unimod := by
  intro v
  have e : v ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ (UnitaryAdjointCongruence.adjM γ).mulVec v ∈ Λ.La := by
    rw [mem_actLat]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    · intro hv
      exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, mul_adj h, Matrix.one_mulVec]⟩
  rw [e, hΛ]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := (mem_actLat _ _ _).1 hw
    rw [form_adj]
    exact hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ((mem_actLat _ _ _).2 ⟨w, hw, rfl⟩)

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Letters

variable (c : Coeff l) {n : ℕ}

theorem push_mem {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) :
    UnitaryAdjointCongruence.pushLet c γ P ∈ harmL c (UnitaryAdjointCongruence.actLat γ Λ) a := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  refine ⟨⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n γ P h h1, (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).1 h2,
    (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).2 h3⟩, ?_⟩
  have : symO (Dw := Dw) c Λ ≤ (symO c (UnitaryAdjointCongruence.actLat γ Λ)).comap (UnitaryAdjointCongruence.pushLet c γ).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      exact (algHom_C (UnitaryAdjointCongruence.pushLet c γ) (o : c.F)).symm
    · exact Subring.subset_closure (Or.inr ⟨σ, i, _, (mem_actLat _ _ _).2 ⟨b, hb, rfl⟩, UnitaryAdjointCongruence.pushLet_letB c γ σ i b⟩)
  exact this h4

end Letters

section Values

variable (Xo : Moduli Dw l) (c : Coeff l)

structure FrameLaws : Prop where
  cover : ChartCoverF Xo c
  test : AllTest Xo c
  bc : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

theorem frameLaws : FrameLaws Xo c :=
  have hB := GlobalTheory.allSixLaws.1.secBaseChange
  ⟨GlobalTheory.Frames.chartCoverF_of_secBaseChange hB E H Dw l Xo c, GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c,
    fun S T _ _ _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y⟩

instance (K : Type) [Field K] (p : TRing K) : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

variable {Xo c} {nab : NabV Xo c} {n : ℕ}

end Values

section Clauses

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ}




end Clauses

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

end Cover

section Main

variable [StarRing (𝓞 E)] (Dw) (n : ℕ)

variable {Dw n}

end Main

end GlobalTheory.RepCompare
end
end
