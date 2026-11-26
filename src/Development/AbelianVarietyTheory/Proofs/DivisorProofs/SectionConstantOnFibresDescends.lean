module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGood

theorem hom_spQ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℚ) : f = g := by
  have key : ∀ h : X ⟶ Sp ℚ, h = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ h.appTop) := by
    intro h
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key f, key g]
  congr 2
  ext1
  exact RingHom.ext_rat _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_objMap_lower' {l l₂ : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B'} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj Dw l b' s} {o₂ : Obj Dw l₂ b₂ s₂} {o' : Obj Dw l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    Nonempty (ObjMap (GlobalTheory.ObjLower.lower o' h hρ hζ) o (g ≫ π)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₁ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.eta_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₂ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.etaA_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

theorem eq_of_levelMaps {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} (hd : l.Dvd l₂)
    (jK : KA l →+* KA l₂) (hjK : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {r r' : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (m' : SABMap Xo₂.univ.t Xo.univ.t r')
    (he : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (heA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (he' : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = r' ≫ (Xo.univ.eta a).left)
    (heA' : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = r' ≫ (Xo.univ.etaA a).left)
    {T : Scheme.{0}} [IsReduced T] (iU : T ⟶ Xo₂.X) (h : iU ≫ r ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK)
    (h' : iU ≫ r' ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK) : iU ≫ r = iU ≫ r' := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o', ⟨u⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) (KA l₂) (baseKA l₂) (baseKA l₂) (RingHom.id _) Xo₂.X T Xo₂.s
    (iU ≫ Xo₂.s) iU rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨w⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m he heA u
  obtain ⟨w'⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m' he' heA' u
  have hρ : jK (baseKA l).ρ = (GlobalTheory.baseOfFinerLevel hA).ρ :=
    Subtype.ext ((hjK _).trans ((GlobalTheory.coe_baseKA_rho l).trans (GlobalTheory.coe_baseKA_rho l₂).symm))
  have hζ : jK (baseKA l).ζ = (GlobalTheory.baseOfFinerLevel hA).ζ :=
    Subtype.ext ((hjK _).trans (GlobalTheory.coe_levelFieldIncl hA _).symm)
  have hu := GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H Dw l Xo (KA l₂) (GlobalTheory.baseOfFinerLevel hA) jK T
    (iU ≫ Xo₂.s) (GlobalTheory.ObjLower.lower o' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA))
    inferInstance hρ hζ
  exact hu.unique ⟨by rw [Category.assoc, h, Category.assoc], ⟨w⟩⟩ ⟨by rw [Category.assoc, h', Category.assoc], ⟨w'⟩⟩

theorem formallyUnramified_spQ (l : Level H) : FormallyUnramified (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.formallyUnramified_algebraMap.mpr (Algebra.FormallyUnramified.of_isSeparable ℚ (KA l))

theorem locallyOfFiniteType_spQ (l : Level H) : LocallyOfFiniteType (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end GlobalTheory.CoverGood

theorem GlobalTheory.CoverGood.exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  intro E _ _ _ H Dw l Xo c d hpq hl
  obtain ⟨hdvd, hM, -, -, -, ⟨he, heA⟩, hlift, -, -⟩ := hl
  obtain ⟨r₀, jK, m₀, hjK, hr₀s, he₀, heA₀, -, hrF⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h₁, h₂, hfin, het, -, -⟩ := hrF c d.c₂ d.hF.symm
  have hdiv : d.l₂.M / l.M = d.pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  rw [← hdiv] at he

  have hab : (d.r ≫ Xo.s) ≫ spMap (algebraMap ℚ (KA l)) = (d.Xo₂.s ≫ spMap jK) ≫ spMap (algebraMap ℚ (KA l)) :=
    GlobalTheory.CoverGood.hom_spQ_ext _ _
  have := GlobalTheory.CoverGood.formallyUnramified_spQ l
  have := GlobalTheory.CoverGood.locallyOfFiniteType_spQ l
  have hop : IsOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified _ hab
  have hcl : IsClosedImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  have hred₂ : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim d.Xo₂.s)).1
  have hredU : IsReduced (equalizer (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    isReduced_of_isOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
  have hagree : equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ d.r =
      equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ r₀ :=
    GlobalTheory.CoverGood.eq_of_levelMaps hdvd jK hjK d.m m₀ he heA he₀ heA₀ _
      (equalizer.condition (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
      (by rw [hr₀s])

  obtain ⟨U, iU, hop', hcl', hagree', hlU⟩ : ∃ (U : Scheme.{0}) (iU : U ⟶ d.Xo₂.X), IsOpenImmersion iU ∧
      IsClosedImmersion iU ∧ iU ≫ d.r = iU ≫ r₀ ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ d.Xo₂.X),
        x ≫ d.r ≫ Xo.s = x ≫ d.Xo₂.s ≫ spMap jK → ∃ u : Sp K ⟶ U, u ≫ iU = x :=
    ⟨_, _, hop, hcl, hagree, fun K _ x hx =>
      ⟨equalizer.lift x (by simpa only [Category.assoc] using hx), equalizer.lift_ι _ _⟩⟩
  clear hop hcl hagree hredU
  haveI := hop'; haveI := hcl'; haveI := hfin; haveI := het
  have hsp : spMap (IntermediateField.inclusion d.hF.symm.le).toRingHom ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) =
      spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨pullback iU (pullback.fst d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)),
    pullback.snd _ _ ≫ rF, pullback.fst _ _ ≫ iU, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, _, _, j, ⟨k0, hk0⟩⟩ := GlobalTheory.ZM.IsGaloisCover.exists_algClosed_point (Xo.XF c) x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ pullback.snd _ _ : Sp K ⟶ Sp c.F)
    letI : Algebra c.F K := φ.hom.toAlgebra
    letI : Algebra d.c₂.F K := ((algebraMap c.F K).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a := fun a => by
      show algebraMap c.F K (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    have hjs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := hφ.symm
    have hx₀ : (j ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, sOf, spMap, spMap, ← Spec.map_comp]
      rfl
    have hex : ∃ y : FrPt Xo c K, y.x = j ≫ pullback.fst _ _ := by
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx₀ τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist (j ≫ pullback.fst _ _)
      exact ⟨⟨_, hx₀, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
    obtain ⟨y, hy⟩ := hex
    obtain ⟨y₂, hy₂⟩ := hlift K hk y
    have hyr : y₂.x ≫ d.r = y.x := hy₂.1
    have hgood : y₂.x ≫ d.r ≫ Xo.s = y₂.x ≫ d.Xo₂.s ≫ spMap jK := by
      rw [reassoc_of% hyr, y.x_over, reassoc_of% y₂.x_over, sOf, sOf]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext t
      show algebraMap c.F K (IntermediateField.inclusion c.le t) =
        algebraMap c.F K (d.eF.symm (IntermediateField.inclusion d.c₂.le (jK t)))
      exact congrArg (algebraMap c.F K) (Subtype.ext (hjK t).symm)
    obtain ⟨u, hu⟩ := hlU K y₂.x hgood
    have hw : y₂.x ≫ d.Xo₂.s =
        spMap (algebraMap d.c₂.F K) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
      rw [y₂.x_over, sOf, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have hr₀ : y₂.x ≫ r₀ = y.x := by
      rw [← hu, Category.assoc, ← hagree', ← Category.assoc, hu, hyr]
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Sp K ⟶ d.Xo₂.XF d.c₂, w ≫ pullback.fst _ _ = y₂.x ∧
        w ≫ pullback.snd _ _ = spMap (algebraMap d.c₂.F K) :=
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨z, hz⟩ : ∃ z : Sp K ⟶ pullback iU (pullback.fst d.Xo₂.s
        (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)), z ≫ pullback.snd _ _ = w :=
      ⟨pullback.lift u w (by rw [hu, hw₁]), pullback.lift_snd _ _ _⟩
    have e : z ≫ pullback.snd _ _ ≫ rF = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, reassoc_of% hz, reassoc_of% hw₁, hr₀, hy]
      · rw [Category.assoc, Category.assoc, h₂, reassoc_of% hz, reassoc_of% hw₂, hjs, spMap, spMap,
          spMap, ← Spec.map_comp]
        rfl
    exact ⟨z k0, by rw [← Scheme.Hom.comp_apply, e, hk0]⟩
  · simp only [Category.assoc]
    rw [hagree', h₁, pullback.condition_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% h₂, hsp, pullback.condition]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_goodCover_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  first | exact @GlobalTheory.CoverGood.exists_good_cover | exact GlobalTheory.CoverGood.exists_good_cover | (intros; apply GlobalTheory.CoverGood.exists_good_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRing
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem exists_lift_finiteEtale_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  intro Y Z π hfin het hsurj K _ p x
  let P := pullback π x
  let f : P ⟶ Sp p.R := pullback.snd π x
  have : IsFinite f := inferInstance
  have : Etale f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine P := isAffine_of_isAffineHom f
  let g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R) := P.isoSpec.inv ≫ f
  let φ : CommRingCat.of p.R ⟶ Γ(P, ⊤) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hg_et : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hg_surj : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hφet : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et
  have hφff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩
  letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra
  have hBet : Algebra.Etale p.R Γ(P, ⊤) := hφet
  have hBff : Module.FaithfullyFlat p.R Γ(P, ⊤) := hφff
  have hpred : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hBred : _root_.IsReduced Γ(P, ⊤) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)
  letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra
  haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType K Γ(P, ⊤))
  have hrad : (RingHom.ker s).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))
  let q : TRing K := ⟨n, RingHom.ker s, hrad⟩
  let e : q.R ≃ₐ[K] Γ(P, ⊤) := Ideal.quotientKerAlgEquivOfSurjective hs
  let φK : p.R →ₐ[K] Γ(P, ⊤) := { φ.hom with commutes' := fun _ => rfl }
  let ι : p.R →ₐ[K] q.R := e.symm.toAlgHom.comp φK
  refine ⟨q, ι, ?_, ?_⟩
  · letI := ι.toRingHom.toAlgebra
    let e' : Γ(P, ⊤) ≃ₐ[p.R] q.R := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)
    exact ⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩
  · refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩
    have hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom := rfl
    rw [Category.assoc, Category.assoc, pullback.condition]
    change _ ≫ g ≫ x = _
    rw [← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  first | exact @GlobalTheory.exists_lift_finiteEtale_testRing | exact GlobalTheory.exists_lift_finiteEtale_testRing | (intros; apply GlobalTheory.exists_lift_finiteEtale_testRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleGeomDescent

open scoped TensorProduct

theorem eq_of_geometric_points' {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rwa [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this

theorem descent : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ _ hff het b hb
  have hBr : _root_.IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced A B
  have : Algebra.Smooth B (B ⊗[A] B) := inferInstance
  have hCr : _root_.IsReduced (B ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B (B ⊗[A] B)
  have hC : (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b := by
    refine eq_of_geometric_points' _ _ fun k _ _ χ => ?_
    have key := hb k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom) ?_
    · simpa using key
    · ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hx := (Algebra.IsEffective.of_faithfullyFlat A B b).mp (by simp [hC])
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha⟩

end GlobalTheory.EtaleGeomDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPointsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  first | exact @GlobalTheory.EtaleGeomDescent.descent | exact GlobalTheory.EtaleGeomDescent.descent | (intros; apply GlobalTheory.EtaleGeomDescent.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescends
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_lift_pt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType

theorem exists_eq_of_geom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points

theorem exists_etale_lift : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing

theorem exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := GlobalTheory.T.exists_finiteEtale_goodCover_levelMap

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev algAbove (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] : Algebra d.c₂.F S :=
  ((algebraMap c.F S).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra

theorem algAbove_compat (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] :
    letI := algAbove d S
    ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := by
  intro a
  show algebraMap c.F S (d.eF.symm (d.eF a)) = _
  rw [AlgEquiv.symm_apply_apply]

def Val (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) (p : TRing c.F) (y : FrPt Xo c p.R) (v : p.R) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (φ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap φ y z → FrOver d z₂ z →
      φ v = evR d.Xo₂ d.c₂ g z₂

def Lifts (d : DeltaDat Xo c 0) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

theorem val_unique (d : DeltaDat Xo c 0) (hL : Lifts d) {g : Rul d.Xo₂ d.c₂} {p : TRing c.F} {y : FrPt Xo c p.R}
    {v v' : p.R} (h : Val d g p y v) (h' : Val d g p y v') : v = v' := by
  by_contra hne
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstance
  have hJ : (⊥ : Ideal p.R).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (fun x ⟨m, hm⟩ => Ideal.mem_bot.2 (IsNilpotent.eq_zero ⟨m, Ideal.mem_bot.1 hm⟩))
  have hn : v - v' ∉ (⊥ : Ideal p.R).jacobson := by
    rw [hJ]
    exact fun h₀ => hne (sub_eq_zero.1 (Ideal.mem_bot.1 h₀))
  rw [Ideal.jacobson, Ideal.mem_sInf] at hn
  push Not at hn
  obtain ⟨m, ⟨-, hm⟩, ha⟩ := hn
  haveI := hm
  letI := Ideal.Quotient.field m
  let χ : p.R →ₐ[c.F] AlgebraicClosure (p.R ⧸ m) :=
    (IsScalarTower.toAlgHom c.F (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m))).comp (Ideal.Quotient.mkₐ c.F m)
  letI := algAbove d (AlgebraicClosure (p.R ⧸ m))
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ χ y
  obtain ⟨z₂, hz₂⟩ := hL _ (algAbove_compat d _) z
  have e := (h _ (algAbove_compat d _) χ z z₂ hz hz₂).trans (h' _ (algAbove_compat d _) χ z z₂ hz hz₂).symm
  apply ha
  have e' : algebraMap (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m)) (Ideal.Quotient.mk m (v - v')) = 0 := by
    have : χ (v - v') = 0 := by rw [map_sub, e, sub_self]
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (algebraMap _ _).injective).1 e')

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def ptF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by rw [y.x_over, sOf, ← Spec.map_comp]; rfl)

theorem sOf_cover (d : DeltaDat Xo c 0) (p q : TRing c.F) (ι : p.R →ₐ[c.F] q.R) :
    letI := algAbove d q.R
    spMap ι.toRingHom ≫ spMap (algebraMap c.F p.R) ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) = sOf d.c₂ q.R := by
  letI := algAbove d q.R
  simp only [sOf, spMap, ← Spec.map_comp]
  congr 1
  ext t
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact ι.commutes _

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

set_option synthInstance.maxHeartbeats 200000 in
include hpq hl in
theorem val_exists {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : ∃ v, Val d g p y v := by
  obtain ⟨Z, π, z₂, hfin, het, hsur, hr, hs⟩ := exists_good_cover E H Dw l Xo c d hpq hl
  obtain ⟨q, ι, ⟨hff, het'⟩, z, hz⟩ := exists_etale_lift _ _ π hfin het hsur c.F p (ptF y)
  letI := algAbove d q.R
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  have e1 : (z ≫ z₂) ≫ d.r = spMap ι.toRingHom ≫ y.x := by
    rw [Category.assoc, hr, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_fst]
  have e2 : (z ≫ z₂) ≫ d.Xo₂.s = sOf d.c₂ q.R := by
    rw [Category.assoc, hs, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_snd_assoc]
    exact sOf_cover d p q ι
  obtain ⟨y', hy'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ι y
  obtain ⟨y₂, -, hy₂⟩ := GlobalTheory.FrameLift.exists_frOver d (algAbove_compat d q.R) y' (z ≫ z₂) (e1.trans hy'.1.symm) e2
  have hN₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of d.Xo₂ d.c₂ (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂)
    (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂) g hg.1
  letI : Algebra p.R q.R := ι.toRingHom.toAlgebra
  haveI : IsScalarTower c.F p.R q.R := IsScalarTower.of_algebraMap_eq fun t => (ι.commutes t).symm
  obtain ⟨v, hv⟩ := exists_eq_of_geom p.R q.R hff het' (evR d.Xo₂ d.c₂ g y₂) (by
    intro k _ _ φ ψ hφψ
    letI : Algebra c.F k := (φ.comp (algebraMap c.F q.R)).toAlgebra
    letI := algAbove d k
    have hc : ∀ t : c.F, ψ (algebraMap c.F q.R t) = φ (algebraMap c.F q.R t) := fun t => by
      rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, ← hφψ, RingHom.comp_apply]
    let φ' : q.R →ₐ[c.F] k := { φ with commutes' := fun _ => rfl }
    let ψ' : q.R →ₐ[c.F] k := { ψ with commutes' := fun t => hc t }
    let φ₂ : q.R →ₐ[d.c₂.F] k := { φ with commutes' := fun _ => rfl }
    let ψ₂ : q.R →ₐ[d.c₂.F] k := { ψ with commutes' := fun t => hc _ }
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
    obtain ⟨w', hw'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ψ' y'
    obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
    obtain ⟨w₂', hw₂'⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ ψ₂ y₂
    have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
    have o₂ : FrOver d w₂' w' := GlobalTheory.FrameLift.frOver_map d (ψ := ψ') (ψ₂ := ψ₂) rfl hy₂ hw' hw₂'
    have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
    have t₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι ψ' hy' hw'
    have ec : ψ'.comp ι = φ'.comp ι := AlgHom.ext fun t => (RingHom.congr_fun hφψ t).symm
    rw [ec] at t₂
    obtain rfl : w = w' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (φ'.comp ι) y).1 w w' t₁ t₂
    have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
    have k₂ := hN₂ q.R k ψ₂ y₂ w₂' hw₂'
    have k₃ := hF k (algAbove_compat d k) w₂ w₂' w o₁ o₂
    exact k₁.symm.trans (k₃.trans k₂))
  refine ⟨v, fun k _ _ _ _ hk φ zz zz₂ hzz hzz₂ => ?_⟩
  have hft : Algebra.FiniteType p.R q.R := by haveI := het'; infer_instance
  obtain ⟨φ₁, hφ₁⟩ := exists_lift_pt p.R q.R hff hft k φ.toRingHom
  have hc : ∀ t : c.F, φ₁ (algebraMap c.F q.R t) = algebraMap c.F k t := fun t => by
    rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, hφ₁]
    exact φ.commutes t
  let φ' : q.R →ₐ[c.F] k := { φ₁ with commutes' := hc }
  have hc₂ : ∀ t : d.c₂.F, φ₁ (algebraMap d.c₂.F q.R t) = algebraMap d.c₂.F k t := fun t => by
    show φ₁ (algebraMap c.F q.R (d.eF.symm t)) = _
    rw [hc, ← hk, AlgEquiv.apply_symm_apply]
  let φ₂ : q.R →ₐ[d.c₂.F] k := { φ₁ with commutes' := hc₂ }
  obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
  have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
  have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
  have ec : φ'.comp ι = φ := AlgHom.ext fun t => RingHom.congr_fun hφ₁ t
  rw [ec] at t₁
  obtain rfl : w = zz := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ φ y).1 w zz t₁ hzz
  have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
  have k₃ := hF k hk w₂ zz₂ w o₁ hzz₂
  rw [← k₃, k₁, ← hv]
  exact (RingHom.congr_fun hφ₁ v).symm

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem lifts_of_isLev (d : DeltaDat Xo c 0) (hl : d.IsLev) : Lifts d := by
  obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hl
  exact hlift


open Classical in
def ruleDown (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Rul Xo c := fun p y =>
  if h : ∃ v, Val d g p y v then h.choose else 0

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

include hpq hl in
theorem val_ruleDown {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : Val d g p y (ruleDown d g p y) := by
  have h := val_exists d hpq hl hg hF p y
  have e : ruleDown d g p y = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

include hpq hl in
theorem ruleDown_mem {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) : ruleDown d g ∈ sec Xo c a n := by
  have hV := val_ruleDown d hpq hl hg hF
  have hL := lifts_of_isLev d hl
  refine ⟨fun p q φ y z hz => ?_, fun p t y y' hb => ?_⟩
  · refine val_unique d hL (hV q z) fun k _ _ _ _ hk χ w w₂ hw hw₂ => ?_
    have := hV p y k hk (χ.comp φ) w w₂ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ χ hz hw) hw₂
    rw [← this, AlgHom.comp_apply]
  · refine val_unique d hL (hV p y') fun k _ _ _ _ hk φ z' z₂' hz' hz₂' => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ y
    have hbz := frBorBC (Xo := Xo) (c := c) p.R k φ t y y' z z' hb hz hz'
    obtain ⟨z₂, hz₂⟩ := hL k hk z
    have ex : z₂.x ≫ d.r = z'.x := by rw [hbz.1, ((GlobalTheory.FrameLift.frOver_iff d _ _).1 hz₂).1]
    obtain ⟨z₂'', hx'', hz₂''⟩ := GlobalTheory.FrameLift.exists_frOver d hk z' z₂.x ex z₂.x_over
    have hb₂ := GlobalTheory.FrameLift.frBor_lift d GlobalTheory.abelianSchemeLaws_all.1.globalFns hz₂ hz₂'' hx'' hbz
    have w₁ := GlobalTheory.CoverSec.wtRed d.Xo₂ d.c₂ a n g hg k _ z₂ z₂'' hb₂
    have w₂ := hF k hk z₂' z₂'' z' hz₂' hz₂''
    have w₃ := hV p y k hk φ z z₂ hz hz₂
    rw [w₂, w₁, ← w₃, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]

end GlobalTheory.CoverDesc

section Main

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem GlobalTheory.CoverDesc.section_descends :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  intro E _ _ _ H Dw l Xo c d hpq hl a n g hg hF
  have hm := GlobalTheory.CoverDesc.ruleDown_mem d hpq hl hg hF
  refine ⟨_, hm, fun k _ _ _ _ hk y₂ y ho => ?_⟩
  obtain ⟨p, φ, y₀, hy₀⟩ := GlobalTheory.TransferCompare.allTest_framed Xo c k y
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hm.1 hy₀]
  exact (GlobalTheory.CoverDesc.val_ruleDown d hpq hl hg hF p y₀ k hk φ y y₂ hy₀ ho).symm

end Main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescendsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_constant_on_fibres_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  first | exact @GlobalTheory.CoverDesc.section_descends | exact GlobalTheory.CoverDesc.section_descends | (intros; apply GlobalTheory.CoverDesc.section_descends <;> assumption)
end
