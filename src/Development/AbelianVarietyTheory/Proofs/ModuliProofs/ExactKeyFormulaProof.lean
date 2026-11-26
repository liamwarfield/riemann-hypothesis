module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaOfConnFam
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ConnFamHolds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianSchemeUniformisationExistsGeometric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExtendValuation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeIffOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyFam

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.KeyFam.keyFormula_holds : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.KeyFormula :=
  _root_.GlobalTheory.keyFormula_of_connFam
    (_root_.GlobalTheory.KeyFam.connFam_of_polFam _root_.GlobalTheory.abelianSchemeLaws_all.1
      _root_.GlobalTheory.abelianSchemeLaws_all.2
      (_root_.GlobalTheory.KeyFam.polFam _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.abelianSchemeLaws_all.2
        _root_.GlobalTheory.thetaUnifAV_closed _root_.GlobalTheory.torusAlgebraic_holds))

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProofStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exactKeyFormula_proof : KeyFormula := by
  first | exact @GlobalTheory.KeyFam.keyFormula_holds | exact GlobalTheory.KeyFam.keyFormula_holds | (intros; apply GlobalTheory.KeyFam.keyFormula_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem zhGeo_of_semistableReduction :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := fun S => by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.allSixLaws
  exact GlobalTheory.T.semiAbelianScheme_uniformisation_exists_geometric GlobalTheory.homExtension_semiAbelian_dvr S GlobalTheory.ZH.thmU_and_uTors.1 L L2 L3 L4 L5
    GlobalTheory.ZH.thmU_and_uTors.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReductionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinGeometric_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := by
  first | exact @GlobalTheory.zhGeo_of_semistableReduction | exact GlobalTheory.zhGeo_of_semistableReduction | (intros; apply GlobalTheory.zhGeo_of_semistableReduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubring
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.GoodTrait
set_option linter.style.haveILetI false

theorem exists_unit_prime (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + -((5 : ℕ) : O)) := by
    have : ((3 : ℕ) : O) * 2 + -((5 : ℕ) : O) = 1 := by push_cast; norm_num
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, (IsUnit.neg_iff _).1 h⟩

theorem norm_eq_one_of_isUnit {W C : Type} [CommRing W] [NormedField C] (f : W →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {x : W}
    (hx : IsUnit x) : ‖f x‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h : ‖f x‖ * ‖f y‖ = 1 := by rw [← norm_mul, ← map_mul, hy, map_one, norm_one]
  have h₁ := hf x
  have h₂ := hf y
  have h₃ := norm_nonneg (f x)
  nlinarith

theorem exists_valuationSubring {K C : Type} [Field K] [NormedField C] [IsUltrametricDist C] (f : K →+* C) :
    ∃ S : ValuationSubring K, (∀ x, x ∈ S ↔ ‖f x‖ ≤ 1) ∧ ∀ x, S.valuation x = 1 ↔ ‖f x‖ = 1 := by
  let v := (NormedField.valuation (K := C)).comap f
  refine ⟨v.valuationSubring, fun x => ?_, fun x => ?_⟩
  · rw [Valuation.mem_valuationSubring_iff]
    exact Iff.rfl
  · rw [← (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one]
    exact NNReal.coe_inj.symm

theorem isDominant_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (spMap f) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap f)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot f).1 hf]
  exact bot_le

set_option maxHeartbeats 1000000 in
theorem range_subset_abLocus : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ThetaInt Y g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → IsUnit (φ (g PowerSeries.X)) → Set.range χ ⊆ abLocus Y.t.G := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO R₁ _ _ g y₁ _ _ _ hT hy W _ _ _ hW φ gam hgam χ hχ hu
  haveI : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField
      exact inferInstance
    · exact inferInstance
  obtain ⟨n, hn, hodd, hnu⟩ := exists_unit_prime O'
  obtain ⟨hdvr, -, hch⟩ := id hW
  obtain ⟨C, _, _, _, _, alg, -, -, hC⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  let iC : W →+* C := (algebraMap (FractionRing W) C).comp (algebraMap W _)
  have hiC : Function.Injective iC := (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  haveI : CharZero C := charZero_of_injective_ringHom hiC
  obtain ⟨o, ho, hθ⟩ := hT
  haveI := o.charZero
  let Γ : AlgebraicClosure (FractionRing R₁) →+* C :=
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).toRingHom
  have hΓ : Γ.comp (algebraMap (FractionRing R₁) _) = (algebraMap (FractionRing W) C).comp gam := by
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    exact RingHom.ext fun x => (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).commutes x
  have hΓ' : ∀ r, Γ (((algebraMap (FractionRing R₁) _).comp (algebraMap R₁ _)) r) = iC (φ r) := fun r => by
    have := DFunLike.congr_fun hΓ (algebraMap R₁ _ r)
    simp only [RingHom.comp_apply, hgam] at this
    exact this
  obtain ⟨o', hext, hth, -⟩ := GlobalTheory.FullExtend.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D _ C Γ o
  have e₀ : spMap Γ ≫ spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ =
      spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ := by
    rw [← Category.assoc, ← spMap_comp', hΓ, spMap_comp', Category.assoc]
  have bF : c.F →+* AlgebraicClosure (FractionRing R₁) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
      ((spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁) ≫ pullback.snd _ _).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing R₁)))).hom).hom
  have ho' := (GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y _ bF).2.2 C Γ _ o o' ho hext
  rw [e₀] at ho'
  have e₁ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp' (algebraMap R₁ _) gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp' φ (algebraMap W _)))
  have e₂ : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
  obtain ⟨M, f, χ', mp, hf, hfC, hχ', -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y C W hW hC
    (FractionRing W) (algebraMap (FractionRing W) C) (fun _ => rfl) (spMap gam ≫ y₁)
    (φ.comp (g.comp ((PowerSeries.C (R := O')).comp b))) (by
      rw [e₂, Category.id_comp, Category.assoc, hy, spMap_comp', spMap_comp', spMap_comp', ← Category.assoc, e₁,
        Category.assoc]) o' ho'
  obtain ⟨v, hv, hint⟩ := hθ n 2 hn hodd hnu one_le_two
  obtain ⟨S, hS, hS'⟩ := exists_valuationSubring Γ
  obtain ⟨a₁, -, a₃⟩ := hint S fun r => by rw [hS, hΓ']; exact hC.1 _
  have a₄ := a₃ (by rw [hS', hΓ']; exact norm_eq_one_of_isUnit iC hC.1 hu)
  have hnC : ‖(n : C)‖ = 1 := by
    have := norm_eq_one_of_isUnit iC hC.1 (hnu.map (φ.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, map_natCast] at this
  have hprop : IsProper M.t.G.hom := GlobalTheory.T.isProper_of_theta_unit_in_every_coset h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D C o' M n 2 hn hodd hnC le_rfl _ (hth _ _ hv)
    (fun x => (hS _).1 (a₁ x)) fun x => (a₄ x).imp fun h hh => (hS' _).1 hh
  let jC : M.W →+* C := (algebraMap (FractionRing M.W) C).comp (algebraMap M.W _)
  have hjC : Function.Injective jC := (algebraMap (FractionRing M.W) C).injective.comp (IsFractionRing.injective M.W _)
  have hjf : jC.comp f = iC := RingHom.ext hfC
  have hfi : Function.Injective f := Function.Injective.of_comp (f := jC) (by rw [← RingHom.coe_comp, hjf]; exact hiC)
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have := isDominant_spMap jC hjC
  have e₃ : χ' = spMap f ≫ χ := by
    refine ext_of_isDominant (spMap jC) ?_
    have e₄ : spMap jC = jFK (R := M.W) C ≫ jK M.W := spMap_comp' _ _
    have e₅ : spMap iC = spMap (algebraMap (FractionRing W) C) ≫ jK W := spMap_comp' _ _
    rw [← Category.assoc, ← spMap_comp', hjf, e₅, e₄, Category.assoc, hχ', Category.assoc, Category.assoc, hχ]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := hf.to_isIntegral.comap_surjective hfi x
  have h := (abLocus_pullback abLocusOne Y.t.semi mp.cart.1 x').2 fun K _ _ t _ => inferInstance
  rw [e₃] at h
  exact h

end GlobalTheory.Ex.GoodTrait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFramePull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.Mono

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨_, fun Z r z J hJ => ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem isFrame_pull {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂)
    (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) (x : Sp (FractionRing R₁) ⟶ S)
    (x' : Sp (FractionRing R₂) ⟶ S) (hx : spMap h' ≫ x = x') {n : ℕ} (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)))
    (hf : GlobalTheory.LN.IsFrame G L N x f) : ∃ f', GlobalTheory.LN.IsFrame (n := n) G L N x' f' := by
  let ρ : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap h') hx
  have e : ∀ _ : Fin 1, (ρ ▷ G).left ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left := fun _ => by
    rw [← Over.comp_left, whiskerRight_snd]
  choose f' hf' using fun i => exists_pull (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk x) G).left)
    (φ' := fun _ : Fin 1 => (snd (Over.mk x') G).left) (ε := fun _ => (N : ℤ)) (f i) (ρ ▷ G).left e
  refine ⟨f', fun W _ _ _ hW φ gam hg χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ x = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx, hχ]
  obtain ⟨b', hb, hs⟩ := hf W hW (φ.comp h) (gam.comp h') (fun r => by
    rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ hχ'
  refine ⟨b', hb, fun i => ?_⟩
  obtain ⟨s, h₁, h₂⟩ := hs i
  refine ⟨s, fun z J hJ => (h₁ z J hJ).trans ?_, h₂⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  refine congrArg _ (Eq.trans ?_ (hf' i _ _ z J hJ).symm)
  have hc : (Over.homMk (spMap (gam.comp h')) hχ' : Over.mk (jK W ≫ χ) ⟶ Over.mk x) =
      (Over.homMk (spMap gam) hχ : Over.mk (jK W ≫ χ) ⟶ Over.mk x') ≫ ρ := Over.OverMorphism.ext (sp_comp h' gam)
  rw [hc, comp_whiskerRight, Over.comp_left]

theorem mono : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), h.Finite → (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) → (GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.LN.TraitData Y a (h.comp g) (spMap h' ≫ y₁)) ∧ (RealAt Y a g y₁ → RealAt Y a (h.comp g) (spMap h' ≫ y₁)) ∧ ∀ (N n : ℕ) f, GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N (y₁ ≫ Y.j) f → ∃ f', GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N ((spMap h' ≫ y₁) ≫ Y.j) f' := by
  intro _ _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ R₁ _ _ g y₁ _ _ _ R₂ _ _ h h' hfin hh
  refine ⟨fun hT => ⟨?_, fun W _ _ _ hW φ gam hg χ hχ => ?_⟩, fun hR => hR.comp h h' hfin hh,
    fun N n f hf => isFrame_pull _ _ N h h' hh _ _ (Category.assoc _ _ _).symm f hf⟩
  · have e : spMap h' ≫ jK R₁ = jK R₂ ≫ spMap h :=
      (sp_comp (algebraMap R₁ _) h').symm.trans ((congrArg spMap (RingHom.ext hh)).trans (sp_comp h (algebraMap R₂ _)))
    rw [Category.assoc, hT.1, sp_comp, ← Category.assoc, e]
    simp only [Category.assoc]
  · exact hT.2 W hW (φ.comp h) (gam.comp h') (fun r => by rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ
      (by rw [sp_comp, Category.assoc, ← hχ, Category.assoc])

end GlobalTheory.Ex.Mono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLaws
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcFam : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → GlobalTheory.LN.ArcFamSt := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb m hm hmu
  have pt := GlobalTheory.ArcPoint.exists_point h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have bad := GlobalTheory.Ex.Trait.hasArcData_at_trait h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have good := GlobalTheory.Ex.GoodTrait.range_subset_abLocus h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have fr₁ := GlobalTheory.T.exists_single_polarisation_generator_all_traits h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have frm := GlobalTheory.OneBasis.exists_isFrame_pow_sq h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have mono := GlobalTheory.Ex.Mono.mono h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  obtain ⟨R₁, _, _, g, y₁, gi, gf, n₁, hy, hr, ht⟩ := pt
  have td : GlobalTheory.LN.TraitData Y a g y₁ := ⟨hy, fun W _ _ _ hW φ gam hg χ hχ =>
    ⟨good R₁ g y₁ gi gf n₁ ht hy W hW φ gam hg χ hχ, bad R₁ g y₁ gi gf n₁ hr hy W hW φ gam hg χ hχ⟩⟩
  obtain ⟨R₂, _, _, h, h', hi, hf, n₂, hh, hθ⟩ := fr₁ R₁ g y₁ gi gf n₁ td ht
  obtain ⟨td₂, hr₂, -⟩ := mono R₁ g y₁ gi gf n₁ R₂ h h' hf hh
  have gi₂ : Function.Injective (h.comp g) := hi.comp gi
  have gf₂ : (h.comp g).Finite := hf.comp gf
  obtain ⟨R₃, _, _, k, k', ki, kf, n₃, kk, hfm⟩ :=
    frm R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ (td₂ td) (hr₂ hr) hθ m hm hmu
  obtain ⟨td₃, -, hfr⟩ := mono R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ R₃ k k' kf kk
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨f', hf'⟩ := hfr 1 1 _ hθ
  refine ⟨R₃, inferInstance, inferInstance, k.comp (h.comp g), spMap k' ≫ spMap h' ≫ y₁, ki.comp gi₂, kf.comp gf₂, n₃,
    td₃ (td₂ td), ⟨f' 0, ?_⟩, hfm⟩
  have e : (fun _ : Fin 1 => f' 0) = f' := funext fun i => by rw [Subsingleton.elim i 0]
  rw [e]; exact hf'
end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLawsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arc_family_point_with_frames_of_laws : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → GlobalTheory.LN.ArcFamSt := by
  first | exact @GlobalTheory.Ex.arcFam | exact GlobalTheory.Ex.arcFam | (intros; apply GlobalTheory.Ex.arcFam <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem arcFam_closed : GlobalTheory.LN.ArcFamSt :=
  GlobalTheory.T.exists_arc_family_point_with_frames_of_laws GlobalTheory.lawsAndExpansions GlobalTheory.allSixLaws.2.2.2.2.2 GlobalTheory.T.uniformisation_triples_complete_DVR_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing
    GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.1 GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.2 GlobalTheory.thetaUnifAV_closed

end GlobalTheory
end
