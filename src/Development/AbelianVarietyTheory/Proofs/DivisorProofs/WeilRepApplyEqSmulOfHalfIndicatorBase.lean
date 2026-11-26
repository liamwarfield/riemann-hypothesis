module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullModelLaw

theorem om_apply_eq_smul_pull : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∀ (p : GA D S × GA D T) (κ : ℂ), (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull p Φ)) → om p f₀ = κ • Tm (actPull p (halfInd e (latAll S T ΛS ΛT))) → ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → om p (Tm Φ) = κ • Tm (actPull p Φ) := by
  intro D ψ S T χS χT om hW ΛS ΛT hsS hsT Q e he f₀ hf₀ _ Tm hTm p κ hsb hκ Φ hΦ
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hthm : ∀ Ψ, IsSBHalf e (latAll S T ΛS ΛT) Ψ → IsThetaFunO ψ S T (Tm Ψ) :=
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hsS hsT e hee hinf f₀ hf₀ Tm hTm
  have hqp : ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) * p = 1 := Prod.ext (by simp) (by simp)
  have hpq : p * ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) = 1 := Prod.ext (by simp) (by simp)
  have hback : ∀ x : WO S T, actO S T p.1⁻¹ p.2⁻¹ (actO S T p.1 p.2 x) = x := fun x => by
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have hsmul : ∀ (w : WO S T) (c : ℂ) (F : WO S T → ℂ), c • heisO ψ S T w F = heisO ψ S T w (c • F) :=
    fun w c F => by
      funext t
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
  let L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := actPull p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := κ • ((om (p.1⁻¹, p.2⁻¹)).comp (Tm.comp L))
  have hTm'ap : ∀ Ψ, Tm' Ψ = κ • om (p.1⁻¹, p.2⁻¹) (Tm (actPull p Ψ)) := fun Ψ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf e (actO S T p.1 p.2 x) := (isHalf_actO p.1 p.2 x).2 hx
      have e1 : actPull p (fun t => Ψ (t + x)) = fun t => actPull p Ψ (t + actO S T p.1 p.2 x) := by
        funext t
        show Ψ (actO S T p.1⁻¹ p.2⁻¹ t + x) = Ψ (actO S T p.1⁻¹ p.2⁻¹ (t + actO S T p.1 p.2 x))
        rw [actO_add, hback]
      rw [hTm'ap, hTm'ap, e1, hTm.trans _ (hsb Ψ hΨ) _ hx',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · have hy' : IsHalf (cA D e) (actO S T p.1 p.2 y) := (isHalf_actO p.1 p.2 y).2 hy
      have e1 : actPull p (fun t => ψ (symplO S T t y) * Ψ t) =
          fun t => ψ (symplO S T t (actO S T p.1 p.2 y)) * actPull p Ψ t := by
        funext t
        show ψ (symplO S T (actO S T p.1⁻¹ p.2⁻¹ t) y) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t) =
          ψ (symplO S T t (actO S T p.1 p.2 y)) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t)
        conv_lhs => rw [← hback y]
        rw [Formalism.IndefR.Eqv.symplO_actO]
      rw [hTm'ap, hTm'ap, e1, hTm.modul _ (hsb Ψ hΨ) _ hy',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · rw [one_smul, hTm'ap, ← map_smul, ← hκ, ← Module.End.mul_apply, ← map_mul, hqp, map_one,
        Module.End.one_apply]
  have e3 : Tm Φ = Tm' Φ := GlobalTheory.PlaceVec.placeModel_unique hW.std hsS hsT hee hinf hTm hTm' hΦ
  rw [e3, hTm'ap, map_smul, ← Module.End.mul_apply, ← map_mul, hpq, map_one, Module.End.one_apply]

end GlobalTheory.PullModelLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∀ (p : GA D S × GA D T) (κ : ℂ), (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull p Φ)) → om p f₀ = κ • Tm (actPull p (halfInd e (latAll S T ΛS ΛT))) → ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → om p (Tm Φ) = κ • Tm (actPull p Φ) := by
  first | exact @GlobalTheory.PullModelLaw.om_apply_eq_smul_pull | exact GlobalTheory.PullModelLaw.om_apply_eq_smul_pull | (intros; apply GlobalTheory.PullModelLaw.om_apply_eq_smul_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsRational

open Polynomial

theorem exists_ext_factor (K R : Type) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (φ : R →+* Ω), φ.comp (algebraMap K R) = σ.comp (algebraMap K K'') →
        ∃ φ'' : R →+* K'', σ.comp φ'' = φ := by
  classical
  let b := Module.finBasis K R
  let f : K[X] := ∏ i, minpoly K (b i)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b i))
  have hroot : ∀ r ∈ Set.range b, aeval r f = 0 := by
    rintro _ ⟨i, rfl⟩
    simp only [f, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K _)
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K'' Ω _ _ _ _ _ σ φ hφ
  have hs : (f.map (algebraMap K K'')).Splits := by
    rw [IsScalarTower.algebraMap_eq K f.SplittingField K'', ← Polynomial.map_map]
    exact (SplittingField.splits f).map _
  have hmem : ∀ r, φ r ∈ σ.range := by
    intro r
    have hr : r ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      refine hs.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) ?_
      rw [Polynomial.map_map, ← hφ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, hroot x hx, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ⟨algebraMap K K'' c, ?_⟩ hx
      rw [← RingHom.comp_apply, ← hφ, RingHom.comp_apply]
  let e := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict σ.range hmem), ?_⟩
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict σ.range hmem r))

theorem exists_ext_points (K : Type) [Field K] (T : Over (Sp K)) (hT : IsFinite T.hom) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
        (σ : K'' →+* Ω) (t : Sp Ω ⟶ T.left), t ≫ T.hom = spMap (σ.comp (algebraMap K K'')) →
        ∃ w : Sp K'' ⟶ T.left, spMap σ ≫ w = t := by
  haveI : IsAffine T.left := isAffine_of_isAffineHom T.hom
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(T.left, ⊤) := by
    have : IsFinite (Spec.map ρ) := by rw [hρ]; infer_instance
    exact (IsFinite.SpecMap_iff ρ).1 this
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_factor K Γ(T.left, ⊤)
  refine ⟨K', _, _, hfin, fun K'' Ω _ _ _ _ _ σ t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ T.left.isoSpec.hom)
  have h1 : φ.hom.comp (algebraMap K Γ(T.left, ⊤)) = σ.comp (algebraMap K K'') := by
    have : Spec.map (ρ ≫ φ) = Spec.map (CommRingCat.ofHom (σ.comp (algebraMap K K''))) := by
      rw [Spec.map_comp, hφ, hρ, Category.assoc, Iso.hom_inv_id_assoc, ht]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨φ'', hφ''⟩ := H K'' Ω σ φ.hom h1
  refine ⟨Spec.map (CommRingCat.ofHom φ'') ≫ T.left.isoSpec.inv, ?_⟩
  have e : CommRingCat.ofHom φ'' ≫ CommRingCat.ofHom σ = φ := by
    ext r
    exact congrArg (fun g => g r) hφ''
  rw [← Category.assoc, spMap, ← Spec.map_comp, e, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TorsRational
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullPres

theorem fnOf_app {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} (h : genericPoint X ∈ q ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (q ⁻¹ᵁ U) h ((q.app U).hom a) =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) h) a) := by
  rw [← algebraMap_germ h, ← algebraMap_germ (show q (genericPoint X) ∈ U from h),
    functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply]

theorem fnOf_res_pullU {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} {V : X.Opens} (le : V ≤ q ⁻¹ᵁ U) (hV : genericPoint X ∈ V) (u : Γ(W, U)ˣ) :
    fnOf V hV (res le (pullU q U u)).val =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) (le hV)) u.val) :=
  (fnOf_resG le hV _).trans (fnOf_app q (le hV) _)

theorem presents_pull {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W)
    (hDE : ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) :
    Presents D ((toLB E).pull q) fun J => Units.map (functionFieldMap q).toMonoidHom (J PUnit.unit).1.2 := by
  refine ⟨pull_isLB (isLB_toLB E) q, fun J K h => ?_, fun J x hx => hDE _ _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx)) x rfl⟩
  have le : ((toLB E).pull q).U J ⊓ ((toLB E).pull q).U K ≤
      q ⁻¹ᵁ ((toLB E).U (J PUnit.unit) ⊓ (toLB E).U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hg : ((toLB E).pull q).g J K = res le (pullU q _ ((toLB E).g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  rw [hg, fnOf_res_pullU, fnOf_toLB_g]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀]
  exact (div_mul_cancel₀ _ ((map_ne_zero _).2 (Units.ne_zero _))).symm

theorem pull_cls_toLB : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  intro X W _ _ q _ D E hDE
  rw [← cls_pull (isLB_toLB E) q (pull_isLB (isLB_toLB E) q), ← (presents_pull q D E hDE).toPic_eq,
    toPic_apply]

end GlobalTheory.Cartier.PullPres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  first | exact @GlobalTheory.Cartier.PullPres.pull_cls_toLB | exact GlobalTheory.Cartier.PullPres.pull_cls_toLB | (intros; apply GlobalTheory.Cartier.PullPres.pull_cls_toLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodWeightDictionary
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.GoodWCore

theorem fullLat_congr {K Rg : Type} [Field K] [NumberField K] [CommRing Rg] [Algebra K Rg] [Algebra (𝓞 K) Rg]
    [IsScalarTower (𝓞 K) K Rg] {C C' : Submodule K Rg} (h : C = C')
    {Vs : HeightOneSpectrum (𝓞 K) → Set (Rg → EReal)} {hV : ∀ la, ∀ v ∈ Vs la, IsVal la v}
    (hl : FullLat C Vs hV) : FullLat C' Vs hV := by
  subst h
  exact hl


set_option maxHeartbeats 8000000 in
theorem goodW_core {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j)
    (hl : Submodule.IsFullLattice T.Q.c.F (supLat (T.cuspA j (wtA w) w.n))) :
    GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) := by
  have hlat : Submodule.IsFullLattice T.Q.c.F (AllWt.latW (T.U j) (wtZ (wtA w) w.n)) := by
    rw [AllWt.latW, cuspW_wtZ]
    exact hl
  have hspan := Submodule.IsFullLattice.span_eq_top (self := hlat)
  refine ⟨?_, hlat.fg, hspan⟩
  have : FiniteDimensional T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n)) := by
    obtain ⟨s, hs⟩ := hlat.fg
    refine ⟨⟨s, ?_⟩⟩
    rw [← hspan, ← hs, Submodule.span_span_of_tower]
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  set σ := goodOf T.Q.c v.embedding with hσdef
  have hσ : GoodEmb T.Q.c σ := goodEmb_goodOf _ _
  have hD : Dom (wtA w) w.n := dom_wtA w
  let ι := LinearEquiv.ofEq _ _ (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n)
  let cf : ℝ := lieFac (T.Q.Dw j) (xiR D) (wtA w)
  have hcf : 0 < cf := lieFac_pos _ _ _
  let J := uniformisationL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ)
    (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD)
  let Φ : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n) →+ MeasureTheory.Lp ℂ 2 (muQ1 (T.V j σ)) :=
    AddMonoidHom.mk' (fun f => (cf : ℂ) • J (ι f)) (fun f g => by rw [map_add (f := _), map_add (f := _), smul_add])
  have hΦ : ∀ f, Φ f = (cf : ℂ) • J (ι f) := fun _ => rfl
  have hs : ∀ (a : T.Q.c.F) f, Φ (a • f) = σ a • Φ f := fun a f => by
    rw [hΦ, hΦ, map_smul, map_smulₛₗ]
    exact smul_comm _ _ _
  refine ⟨_, inferInstance, inferInstance, Φ, ?_, ?_, ?_⟩
  · by_cases hg : GoodEmb T.Q.c v.embedding
    · left
      intro a f
      have e' : σ a = v.embedding a := by
        rw [hσdef]; unfold goodOf; rw [ite_eq_left hg]
      rw [hs, e']
    · right
      intro a f
      have e' : σ a = starRingEnd ℂ (v.embedding a) := by
        rw [hσdef]; unfold goodOf; rw [ite_eq_right hg]; rfl
      rw [hs, e']
  · intro f
    have hf : (f : Rul (T.Q.Xo j) T.Q.c) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (ι f).2
    have e1 : normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) v.embedding f =
        petAt (T.U j σ) (xiR D) (T.V j σ) (T.dict j σ) (muQ1 (T.V j σ)) (wtZ (wtA w) w.n) f := rfl
    rw [e1, petAt_wtZ (T.U j) (xiR D) (T.V j σ) (T.dict j σ) (T.mu j σ) (hT.muUnit j hj σ hσ) _ _
      (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD) hf, l2C, dite_eq_left hf, hΦ, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hcf.le]
    rfl
  · intro m e he
    have hi : LinearIndependent T.Q.c.F fun k => ι (e k) := he.map' ι.toLinearMap ι.ker
    have h1 := (GlobalTheory.VolPairExists.adelic_linearIndependent D T hT j hj σ hσ (wtA w) w.n hD).2 m _ hi
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro c hc
    refine h1 c ?_
    have : (cf : ℂ) • ∑ k, c k • J (ι (e k)) = 0 := by
      rw [Finset.smul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hc
      rw [hΦ]
      exact smul_comm _ _ _
    exact (smul_eq_zero.1 this).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')

end GlobalTheory.CovTop.GoodWCore

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactor
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvV

theorem irrV : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hnr N hAN hNS hstab
  obtain ⟨ν₀, β₀, ι, ⟨t, ht⟩, s1, u1, s2, u2, hbij, hg1, hg2, hh⟩ := GlobalTheory.T.exists_local_characters_linear_bar hP F E σ B a a' G X om om' hT v hv
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hν : ν₀ (unifAt v) ≠ 1 := by
    have h1 := hnr t 1 one_ne_zero
    rw [zpow_one] at h1
    rcases ht with rfl | rfl
    · exact h1
    · intro h; apply h1; simpa using congrArg (·⁻¹) h
  set augL : Submodule ℂ (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) := Submodule.span ℂ
    {z | ∃ (g : GL (Fin a) (Fv F v)) (Ψ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ - Ψ} with haugL
  have augS : augAt om v ≤ SB _ :=
    Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ
  have c1 : augAt om v ≤ augL.comap ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    obtain ⟨g', hg'⟩ := hg1 g hg
    show ι (φ₁ - φ) ∈ augL
    rw [map_sub, hg' φ hφ φ₁ hφ₁ hA]
    exact Submodule.subset_span ⟨g', ι φ, hbij.mapsTo hφ, rfl⟩
  have c2 : augL ≤ (augAt om v).map ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
    obtain ⟨g, hg, hgg⟩ := hg2 g'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hgg φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, ?_⟩
    rw [map_sub, he]
  have c3 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ augL → φ ∈ augAt om v := by
    intro φ hφ h
    obtain ⟨ψ, hψ, he⟩ := c2 h
    rwa [← hbij.injOn (augS hψ) hφ he]
  set N' := N.map ι with hN'
  have n1 : augL ≤ N' := c2.trans (Submodule.map_mono hAN)
  have n2 : N' ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rintro _ ⟨φ, hφ, rfl⟩; exact hbij.mapsTo (hNS hφ)
  have n3 : ∀ (h' : GL (Fin (a + a')) (Fv F v)), ∀ Ψ ∈ N', GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' Ψ ∈ N' := by
    rintro h' _ ⟨φ, hφ, rfl⟩
    obtain ⟨h, hhW, hk⟩ := hh h'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hk φ (hNS hφ)
    exact ⟨φ₁, hstab h hhW φ hφ φ₁ hφ₁ hA, he⟩
  have hle : a ≤ a + a' := Nat.le_add_right a a'
  rcases GlobalTheory.T.span_character_translates_coinvariant hP.bernsteinUnitaryProductIrreducible (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 s2 u2 N' n1 n2 n3 with hA | hB
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    have hφS := hNS hφ
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : Ψ₀ ∈ N' := by
      have := N'.sub_mem (Submodule.mem_map_of_mem hφ) (n1 hd)
      rwa [sub_sub_cancel] at this
    have h1 := hA Ψ₀ h0 hr
    refine c3 φ hφS ?_
    have := augL.add_mem hd h1
    rwa [sub_add_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφS => ?_)
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : ι φ ∈ N' := by
      have := N'.add_mem (n1 hd) (hB Ψ₀ hΨ₀ hr)
      rwa [sub_add_cancel] at this
    obtain ⟨n, hn, he⟩ := h0
    rwa [← hbij.injOn (hNS hn) hφS he]

end GlobalTheory.IrrCoinvV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactorStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_submodule_first_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  first | exact @GlobalTheory.IrrCoinvV.irrV | exact GlobalTheory.IrrCoinvV.irrV | (intros; apply GlobalTheory.IrrCoinvV.irrV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CoreSlope

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem coreAt_of (C : ℝ) (hg : GramAt p i) (hm : MeasAt p i C) (hr : RatAt p i) : CoreAt p i (2 * C) := by
  obtain ⟨ι, hι, hli, himg⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hTC : IsTotallyComplex p.T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hc : ∀ σ x, nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := fun σ x => by
    simp only [nrmK]
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hfg : (latTypeK p.fw p.F.lv2 i).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hg.2.2.2.2.1
    exact Submodule.FG.of_le_of_isNoetherian (T := latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n)) inf_le_left
  have hN : ∀ σ' x, nrmR p.R.toRealDat i σ' (ι x) ≤ Real.exp (C * unitE p) * nrmK p.fw i (σ'.comp (algebraMap p.T.Q.c.F D.what₂.LL)) x := by
    intro σ' x
    obtain ⟨c, hc0, hcl, hcf⟩ := hm σ'
    obtain ⟨h, hx⟩ := hι x
    rw [hx, hcf ⟨x, h⟩]
    have hce : c ≤ Real.exp (C * unitE p) := by
      calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
        _ ≤ Real.exp (C * unitE p) := Real.exp_le_exp.2 ((le_abs_self _).trans hcl)
    exact mul_le_mul_of_nonneg_right hce (petAt_nonneg _ _ _ _ _ _ _)
  have hS : latType p.R.toRealDat p.F.lv2 i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latTypeK p.fw p.F.lv2 i : Set (VK p.fw i))) := by
    rw [hr]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ (ι '' (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i))) := by
        rw [himg]; exact hy1
      obtain ⟨x, hx, rfl⟩ := hy1'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      show (x : p.T.R _) ∈ Submodule.span _ (typeK p.fw p.F.lv2 i)
      obtain ⟨h, hx'⟩ := hι x
      exact Submodule.subset_span ⟨h, hx' ▸ hy2⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(show ι x ∈ ((p.R.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) by rw [← himg]; exact ⟨x, hx1, rfl⟩), ?_⟩
      have hsp : Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i) ≤
          ((spType p.R.toRealDat p.F.lv2 i).comap ι).map (VK p.fw i).subtype := by
        rw [Submodule.span_le]
        rintro f ⟨h, hf⟩
        have hfV : f ∈ VK p.fw i := by rw [VK, cuspW_wtZ]; exact h
        refine ⟨⟨f, hfV⟩, ?_, rfl⟩
        obtain ⟨h', e⟩ := hι ⟨f, hfV⟩
        show ι ⟨f, hfV⟩ ∈ spType p.R.toRealDat p.F.lv2 i
        rw [e]
        exact hf
      obtain ⟨z, hz, hzx⟩ := hsp hx2
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
  have h0 : latTypeK p.fw p.F.lv2 i ≠ ⊥ := by
    intro h0
    apply hg.2.2.1
    rw [eq_bot_iff]
    refine (latGood_le _ _ _).trans ?_
    rw [hS, h0]
    simp
  have key := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    (nrmK p.fw i) (nrmR p.R.toRealDat i) ι (latTypeK p.fw p.F.lv2 i) (C * unitE p) hg.2.2.2.1 hg.1 hc hli hfg h0 hN
  unfold CoreAt muCore
  rw [hS]
  linarith

theorem coreLe_of_gram_meas_rat : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  intro hg hm hr
  unfold Gram Meas GlobalTheory.CovTop.Rat CoreLe Lifts at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩

end GlobalTheory.CoreSlope
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitGenericPointMemCompactFlagSpaceOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitGenericPointMemCompactFlagSpaceOpenPart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenTrait

theorem mem_of_dense_of_forall_specializes {X : Scheme.{0}} [IsLocallyNoetherian X] {U : X.Opens}
    (hU : Dense (U : Set X)) {z : X} (hz : ∀ ξ : X, ξ ⤳ z → ξ = z) : z ∈ U := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have : IsAffine V := hV
  have : IsNoetherian V.toScheme := {}
  have : NoetherianSpace V.toScheme := inferInstance
  let z' : V.toScheme := ⟨z, hzV⟩
  have hC := irreducibleComponent_mem_irreducibleComponents z'
  obtain ⟨o, ho, ⟨u, huo⟩, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hoX : IsOpen (V.ι '' o) := V.ι.isOpenEmbedding.isOpenMap o ho
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwU⟩ := hU.inter_open_nonempty _ hoX ⟨_, u, huo, rfl⟩
  have h1 : V.ι hC.1.genericPoint ⤳ V.ι w := (hg.specializes (hoC hwo)).map V.ι.continuous
  have h2 : V.ι hC.1.genericPoint ⤳ V.ι z' := (hg.specializes mem_irreducibleComponent).map V.ι.continuous
  have h3 : V.ι z' = z := rfl
  rw [h3] at h2
  rw [← hz _ h2]
  exact h1.mem_open U.isOpen hwU

end GlobalTheory.GenTrait

namespace GlobalTheory.GenTrait

theorem isLocallyNoetherian_flag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) :
    IsLocallyNoetherian TF.X.YY := by
  have := TF.smooth
  have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have := TF.X.proper
  exact LocallyOfFiniteType.isLocallyNoetherian (TF.X.π ≫ TF.Y.s)

theorem top_le_preimage_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z) (K : Type) [Field K] (g : (Y₀ TF.X Z).presheaf.stalk y →+* K), Function.Injective g → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by
  intro E _ _ _ H Dw l Xo c TF Z y K _ g hg p _
  have := isLocallyNoetherian_flag TF
  let q := Spec.map (CommRingCat.ofHom g) p
  have hq0 : q.asIdeal = ⊥ := by
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime
    change Ideal.comap g p.asIdeal = ⊥
    rw [hp, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot g).1 hg
  have hq : ∀ q' : Spec ((Y₀ TF.X Z).presheaf.stalk y), q' ⤳ q → q' = q := fun q' h =>
    PrimeSpectrum.ext (le_antisymm ((show q'.asIdeal ≤ q.asIdeal from (PrimeSpectrum.le_iff_specializes _ _).2 h)) (hq0.le.trans bot_le))
  change ((Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) p) ∈ flagOpen TF.X
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  refine mem_of_dense_of_forall_specializes (dense_flagOpen TF.X) fun ξ hξ => ?_
  have hy : (Y₀ TF.X Z).fromSpecStalk y q ⤳ y := by
    have : (Y₀ TF.X Z).fromSpecStalk y q ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hmem : ξ ∈ Set.range (inc₀ TF.X Z) := by
    rw [Scheme.Opens.range_ι]
    refine hξ.mem_open (TopologicalSpace.Opens.isOpen _) ?_
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨ξ₀, rfl⟩ := hmem
  have h₀ : ξ₀ ⤳ (Y₀ TF.X Z).fromSpecStalk y q := (inc₀ TF.X Z).isEmbedding.specializes_iff.1 hξ
  obtain ⟨q', rfl⟩ : ξ₀ ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact h₀.trans hy
  rw [hq q' (((Y₀ TF.X Z).fromSpecStalk y).isEmbedding.specializes_iff.1 h₀)]

end GlobalTheory.GenTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitGenericPointMemCompactFlagSpaceOpenPartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitGenericPoint_mem_compactFlagSpaceOpenPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z) (K : Type) [Field K] (g : (Y₀ TF.X Z).presheaf.stalk y →+* K), Function.Injective g → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by
  first | exact @GlobalTheory.GenTrait.top_le_preimage_flagOpen | exact GlobalTheory.GenTrait.top_le_preimage_flagOpen | (intros; apply GlobalTheory.GenTrait.top_le_preimage_flagOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeTheta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblUnitaryBox

section Alg

variable {A α β : Type} [CommRing A] [Fintype β] [DecidableEq β]

end Alg

section Meas

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance (priority := high) measTup : MeasurableSpace (κ → AF F) := borel _

local instance borelTup : BorelSpace (κ → AF F) := ⟨rfl⟩

theorem integrable_normSq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ :=
  (schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero

theorem lintegral_eq_ofReal (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integral_mul_star_eq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ)
    (hT : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {φ₁ φ₂ : (κ → AF F) → ℂ}
    (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ) :
    ∫ x, T φ₁ x * star (T φ₂ x) ∂μ = ∫ x, φ₁ x * star (φ₂ x) ∂μ := by
  have hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := fun φ hφ => by
    have h := hT φ hφ
    rw [lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ := fun f hf g hg c =>
    (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)
  have pol : ∀ (f : (κ → AF F) → ℂ), f ∈ schA F κ →
      ∀ (g : (κ → AF F) → ℂ), g ∈ schA F κ → ∫ x, f x * star (g x) ∂μ =
      (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ)) / 4 := fun f hf g hg => by
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
      (integrable_normSq μ hμ (hm f hf g hg c)).ofReal
    simp only [← integral_complex_ofReal]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _),
      ← integral_add, ← integral_sub, ← integral_div]
    rotate_left
    · exact ((hi _).sub (hi _)).add ((hi _).const_mul _)
    · exact (hi _).const_mul _
    · exact (hi _).sub (hi _)
    · exact (hi _).const_mul _
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      map_add, map_mul, map_neg, map_one, Complex.conj_I, Complex.star_def]
    linear_combination ((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I
  rw [pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]
  simp only [← hn _ (hm _ h₁ _ h₂ _), map_add (f := _), map_smul]


end Meas

section Shape

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {M : Type} [AddCommGroup M] [Module (AF F) M]
  {Bf : M → M → AF F}

attribute [local instance] measTup borelTup

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Shape

section Lagr

variable {R A α β m κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype α] [DecidableEq α] [Fintype κ]
  {Bf : Matrix α β A → Matrix α β A → R} (co : Darboux Bf κ)



end Lagr

section Value

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] measTup borelTup

end Value

end GlobalTheory.DblUnitaryBox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt

open IsDedekindDomain

def intZ (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ :=
  Nat.card (Fin n → LevQ Dw l) * (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w *
    l.M ^ Formalism.L2.Pj.DF Dw w

theorem intZ_eq (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) :
    intZ D Dw l n w = l.M ^ (Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) * n) *
      (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w * l.M ^ Formalism.L2.Pj.DF Dw w := by
  rw [intZ, GlobalTheory.PlaceInt.card_fun_levQ]

theorem sum_padicValNat_mul_le (v : ℕ → ℤ) (hv : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) (h0 : ∀ a, 0 ≤ v a)
    {N : ℕ} (hN : N ≠ 0) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
  classical
  have h1 : v 1 = 0 := by have := hv 1 1 one_ne_zero one_ne_zero; rw [Nat.mul_one] at this; omega
  have key : ∀ N : ℕ, N ≠ 0 → ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => intro _; simp [Nat.padicValNat_def, h1]
    | prime l hl =>
      intro _
      have : ∀ p ∈ s, (padicValNat p l : ℤ) * v p = if p = l then v l else 0 := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        haveI := Fact.mk hl
        split_ifs with h
        · subst h; simp [Nat.padicValNat_def, Nat.Prime.multiplicity_self]
        · simp [Nat.padicValNat_def, multiplicity_primes h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs
      exacts [le_rfl, h0 _]
    | mul a b iha ihb =>
      intro hab
      have ha := left_ne_zero_of_mul hab
      have hb := right_ne_zero_of_mul hab
      have : ∀ p ∈ s, (padicValNat p (a * b) : ℤ) * v p = (padicValNat p a : ℤ) * v p + (padicValNat p b : ℤ) * v p := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) ha hb]; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hv a b ha hb]
      exact add_le_add (iha ha) (ihb hb)
  exact key N hN

theorem ram_sum_le_vV_discr (E : Type) [Field E] [NumberField E] (T : CDVR) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (e X : ℕ) :
    ∑ p ∈ s, (vV T.V (p : T.Fr) : ℝ) / e *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) * (X : ℝ) / 2 ≤
      (vV T.V (((NumberField.discr E).natAbs ^ X : ℕ) : T.Fr) : ℝ) / e := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hN : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have h0 : ∀ a : ℕ, 0 ≤ vV T.V (a : T.Fr) := fun a => GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T a
  have h1 := sum_padicValNat_mul_le (fun a => vV T.V (a : T.Fr))
    (fun a b ha hb => by
      simp only [Nat.cast_mul]
      exact vV_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb)) h0 hN s hs
  have h2 : ∑ p ∈ s, (padicValNat p (NumberField.discr E).natAbs : ℝ) * (vV T.V (p : T.Fr) : ℝ) ≤
      (vV T.V (((NumberField.discr E).natAbs : ℕ) : T.Fr) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).2 h1
    rw [Int.cast_sum] at h
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  have hk : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  rw [Nat.cast_pow, GlobalTheory.ShortBound.vV_pow (Nat.cast_ne_zero.2 hN), Int.cast_mul, Int.cast_natCast]
  have hX : (0 : ℝ) ≤ (X : ℝ) / e := by positivity
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left h2 hX).trans (le_of_eq (by ring)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h3 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast h0 p
  have h4 : (padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) ≤
      (padicValNat p (NumberField.discr E).natAbs : ℝ) := div_le_self (Nat.cast_nonneg _) hk
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hX h3)
  have h6 : (0 : ℝ) ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) :=
    mul_nonneg (mul_nonneg hX h3) (Nat.cast_nonneg _)
  calc _ = (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) / 2 := by ring
    _ ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) := by linarith
    _ = _ := by ring

theorem log_discr_natAbs_le (E : Type) [Field E] [NumberField E] :
    Real.log ((NumberField.discr E).natAbs : ℝ) ≤ (Module.finrank ℚ E : ℝ) * fieldSz E := by
  have hk : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  have h := (div_le_iff₀ hk).1 (log_rd_le_fieldSz E)
  rw [Nat.cast_natAbs, Int.cast_abs]
  linarith

theorem isIntegral_fourierCoeff_classIndicator_levelPoint {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hM : l.M ≠ 0) {n : ℕ} (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw l) : IsIntegral ℤ (x0Dat c x0 q) := by
  unfold x0Dat
  refine ⟨Polynomial.X ^ l.M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  have h1 : zetaM c ^ l.M = 1 := GlobalTheory.Survey.BaseClassMove.zetaM_pow c
  have h2 : (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) ^ l.M = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  simp [h2]

end GlobalTheory.CovInt
end
end
