module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSide
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSide
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullSquare

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_of_eq {θ θ' : R →+* R'} (e : θ = θ') {D : DegPre R} {D' : DegPre R'} (r : IsPullDeg θ D D') :
    ∃ r' : IsPullDeg θ' D D', (∀ x, r'.xe x = r.xe x) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g : GtPtF D F)
        (g' : GtPtF D' F), IsPullGtF θ r F g g' → IsPullGtF θ' r' F g g' := by
  subst e
  exact ⟨r, fun _ => rfl, fun _ _ _ _ _ _ h => h⟩

end GlobalTheory.PullSquare

theorem GlobalTheory.Mum.isPullDeg_square : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  intro R R₁ W W₁ _ _ _ _ _ _ _ _ I I₁ J J₁ _ _ _ _ ρ φ iw φ₁ hsq hφ₁ hρi hφi hiw D D₁ D' D'₁ hρ hD hX
  obtain ⟨r, Tr⟩ := GlobalTheory.LabTrans.exists_comp hφi hiw hD hX
  obtain ⟨r', hx', hg'⟩ := GlobalTheory.PullSquare.exists_of_eq hsq.symm r
  obtain ⟨h, Th⟩ := GlobalTheory.LabTrans.exists_cancel hρi hφ₁ hρ r'
  refine ⟨h, fun x => ?_, ?_⟩
  · rw [Th.xe_eq, hx', ← Tr.xe_eq]
  · intro F _ _ _ _ _ cρ cφ ci c₁ g g₁ g' g'₁ Hρ HD HX
    have cθ : GlobalTheory.ArcPull.Compat (iw.comp φ) F := fun a => (cφ a).trans (ci (φ a))
    have cθ' : GlobalTheory.ArcPull.Compat (φ₁.comp ρ) F := fun a => (cρ a).trans (c₁ (ρ a))
    have H : IsPullGtF (φ₁.comp ρ) r' F g g'₁ := hg' F g g'₁ (Tr.isPullGtF cθ HD HX)
    obtain ⟨g'', H''⟩ := GlobalTheory.ArcPull.exists_pullGt h GlobalTheory.ExpansionTotal.globalFns c₁ g₁
    have H2 := Th.isPullGtF cθ' Hρ H''
    rwa [GlobalTheory.ArcPull.pullGt_unique r' cθ' H2 H] at H''
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegSquareFourthSideStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullDeg_square_fourth_side : ∀ (R R₁ W W₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [CommRing W₁] [IsDomain W₁] (I : Ideal R) (I₁ : Ideal R₁) (J : Ideal W) (J₁ : Ideal W₁), AdmBase R I → AdmBase R₁ I₁ → AdmBase W J → AdmBase W₁ J₁ → ∀ (ρ : R →+* R₁) (φ : R →+* W) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁), φ₁.comp ρ = iw.comp φ → Function.Injective φ₁ → Function.Injective ρ → Function.Injective φ → Function.Injective iw → ∀ (D : DegData R I) (D₁ : DegData R₁ I₁) (D' : DegData W J) (D'₁ : DegData W₁ J₁) (hρ : IsPullDeg ρ D.toPre D₁.toPre) (hD : IsPullDeg φ D.toPre D'.toPre) (hX : IsPullDeg iw D'.toPre D'₁.toPre), ∃ h : IsPullDeg φ₁ D₁.toPre D'₁.toPre, (∀ x, hρ.xe (h.xe x) = hD.xe (hX.xe x)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R₁) F] [Algebra (FractionRing W) F] [Algebra (FractionRing W₁) F], GlobalTheory.ArcPull.Compat ρ F → GlobalTheory.ArcPull.Compat φ F → GlobalTheory.ArcPull.Compat iw F → GlobalTheory.ArcPull.Compat φ₁ F → ∀ (g : GtPtF D.toPre F) (g₁ : GtPtF D₁.toPre F) (g' : GtPtF D'.toPre F) (g'₁ : GtPtF D'₁.toPre F), IsPullGtF ρ hρ F g g₁ → IsPullGtF φ hD F g g' → IsPullGtF iw hX F g' g'₁ → IsPullGtF φ₁ h F g₁ g'₁ := by
  first | exact @GlobalTheory.Mum.isPullDeg_square | exact GlobalTheory.Mum.isPullDeg_square | (intros; apply GlobalTheory.Mum.isPullDeg_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitExt

theorem exists_finite_trait_extension : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  intro R W R₁ _ _ _ _ _ _ _ _ _ hW φ hφ hφl ρ hρ Ω _ _ _ _ e he
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨-, hρi, hρf⟩ := hρ

  letI : Algebra W Ω := ((algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hWΩ : Function.Injective (algebraMap W Ω) :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  haveI : FaithfulSMul W Ω := (faithfulSMul_iff_algebraMap_injective W Ω).2 hWΩ
  haveI : Algebra.IsAlgebraic W Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := Ω)).mpr inferInstance

  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hρf
  letI : Algebra R W := φ.toAlgebra
  letI : Algebra R Ω := ((algebraMap W Ω).comp φ).toAlgebra
  haveI : IsScalarTower R W Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₀ : R₁ →+* Ω := e.comp (algebraMap R₁ (FractionRing R₁))
  have hf₀ : ∀ r, f₀ (ρ r) = algebraMap W Ω (φ r) := he
  let f : R₁ →ₐ[R] Ω := { f₀ with commutes' := fun r => hf₀ r }
  have hint : ∀ x : R₁, IsIntegral W (f₀ x) := fun x =>
    IsIntegral.tower_top (A := W) (IsIntegral.map f (show IsIntegral R x from RingHom.Finite.to_isIntegral hρf x))
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule R R₁).FG)
  classical
  obtain ⟨W₁, hd, hc, -, hfin, -, hloc, -, hmem⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra W Ω (S.image f₀)
  have hin : ∀ x : R₁, f₀ x ∈ W₁ := by
    intro x
    have hx : x ∈ Submodule.span R (S : Set R₁) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmem _ (Finset.mem_image_of_mem _ hy) (hint y)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact W₁.add_mem hy hz
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine W₁.mul_mem ?_ hy
      change f₀ (ρ a) ∈ W₁
      rw [hf₀]; exact W₁.algebraMap_mem _

  let iw : W →+* W₁ := algebraMap W W₁
  let φ₁ : R₁ →+* W₁ := f₀.codRestrict W₁ hin
  have hiwinj : Function.Injective iw := fun a b h => hWΩ (congrArg Subtype.val h)
  haveI : CharZero W₁ := charZero_of_injective_ringHom hiwinj
  have hcomp : φ₁.comp ρ = iw.comp φ := by
    ext r; exact hf₀ r
  have hφ₁inj : Function.Injective φ₁ := fun a b h => by
    have : f₀ a = f₀ b := congrArg Subtype.val h
    exact IsFractionRing.injective R₁ (FractionRing R₁) (e.injective this)
  have hφ₁l : IsLocalHom φ₁ := by
    have h1 : (maximalIdeal W₁).comap iw = maximalIdeal W := ((local_hom_tfae iw).out 1 5).mp hloc
    have h2 : (maximalIdeal W).comap φ = maximalIdeal R := ((local_hom_tfae φ).out 1 5).mp hφl
    have hP : ((maximalIdeal W₁).comap φ₁).comap ρ = maximalIdeal R := by
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, h1, h2]
    have hmax : ((maximalIdeal W₁).comap φ₁).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ (RingHom.Finite.to_isIntegral hρf) _
        (by rw [hP]; infer_instance)
    exact ((local_hom_tfae φ₁).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hmax)
  haveI : Algebra.IsAlgebraic W₁ Ω := Algebra.IsAlgebraic.extendScalars hiwinj
  haveI : Module.IsTorsionFree W₁ Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  haveI : Module.IsTorsionFree W₁ (AlgebraicClosure (FractionRing W₁)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq W₁ (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))]
      exact (algebraMap (FractionRing W₁) _).injective.comp (IsFractionRing.injective W₁ (FractionRing W₁)))
  let σ' : Ω →ₐ[W₁] AlgebraicClosure (FractionRing W₁) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ : ∀ x : W₁, σ' (x : Ω) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁))
      (algebraMap W₁ (FractionRing W₁) x) := fun x => by
    rw [← IsScalarTower.algebraMap_apply]; exact σ'.commutes x
  refine ⟨W₁, inferInstance, inferInstance, inferInstance, iw, φ₁, σ'.toRingHom, ⟨hd, hc, inferInstance⟩,
    hiwinj, RingHom.finite_algebraMap.2 hfin, hloc, hφ₁inj, hφ₁l, hcomp, fun w => hσ (iw w), fun r => hσ (φ₁ r)⟩

end GlobalTheory.TraitExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_complete_trait_extension_of_base : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  first | exact @GlobalTheory.TraitExt.exists_finite_trait_extension | exact GlobalTheory.TraitExt.exists_finite_trait_extension | (intros; apply GlobalTheory.TraitExt.exists_finite_trait_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitExt

theorem exists_fracHom {R R₁ M : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [Field M] [IsAlgClosed M]
    (ρ : R →+* R₁) (hρ : Function.Injective ρ) (hfin : ρ.Finite) (g : R →+* M) (hg : Function.Injective g) :
    ∃ e : FractionRing R₁ →+* M, ∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = g r := by
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R M := g.toAlgebra
  have hinj : Function.Injective (algebraMap R (FractionRing R₁)) := by
    rw [IsScalarTower.algebraMap_eq R R₁ (FractionRing R₁)]
    exact (IsFractionRing.injective R₁ (FractionRing R₁)).comp hρ
  haveI : Module.IsTorsionFree R (FractionRing R₁) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hg
  haveI : Algebra.IsIntegral R R₁ := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R (FractionRing R₁) :=
    (IsFractionRing.isAlgebraic_iff' R R₁ (FractionRing R₁)).1 inferInstance
  refine ⟨(IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).toRingHom, fun r => ?_⟩
  have h := (IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).commutes r
  rw [IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁)] at h
  exact h

end GlobalTheory.Mum.TraitExt

namespace GlobalTheory.Mum.TraitExt

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem unifTrait_pull : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  intro R R₁ _ _ _ _ _ _ ρ hR hfin D D₁ hρD G _ _ G₁ _ _ β₁ hG hpb L hL hU
  obtain ⟨hρD⟩ := hρD
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφi, hφl, hpb', hLB, ⟨hD⟩⟩ := hU
  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    GlobalTheory.T.exists_finite_complete_trait_extension_of_base R W R₁ hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨eI, heI, -⟩ := grpPullback_iso hpb' (isGrpPullback_pullback G (spMap φ))
    haveI := heI
    exact GlobalTheory.isSemiAbelian_of_grpIso eI (IsSemiAbelian.pullback _ G hG)
  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hG' U'
  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G' (spMap iw) (pullback.fst G'.hom (specOf iw)) :=
    isGrpPullback_pullback G' (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [spMap_comp, spMap_comp, hcomm]
  have hpb2 := hpb1.comp hpb'
  have hsq : (pullback.fst G'.hom (specOf iw) ≫ β) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hpb'.1.w, ← Category.assoc, pullback.condition]
    rfl
  set β'' : ((Over.pullback (specOf iw)).obj G').left ⟶ G₁.left :=
    hpb.1.lift (pullback.fst G'.hom (specOf iw) ≫ β) (((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁) hsq
    with hβ''
  have hβ1 : β'' ≫ β₁ = pullback.fst G'.hom (specOf iw) ≫ β := hpb.1.lift_fst _ _ _
  have hβ2 : β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ := hpb.1.lift_snd _ _ _
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G₁ (spMap φ₁) β'' :=
    hpb.cancel (hpb2.congr hsp hβ1.symm) hβ2
  obtain ⟨h, -, -⟩ := GlobalTheory.T.isPullDeg_square_fourth_side R R₁ W W₁ _ _ _ _ hR.1 hfin.1 hAW hAW₁ ρ φ iw φ₁ hcomm hφ₁i hfin.2.1 hφi hiwi
    D D₁ D' D'' hρD hD hD''
  have hw1 : LBIso U''.LG.L
      (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫ pullback.fst G'.hom (specOf iw))) :=
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
  have hw2 : LBIso (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫
      pullback.fst G'.hom (specOf iw))) (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull hLB _ (by simp)
  have hw3 : LBIso (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) ((L.pull β₁).pull β'') :=
    GlobalTheory.AlgUniq.lbIso_pull_comp hL β₁ β'' _ hβ1
  have hw : LBIso U''.LG.L ((L.pull β₁).pull β'') :=
    LBIso.trans U''.LG.isLB (pull_isLB U'.LG.isLB _) (pull_isLB (pull_isLB hL _) _) hw1
      (LBIso.trans (pull_isLB U'.LG.isLB _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hw2 hw3)
  exact ⟨W₁, inferInstance, inferInstance, inferInstance, φ₁, (Over.pullback (specOf iw)).obj G', inferInstance,
    inferInstance, β'', D'', A'', U'', hW₁, hφ₁i, hφ₁l, hpb3, hw, ⟨h⟩⟩

end GlobalTheory.Mum.TraitExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitUniformisation_pullback_finiteExtension : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  first | exact @GlobalTheory.Mum.TraitExt.unifTrait_pull | exact GlobalTheory.Mum.TraitExt.unifTrait_pull | (intros; apply GlobalTheory.Mum.TraitExt.unifTrait_pull <;> assumption)
end
