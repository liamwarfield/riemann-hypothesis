module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphisms
namespace GlobalTheory

theorem galois_of_finite_generating_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  intro K K' _ _ i hfin Γ _ s hs hfix
  letI := i.toAlgebra
  haveI : FiniteDimensional K K' := hfin
  let t : Γ → (K' ≃ₐ[K] K') := fun g => AlgEquiv.ofRingEquiv (f := s g) (hs g)
  let H : Subgroup (K' ≃ₐ[K] K') := Subgroup.closure (Set.range t)
  have hH : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : ∀ g, s g y = y := fun g => hy ⟨t g, Subgroup.subset_closure ⟨g, rfl⟩⟩
    obtain ⟨x, rfl⟩ := hfix y h1
    exact IntermediateField.algebraMap_mem _ x
  have hG : IsGalois K K' := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff, ← hH]
    exact IntermediateField.fixedField_le le_top
  refine ⟨hG, ?_⟩
  intro σ hσ
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hH, IntermediateField.fixingSubgroup_bot]
  let σ' : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := σ) hσ
  have hmem : σ' ∈ Submonoid.closure (Set.range t) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    show σ' ∈ H
    rw [hHtop]; exact Subgroup.mem_top _
  let φ : (K' ≃ₐ[K] K') →* (K' ≃+* K') :=
    { toFun := fun τ => τ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmap := Submonoid.mem_map_of_mem φ hmem
  rw [MonoidHom.map_mclosure, ← Set.range_comp] at hmap
  have hc : (φ ∘ t) = s := by
    funext g; ext y; rfl
  have hσ' : φ σ' = σ := by ext y; rfl
  rwa [hc, hσ'] at hmap

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphismsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem spMap_mul_aut {K' : Type} [Field K'] (a b : K' ≃+* K') :
    spMap ((a * b : K' ≃+* K') : K' →+* K') = spMap (a : K' →+* K') ≫ spMap (b : K' →+* K') := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem lbIso_pull_comp_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : X ⟶ X)
    (ha : LBIso L (L.pull a)) (hb : LBIso L (L.pull b)) : LBIso L (L.pull (a ≫ b)) :=
  LBIso.trans hL (pull_isLB hL a) (pull_isLB hL _) ha
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L a a rfl) (chartPullSame L _ (fun _ => b) _ a fun _ => rfl) hb)

theorem exists_lb_descent_of_finite_aut : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  intro K K' _ _ i hfin Γ _ s hs hfix A _ A' _ φ hA hp L' hL' hinv
  letI : Algebra K K' := i.toAlgebra
  obtain ⟨hgal, hgen⟩ := GlobalTheory.T.isGalois_of_finite_fixed_automorphisms K K' i hfin Γ s hs hfix
  haveI : FiniteDimensional K K' := hfin
  have hc0 := GlobalTheory.ZM.DwModel.isGaloisCover_field K K'
  have hfixσ : ∀ σ : K' ≃ₐ[K] K', ∀ x, (σ : K' ≃+* K') (i x) = i x := fun σ x => σ.commutes x
  have hσi : ∀ σ : K' ≃ₐ[K] K', spMap (σ : K' →+* K') ≫ spMap i = spMap i := fun σ => by
    simp only [spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x
  have hw : ∀ σ : K' ≃ₐ[K] K', (A'.hom ≫ spMap (σ : K' →+* K')) ≫ spMap i = φ ≫ A.hom := fun σ => by
    rw [Category.assoc, hσi σ, hp.1.w]
  let t : (K' ≃ₐ[K] K') → (A'.left ⟶ A'.left) := fun σ =>
    hp.1.lift φ (A'.hom ≫ spMap (σ : K' →+* K')) (hw σ).symm
  have ht1 : ∀ σ, t σ ≫ φ = φ := fun σ => hp.1.lift_fst _ _ _
  have ht2 : ∀ σ, t σ ≫ A'.hom = A'.hom ≫ spMap (σ : K' →+* K') := fun σ => hp.1.lift_snd _ _ _
  have hGC : GlobalTheory.ZM.IsGaloisCover (K' ≃ₐ[K] K') t φ :=
    hc0.of_isPullback (u := A'.hom) (v := A.hom) hp.1.flip (fun a => ht2 a) ht1

  have hQ : ∀ τ ∈ Submonoid.closure (Set.range s), ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧
      ψ ≫ A'.hom = A'.hom ≫ spMap (τ : K' →+* K') ∧ LBIso L' (L'.pull ψ) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hinv g
    | one =>
      refine ⟨𝟙 _, Category.id_comp _, ?_, ?_⟩
      · rw [Category.id_comp]
        have : ((1 : K' ≃+* K') : K' →+* K') = RingHom.id K' := rfl
        rw [this]
        exact (Category.comp_id _).symm.trans (by simp [spMap])
      · exact LBIso.symm (lbIso_of_chartPull (chartPullPull L' (𝟙 _)) hL')
    | mul x y _ _ hx hy =>
      obtain ⟨ψ₁, a1, b1, c1⟩ := hx
      obtain ⟨ψ₂, a2, b2, c2⟩ := hy
      refine ⟨ψ₁ ≫ ψ₂, by rw [Category.assoc, a2, a1], ?_, lbIso_pull_comp_self hL' _ _ c1 c2⟩
      rw [Category.assoc, b2, ← Category.assoc, b1, Category.assoc, spMap_mul_aut]
  have hall : ∀ σ : K' ≃ₐ[K] K', LBIso L' (L'.pull (t σ)) := fun σ => by
    obtain ⟨ψ, a1, b1, c1⟩ := hQ (σ : K' ≃+* K') (hgen _ (hfixσ σ))
    have : ψ = t σ := hp.1.hom_ext (by rw [a1, ht1]) (by rw [b1, ht2]; rfl)
    exact this ▸ c1
  have hA' : IsAbelianScheme A' := by
    have := hA.comm
    have hcomm : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hp.2 T x y (pushPt hp.1.w x) (pushPt hp.1.w y) rfl rfl,
        ← hp.2 T y x (pushPt hp.1.w y) (pushPt hp.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm
            smooth := MorphismProperty.of_isPullback (P := @Smooth) hp.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) hp.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp.1 hA.geomConnected }
  have hsurj : Function.Surjective A'.hom.appTop.hom := (GlobalTheory.globalFns_holds (Sp K') A' hA').2
  let e : Sp K' ⟶ A'.left := hp.1.lift (spMap i ≫ eSec A) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]; exact Category.comp_id _)
  have he : e ≫ A'.hom = 𝟙 _ := hp.1.lift_snd _ _ _
  have heθ : ∀ σ : K' ≃ₐ[K] K', e ≫ t σ = spMap (σ : K' →+* K') ≫ e := fun σ => by
    refine hp.1.hom_ext ?_ ?_
    · rw [Category.assoc, ht1, Category.assoc, hp.1.lift_fst, ← Category.assoc, hσi σ]
    · rw [Category.assoc, ht2, ← Category.assoc, he, Category.assoc, he]
      simp
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle (Sp K') A'.left A'.hom e he hsurj L' hL'
    (GlobalTheory.SS.HtForm.gen_field _ (pull_isLB hL' e)) (K' ≃ₐ[K] K') t (fun σ => spMap (σ : K' →+* K'))
    (fun a c => hGC.mul a c) (fun a c => hc0.mul a c) heθ hall
  exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ _ t L' hGC hL' u hu hcoc

end GlobalTheory.Mum.GenDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  first | exact @GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut | exact GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut | (intros; apply GlobalTheory.Mum.GenDesc.exists_lb_descent_of_finite_aut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.Mum.GenDesc

theorem fracMap_finite : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  intro R R' _ _ _ _ ρ hρ hfin
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  have hinj : Function.Injective (algebraMap R R') := hρ
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')
  haveI : IsScalarTower R (FractionRing R) (FractionRing R') :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing R')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') :=
    inferInstance
  haveI : Module.Finite (FractionRing R) (FractionRing R') :=
    Module.Finite.of_isLocalization R R' (nonZeroDivisors R)
  have heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R') := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    rw [fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.Mum.GenDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionFieldMap_finite_of_finite_injective : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  first | exact @GlobalTheory.Mum.GenDesc.fracMap_finite | exact GlobalTheory.Mum.GenDesc.fracMap_finite | (intros; apply GlobalTheory.Mum.GenDesc.fracMap_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem fixed_mem_range : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) →
    y ∈ (fracMap ρ hρ).range := by
  classical
  intro R R' _ _ _ _ ρ hρ hG y hy
  obtain ⟨hfin, hinv⟩ := hG
  letI : Fintype (Gal ρ) := Fintype.ofFinite _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R') y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set P : R' := ∏ σ ∈ (Finset.univ : Finset (Gal ρ)).erase 1, σ.1 b with hP
  set N : R' := ∏ σ : Gal ρ, σ.1 b with hN
  have hNP : N = b * P := by
    rw [hN, hP, ← Finset.mul_prod_erase Finset.univ (fun σ : Gal ρ => σ.1 b) (Finset.mem_univ 1)]
    rfl
  have hσ0 : ∀ σ : Gal ρ, σ.1 b ≠ 0 := fun σ => (map_ne_zero_iff σ.1 σ.1.injective).2 hb0
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hNfix : ∀ τ ∈ Gal ρ, τ N = N := by
    intro τ hτ
    rw [hN, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : Gal ρ)) _ _ (fun σ => rfl)
  obtain ⟨n, hn⟩ := hinv N hNfix
  have inj := IsFractionRing.injective R' (FractionRing R')
  have hPK : algebraMap R' (FractionRing R') P ≠ 0 := (map_ne_zero_iff _ inj).2 hP0
  have hNK : algebraMap R' (FractionRing R') N ≠ 0 := (map_ne_zero_iff _ inj).2 hN0
  have hy' : algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b
      = algebraMap R' (FractionRing R') (a * P) / algebraMap R' (FractionRing R') N := by
    rw [hNP, map_mul, map_mul, mul_div_mul_right _ _ hPK]
  have hcfix : ∀ τ ∈ Gal ρ, τ (a * P) = a * P := by
    intro τ hτ
    apply inj
    have hyN : algebraMap R' (FractionRing R') (a * P)
        = (algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b) * algebraMap R' (FractionRing R') N := by
      rw [hy', div_mul_cancel₀ _ hNK]
    rw [← fracAut_algebraMap, hyN, map_mul, hy ⟨τ, hτ⟩, fracAut_algebraMap, hNfix τ hτ]
  obtain ⟨m, hm⟩ := hinv (a * P) hcfix
  refine ⟨algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) n, ?_⟩
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hm, hn, hy']

end GlobalTheory.Mum.GenDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) → y ∈ (fracMap ρ hρ).range := by
  first | exact @GlobalTheory.Mum.GenDesc.fixed_mem_range | exact GlobalTheory.Mum.GenDesc.fixed_mem_range | (intros; apply GlobalTheory.Mum.GenDesc.fixed_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem isGrpPullback_genMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  intro R R' _ _ _ _ ρ hρ G' _ G _ β h
  have n : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap ρ hρ) ≫ jK R)
      (genMap hρ β h.1.w ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_pullback G' (jK R')).comp h).congr (jK_comp_spMap ρ hρ) (genMap_fst hρ β h.1.w).symm
  exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n (genMap_snd hρ β h.1.w)

end GlobalTheory.Mum.GenDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  first | exact @GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | exact GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | (intros; apply GlobalTheory.Mum.GenDesc.isGrpPullback_genMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem exists_inv (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R))
    (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
    (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U')
    (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'),
      ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧
      ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧
      LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  intro hinv σ
  have h₁ : G'.hom ≫ spMap (Gal.hom σ) = a.act σ ≫ G'.hom := ((a.cart σ).1.w).symm
  have h₂ : jK R' ≫ spMap (Gal.hom σ) = spMap (fracAut σ.1).toRingHom ≫ jK R' := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (fracAut_algebraMap σ.1 x).symm
  let ψ := pullback.map G'.hom (jK R') G'.hom (jK R') (a.act σ) (spMap (fracAut σ.1).toRingHom) (spMap (Gal.hom σ)) h₁ h₂
  have hψ₁ : ψ ≫ pullback.fst G'.hom (jK R') = pullback.fst G'.hom (jK R') ≫ a.act σ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom :=
    pullback.lift_snd _ _ _
  have hfr : spMap (fracAut σ.1).toRingHom ≫ spMap (fracMap ρ hρ) = spMap (fracMap ρ hρ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fracAut_fracMap hρ σ x
  refine ⟨ψ, ?_, hψ₂, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, genMap_fst, ← Category.assoc, hψ₁, Category.assoc, hinv σ]
    · rw [Category.assoc, genMap_snd, ← Category.assoc, hψ₂, Category.assoc, hfr]
  · obtain ⟨h, bc, hbc, hU, -⟩ := a.unif σ
    obtain ⟨wL, hwL, -⟩ := hU.lg
    have hL : LBIso U'.LG.L (U'.LG.L.pull (a.act σ)) := by
      rw [← hbc]
      exact ⟨wL, hwL⟩
    have hL₀ := U'.LG.isLB
    refine LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL₀ _) (pull_isLB (pull_isLB hL₀ _) _)
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL (pullback.fst G'.hom (jK R')) rfl) ?_
    exact GlobalTheory.GenSpread.lbIso_pull_pull hL₀ ψ hψ₁.symm

end GlobalTheory.Mum.GenDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConjugate_genericBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ), (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'), ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧ ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  first | exact @GlobalTheory.Mum.GenDesc.exists_inv | exact GlobalTheory.Mum.GenDesc.exists_inv | (intros; apply GlobalTheory.Mum.GenDesc.exists_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProper
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProper
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem abelian_of_field_of_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  intro K K' _ _ i G _ B _ φ g hG h hP hB
  have hc := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : Flat (spMap i) := inferInstance
  have : Surjective (spMap i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper G.hom := ⟨⟩
  have : ConnectedSpace G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))
  have hd' : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd
  have e : d = g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))
  subst e
  exact ⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩

end GlobalTheory.Mum.GenDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProperStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_of_fieldExtension_pullback_proper : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback | exact GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback | (intros; apply GlobalTheory.Mum.GenDesc.abelian_of_field_of_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem rigidified_and_sym_of_field_extension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  intro K K' _ _ i A _ A' _ φ hA h L L' hL hL' hw hS
  refine ⟨?_, (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K K' i A A' φ L L' hA h hL hL' hw).2.1 hS⟩
  have : Subsingleton (𝟙_ (Over (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum K) (pull_isLB hL _)

end GlobalTheory.Mum.GenDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPullStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  first | exact @GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | exact GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | (intros; apply GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGalois
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

open GlobalTheory.Mum

theorem polarisedGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  intro R _ _ _ _ R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ _ U' a G _ _ β hG hpb hinv
  have hρ : Function.Injective ρ := hfin.2.1
  haveI := hgal.1
  have hκ := GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap R R' ρ hρ G' G β hpb
  let L' := U'.LG.L.pull (pullback.fst G'.hom (jK R'))
  have hL' : L'.IsLB := pull_isLB U'.LG.isLB _
  have hiso : LBIso L' (A'.L.pull U'.gen.hom.left) := LBIso.symm U'.ext
  have := U'.gen_hom
  obtain ⟨hP', hdim', hsym', hamp', hkt'⟩ := GlobalTheory.T.principalPolarisation_of_groupScheme_iso _ A' _ U'.gen U'.gen_hom L' hL' hiso
  have hsemi : IsSemiAbelian ((Over.pullback (jK R)).obj G) := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_of_fieldExtension_pullback_proper _ _ (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) _ _ A'.g hsemi hκ hP' hdim'
  obtain ⟨L, hL, hLL⟩ := GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite (FractionRing R) (FractionRing R') (fracMap ρ hρ)
    (GlobalTheory.T.fractionFieldMap_finite_of_finite_injective R R' ρ hρ hfin.2.2) (Gal ρ) (fun σ => fracAut σ.1) (fun σ x => fracAut_fracMap hρ σ x)
    (GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants R R' ρ hρ hgal) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hab hκ L' hL'
    (GlobalTheory.T.exists_galoisConjugate_genericBundle_iso R R' ρ hρ D D' hD A' G' U' a G β hpb.1.w hinv)
  obtain ⟨hrig, hsym⟩ := GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback _ _ (fracMap ρ hρ) _ _ _ hab hκ L L' hL hL' hLL hsym'
  have := hsemi.quasiCompact
  have := hsemi.separated
  have := hsemi.smooth
  obtain ⟨-, hamp, hkt⟩ := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (FractionRing R) (FractionRing R')
    (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hκ L L' hL hL' hLL hP' hamp' hkt'
  let P : PolAV (Sp (FractionRing R)) :=
    { A := (Over.pullback (jK R)).obj G
      isAb := hab
      g := A'.g
      smoothDim := hdim
      L := L
      isLB := hL
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  refine ⟨P, Iso.refl _, genMap hρ β hpb.1.w, ?_, genMap_fst _ _ _, ?_⟩
  · show IsMonHom (𝟙 _)
    infer_instance
  · simpa using hLL

end GlobalTheory.Mum.GenDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_generic_fibre_descends_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  first | exact @GlobalTheory.Mum.GenDesc.polarisedGeneric | exact GlobalTheory.Mum.GenDesc.polarisedGeneric | (intros; apply GlobalTheory.Mum.GenDesc.polarisedGeneric <;> assumption)
end
