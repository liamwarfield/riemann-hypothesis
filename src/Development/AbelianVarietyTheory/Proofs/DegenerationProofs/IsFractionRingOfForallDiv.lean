module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGeneric
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

open SpreadAb (grpObj_of_dominant isPullback_square)

theorem exists_grpObj : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  intro R K _ _ _ _ _ _ X f A _ _ φ h _ _
  obtain ⟨a₁, ha₁, H₁⟩ := exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨a₂, ha₂, H₂⟩ := exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨a₃, ha₃, H₃⟩ := exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  refine ⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃,
    fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hg
  obtain ⟨⟨u₁, u₂⟩, u₃⟩ := hg
  have hc : spMap ψ ≫ spMap g = spMap (algebraMap R K) := by
    rw [← hψg, ← Spec.map_comp]; rfl
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ
  have : Flat G.hom := MorphismProperty.of_isPullback (P := @Flat) hG inferInstance
  have : IsSeparated G.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' g u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' g u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hc
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.GenSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGenericStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  first | exact @GlobalTheory.GenSpread.exists_grpObj | exact GlobalTheory.GenSpread.exists_grpObj | (intros; apply GlobalTheory.GenSpread.exists_grpObj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GenSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.ConnFibre

theorem exists_geometricallyConnected : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  intro R K _ _ _ _ _ _ X X₀ f f₀ φ hb hs hp hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R X f hp
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hg₀ : Function.Injective g₀ := (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let y₀ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h₀ : IsPullback (pullback.fst f₀ y₀ ≫ φ) (pullback.snd f₀ y₀) f
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback f₀ y₀).paste_horiz hb
    erw [← Spec.map_comp] at this
    exact this
  have hs₀ : Smooth f₀ := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f₀ hs₀ hc
  have hint : IsIntegral (pullback f₀ y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback f₀ y₀)
  have hpr₀ : IsProper (pullback.snd f₀ y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback f₀ y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst f₀ y₀ ≫ φ) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hsurj : Surjective f := by
    have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range f := by
      refine ⟨(pullback.fst f₀ y₀ ≫ φ) x₀, ?_⟩
      have e : f ((pullback.fst f₀ y₀ ≫ φ) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd f₀ y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext (le_bot_iff.1 fun a ha => ?_))
      have ha' : g₀ a ∈ (pullback.snd f₀ y₀ x₀).asIdeal := ha
      by_contra hne
      have hne' : g₀ a ≠ 0 := fun h => hne (hg₀ (h.trans (map_zero g₀).symm))
      exact (PrimeSpectrum.isPrime (pullback.snd f₀ y₀ x₀)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ ha' (IsUnit.mk0 _ hne'))
    refine ⟨fun z => ?_⟩
    have hsp : (⊥ : PrimeSpectrum R) ⤳ (z : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hcl hbot
  refine ⟨δ, fun h => hδ (h ▸ map_zero g₀), fun R' _ g hg X' π f' hπ => ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have h' : IsPullback (fst ≫ π) snd f (Spec.map (CommRingCat.ofHom ((algebraMap R' F).comp g))) := by
    have := h.paste_horiz hπ
    erw [← Spec.map_comp] at this
    exact this
  have : Surjective snd := MorphismProperty.of_isPullback h' hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h' _ (hker F _ (hg.map (algebraMap R' F)))
  exact ⟨⟨z⟩⟩

end GlobalTheory.GenSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  first | exact @GlobalTheory.GenSpread.exists_geometricallyConnected | exact GlobalTheory.GenSpread.exists_geometricallyConnected | (intros; apply GlobalTheory.GenSpread.exists_geometricallyConnected <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibres
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem map_linComb_pts {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (linComb x a) = linComb (fun i => ρ (x i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

theorem linComb_left_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (T'.hom ≫ f) ≫ (x i).left) (a : Fin n → ℕ) :
    (linComb x' a).left ≫ φ = (T'.hom ≫ f) ≫ (linComb x a).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ baseOver S := Over.homMk (T'.hom ≫ f) (Category.comp_id _)
  have hx' : ∀ i, pushPt h.1.w (x' i) = U ≫ x i := fun i => Over.OverMorphism.ext (hx i)
  have e : pushPt h.1.w (linComb x' a) = U ≫ linComb x a :=
    (map_linComb_pts (pushHom h T') x' a).trans ((congrArg (fun z => linComb z a) (funext hx')).trans
      (map_linComb_pts (preHom U) x a).symm)
  exact congrArg (fun z => z.left) e

theorem exists_forall_sections_ne {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [IsSeparated G.hom]
    {z z' : baseOver (Sp R) ⟶ G} (hz : z ≠ z') :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'), (s ≫ spMap g) ≫ z.left ≠ (s ≫ spMap g) ≫ z'.left := by
  let j : (equalizer z z').left ⟶ Sp R := (equalizer.ι z z').left
  have hj : IsClosedImmersion j := isClosedImmersion_equalizer_ι_left z z'
  have hC : IsClosed (Set.range j) := j.isClosedEmbedding.isClosed_range
  have hg : genericPoint (Sp R) ∉ Set.range j := by
    intro hg
    have hd : IsDominant j := by
      refine ⟨?_⟩
      rw [DenseRange, dense_iff_closure_eq, hC.closure_eq]
      exact Set.eq_univ_of_univ_subset (((genericPoint_spec (Sp R)).mem_closed_set_iff hC).1 hg)
    refine hz (Over.OverMorphism.ext ?_)
    have hr : IsReduced (baseOver (Sp R)).left := inferInstanceAs (IsReduced (Sp R))
    refine ext_of_isDominant_of_isSeparated G.hom ((Over.w z).trans (Over.w z').symm) j ?_
    exact congrArg (fun u => u.left) (equalizer.condition z z')
  obtain ⟨a, ha, H⟩ := exists_forall_mem (V := ⟨(Set.range j)ᶜ, hC.isOpen_compl⟩) hg
  refine ⟨a, ha, fun R' _ g hga X hX s e => ?_⟩
  obtain ⟨x⟩ := hX
  let U : Over.mk (s ≫ spMap g) ⟶ baseOver (Sp R) := Over.homMk (s ≫ spMap g) (Category.comp_id _)
  have hU : U ≫ z = U ≫ z' := Over.OverMorphism.ext e
  have hl : (equalizer.lift U hU).left ≫ j = s ≫ spMap g := congrArg (fun u => u.left) (equalizer.lift_ι U hU)
  refine H R' g hga (s x) ⟨(equalizer.lift U hU).left x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  rfl

theorem exists_forall_linComb_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  intro R K _ _ _ _ _ _ G _ A _ φ hsep hA n k y y₀ hy hind
  have key : ∀ p : (Fin n → Fin k) × (Fin n → Fin k), ∃ a : R, a ≠ 0 ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
        ∀ (X : Scheme.{0}) [Nonempty X] (s : X ⟶ Sp R'),
          (s ≫ spMap g) ≫ (linComb y (fun i => (p.1 i : ℕ))).left =
            (s ≫ spMap g) ≫ (linComb y (fun i => (p.2 i : ℕ))).left → p.1 = p.2 := by
    rintro ⟨c, c'⟩
    by_cases hc : c = c'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ _ _ _ _ => hc⟩
    have hne : linComb y (fun i => (c i : ℕ)) ≠ linComb y (fun i => (c' i : ℕ)) := by
      intro e
      refine hc (hind c c' (Over.OverMorphism.ext (hA.1.hom_ext ?_ ?_)))
      · have hy' : ∀ i, (y₀ i).left ≫ φ =
            ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ≫ (y i).left := fun i =>
          (hy i).trans (congrArg (· ≫ (y i).left) (Category.id_comp _).symm)
        rw [linComb_left_push hA y₀ y hy', linComb_left_push hA y₀ y hy', e]
      · exact (Over.w _).trans (Over.w _).symm
    obtain ⟨a, ha, H⟩ := exists_forall_sections_ne hne
    exact ⟨a, ha, fun R' _ g hg X _ s e => (H R' g hg X s e).elim⟩
  choose a ha H using key
  refine ⟨∏ p, a p, Finset.prod_ne_zero_iff.2 fun p _ => ha p, ?_⟩
  intro R' _ g hg G' _ π y' hπ hy' F _ _ s c c' e
  have hu : IsUnit (g (a (c, c'))) :=
    isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem a (Finset.mem_univ _))) hg
  refine H (c, c') R' g hu _ s ?_
  have hx : ∀ i, ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i).left ≫ π =
      ((Over.mk s).hom ≫ spMap g) ≫ (y i).left := fun i => by
    show (s ≫ (y' i).left) ≫ π = (s ≫ spMap g) ≫ (y i).left
    rw [Category.assoc, hy' i, Category.assoc]
  have e₁ := linComb_left_push hπ _ y hx (fun i => (c i : ℕ))
  have e₂ := linComb_left_push hπ _ y hx (fun i => (c' i : ℕ))
  rw [e] at e₁
  exact e₁.symm.trans e₂

end GlobalTheory.GenSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  first | exact @GlobalTheory.GenSpread.exists_forall_linComb_injective | exact GlobalTheory.GenSpread.exists_forall_linComb_injective | (intros; apply GlobalTheory.GenSpread.exists_forall_linComb_injective <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.GenSpread

section Rings

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isFractionRing_of_forall_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem isNoetherianRing_of_fg [IsNoetherianRing o] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R :=
  have : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 h
  Algebra.FiniteType.isNoetherianRing o R

theorem exists_shrink {R : Subalgebra o Ω} (hR : R.FG) {J : Type} [Finite J] (a : J → R) (ha : ∀ i, a i ≠ 0)
    {X X₀ : Scheme.{0}} {f : X ⟶ Sp R} {f₀ : X₀ ⟶ Sp Ω} {φ : X₀ ⟶ X}
    (h : IsPullback φ f₀ f (spMap (algebraMap R Ω))) :
    ∃ (R' : Subalgebra o Ω) (g : R →+* R'), R ≤ R' ∧ R'.FG ∧ (algebraMap R' Ω).comp g = algebraMap R Ω ∧
      (∀ i, IsUnit (g (a i))) ∧ ∃ φ' : X₀ ⟶ pullback f (spMap g), φ' ≫ pullback.fst _ _ = φ ∧
        IsPullback φ' f₀ (pullback.snd f (spMap g)) (spMap (algebraMap R' Ω)) := by
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (Set.range fun i => (a i : Ω)⁻¹)
  have hle : R ≤ R' := le_sup_left
  let g : R →+* R' := (Subalgebra.inclusion hle).toRingHom
  have e : spMap (algebraMap R' Ω) ≫ spMap g = spMap (algebraMap R Ω) := by
    rw [← Spec.map_comp]; rfl
  refine ⟨R', g, hle, hR.sup ?_, rfl, fun i => ?_,
    pullback.lift φ (f₀ ≫ spMap (algebraMap R' Ω)) (by rw [Category.assoc, e, h.w]), pullback.lift_fst _ _ _, ?_⟩
  · exact (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  · have hm : (a i : Ω)⁻¹ ∈ R' := (le_sup_right : _ ≤ R') (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)
    exact mul_inv_cancel₀ (fun h0 => ha i (Subtype.ext h0))
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (spMap g))
    rwa [pullback.lift_fst, e]

end Rings

theorem comp_linComb {S : Scheme.{0}} {A : Over S} [GrpObj A] {T T' : Over S} (t : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : t ≫ linComb y c = linComb (fun i => t ≫ y i) c := by
  have := map_list_prod (preHom (G := A) t) (List.ofFn fun i => y i ^ c i)
  simp only [List.map_ofFn, Function.comp_def, map_pow] at this
  exact this

theorem polAV_spreads_out : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), IsUnit (M : o) → HypS P.A P.L → ∀ lev : Out.Level P M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze)), Laws → ∃ (R : Subalgebra o Ω) (P' : PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left) (lev' : Out.Level P' M (unitOn (Units.map (algebraMap o R).toMonoidHom ze))), R₀ ≤ R ∧ R.FG ∧ P'.g = P.g ∧ HypS P'.A P'.L ∧ IsGrpPullback P.A P'.A (spMap R.val.toRingHom) φ ∧ LBIso P.L (P'.L.pull φ) ∧ ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev.pt i).left ≫ φ = spMap R.val.toRingHom ≫ (lev'.pt i').left := by
  intro o Ω _ _ _ hB R₀ hR₀ hfr P M ze hM hS lev hL
  have := hB.ded
  obtain ⟨w₀, wd₀, hw₀, hwd₀, hww, hS₁, hS₂⟩ := hS
  have := P.isAb.proper
  have := P.isAb.smooth

  have := isFractionRing_of_forall_div hfr
  have := isNoetherianRing_of_fg hR₀
  obtain ⟨X₀, f₀, φ₀, H₀, N, hf₀, p₀, hH₀, aH₀, hN, eH₀⟩ := exists_projective_model (R := R₀) P.A.hom
    (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample) P.isLB
  obtain ⟨a₀, ha₀, Hsm⟩ := GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre R₀ Ω P.g X₀ _ f₀ _ φ₀ p₀ hf₀ P.smoothDim
  obtain ⟨R₁, g₁, le₁, hR₁, c₁, u₁, φ₁, e₁, p₁⟩ := exists_shrink hR₀ (fun _ : PUnit => a₀) (fun _ => ha₀) p₀
  have hsm₁ := Hsm R₁ g₁ (u₁ ⟨⟩) _ _ _ (IsPullback.of_hasPullback f₀ (spMap g₁))
  have hH₁ := LB.isLB_pull hH₀ (pullback.fst f₀ (spMap g₁))
  have aH₁ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₀ (pullback.fst f₀ (spMap g₁))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f₀ (spMap g₁)).flip inferInstance)
  have eH₁ := LBIso.trans (isLB_lbPow P.isLB N) (LB.isLB_pull hH₀ _) (LB.isLB_pull hH₁ _) eH₀
    (lbIso_pull_pull hH₀ φ₁ e₁.symm)
  have hf₁ : IsProper (pullback.snd f₀ (spMap g₁)) := inferInstance
  generalize H₀.pull (pullback.fst f₀ (spMap g₁)) = H₁ at hH₁ aH₁ eH₁
  clear e₁
  generalize pullback.snd f₀ (spMap g₁) = f₁ at hsm₁ hf₁ p₁
  generalize pullback f₀ (spMap g₁) = X₁ at f₁ φ₁ H₁ hsm₁ hf₁ p₁ hH₁ aH₁ eH₁
  have hfr₁ : ∀ x : Ω, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr x
    exact ⟨a, le₁ ha, b, le₁ hb, e⟩
  clear Hsm u₁ c₁ eH₀ aH₀ hH₀ p₀ ha₀

  have := isFractionRing_of_forall_div hfr₁
  have := isNoetherianRing_of_fg hR₁
  have hs₁ : Smooth f₁ := SmoothOfRelativeDimension.smooth P.g f₁
  have : LocallyOfFinitePresentation f₁ := inferInstance
  obtain ⟨a₁, ha₁, Hconn⟩ := GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre R₁ Ω X₁ _ f₁ _ φ₁ p₁ hs₁
    ((ProjSpace.isProjBy_iff_isProjOver f₁).2 (aH₁.isProjOver f₁)) P.isAb.geomConnected
  obtain ⟨a₂, ha₂, Hgrp⟩ := GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic R₁ Ω X₁ f₁ P.A φ₁ p₁ hs₁ hf₁
  obtain ⟨a₃, ha₃, Hlb⟩ := GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper R₁ Ω X₁ _ f₁ _ φ₁ p₁ inferInstance hf₁ P.L P.isLB
  obtain ⟨a₄, ha₄, Hw⟩ := exists_hom f₁ f₁ p₁ (w₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  obtain ⟨a₅, ha₅, Hwd⟩ := exists_hom f₁ f₁ p₁ (wd₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  choose b hb Hpt using fun i => exists_hom (𝟙 (Sp R₁)) f₁ (φ := spMap (algebraMap R₁ Ω)) (p₀ := 𝟙 (Sp Ω))
    (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₁) (by
      rw [Category.assoc, p₁.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, φ₂, e₂, p₂⟩ := exists_shrink hR₁ (Sum.elim ![a₁, a₂, a₃, a₄, a₅] b)
    (by rintro (i | i); · fin_cases i <;> assumption
        · exact hb i) p₁
  have es₂ : spMap (algebraMap R₂ Ω) ≫ spMap g₂ = spMap (algebraMap R₁ Ω) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have q₂ := IsPullback.of_hasPullback f₁ (spMap g₂)
  let G : Over (Sp R₂) := Over.mk (pullback.snd f₁ (spMap g₂))
  obtain ⟨_, hcomm, hG⟩ := Hgrp R₂ g₂ (u₂ (.inl 1)) (algebraMap R₂ Ω) Subtype.val_injective c₂ G
    (pullback.fst _ _) φ₂ q₂ e₂ p₂.w
  obtain ⟨L₂, hL₂, eL₂⟩ := Hlb R₂ g₂ (u₂ (.inl 2)) _ _ _ q₂.w
  replace eL₂ := eL₂ φ₂ e₂
  have endo : ∀ v₀ : P.A ⟶ P.A, (∃ u : G.left ⟶ X₁, u ≫ f₁ = pullback.fst f₁ (spMap g₂) ≫ f₁ ∧
      ∀ φ' : P.A.left ⟶ G.left, φ' ≫ pullback.fst f₁ (spMap g₂) = φ₁ → φ' ≫ u = v₀.left ≫ φ₁) →
      ∃ v : G ⟶ G, φ₂ ≫ v.left = v₀.left ≫ φ₂ := by
    rintro v₀ ⟨u, hu, hu'⟩
    refine ⟨Over.homMk (q₂.lift u G.hom (hu.trans q₂.w)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact hu' φ₂ e₂
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      exact p₂.w
  obtain ⟨w, hw⟩ := endo w₀ (Hw R₂ g₂ (u₂ (.inl 3)) _ _ _ q₂.w)
  obtain ⟨wd, hwd⟩ := endo wd₀ (Hwd R₂ g₂ (u₂ (.inl 4)) _ _ _ q₂.w)
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ G, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω) ≫ y.left := fun i => by
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ (.inr i)) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact (hu' _ es₂).symm
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      simp
  choose y hy using pts
  have hsm₂ : SmoothOfRelativeDimension P.g G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₂ hsm₁
  have hab : IsAbelianScheme G :=
    { comm := hcomm
      smooth := SmoothOfRelativeDimension.smooth P.g G.hom
      proper := inferInstanceAs (IsProper (pullback.snd f₁ (spMap g₂)))
      geomConnected := Hconn R₂ g₂ (u₂ (.inl 0)) _ _ _ q₂ }
  have hH₂ := LB.isLB_pull hH₁ (pullback.fst f₁ (spMap g₂))
  have aH₂ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₁ (pullback.fst f₁ (spMap g₂))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) q₂.flip inferInstance)
  have eH₂ := LBIso.trans (isLB_lbPow P.isLB N) (LB.isLB_pull hH₁ _) (LB.isLB_pull hH₂ _) eH₁
    (lbIso_pull_pull hH₁ φ₂ e₂.symm)
  have hfr₂ : ∀ x : Ω, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₁ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩

  have := isFractionRing_of_forall_div hfr₂
  have := isNoetherianRing_of_fg hR₂
  have := hab.proper
  obtain ⟨d₀, hd₀, Hrig⟩ := GlobalTheory.T.exists_rigidification_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.rigid
  obtain ⟨d₁, hd₁, Hsym⟩ := GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.sym
  obtain ⟨d₂, hd₂, Hk⟩ := GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation hL.globalFns R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂
    ((ProjSpace.isProjBy_iff_isProjOver G.hom).2 (aH₂.isProjOver G.hom)) P.ktriv
  obtain ⟨d₃, hd₃, Hs⟩ := GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ w wd w₀ wd₀ hw hwd hw₀ hwd₀ hww hS₁ hS₂
  obtain ⟨d₄, hd₄, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω G P.A φ₂ inferInstance hG _ M y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω) (spMap (algebraMap Ω _)) c c' ?_
    rw [← comp_linComb, ← comp_linComb, h]
  obtain ⟨d₅, hd₅, Ha⟩ := exists_isAmpleLB G.hom hG.1 hL₂ hH₂ P.isLB aH₂ hN eL₂ eH₂
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, φ₃, e₃, p₃⟩ := exists_shrink hR₂ ![d₀, d₁, d₂, d₃, d₄, d₅]
    (by intro i; fin_cases i <;> assumption) hG.1
  have es₃ : spMap (algebraMap R₃ Ω) ≫ spMap g₃ = spMap (algebraMap R₂ Ω) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := isGrpPullback_pullback G (spMap g₃)
  have hL₃ := LB.isLB_pull hL₂ (pullback.fst G.hom (spMap g₃))
  have hab₃ : IsAbelianScheme ((Over.pullback (spMap g₃)).obj G) := by
    have hcomm₃ : IsCommMonObj ((Over.pullback (spMap g₃)).obj G) := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (q₃.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← q₃.2 T x y (pushPt q₃.1.w x) (pushPt q₃.1.w y) rfl rfl,
        ← q₃.2 T y x (pushPt q₃.1.w y) (pushPt q₃.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm₃
            smooth := MorphismProperty.of_isPullback (P := @Smooth) q₃.1 hab.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) q₃.1 hab.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) q₃.1 hab.geomConnected }
  have := hab₃.comm
  have := hab₃.proper
  let P' : PolAV (Sp R₃) :=
    { A := (Over.pullback (spMap g₃)).obj G
      isAb := hab₃
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₃.1 hsm₂
      L := L₂.pull (pullback.fst G.hom (spMap g₃))
      isLB := hL₃
      rigid := Hrig R₃ g₃ (u₃ 0) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      sym := Hsym R₃ g₃ (u₃ 1) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      ample := (relAmple_iff_isAmpleLB_of_isAffine _ hL₃).2 (Ha R₃ g₃ (u₃ 5) _ _ _ q₃.1)
      ktriv := Hk R₃ g₃ (u₃ 2) _ _ _ q₃ hL₃ (lbIso_refl hL₃) }
  have hG₃ : IsGrpPullback P.A P'.A (spMap (algebraMap R₃ Ω)) φ₃ :=
    IsGrpPullback.cancel q₃ (hG.congr es₃.symm e₃.symm) p₃.w
  have eL₃ : LBIso P.L (P'.L.pull φ₃) := LBIso.trans P.isLB (LB.isLB_pull hL₂ _) (LB.isLB_pull hL₃ _) eL₂
    (lbIso_pull_pull hL₂ φ₃ e₃.symm)
  let y' : Fin (2 * P.g) → (baseOver (Sp R₃) ⟶ P'.A) := fun i =>
    Over.homMk (q₃.1.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.1.lift_fst _ _ _
  have hy₃ : ∀ (i₀ : Fin (2 * P.g)) (i : Fin (2 * P'.g)), (i₀ : ℕ) = i →
      (lev.pt i₀).left ≫ φ₃ = spMap (algebraMap R₃ Ω) ≫ (y' i).left := by
    intro i₀ i hi
    obtain rfl : i₀ = i := Fin.ext hi
    refine q₃.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hy', e₃, hy, reassoc_of% es₃]
    · rw [Category.assoc, Category.assoc, hG₃.1.w, Over.w_assoc, Over.w]
      simp
  have hfr₃ : ∀ x : Ω, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := isFractionRing_of_forall_div hfr₃
  have := isNoetherianRing_of_fg hR₃
  obtain ⟨lev', hlev⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep hL R₃ Ω P' P φ₃ hG₃ eL₃ rfl M (Units.map (algebraMap o R₃).toMonoidHom ze) _
    (by simpa using hM.map (algebraMap o R₃)) rfl lev y' hy₃ (Hi R₃ g₃ (u₃ 4) _ _ y' q₃ hy')
  refine ⟨R₃, P', φ₃, lev', le₁.trans (le₂.trans le₃), hR₃, rfl, Hs R₃ g₃ (u₃ 3) _ _ _ q₃ hL₃ (lbIso_refl hL₃),
    hG₃, eL₃, ?_⟩
  rw [hlev]
  exact hy₃

end GlobalTheory.GenSpread
