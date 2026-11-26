module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.H0IsIffNonemptyLinearEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

theorem symB_iff_exists_gen {A : Over (Sp K)} [GrpObj A] (M : LB A.left) :
    SymB M ↔ ∃ u : LB.Gen (LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  have g : ∀ (y : A.left) (j j' : (PUnit → M.ι) × M.ι) (J J' : Fin 2 → M.ι), J 0 = j.1 PUnit.unit → J 1 = j.2 →
      J' 0 = j'.1 PUnit.unit → J' 1 = j'.2 →
      y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j → y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j' →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J' →
      gm (𝟙 _) y _ ((LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).g j j') =
        gm (𝟙 _) y _ ((LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]).g J J') := by
    intro y j j' J J' a b c d hj hj' hJ hJ'
    obtain rfl : J = ![j.1 PUnit.unit, j.2] := by
      funext k; fin_cases k; exacts [a, b]
    obtain rfl : J' = ![j'.1 PUnit.unit, j'.2] := by
      funext k; fin_cases k; exacts [c, d]
    refine (gm_div M (M.pull (GrpObj.inv : A ⟶ A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
      (Eq.trans ?_ (gm_linComb M _ _ (𝟙 _) y _ _ hJ hJ').symm)
    refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
    · exact (gm_pull_g M _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
    · exact (zpow_neg_one _).symm
  constructor
  · rintro ⟨u, hu⟩
    have le : ∀ J : Fin 2 → M.ι, LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J ≤
        (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U (fun _ => J 0, J 1) :=
      fun J y hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.1 hy 1⟩
    exact gen_chartPull (h := 𝟙 _) (A := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A' := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun J => (fun _ => J 0, J 1), le, fun y J J' hJ hJ' =>
        (g y _ _ J J' rfl rfl rfl rfl (le J hJ) (le J' hJ') hJ hJ').symm⟩ u hu
  · rintro ⟨u, hu⟩
    have le : ∀ j : (PUnit → M.ι) × M.ι, (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j ≤
        LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
      fun j y hy => Set.mem_iInter.2 fun k => by
        fin_cases k
        exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
    exact gen_chartPull (h := 𝟙 _) (A' := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' =>
        g y j j' _ _ rfl rfl rfl rfl hj hj' (le j hj) (le j' hj')⟩ u hu

theorem symB_iff_sym {A : Over (Sp K)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) : SymB M ↔ Out.Sym A M := by
  rw [symB_iff_exists_gen]
  have e : ∀ U : (Sp K).Opens, (fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) =
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] := fun U => by
    funext k
    fin_cases k
    exacts [rfl, Category.comp_id _]
  constructor
  · rintro ⟨u, hu⟩ s
    refine ⟨⊤, trivial, ?_⟩
    rw [← e]
    exact ⟨_, DVR.pullGen_isGen M _ _ u hu _⟩
  · intro h
    refine DVR.gen_of_local_base hM _ _ fun s => ?_
    obtain ⟨U, hU, ht⟩ := h s
    exact ⟨U, hU, (e U).symm ▸ ht⟩

namespace Example

section Proj
open GlobalTheory.ProjSpace MvPolynomial

end Proj

end Example
end GlobalTheory.ZV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBaseStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBase
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymCubDense

open GlobalTheory.UU

theorem gen_unique_dense {S U X Y : Scheme.{0}} [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (T : Over S) [Smooth T.hom]
    {F : Y ⟶ T.left} {p : Y ⟶ U} (hP : IsPullback F p T.hom j) (e : U ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (T.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (T.left ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (e ≫ F) y J = val u' (e ≫ F) y J)
    (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J) (hJ : Good M z J) : val u r z J = val u' r z J := by
  refine val_corr hJ (DenseCubeExt.corr_of_open hS j T hM (fun V _ k => (hF V k).symm) hu hu' fun y I hI => ?_) r
  rw [← hP.lift_fst (pullback.fst T.hom j) (pullback.snd T.hom j) pullback.condition]
  refine (val_pull hI _ _ _).symm.trans (Eq.trans ?_ (val_pull hI _ _ _))
  exact gen_unique' hM (fun V _ k => hF V (fun q => k (F ≫ q))) p e he hp (DVR.pullGen_isGen _ _ _ _ hu F)
    (DVR.pullGen_isGen _ _ _ _ hu' F)
    (fun y J hJ => (val_pull hJ _ _ _).trans ((h y J hJ).trans (val_pull hJ _ _ _).symm)) _ _ y I hI

theorem sym_cub_of_dense_abelian : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  intro S U _ hS j _ _ _ _ G _ _ _ _ A _ _ F gp hG hA L c sym hs hr T x y u z J hJ
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ : Smooth (G3 G).hom := CubeExtension.smooth_tensor G (G ⊗ G)
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let sy := fun p : G3 G ⟶ G => LB.pullGen L.L _ _ sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hs _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vs : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (sy p) σ.left z J = val sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a⁻¹ b⁻¹ d⁻¹) (sy (a * b)))
    (sy (a * d))) (sy (b * d))
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a b d)
    (sy (a * b * d))) (sy a)) (sy b)) (sy d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a)⁻¹ (σ ≫ b)⁻¹ (σ ≫ d)⁻¹ * val sym ((σ ≫ a) * (σ ≫ b)).left z J *
        val sym ((σ ≫ a) * (σ ≫ d)).left z J * val sym ((σ ≫ b) * (σ ≫ d)).left z J ∧
      val t₂ σ.left z J = cubV c z J (σ ≫ a) (σ ≫ b) (σ ≫ d) * val sym ((σ ≫ a) * (σ ≫ b) * (σ ≫ d)).left z J *
        val sym (σ ≫ a).left z J * val sym (σ ≫ b).left z J * val sym (σ ≫ d).left z J := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv,
        ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
  let e : Over.mk j ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  have he : eSec (G3 A) ≫ (cubeMapOf gp).F3 = e.left := by
    rw [CubeExtension.eSec_three, GlobalTheory.NormalCubeExt.groupPullback_tripleProductMap_lift, map_one]
  let ρ : T ⟶ G3 G := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique_dense hS j (G3 G) (NormalCubeExt.isPullback_tripleProduct_groupPullback gp) (eSec (G3 A)) (CubeExtension.eSec_comp _)
      (surjective_cube hG hA) L.isLB (fun V _ k => ?_)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _))
        (gs _)) (gs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _)) (gs _)) (gs _)) (gs _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := ((thK ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a b d k) (prod_sym (a * b * d) k))
            (prod_sym a k)) (prod_sym b k)) (prod_sym d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a⁻¹ b⁻¹ d⁻¹ k) (prod_sym (a * b) k))
            (prod_sym (a * d) k)) (prod_sym (b * d) k)).symm)
      simp only [← mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val sym (1 : Over.mk j ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI sym (eSec G) _).symm.trans ((val_corr hI hr _).trans (val_one _))
      rw [he]
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, e₂]
      simp only [inv_one, _root_.mul_one, s1]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁, r₂] at this

end GlobalTheory.SymCubDense
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  first | exact @GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | exact GlobalTheory.SymCubDense.sym_cub_of_dense_abelian | (intros; apply GlobalTheory.SymCubDense.sym_cub_of_dense_abelian <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CubSymPkg

theorem exists_cp_of_generic_sym : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ _ _ G _ _ hG hP L hL hS
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have := hG.smooth
  have := hG.geomConnected
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have hN : Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.ZJ.isNormalScheme_sp R
  let A := (Over.pullback (jK R)).obj G
  let F : A.left ⟶ G.left := pullback.fst G.hom (jK R)
  have gp : IsGrpPullback A G (jK R) F := isGrpPullback_pullback G (jK R)
  have hsA : IsSemiAbelian A := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  have : IsProper A.hom := hP
  have hA : IsAbelianScheme A := Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper A hsA
  have hM : (L.pull F).IsLB := pull_isLB hL F

  obtain ⟨rA, hrA⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hM (eSec A))
  let LA : RigLB A := ⟨L.pull F, rA, hM, hrA⟩
  obtain ⟨t, ht⟩ := GlobalTheory.GenericAmpleDvr.triv_theta hA hM
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hM t ht
  let cA : CubicalStr A LA := AbLaw.Cube.cubicalOfNormalised laws.globalFns hA LA t' ht' hn
  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.ZV.symB_iff_exists_gen _).1 ((GlobalTheory.ZV.symB_iff_sym hM).2 hS)
  obtain ⟨s₁, hs₁, hr₁⟩ := GlobalTheory.AbPackage.exists_rigidified_sym hM s₀ hs₀
  have symA : LA.IsSymmetric := (GlobalTheory.isSymmetric_iff_exists_gen _ A LA).2 ⟨s₁, hs₁, hr₁⟩

  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hL (eSec G))
  let L' : RigLB G := ⟨L, r, hL, hr⟩
  have hw : PGen (GlobalTheory.UU.pullIso L F) := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen hL F)
  obtain ⟨c', -⟩ := GlobalTheory.DenseCubeExt.exists_cubical (L := LA) hN gp cA L' hw
  obtain ⟨s, hs, hrs⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ G L').1
    (GlobalTheory.DenseCubeExt.isSymmetric (L := LA) hN gp L' hw symA)
  exact ⟨⟨L', c', s, hs, hrs, GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base hN (jK R) G A F gp laws.globalFns hA L' c' s hs hrs⟩, rfl⟩

end GlobalTheory.CubSymPkg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetriStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | exact GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | (intros; apply GlobalTheory.CubSymPkg.exists_cp_of_generic_sym <;> assumption)
end
