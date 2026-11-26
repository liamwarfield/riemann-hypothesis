module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultTensorOfFinrank
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LieLattice

theorem exists_smul_eq_sum_rows {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {g : ℕ} (M : Matrix (Fin g) (Fin g) K) (hM : M.det ≠ 0) (c : Fin g → K) :
    ∃ d : O, d ≠ 0 ∧ ∃ a : Fin g → O, d • c = ∑ j, a j • M j := by
  obtain ⟨x, hx⟩ : ∃ x : Fin g → K, Matrix.vecMul x M = c :=
    ⟨Matrix.vecMul c M⁻¹, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.vecMul_one]⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  rw [← hx, Matrix.vecMul_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_assoc, ← ha j, algebraMap_smul]

theorem fg_and_span_eq_top {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {g n : ℕ} (L : Submodule O (Fin g → K)) (r : Fin n → O)
    (M : Fin n → Matrix (Fin g) (Fin g) K) (hr : Ideal.span (Set.range r) = ⊤) (hM : ∀ i, (M i).det ≠ 0)
    (hL : ∀ c, c ∈ L ↔ ∀ i, ∃ (k : ℕ) (a : Fin g → O), r i ^ k • c = ∑ j, a j • M i j) :
    L.FG ∧ Submodule.span K (L : Set (Fin g → K)) = ⊤ := by
  constructor
  · let N : Submodule O (Fin g → K) := Submodule.span O (Set.range fun p : Fin n × Fin g => M p.1 p.2)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine Submodule.FG.of_le hN fun c hc => ?_
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N (Set.range r) hr c ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨k, a, h⟩ := (hL c).1 hc i
    refine ⟨k, ?_⟩
    change r i ^ k • c ∈ N
    rw [h]
    exact N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  · classical
    rw [eq_top_iff]
    intro c _
    choose d hd a ha using fun i => exists_smul_eq_sum_rows (O := O) (M i) (hM i) c
    have hD : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd i
    have hmem : (∏ i, d i) • c ∈ L := by
      refine (hL _).2 fun i => ⟨0, fun j => (∏ l ∈ Finset.univ.erase i, d l) * a i j, ?_⟩
      rw [pow_zero, one_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ha, Finset.smul_sum]
      simp only [mul_smul]
    have hK : algebraMap O K (∏ i, d i) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    have e : c = (algebraMap O K (∏ i, d i))⁻¹ • ((∏ i, d i) • c) := by
      rw [← algebraMap_smul K (∏ i, d i) c, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lieLat_fg_and_span_eq_top :
    ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P),
      F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  intro K _ _ P F
  obtain ⟨n, r, M, hr, hM, hL, -⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
  exact fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL

end GlobalTheory.CM.LieLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  first | exact @GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | exact GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | (intros; apply GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieLoc

theorem coord_eq_sum {R₀ R K : Type} [CommRing R₀] [CommRing R] [CommRing K] {f : R₀ →+* R} {g : R →+* K}
    {A₀ : Over (Sp R₀)} {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj A₀] [GrpObj G] [GrpObj A] [IsCommMonObj A]
    {φ : G.left ⟶ A₀.left} {ψ : A.left ⟶ G.left} (hφ : IsGrpPullback G A₀ (spMap f) φ)
    (hψ : IsGrpPullback A G (spMap g) ψ) {n m : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v)
    {e : Fin m → (epsR R ⟶ G)} (he : IsLieBasis e) {M : Fin m → Fin n → K}
    (hM : ∀ i, ∃ w, IsVecOver g ψ (e i) w ∧ IsLieComb (M i) v w)
    {u : epsR R₀ ⟶ A₀} (hu : IsTangent u) {w : epsR K ⟶ A} (hw : IsVecOver (g.comp f) (ψ ≫ φ) u w)
    {c : Fin n → K} (hc : IsLieComb c v w) : ∃ a : Fin m → R, c = ∑ i, g (a i) • M i := by
  choose e₀ h₁ h₂ using hM
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hφ.1 u
  obtain ⟨a, ha, -⟩ := he.2 u' (hu'.isTangent hφ hu)
  have h₃ := (lieComb_baseChange R K g G A ψ hψ m e u' a e₀ w h₁ ha).1
    (EllComp.isVecOver_cancel hφ.1 hψ.1 hu' hw)
  obtain ⟨-, ht, hcomp, -⟩ := LieComb.lieComb_algebra K A n v hv.1
  exact ⟨a, (hv.2 w (ht _ _ hc)).unique hc (hcomp m M e₀ _ w h₂ h₃)⟩

theorem exists_denom {O R R' K : Type} [CommRing O] [CommRing R] [CommRing R'] [CommRing K] [Algebra O R]
    [Algebra R R'] [Algebra O K] (N : Submonoid O) [IsLocalization N R] (r : O)
    [IsLocalization.Away (algebraMap O R r) R'] (g : R' →+* K)
    (hg : ∀ x, g (algebraMap R R' (algebraMap O R x)) = algebraMap O K x) {m : ℕ} (b : Fin m → R') :
    ∃ s ∈ N, ∃ (k : ℕ) (a : Fin m → O), ∀ i, (r ^ k * s) • g (b i) = algebraMap O K (a i) := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (algebraMap O R r)) b
  choose x hx using hk
  obtain ⟨⟨s, hs⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite N x
  choose a ha using h
  refine ⟨s, hs, k, a, fun i => ?_⟩
  rw [← hg, ha, Algebra.smul_def, Algebra.smul_def, map_mul (algebraMap R R'), hx, ← hg, Algebra.smul_def, ← map_mul]
  simp only [map_mul, map_pow]
  ring

theorem lieLat_localization : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  intro K _ _ P F R _ _ _ _ N _ G _ φ ψ e e₀ M hφ hψ hF he hM
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨n, r, M', -, hr, hL, hb⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
    have key : ∀ j, ∃ s ∈ N, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), (r j ^ k * s) • M i = ∑ l, a l • M' j l := by
      intro j
      let R' := Localization.Away (algebraMap (𝓞 K) R (r j))
      have hu : IsUnit (algebraMap R K (algebraMap (𝓞 K) R (r j))) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact IsUnit.mk0 _ (by simpa using (hr j).1)
      let g : R' →+* K := IsLocalization.Away.lift (algebraMap (𝓞 K) R (r j)) hu
      have hg : g.comp (algebraMap R R') = algebraMap R K := IsLocalization.Away.lift_comp _ hu
      have hg' : ∀ x, g (algebraMap R R' (algebraMap (𝓞 K) R x)) = algebraMap (𝓞 K) K x := fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R K, ← hg]; rfl
      let _ : Algebra R' K := g.toAlgebra
      have : IsScalarTower (𝓞 K) R' K := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact (hg' x).symm
      have h' := isGrpPullback_pullback G (spMap (algebraMap R R'))
      have n' : IsGrpPullback F.P₀.A G (spMap g ≫ spMap (algebraMap R R')) ψ :=
        hψ.congr (by rw [spMap_comp_spMap, hg]) rfl
      have w : ψ ≫ G.hom = (F.P₀.A.hom ≫ spMap g) ≫ spMap (algebraMap R R') :=
        n'.1.w.trans (Category.assoc _ _ _).symm
      have e₁ := h'.1.lift_fst _ _ w
      have hψ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ w)
      obtain ⟨e', he', hM'⟩ := hb j R' _ _ _
        (by rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact IsLocalization.Away.algebraMap_isUnit _)
        ((h'.comp hφ).congr (by rw [spMap_comp_spMap, ← IsScalarTower.algebraMap_eq]) rfl) hψ'
        (by rw [← Category.assoc, e₁, hF])
      obtain ⟨b, hb⟩ := coord_eq_sum h' hψ' F.basis he' hM' (he.1 i) (by rw [e₁, hg]; exact (hM i).1) (hM i).2
      obtain ⟨s, hs, k, a, ha⟩ := exists_denom N (r j) g hg' b
      refine ⟨s, hs, k, a, ?_⟩
      rw [hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← smul_assoc, ha, algebraMap_smul]
    classical
    choose s hs k a h using key
    refine ⟨∏ j, s j, prod_mem fun j _ => hs j, (hL _).2 fun j => ⟨k j, (∏ l ∈ Finset.univ.erase j, s l) • a j, ?_⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), smul_smul, ← _root_.mul_assoc, _root_.mul_comm, ← smul_smul, h,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]; rfl
  · induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      exact coord_eq_sum hφ hψ F.basis he (fun i => ⟨_, hM i⟩) hu
        (by rw [hF, ← IsScalarTower.algebraMap_eq]; exact hw) hc
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul t x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨algebraMap (𝓞 K) R t • a, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul K t]

end GlobalTheory.CM.LieLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_localization_modelLieAlgebra : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  first | exact @GlobalTheory.CM.LieLoc.lieLat_localization | exact GlobalTheory.CM.LieLoc.lieLat_localization | (intros; apply GlobalTheory.CM.LieLoc.lieLat_localization <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CM

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

variable {S : Scheme.{0}} {A B X Y : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj Y] [IsCommMonObj Y]

theorem exists_gen_lam_two (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : X ⟶ A) (g : Y ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ X)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ Y) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ Y)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫ (psum A ![fst X Y ≫ a, snd X Y ≫ g] I).left =
          (psum A ![fst T Y ≫ y ≫ a, (snd T Y ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T Y ≫ y) (snd T Y ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst X Y ≫ a = fst T Y ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd X Y ≫ g = (snd T Y ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T Y).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T Y ≫ y ≫ a).left)⁻¹ * h (fst T Y ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T Y) (snd T Y ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T Y) (snd T Y ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ Y, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

theorem weil_value_eq_of_lamEq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hY : IsAbelianScheme Y) {N : RigLB A} {L : RigLB B} (cN : CubicalStr A N) (cL : CubicalStr B L)
    (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) [IsMonHom f₂] [IsMonHom g₂]
    (H : LamEq N.L f₁ f₂ L.L g₁ g₂) {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ X)
    (z : T ⟶ Y) (hf : (y ≫ f₁) ^ n = 1) (hg : (y ≫ g₁) ^ n = 1) (hz : z ^ n = 1) (e e' : Γ(T.left, ⊤)ˣ)
    (he : WeilIs B L.L n (y ≫ g₁) (z ≫ g₂) e) (he' : WeilIs A N.L n (y ≫ f₁) (z ≫ f₂) e') : e = e' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨t, ht, v⟩ := exists_gen_lam_two hG hB cL p₀ hT g₁ g₂ n y hg
  obtain ⟨t', ht', v'⟩ := exists_gen_lam_two hG hA cN p₀ hT f₁ f₂ n y hf
  choose J hJ using fun χ : T.left ⟶ B.left => exists_chart L.isLB (χ p)
  choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := PairingOfLam.val_ratio L.isLB N.isLB H _ t ht t' ht' (fst T Y).left (WeilCube.surj_fst hG hY T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ Y)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ'
  rw [v z e hz he p J hJ, v' z e' hz he' p J' hJ'] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem weilEq_of_lamEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) := by
  intro hl k _ _ _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ H n x y c _ hx hy
  haveI := A.isAb.comm
  haveI := B.isAb.comm
  haveI := Y.isAb.comm
  obtain ⟨rA, hrA⟩ := A.rigid
  obtain ⟨rB, hrB⟩ := B.rigid
  obtain ⟨⟨cA⟩, -⟩ := hl.cube _ A ⟨A.L, rA, A.isLB, hrA⟩ rfl
  obtain ⟨⟨cB⟩, -⟩ := hl.cube _ B ⟨B.L, rB, B.isLB, hrB⟩ rfl
  let T : Over (Sp k) := Over.mk (𝟙 _)
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have h₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have h₃ : (x ≫ g₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₄ : (y ≫ g₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have key := weil_value_eq_of_lamEq hl.globalFns A.isAb B.isAb Y.isAb cA cB f₁ f₂ g₁ g₂ H p₀ hT n x y h₁ h₃ hy
  constructor
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ B n T).1 _ _ h₃ h₄
    exact key e _ he h ▸ he
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ A n T).1 _ _ h₁ h₂
    exact (key _ e h he).symm ▸ he

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.weil_pairing_eq_of_isomorphic_cube_pairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) := by
  first | exact @GlobalTheory.CM.weilEq_of_lamEq | exact GlobalTheory.CM.weilEq_of_lamEq | (intros; apply GlobalTheory.CM.weilEq_of_lamEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
  obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
  obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
  have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
    Φ'.th hx hn.symm hs hw hθ).1 ht'
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
  have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
    rintro _ rfl
    exact hu
  have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
    fun i => huv _
  have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
  have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
      rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, Formalism.L2.Pj.dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
    fun a => ?_, ?_, hv⟩, fun i => ?_⟩
  · exact (hr _ n.base he).symm ▸ hw.2
  · refine Eq.trans ?_ (hm j i)
    have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
    rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Formalism.L2.Pj.dualMap]
  · rw [← hn, ← Category.assoc, hv, Category.assoc]

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.fibKey_keyPB | exact GlobalTheory.LamT.fibKey_keyPB | (intros; apply GlobalTheory.LamT.fibKey_keyPB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF

theorem exists_pat_of_polAV : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → ∃ (T : PAT H (Sp R)) (e : T.t.G ≅ P.A), T.g = P.g ∧ Serre.IsLinearHom T.t.act act e.hom ∧ LamEq P.L e.hom e.hom T.t.PP.L (𝟙 T.t.G) (𝟙 T.t.G) := by
  intro laws E _ _ _ H R _ _ P act hadj
  have : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨L', hL', ⟨rig, hrig⟩, hsym, hamp, hk, hlam, prim⟩ :=
    exists_normalised_polarisation laws R P (act.act H.w0) (act.act (H.bar H.w0)) (act.hom _) (act.hom _)
      (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (hadj H.w0)
  let PP : RigLB P.A := ⟨L', rig, hL', hrig⟩
  let P' : Out.PolAV (Sp R) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := L', isLB := hL', rigid := ⟨rig, hrig⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  obtain ⟨cub⟩ := (laws.cube _ P' PP rfl).1
  have sym : PP.IsSymmetric :=
    GlobalTheory.PrimNorm.isSymmetric_of_hasGen PP (exists_gen_neg_of_sym laws.globalFns P.isAb hL' hsym)
  have lb : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ P.A)) {L : LB P.A.left}, L.IsLB → (cubeLB P.A x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have pts := ((GlobalTheory.LamCalc.lamEq_calculus _ P.A P.A P.A P.A P.A L' P.L P.L hL' P.isLB P.isLB
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hlam).2.2.2.2
  simp only [Category.comp_id] at pts
  have adj : ∀ a, LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] L')
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act (H.bar a)] L') := fun a =>
    LBIso.trans (lb _ hL') (lb _ P.isLB) (lb _ hL') (pts _ _ _)
      (LBIso.trans (lb _ P.isLB) (lb _ P.isLB) (lb _ hL')
        (by simpa only [LamEq, Category.comp_id] using hadj a) (pts _ _ _).symm)
  exact ⟨{ t := { G := P.A, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb, act := act, PP := PP, cub := cub,
                  sym := sym, adj := adj, prim := prim },
           ab := P.isAb, g := P.g, dim := P.smoothDim, sym := hsym, ample := hamp, ktriv := hk },
    Iso.refl _, rfl, Serre.IsLinearHom.id act, LBIso.symm hlam⟩

end GlobalTheory.LamF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

theorem locMod_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  intro E _ _ _ H Dw l Xo c _ z T iK
  refine ⟨fun h => ?_, fun M T' ψ i hψ => ?_⟩
  · have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
    let ρ : 𝓞 z.K →+* T.V := e.symm.toRingHom.comp
      ((iK.comp (algebraMap (𝓞 z.K) z.K)).codRestrict (algebraMap T.V T.Fr).range fun a => h a)
    have hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K) := by
      ext a
      exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h a⟩)
    obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ρ z.B).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ iK z.Φ.T).1
    obtain ⟨m1, h1⟩ := sab_comp_exists n' z.Φ.m _ rfl
    obtain ⟨k, hk⟩ := sab_comp_exists n' z.m' _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T.V T.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hρ])
    exact ⟨⟨ρ, hρ, G, t', n, n', m1, m2, h1, h2.trans hk⟩⟩
  · obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ψ M.G).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ i M.t').1
    obtain ⟨N, hN⟩ := sab_comp_exists n M.n _ (spectrumMap_comp M.ρ ψ)
    obtain ⟨N', hN'⟩ := sab_comp_exists n' M.n' _ (spectrumMap_comp iK i)
    obtain ⟨m1, h1⟩ := sab_comp_exists n' M.m1 (spMap (i.comp iK) ≫ z.x)
      (by rw [spectrumMap_comp, Category.assoc])
    obtain ⟨k, hk⟩ := sab_comp_exists n' M.m2 _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T'.V T'.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hψ])
    refine ⟨⟨ψ.comp M.ρ, ?_, G, t', N, N', m1, m2, ?_, ?_⟩, n, n', h1, h2.trans hk⟩
    · rw [← RingHom.comp_assoc, hψ, RingHom.comp_assoc, M.hρ, RingHom.comp_assoc]
    · rw [h1, hN', M.h1, Category.assoc]
    · rw [hN, hN', ← Category.assoc, h2, hk, Category.assoc, M.h2, Category.assoc]

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPoint_localModel_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  first | exact @GlobalTheory.LamT.locMod_exists | exact GlobalTheory.LamT.locMod_exists | (intros; apply GlobalTheory.LamT.locMod_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyPolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

theorem exists_inverse_isogeny_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → Surjective Φ.left → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hU hL K _ σ P P' Φ hg hΦ hs
  obtain ⟨hf, hfl, n, hn, hk⟩ := isogeny_of_surjective_polAV hU hL K σ P P' Φ hg hΦ hs
  have := P.isAb.comm
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 P.A ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 P.A ^ m) (𝟙 P.A) ≫ μ[P.A]))
  have hm := hpow n
  obtain ⟨⟨ψ, hψ, e⟩, hE⟩ := exists_monHom_factor_of_flat_surjective _ P.A P'.A P.A Φ (𝟙 P.A ^ n) hΦ hm hfl hs inferInstance
    (fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hk T x hx])
  refine ⟨n, ψ, hn, hψ, e, ?_⟩
  rw [← cancel_epi Φ, reassoc_of% e, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
    Category.comp_id]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyPolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_isogeny_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → Surjective Φ.left → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  first | exact @GlobalTheory.exists_inverse_isogeny_polAV | exact GlobalTheory.exists_inverse_isogeny_polAV | (intros; apply GlobalTheory.exists_inverse_isogeny_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isGrpPullback_polAV (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', g, hg, hd, hm, -⟩ := hB S S' f P
  refine ⟨P', g, hd, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
  have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
  rw [ex, ey, ← hm]
  rfl

theorem IsGrpPullback.id_pow_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h G'
  have h1 : (E (𝟙 G')).left = φ := by rw [hE]; exact Category.id_comp _
  have h2 : E (𝟙 G' ^ N) = E (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← hE, h2, Over.comp_left, h1]

theorem exists_inverse_isogeny_ringOfIntegers :
    ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hT hL hE K _ _ σ P P' Φ hg hΦ honto
  obtain ⟨Q, φ, hQ, hφ⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P
  obtain ⟨Q', φ', hQ', hφ'⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P'
  obtain ⟨⟨Φ₀, hΦ₀, -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ _ P.A P'.A Q.A Q'.A φ φ' hφ hφ' Φ
  have hm₀ : IsMonHom Φ₀ := hmon Φ₀ hΦ₀ hΦ
  have hs : Surjective Φ.left :=
    (GlobalTheory.OntoSurj.surjective_of_onto_complex_points (𝓞 K) (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) P'.A P.A Φ P'.isAb P.isAb honto).1
  have hpb : IsPullback φ Φ₀.left Φ.left φ' := by
    refine IsPullback.of_bot ?_ hΦ₀.symm hφ'.1
    rw [Over.w Φ₀, Over.w Φ]
    exact hφ.1
  have hs₀ : Surjective Φ₀.left := MorphismProperty.of_isPullback (P := @Surjective) hpb hs
  obtain ⟨N, ψ₀, hN, hψ₀, e₁, e₂⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_polAV hT hL K σ Q Q' Φ₀ (hQ.trans (hg.trans hQ'.symm)) hm₀ hs₀
  obtain ⟨ψ, hψ, eψ, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P.A Q'.A Q.A φ' φ
    P'.isAb P.isAb hφ' hφ ψ₀ hψ₀
  refine ⟨N, ψ, hN, hψ, ?_, ?_⟩
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P.A P.A Q.A Q.A φ φ
      P.isAb P.isAb hφ hφ (Φ₀ ≫ ψ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, eψ, ← Category.assoc, hΦ₀, Category.assoc]
    · rw [e₁]; exact IsGrpPullback.id_pow_left hφ N
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P'.A Q'.A Q'.A φ' φ'
      P'.isAb P'.isAb hφ' hφ' (ψ₀ ≫ Φ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hΦ₀, ← Category.assoc, eψ, Category.assoc]
    · rw [e₂]; exact IsGrpPullback.id_pow_left hφ' N

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_isogeny_of_surjective_points : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | exact GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekind
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FamDescent

theorem lamEq_descend {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X Y A B : Over (Sp R)} {X' Y' A' B' : Over (Sp k)} [GrpObj X] [GrpObj Y]
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj A'] [IsCommMonObj A'] [GrpObj B'] [IsCommMonObj B']
    (hX : IsAbelianScheme X) (hY : IsAbelianScheme Y)
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hx : IsPullback x X'.hom X.hom (spMap f)) (hy : IsPullback y Y'.hom Y.hom (spMap f))
    (hA : IsGrpPullback A' A (spMap f) a) (hB : IsGrpPullback B' B (spMap f) b)
    {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (iL : LBIso (L.pull a) L') (iM : LBIso (M.pull b) M')
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} [IsMonHom f₁] [IsMonHom f₂] [IsMonHom g₁] [IsMonHom g₂]
    {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'} {g₂' : Y' ⟶ B'}
    (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left)
    (H : LamEq L' f₁' f₂' M' g₁' g₂') : LamEq L f₁ f₂ M g₁ g₂ := by
  obtain ⟨Pic, _, cl, pl, hiso, -, -, hcomp, hlin, -⟩ := CechPicMul.exists_picardGroup
  have hpull : ∀ {U V : Scheme.{0}} (N : LB U), N.IsLB → ∀ g : V ⟶ U, (N.pull g).IsLB ∧ cl (N.pull g) = pl g (cl N) :=
    fun N hN g => ⟨(hlin _ _ N hN _ _ _).1, (hlin _ _ N hN _ _ _).2.trans (by simp)⟩
  let π := pullback.fst (X ⊗ Y).hom (spMap f)
  let p := pullback.snd (X ⊗ Y).hom (spMap f)
  have hπ : π ≫ (X ⊗ Y).hom = p ≫ spMap f := pullback.condition
  let u : Over.mk p ⟶ X' := Over.homMk (hx.lift (π ≫ (fst X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hx.lift_snd _ _ _)
  let v : Over.mk p ⟶ Y' := Over.homMk (hy.lift (π ≫ (snd X Y).left) p (by rw [Category.assoc, Over.w, hπ]))
    (hy.lift_snd _ _ _)
  have hu : u.left ≫ x = π ≫ (fst X Y).left := hx.lift_fst _ _ _
  have hv : v.left ≫ y = π ≫ (snd X Y).left := hy.lift_fst _ _ _
  let U : Over.mk ((Over.mk p).hom ≫ spMap f) ⟶ X ⊗ Y := Over.homMk π hπ
  have gen : ∀ {C : Over (Sp R)} {C' : Over (Sp k)} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C (spMap f) c) {N : LB C.left} {N' : LB C'.left}, N.IsLB → N'.IsLB →
      LBIso (N.pull c) N' → ∀ (s : X ⟶ C) (t : Y ⟶ C) (s' : X' ⟶ C') (t' : Y' ⟶ C'),
      s'.left ≫ c = x ≫ s.left → t'.left ≫ c = y ≫ t.left →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull π) = cl (cubeLB C' ![u ≫ s', v ≫ t'] N') := by
    intro C C' _ _ c hC N N' hN hN' iN s t s' t' hs ht
    have e : pl c (cl N) = cl N' := (hpull N hN c).2.symm.trans ((hiso _ _ _ (hpull N hN c).1 hN').2 iN)
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) π).2.trans ?_
    refine (congrArg (pl π) (hlin _ _ N hN _ _ _).2).trans (Eq.trans ?_ (hlin _ _ N' hN' _ _ _).2.symm)
    rw [map_prod]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [map_zpow, ← hcomp, ← e, ← hcomp]
    refine congrArg (fun z => pl z (cl N) ^ _) (Eq.symm ?_)
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I.down
    fin_cases i
    · refine Over.OverMorphism.ext ?_
      show (u.left ≫ s'.left) ≫ c = π ≫ (fst X Y).left ≫ s.left
      rw [Category.assoc, hs, ← Category.assoc, hu, Category.assoc]
    · refine Over.OverMorphism.ext ?_
      show (v.left ≫ t'.left) ≫ c = π ≫ (snd X Y).left ≫ t.left
      rw [Category.assoc, ht, ← Category.assoc, hv, Category.assoc]
  have zero : ∀ {C : Over (Sp R)} [GrpObj C] [IsCommMonObj C] {N : LB C.left}, N.IsLB →
      ∀ (s : X ⟶ C) (t : Y ⟶ C), IsMonHom s → IsMonHom t →
      cl ((cubeLB C ![fst X Y ≫ s, snd X Y ≫ t] N).pull (eSec (X ⊗ Y))) = 1 := by
    intro C _ _ N hN s t _ _
    refine (hpull _ (LamCalc.cubeLB_isLB hN _) _).2.trans ?_
    rw [LamCalc.class_cubeLB cl (fun z => pl z (cl N)) (fun I _ φ ε => (hlin _ _ N hN I φ ε).2)]
    have w : ∀ z : X ⊗ Y ⟶ C, η[X ⊗ Y] ≫ z = 1 →
        pl (eSec (X ⊗ Y)) (pl z.left (cl N)) = pl (1 : 𝟙_ (Over (Sp R)) ⟶ C).left (cl N) := fun z hz => by
      rw [← hcomp, ← hz]; rfl
    have o : (1 : 𝟙_ (Over (Sp R)) ⟶ C) = η[C] := by simp [Hom.one_def]
    have h₁ : η[X ⊗ Y] ≫ fst X Y ≫ s = 1 := by rw [o]; exact IsMonHom.one_hom _
    have h₂ : η[X ⊗ Y] ≫ snd X Y ≫ t = 1 := by rw [o]; exact IsMonHom.one_hom _
    simp only [map_mul, map_inv]
    rw [w _ h₁, w _ h₂, w 1 (MonObj.comp_one _), w _ (by rw [MonObj.comp_mul, h₁, h₂, _root_.mul_one])]
    simp
  have cL := LamCalc.cubeLB_isLB hL ![fst X Y ≫ f₁, snd X Y ≫ f₂]
  have cM := LamCalc.cubeLB_isLB hM ![fst X Y ≫ g₁, snd X Y ≫ g₂]
  refine GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain R k f hf (X ⊗ Y) (AbelianSchemeGerms.isAbelianScheme_tensor X Y hX hY) _ π p (IsPullback.of_hasPullback _ _)
    _ _ cL cM ?_ ?_
  · exact (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((zero hL f₁ f₂ ‹_› ‹_›).trans (zero hM g₁ g₂ ‹_› ‹_›).symm)
  · refine (hiso _ _ _ (hpull _ cL _).1 (hpull _ cM _).1).1
      ((gen hA hL hL' iL _ _ _ _ e₁ e₂).trans (Eq.trans ?_ (gen hB hM hM' iM _ _ _ _ e₃ e₄).symm))
    exact (hiso _ _ _ (LamCalc.cubeLB_isLB hL' _) (LamCalc.cubeLB_isLB hM' _)).2 (LamCalc.lbIso_of_lamEq H u v)

theorem isFam_descend : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  intro _ E _ _ _ H R _ _ ω C D h T L ψ k _ ω' C' f φ T' m ψ' hf hE hψ hF
  obtain ⟨-, ⟨-, hC, iC⟩, -, hact⟩ := hE
  obtain ⟨hlin, hadd, hsm, hlam⟩ := hF
  have : IsSchemeTheoreticallyDominant (spMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have : QuasiCompact (spMap f) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  have := C.P.isAb.smooth
  have : Flat C.P.A.hom := inferInstance
  have : IsSeparated T.t.G.hom := T.t.semi.separated
  have hm : ∀ a, IsMonHom (ψ a) := fun a =>
    have := (hlin a).isMonHom
    ExtUnique.isMonHom_of_isGrpPullback hC m.cart (ψ' a) (ψ a) (hψ a)
  refine ⟨fun a => ⟨hm a, fun c => ?_⟩, fun a b => ?_, fun s a => ?_, fun a b => ?_⟩
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    have e := congrArg (fun z => z.left ≫ m.φ) ((hlin a).comm c)
    simp only [Over.comp_left, Category.assoc, Serre.comapAct_act] at e ⊢
    rw [hψ, m.act, ← Category.assoc, ← Category.assoc, hact, hψ, Category.assoc, Category.assoc] at e
    exact e
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    let φ₀ : Over.mk (C'.P.A.hom ≫ spMap f) ⟶ C.P.A := Over.homMk φ hC.1.w
    have e := m.cart.2 C'.P.A (ψ' a) (ψ' b) (φ₀ ≫ ψ a) (φ₀ ≫ ψ b) (hψ a).symm (hψ b).symm
    rw [← MonObj.comp_mul] at e
    rw [← hψ, hadd, ← e]
    rfl
  · refine ExtUnique.over_hom_ext_of_isPullback (j := spMap f) hC.1 ?_
    rw [← hψ, hsm, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hψ, Category.assoc]
  · have := hm a
    have := hm b
    have := C.act.hom (h a b)
    exact lamEq_descend f hf C.P.isAb C.P.isAb hC.1 hC.1 m.cart hC T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB
      (LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1))
      iC (hψ a) (hψ b) (hact _) (by simp) (hlam a b)

end GlobalTheory.FamDescent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyIdentitiesDescendFieldToDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_identities_descend_field_to_dedekind : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (k : Type) [Field k] (ω' : k) (C' : Ell H k ω') (f : R →+* k) (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp k)) (m : SABMap T'.t T.t (spMap f)) (ψ' : L → (C'.P.A ⟶ T'.t.G)), Function.Injective f → EllMap C' C f φ → (∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left) → IsFam C' T' h L ψ' → IsFam C T h L ψ := by
  first | exact @GlobalTheory.FamDescent.isFam_descend | exact GlobalTheory.FamDescent.isFam_descend | (intros; apply GlobalTheory.FamDescent.isFam_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VecLineNormSqEqForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM.LieMetric

theorem vecLine_norm_sq_eq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ s : K →+* ℂ, ℓ.n s ^ 2 = (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hU hL K _ _ A x φ hf h H i ℓ hℓ s
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := hℓ.2.2 s
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ s x xs hpb
  have hc : IsLieComb (Pi.single i 1) x.v (x.v i) :=
    (LieComb.isLieComb_iff_tanExp _ _).2 (LieComb.tanExp_single x.basis.1 i).symm
  have hv' : IsVecOver s ψ (x.v i) (xs.v (i.cast hg.symm)) := hv (i.cast hg.symm)
  have := form_eq_pi_mul_hermForm hU hL K A (GenFib.mk x.P φ hf x.v x.basis) h H s xs.P ψ u Hm χ hψ hA
    _ _ _ _ _ _ W W hc hc hv' hv' hW hW
  rw [e]
  refine Eq.trans ?_ (congrArg Complex.re this).symm
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.CM.LieMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDet
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.TopLieVector

theorem sq_eq_det_gram : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (T abelian₂ : MLine K) (s : K →+* ℂ), KeyArchAt x T abelian₂ s → abelian₂.n s ^ 2 = (h.gram s (fun i : Fin x.P.g => Pi.single i 1)).det.re := by
  intro hU _ K _ _ P x φ₀ hf₀ h hH T abelian₂ σ hx
  obtain ⟨x', u, Hm, W, χ, θ, Fd, hx, hA, -, -, hW, hF, -, hn⟩ := hx
  obtain ⟨φ, -, w, e, D, hp, hw, -, -, h₁, h₂, hv⟩ := hx
  obtain rfl := TopDifferential.eq_dualMapR h₁ h₂
  obtain ⟨Q, ψ, v, u', Hm', χ', W', a, b, c, d⟩ := hH σ
  have hf : IsPolFibre σ x.P x'.P φ := ⟨e, hp, LBIso.symm ⟨w, hw⟩⟩
  have key := LieMetric.hermForm_eq hU a hf b hA x.basis.1 c (w' := fun i => x'.v (i.cast e.symm))
    (W' := fun i => W (i.cast e.symm)) fun i => ⟨hv (i.cast e.symm), hW _⟩
  have e₁ : h.gram σ (fun i : Fin x.P.g => Pi.single i 1) =
      (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).submatrix (finCongr e.symm) (finCongr e.symm) := by
    ext i j
    exact (d i j).trans (congrArg (fun z => (Real.pi : ℂ) * z) (key j i))
  obtain ⟨Ef, t₁, t₂, -, -, t₃, -⟩ := AHWeil.tangent_and_weil_of_isAH hU x'.P _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hF
  rw [e₁, Matrix.det_submatrix_equiv_self, TopDifferential.det_gram, hn, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right hvol]

end GlobalTheory.CM.TopLieVector
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topLieVector_norm_sq_eq_gramDet : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (T abelian₂ : MLine K) (s : K →+* ℂ), KeyArchAt x T abelian₂ s → abelian₂.n s ^ 2 = (h.gram s (fun i : Fin x.P.g => Pi.single i 1)).det.re := by
  first | exact @GlobalTheory.CM.TopLieVector.sq_eq_det_gram | exact GlobalTheory.CM.TopLieVector.sq_eq_det_gram | (intros; apply GlobalTheory.CM.TopLieVector.sq_eq_det_gram <;> assumption)
end
end
