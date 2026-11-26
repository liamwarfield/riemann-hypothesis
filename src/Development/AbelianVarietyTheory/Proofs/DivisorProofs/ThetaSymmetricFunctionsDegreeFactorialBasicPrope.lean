module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  have h : (Finset.univ.val.map fun b => c (σ b)) = Finset.univ.val.map c := by
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
    rfl
  funext j
  unfold symTup
  rw [h]

theorem map_symTup {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  have h : (Finset.univ.val.map fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  unfold symTup
  rw [h, map_pow]
  congr 1
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

theorem exists_symTup_ne_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : ∃ a, c a ≠ 0) :
    ∃ j, symTup c j ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  by_contra hne
  push Not at hne
  have hc : Multiset.card (Finset.univ.val.map c) = N := by simp
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := by
    intro k hk hkN
    have := hne ⟨k - 1, by omega⟩
    unfold symTup at this
    have h2 := eq_zero_of_pow_eq_zero this
    simpa [Nat.sub_add_cancel hk] using h2
  have hp : ((Finset.univ.val.map c).map fun t => Polynomial.X - Polynomial.C t).prod = Polynomial.X ^ N := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero]
    · simp [Multiset.esymm]
    · intro k hk
      rw [he (k + 1) (Nat.succ_pos _) (Finset.mem_range.1 hk)]
      simp
  have hev := congrArg (Polynomial.eval (c a)) hp
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero] at hev
  · simp only [Polynomial.eval_pow, Polynomial.eval_X] at hev
    exact pow_ne_zero N ha hev.symm
  · simp only [Multiset.mem_map]
    exact ⟨_, ⟨c a, ⟨a, Finset.mem_univ_val a, rfl⟩, rfl⟩, by simp⟩

theorem symTup_basic :
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N),
      symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)),
      symTup (fun b => c (σ b)) = symTup c) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N),
      i (symTup c j) = symTup (fun b => i (c b)) j) ∧
    ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 :=
  ⟨fun _ _ _ c a j => symTup_mul c a j, fun _ _ _ c σ => symTup_perm c σ,
    fun _ _ _ _ i _ c j => map_symTup i c j, fun _ _ _ c h => exists_symTup_ne_zero c h⟩

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPropeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_basic_properties : (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N), symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧ (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)), symTup (fun b => c (σ b)) = symTup c) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N), i (symTup c j) = symTup (fun b => i (c b)) j) ∧ ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 := by
  first | exact @GlobalTheory.UMin.symTup_basic | exact GlobalTheory.UMin.symTup_basic | (intros; apply GlobalTheory.UMin.symTup_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

open GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem lift_comp_left {S : Scheme.{0}} {B₀ B : Over S} (a b : B₀ ⟶ B) {T : Over S} (p q : T ⟶ B₀) :
    (lift p q).left ≫ (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : B₀ ⊗ B₀ ⟶ B ⊗ B).left =
      (lift (p ≫ a) (q ≫ b)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

theorem lamVal_one_left : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → IsAbelianScheme B₀ → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b] (w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left)), w.IsGen → (∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1) → ∀ (T : Over S) (y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) y).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM hB₀ a b _ _ w hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  let β₂ := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let φ1 : Fin 1 → (B₀.left ⟶ (G2 B₀).left) := fun _ => (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B₀) φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ lamφ B₀ i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B₀)]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [lift_comp_left, prod_lam, one_comp_hom a, Category.id_comp, _root_.one_mul b]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM₀ fe' (LB.oneGen M₀) (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M₀ z₀ J₀ →
      val (L := abelian₂ B₀ M₀) (nest M₀ (lamφ B₀) lamε φ1 ε1 g') r z₀ (ind B₀ J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM₀ hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B₀.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S} (c : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B₀ J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B₀) c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S) ⟶ B₀).left ≫ B₀.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S) ⟶ B₀)
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B₀.hom _ he (hG _ _ hB₀).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM₀ y₀
      refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S) ⟶ B₀), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_value_one_zero_first_factor : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → IsAbelianScheme B₀ → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b] (w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left)), w.IsGen → (∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1) → ∀ (T : Over S) (y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) y).left z J J' = 1 := by
  first | exact @GlobalTheory.MumRigidZero.lamVal_one_left | exact GlobalTheory.MumRigidZero.lamVal_one_left | (intros; apply GlobalTheory.MumRigidZero.lamVal_one_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.GenSmoothCover

theorem isPullback_rat (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] [IsFractionRing k K] :
    IsPullback (spMap (algebraMap k K)) (spMap (algebraMap ℚ K)) (spMap (Int.castRingHom k))
      (spMap (algebraMap ℤ ℚ)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  have := Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ k K
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ℤ k ℚ K)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem genericFibre [IsIntegral X] (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) :
    ∃ _ : IsIntegral Y, topologicalKrullDim Y = D ∧ j (genericPoint Y) = genericPoint X := by
  have := h.isDomain
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h H i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = D :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 (by
    rw [Set.top_eq_univ, ← e₃]; exact isIrreducible_singleton.closure)
  have hr (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    have := GenSpread.isIso_stalkMap_of_flat j y
    exact isReduced_of_injective (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm
      (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm.injective
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced Y, e₁, ?_⟩
  rw [← e₂, (genericPoint_spec Y).eq (show IsGenericPoint (i₀ η) Set.univ from e₃)]

theorem exists_closure (hp : IsProjOver p) {K : Type} [Field K] [Algebra k K] [IsFractionRing k K] {W : Scheme.{0}}
    [IsIntegral W] (w : W ⟶ X) (q : W ⟶ Sp K) (hw : w ≫ p = q ≫ spMap (algebraMap k K)) (hq : IsProjOver q) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y) (j : W ⟶ Y), j ≫ ρ = w ∧ IsProjOver (ρ ≫ p) ∧
      IsPullback j q (ρ ≫ p) (spMap (algebraMap k K)) ∧ IsSchemeTheoreticallyDominant j ∧ QuasiCompact j := by
  obtain ⟨M, i, _, rfl⟩ := hq
  have B := ProjSpace.isPullback_baseChange M (algebraMap k K)
  have hP := ProjSpace.isProjOver_pullback hp (ProjSpace.isProjOver_pspace_str k M)
  let π := pullback.fst p (PSpace.str k M) ≫ p
  have : IsProper π := CommonModel.isProper_of_isProjOver hP
  let j : W ⟶ pullback p (PSpace.str k M) :=
    pullback.lift w (i ≫ ProjSpace.baseChange M (algebraMap k K)) (by rw [hw, Category.assoc, Category.assoc, B.w])
  have hj₁ : j ≫ pullback.fst _ _ = w := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i ≫ ProjSpace.baseChange M (algebraMap k K) := pullback.lift_snd _ _ _
  have G := IsPullback.of_hasPullback π (spMap (algebraMap k K))
  let c := G.lift j (i ≫ PSpace.str K M) (by rw [reassoc_of% hj₁, hw])
  have hc₁ : c ≫ pullback.fst _ _ = j := G.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = i ≫ PSpace.str K M := G.lift_snd _ _ _
  let t := B.lift (pullback.fst π (spMap (algebraMap k K)) ≫ pullback.snd _ _) (pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition, G.w])
  have ht₁ : t ≫ _ = _ := B.lift_fst _ _ _
  have ht₂ : t ≫ _ = _ := B.lift_snd _ _ _
  have : IsSeparated (t ≫ PSpace.str K M) := by rw [ht₂]; infer_instance
  have : IsSeparated t := IsSeparated.of_comp t (PSpace.str K M)
  have hct : c ≫ t = i := B.hom_ext (by rw [Category.assoc, ht₁, reassoc_of% hc₁, hj₂])
    (by rw [Category.assoc, ht₂, hc₂])
  have : IsClosedImmersion (c ≫ t) := by rwa [hct]
  have : IsClosedImmersion c := .of_comp c t
  have := flat_specMap_localization (nonZeroDivisors k) K
  have := mono_specMap_localization (nonZeroDivisors k) K
  have : QuasiCompact j := by rw [← hc₁]; infer_instance
  have H := (isPullback_toImage_of_isClosedImmersion j c _ hc₁).flip.paste_vert G
  rw [hc₂] at H
  refine ⟨j.image, j.imageι ≫ pullback.fst _ _, inferInstance, j.toImage, by simp [hj₁], ?_, ?_, inferInstance,
    inferInstance⟩
  · rw [Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hP
  · rw [Category.assoc]
    exact H

theorem exists_isCov_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ), IsArithVar p D → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y),
      FlagChain.IsCov p D ρ ∧ GenSmooth (ρ ≫ p) D := by
  intro hP k _ X p _ D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ρ, ‹_›, ⟨hA, ?_, ?_⟩, fun σ => ?_⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have h₁ := PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks ((s ∣_ U ≫ U.ι) ≫ f) (genericPoint _)
    rw [← e, CurveDegreesCompare.residueDegree_comp, eη] at h₁
    exact left_ne_zero_of_mul h₁
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩

end GlobalTheory.GenSmoothCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExists
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PosAHIsog

open GlobalTheory.PullUnifHom GlobalTheory.PullHermitian GlobalTheory.CechPic

variable {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B]

def trivUnif {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A (LB.triv A.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun _ _ => 1
  fr_hol := fun _ => differentiableOn_const 1
  fr_ne := fun _ _ _ => one_ne_zero
  fr_compat := fun i j z h => by
    simp [valAt', valAt, h]

theorem trivUnif_factor {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    IsFactorAH (trivUnif u) 0 (fun _ => 1) :=
  ⟨Matrix.isHermitian_zero, fun _ => by simp, fun l i z hz => by simp [trivUnif]⟩

theorem pull_chart_iff (φ : A ⟶ B) {L : LB B.left} {g : ℕ} (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (ex' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ B)) (hφ : ∀ z, ex z ≫ φ = ex' z)
    (j : (L.pull φ.left).ι) (z : Fin g → ℂ) :
    ⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔ ⊤ ≤ (ex' z).left ⁻¹ᵁ L.U (j PUnit.unit) := by
  have keyl : (ex z).left ≫ φ.left = (ex' z).left := by rw [← Over.comp_left, hφ]
  exact (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl]))

def pullUnif (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g) (u' : HolUnif B L g)
    (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) : HolUnif A (L.pull φ.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => u'.fr (j PUnit.unit) z
  fr_hol := fun j => (u'.fr_hol (j PUnit.unit)).mono
    (fun z hz => (pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_ne := fun j z hz => u'.fr_ne _ _ ((pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_compat := fun i j z h => by
    have keyl : (u.ex z).left ≫ φ.left = (u'.ex z).left := by rw [← Over.comp_left, hφ]
    have hi := (pull_chart_iff φ u.ex u'.ex hφ i z).1 (le_left' h)
    have hj := (pull_chart_iff φ u.ex u'.ex hφ j z).1 (le_right' h)
    show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
    rw [valAt'_pull_g' _ L _ i j h, keyl]
    exact u'.fr_compat _ _ _ (inf_of _ hi hj)

theorem pullUnif_factor (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g)
    (u' : HolUnif B L g) (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) (hΛ : u.Λ ≤ u'.Λ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (h : IsFactorAH u' Hm χ') :
    IsFactorAH (pullUnif φ u u' hφ) Hm (fun l => χ' ⟨l.1, hΛ l.2⟩) := by
  obtain ⟨h1, h3, h4⟩ := h
  exact ⟨h1, fun l => h3 _, fun l i z hz =>
    h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((pull_chart_iff φ u.ex u'.ex hφ i z).1 hz)⟩

theorem ex_nsmul {G : Over (Sp ℂ)} [GrpObj G] {g : ℕ} (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G))
    (he : ∀ z w, e (z + w) = e z * e w) (he0 : e 0 = 1) (w : Fin g → ℂ) (n : ℕ) :
    e ((n : ℂ) • w) = e w ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he, ih, pow_succ]

theorem unif_ex_zero {G : Over (Sp ℂ)} [GrpObj G] {L : LB G.left} {g : ℕ} (u : HolUnif G L g) : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

end GlobalTheory.PosAHIsog

namespace GlobalTheory.PosAHIsog

open GlobalTheory.CechPic

theorem exists_isog_principal_lam :
    ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → u.IsAH Hm χ →
    ∃ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), 1 ≤ N ∧ IsMonHom ψ ∧ IsMonHom ρ ∧
      ψ ≫ ρ = (𝟙 A) ^ N ∧ ρ ≫ ψ = (𝟙 P.A) ^ N ∧
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) := by
  intro g A _ hA M u Hm χ hM hAH
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  have hint := GlobalTheory.TorusRM.ahFactor_im_int g A M u Hm χ hM (isFactorAH_of_isAH hAH)
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd1, hf1, hEf, hbij⟩ :=
    GlobalTheory.UnimodOver.exists_unimodular_overlattice g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, -, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  haveI : IsReduced P.A.left := GlobalTheory.isReduced_of_smooth_complex _ P.A.hom P.isAb.smooth
  have hsA := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u
  have hsP := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif P.A P.isAb uB
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A P.A g hA P.isAb hsA hsP M P.L u uB
    LinearMap.id (fun x hx => hle' hx)
  obtain ⟨ρ, hρ, hρe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice P.A A g P.isAb hA hsP hsA P.L M uB u
    ((N : ℂ) • LinearMap.id) (fun x hx => by simpa using hNΛ x (hΛB ▸ hx))
  have hψe' : ∀ w, u.ex w ≫ ψ = uB.ex w := fun w => (hψe w).symm
  have hρe' : ∀ w, uB.ex w ≫ ρ = u.ex ((N : ℂ) • w) := fun w => by simpa using (hρe w).symm
  refine ⟨P, ψ, ρ, N, hN, hψ, hρ, ?_, ?_, ?_⟩
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := u.ex_onto x
    rw [← Category.assoc, hψe', hρe', comp_pow, Category.comp_id,
      ex_nsmul u.ex u.ex_add (unif_ex_zero u)]
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := uB.ex_onto x
    rw [← Category.assoc, hρe', hψe', comp_pow, Category.comp_id,
      ex_nsmul uB.ex uB.ex_add (unif_ex_zero uB)]
  · haveI := hψ
    have hM' : (P.L.pull ψ.left).IsLB := pull_isLB P.isLB _
    have hF₃ := pullUnif_factor ψ u uB hψe' hle' Hm χB (isFactorAH_of_isAH hAHB)
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
    have hamp : Out.RelAmple A H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    have hadd := GlobalTheory.T.hermitian_forms_add_of_factor_product g A hA (GlobalTheory.ProjSpace.isProjOver_of_relAmple hamp) (LB.triv A.left) M (P.L.pull ψ.left) (trivUnif u) u (pullUnif ψ u uB hψe')
      0 Hm Hm (fun _ => 1) χ _ (LB.isLB_triv _) hM hM' rfl rfl (trivUnif_factor u) (isFactorAH_of_isAH hAH) hF₃
      (by rw [zero_add])
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    have hLM' : (abelian₂ A (P.L.pull ψ.left)).IsLB := LB.isLB_linComb hM' _ _
    have hLT : (abelian₂ A (LB.triv A.left)).IsLB := LB.isLB_linComb (LB.isLB_triv _) _ _
    have hD : (LB.div (abelian₂ A (P.L.pull ψ.left)) (abelian₂ A (LB.triv A.left))).IsLB := LB.isLB_div hLM' hLT
    have hR : ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left).IsLB :=
      pull_isLB (LB.isLB_linComb P.isLB _ _) _
    refine (cls_eq_iff hLM hR).1 ?_
    have e₁ : cls _ hLM' = lam (cls _ hM') (fst A A) (snd A A) := cls_cube_two hM' _ _ hLM'
    have e₂ : cls _ hLT = lam (cls _ (LB.isLB_triv A.left)) (fst A A) (snd A A) :=
      cls_cube_two (LB.isLB_triv _) _ _ hLT
    rw [(cls_eq_iff hLM hD).2 hadd, cls_div hLM' hLT hD, GlobalTheory.RealMult.Elliptic.cls_pull_lam P.isLB _ _ hR,
      e₁, e₂, cls_pull P.isLB, lam_pull]
    have h0 : cls (LB.triv A.left) (LB.isLB_triv _) = 0 := rfl
    rw [h0]
    simp [lam]

end GlobalTheory.PosAHIsog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two


open CoordCompare TorusCoord in
theorem exists_level_ratio {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
    {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂) (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a]
    (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X → D₁.X)
    (t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X)
    (ht : TorusHomOf h t) (hi : g₁.i ≫ a = t ≫ g₂.i) (hq : a ≫ g₂.q = g₁.q ≫ (Over.pullback (thick R I e)).map b)
    (χ : D₂.X) :
    ∃ u : LB.Gen (LB.LinComb (JN D₁ D₂) (Y := (thickObj R I e D₁.P.A).left)
      (fun k => pullback.fst D₁.P.A.hom (thick R I e) ≫
        Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
      (Sum.elim Oε Oinvε)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
        val (g₂.t χ) (x ≫ a.left) z (rr J) = val (g₁.t (h χ)) x z (rl J) * val u (x ≫ g₁.q.left) z J := by
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  have hp : (Over.map (thick R I e)).map a ≫ g₂.pG = g₁.pG ≫ b := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g₂.q.left = g₁.q.left ≫ ((Over.pullback (thick R I e)).map b).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D₂.P.A.hom (thick R I e) =
        pullback.fst D₁.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D₂.Oφ g₂.pG χ k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₂.Oφ b χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g₂.pG χ k).trans
      ((congrArg (D₂.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g₁.pG b χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D₁.Oφ g₁.pG (h χ) k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₁.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D₁.Oφ · (h χ) k) (Category.comp_id g₁.pG).symm).trans
      ((WeightPf.Oφ_comp g₁.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen (jn_isLB D₁ D₂)
    (φ' := fun k => g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫
      Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
    (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · refine congrArg₂ (· ^ ·) (congrArg f ?_) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
        exact (congrArg (· ≫ coprod.inl) (e₂ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
      · refine congrArg (fun ψ => f ψ ^ Oinvε k) ?_
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coprod.inr) (e₁ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (LB.invGen (JN D₁ D₂) _ _ (p₁.gen (g₁.t (h χ))))
      (LB.pullGen (JN D₁ D₂) _ _ (p₂.gen (g₂.t χ)) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (p₁.gen_isGen (g₁.t_gen _)))
      (pullGen_isGen _ _ _ _ (p₂.gen_isGen (g₂.t_gen χ)) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
      val u r z J = (val (g₁.t (h χ)) r z (rl J))⁻¹ * val (g₂.t χ) (r ≫ a.left) z (rr J) := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.val_inv _ _).trans (congrArg (·⁻¹) (p₁.val_gen _ _ z hJ)))
        ((Geo.Tor.val_pull hJ _ _ _).trans (p₂.val_gen _ _ z hJ))))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq (jn_isLB D₁ D₂) _ _ g₁.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁).hom := by
      rw [← Over.w g₁.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G₁).hom)
    let c : Z' ⟶ thickObj R I e G₁ := Over.homMk r hw
    let c' : Z' ⟶ thickObj R I e G₁ := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g₁ c c' (Over.OverMorphism.ext hr)
    have hτa : c ≫ a = ((τ ≫ t) ≫ g₂.i) * (c' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g₁ (h χ) (Z := Z') (p₁.good hJ) τ c'
    have v₂ := val_torus g₂ χ (Z := Z') (p₂.good hJ) (τ ≫ t) (c' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D₂.X χ) = gm τ.left z ⊤ (charUnit _ D₁.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

theorem prod_unit_hom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {B : Over (Sp R)} [GrpObj B] (p : B ⟶ D.P.A)
    [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec B ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, eSec B ≫ D.Oφ p χ k = eSec D.P.A ≫ D.Oφ (𝟙 _) χ k := fun k =>
    (WeightPf.Oφ_comp η[B] p χ k).trans ((congrArg (D.Oφ · χ k)
      ((IsMonHom.one_hom p).trans (Category.comp_id _).symm)).trans (WeightPf.Oφ_comp η[D.P.A] (𝟙 _) χ k).symm)
  simp only [e0]
  exact (EndData.prod_unit D (𝟙 _) χ h).2


open EndData in
theorem coord_of_lin : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h ⟨ha, hb, hq, hh⟩ χ
  have hC := hR.2.2.2
  have hB := jn_isLB D₁.toPre D₂.toPre
  have p₁ := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have p₂ := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  choose t ht hi using hh
  choose v hv vv using fun e => exists_level_ratio (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a) b h (t e)
    (ht e) (hi e) (hq e) χ
  have down₁ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good D₁.toPre.P.L z J →
      val ((U₁.gt (e + 1)).t χ) (r ≫ thickMap R I e G₁) z J = val ((U₁.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₁.gt_t e χ) r)
  have down₂ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (J), Good D₂.toPre.P.L z J →
      val ((U₂.gt (e + 1)).t χ) (r ≫ thickMap R I e G₂) z J = val ((U₂.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₂.gt_t e χ) r)
  obtain ⟨u, hu, uv⟩ := T.exists_generator_of_compatible_thickening_generators R I hC D₁.toPre.P.A D₁.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)) _ (JN D₁.toPre D₂.toPre) _ _ _ _ hB
    (fun _ _ => rfl) v hv (fun e z J hJ => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U₁.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv (e + 1) _ (𝟙 _ ≫ thickMap R I e G₁) x J hJ
        have k₀ := vv e _ (𝟙 _) x J hJ
        rw [down₁ _ _ _ _ _ _ (p₁.good hJ), Category.assoc, trans_map, ← Category.assoc,
          down₂ _ _ _ _ _ _ (p₂.good hJ), k₀, Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨u, ⟨hu, fun Z r z J hJ => ?_⟩, fun e Z x z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (t' := LB.oneGen _)
      (corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm) r).trans (val_one _))
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ hu _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·)
        (Eq.trans ?_ (prod_unit D₁.toPre (𝟙 _) (h χ) (fun ψ => k (ψ ≫ coprod.inl))).1)
        (Eq.trans ?_ (prod_unit_hom D₂.toPre b χ (fun ψ => k (ψ ≫ coprod.inr))))).trans
        ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oε j) (Category.assoc _ _ _).symm
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oinvε j) (Category.assoc _ _ _).symm
    · have := (U₁.gt e).q_hom
      have k := vv e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G₁).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ (p₂.good hJ),
        TorusCoord.val_unit _ _ (p₁.good hJ), _root_.one_mul, ← uv e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D₁.toPre.P.A) =
        η[thickObj R I e D₁.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val u p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D₁.toPre.P.A).symm).trans k.symm)
  · refine (vv e Z x z J hJ).trans (congrArg (_ * ·) ((uv e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.Mum.Two
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGeneratorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinates_compare_normalisedGenerators : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  first | exact @GlobalTheory.Mum.Two.coord_of_lin | exact GlobalTheory.Mum.Two.coord_of_lin | (intros; apply GlobalTheory.Mum.Two.coord_of_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompOfIsFilLift
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem valR_algX_cxPts {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (τ : k →+* ℂ)
    (U : Y.Opens) (y : GlobalTheory.CxPts p τ) (h : ⊤ ≤ y.1 ⁻¹ᵁ U) (a : k) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = τ a := by
  have h1 := GlobalTheory.Points.valR_appLE y.1 p (U := ⊤) (V := U) (by simp) h
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  have h2 : y.1 ≫ p = Spec.map (CommRingCat.ofHom τ) := y.2
  rw [h2] at h1
  exact h1.trans (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom τ) a)

theorem valR_section_sum : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev τ i y hy m β u x hx
  have h : ⊤ ≤ y.1 ⁻¹ᵁ L.B.U i := hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.T.imageModel_sections_linear_ringOfIntegers K V Ω Nm W ev D X p L ψ s hM hev m β u x hx i, GlobalTheory.Points.valR_eq _ _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← GlobalTheory.Points.valR_eq _ _ h, GlobalTheory.Points.valR_mul _ _ h, valR_algX_cxPts p τ _ y h]

end GlobalTheory.ImageModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinearStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valR_imageModelSection_semilinear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  first | exact @GlobalTheory.ImageModel.valR_section_sum | exact GlobalTheory.ImageModel.valR_section_sum | (intros; apply GlobalTheory.ImageModel.valR_section_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicProperties
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.CrdBasic

theorem pCrd_basic : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  refine ⟨fun o R R' _ _ _ n x v i h => ?_, fun o R _ _ n x v a ha h => ?_, fun o K _ _ n x => ⟨?_, fun v h => ?_⟩⟩
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).1 R' i
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).2.1 ha.unit
  · exact GlobalTheory.ZM.FieldPoint.exists_secCoord o n K x
  · obtain ⟨c, hc⟩ := RepUniq.exists_spMap (x ≫ PSpace.str o n)
    obtain ⟨hv, -⟩ := GlobalTheory.ZM.ProjExt.eq_pt_of_secCoord c x hc v h
    by_contra h0
    push_neg at h0
    have : Ideal.span (Set.range v) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h0 j
    rw [this] at hv
    exact bot_ne_top hv

end GlobalTheory.UMin.CrdBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicPropertiesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveHomogeneousCoords_basic_properties : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  first | exact @GlobalTheory.UMin.CrdBasic.pCrd_basic | exact GlobalTheory.UMin.CrdBasic.pCrd_basic | (intros; apply GlobalTheory.UMin.CrdBasic.pCrd_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeProjOverModL
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option autoImplicit false

namespace GlobalTheory.FibreProj

theorem isProjOver_closed_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (q : X ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  intro k _ X q D hX Z i _ l _ _
  haveI : Module.Finite ℤ k := hX.finite
  exact GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l i

end GlobalTheory.FibreProj
end
