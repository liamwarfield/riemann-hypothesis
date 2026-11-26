module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem conj_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w l : Fin g → ℂ) :
    l ⬝ᵥ Hm.mulVec (star w) = (starRingEnd ℂ) (w ⬝ᵥ Hm.mulVec (star l)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (Hm i j) = Hm j i := by
    have := hH.apply j i
    simpa using this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [h1]
  ring

theorem exists_basis_in {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (s : Set (Fin g → ℂ)) (b : Module.Basis s ℝ (Fin g → ℂ)), Finite s ∧ ∀ i, b i ∈ Λ := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  let b := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hΛ])
  refine ⟨s, b, ?_, ?_⟩
  · exact Module.Finite.finite_basis b
  · intro i
    rw [Module.Basis.mk_apply]
    exact hs i.2

end GlobalTheory.ThetaLiouville

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem im_form_mem_int (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hθ : Differentiable ℂ θ) (hθ0 : ∀ z, θ z ≠ 0)
    (hper : ∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) :
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  set u : Fin g → ℂ := Hm.mulVec (star w) with hu
  let ψ : (Fin g → ℂ) → ℂ := fun z => θ z * Complex.exp (-(Real.pi * (z ⬝ᵥ u)))
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ u) := by
    have : (fun z : Fin g → ℂ => z ⬝ᵥ u) = fun z => ∑ i, z i * u i := rfl
    rw [this]
    exact Differentiable.fun_sum fun i _ => (differentiable_apply i).mul_const _
  have hψ : Differentiable ℂ ψ :=
    hθ.mul ((hlin.const_mul _).neg.cexp)

  have hshift : ∀ l ∈ Λ, ∀ z, ψ (z + l) = ψ z *
      Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) := by
    intro l hl z
    have hc := conj_form Hm hH w l
    simp only [ψ, hper l hl z, add_dotProduct]
    rw [hc]
    set a := w ⬝ᵥ Hm.mulVec (star l)
    have hsub : a - (starRingEnd ℂ) a = ((2 * a.im : ℝ) : ℂ) * I := by
      rw [Complex.sub_conj]
    rw [← hsub]
    rw [show -(↑Real.pi * (z ⬝ᵥ u + (starRingEnd ℂ) a)) =
        -(↑Real.pi * (z ⬝ᵥ u)) + (-(↑Real.pi * (starRingEnd ℂ) a)) by ring,
      Complex.exp_add,
      show (↑Real.pi * (a - (starRingEnd ℂ) a)) = ↑Real.pi * a + (-(↑Real.pi * (starRingEnd ℂ) a))
        by ring, Complex.exp_add]
    ring
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖ψ (z + l)‖ = ‖ψ z‖ := by
    intro l hl z
    rw [hshift l hl z, norm_mul, Complex.norm_exp]
    simp

  obtain ⟨s, b, hfin, hbΛ⟩ := exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hbΛ i
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul n x _ hx => exact Λ.toAddSubgroup.zsmul_mem hx n
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan _ (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l hl
  have hconst : ψ (0 + l) = ψ 0 := hψ.apply_eq_apply_of_bounded hbd _ _
  rw [hshift l hl 0] at hconst
  have hψ0 : ψ 0 ≠ 0 := mul_ne_zero (hθ0 0) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) = 1 := by
    have := hconst
    rw [mul_eq_left₀ hψ0] at this
    exact this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) = n := by
    have : (Real.pi : ℂ) * 2 * I * ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) =
        (Real.pi : ℂ) * 2 * I * n := by
      push_cast at hn
      linear_combination hn
    have h0 : (Real.pi : ℂ) * 2 * I ≠ 0 := mul_ne_zero (mul_ne_zero hpi two_ne_zero) hI
    exact mul_left_cancel₀ h0 this
  exact_mod_cast h2

end GlobalTheory.ThetaLiouville
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensAct

open GlobalTheory.Mum

section Hom

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

end Hom

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def matAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j)

theorem matAct_pr (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    matAct T A ≫ T.pr i = ∏ j, T.pr j ^ A i j :=
  T.lim.fac (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j) ⟨i⟩

theorem hom_ext (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} {a b : X ⟶ D'.P.A}
    (h : ∀ i, a ≫ T.pr i = b ≫ T.pr i) : a = b :=
  T.lim.hom_ext fun i ↦ h i.as

def latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) : D'.X :=
  T.xe.symm fun i ↦ ∑ j, A i j • T.xe y j

theorem xe_latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (i : Fin r) :
    T.xe (latAct T A y) i = ∑ j, A i j • T.xe y j := by
  simp [latAct]

section Ring

theorem zpow_finsetSum {M : Type} [CommGroup M] (a : M) {K : Type} (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem matAct_hom (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (matAct T A) := by
  have hp := T.pr_hom
  refine GlobalTheory.MatrixAction.isMonHom_of_points _ (fun X ↦ hom_ext T fun i ↦ ?_) (fun X x y ↦ hom_ext T fun i ↦ ?_)
  · rw [Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, MonObj.one_comp (T.pr i)]
    refine Finset.prod_eq_one fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, MonObj.one_comp, one_zpow]
  · rw [MonObj.mul_comp _ _ (T.pr i), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem matAct_one (T : Tens D D' W) : matAct T 1 = 𝟙 _ := by
  refine hom_ext T fun i ↦ ?_
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · rw [Matrix.one_apply_eq, zpow_one]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem matAct_mul (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A * B) = matAct T B ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [Category.assoc, matAct_pr, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  have e1 : ∀ k, matAct T B ≫ T.pr k ^ A i k = ∏ l, T.pr l ^ (A i k * B k l) := fun k ↦ by
    rw [GrpObj.comp_zpow, matAct_pr, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ e1 k, Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.mul_apply, zpow_finsetSum]

theorem matAct_add (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A + B) = matAct T A * matAct T B := by
  refine hom_ext T fun i ↦ ?_
  have := T.pr_hom i
  rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.add_apply, zpow_add]

def latEnd (T : Tens D D' W) : Matrix (Fin r) (Fin r) ℤ →+* Module.End ℤ D'.X where
  toFun A :=
    { toFun := latAct T A
      map_add' := fun y z ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_add (f := _), Pi.add_apply, smul_add, Finset.sum_add_distrib])
      map_smul' := fun n y ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_zsmul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _) }
  map_one' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.one_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h)
  map_mul' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.mul_apply, Matrix.mul_apply,
      Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm)
  map_zero' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp [xe_latAct])
  map_add' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, LinearMap.add_apply, map_add (f := _), Pi.add_apply,
      Matrix.add_apply, add_smul, Finset.sum_add_distrib])

abbrev tensModule (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Module O D'.X :=
  Module.compHom D'.X ((latEnd T).comp ρ)

def ringAct (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : RingAct D'.P.A O where
  act a := matAct T (ρ a)
  hom a := matAct_hom T (ρ a)
  map_one := by rw [map_one, matAct_one]
  map_mul a b := by rw [map_mul, matAct_mul]
  map_add a b := by rw [map_add (f := _), matAct_add]; rfl

def cHom (D : DegPre R) : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (D.c x)) fun a b ↦ by rw [D.c_add]; rfl

theorem c_lin (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) :
    D'.c (latAct T A y) = D'.c y ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [T.c_pr, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, xe_latAct]
  have e := map_sum (cHom D) (fun j ↦ A i j • T.xe y j) Finset.univ
  simp only [map_zsmul] at e
  apply Additive.ofMul.injective
  refine e.trans ?_
  rw [ofMul_prod]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GrpObj.comp_zpow, T.c_pr, ofMul_zpow]
  rfl

end Ring

end GlobalTheory.TensAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBas
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section General

variable {A : Type} [Ring A]

theorem span_mul_mem {S : Set A} (h : ∀ s ∈ S, ∀ y, s * y ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) (y : A) :
    x * y ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx y
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

theorem span_map_mem (f : A →+* A) {S : Set A} (h : ∀ s ∈ S, f s ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) :
    f x ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem sup_mul_mem {I K : Ideal A} (hI : ∀ x ∈ I, ∀ y, x * y ∈ I) (hK : ∀ x ∈ K, ∀ y, x * y ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) (y : A) : x * y ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [add_mul]
  exact add_mem (Ideal.mem_sup_left (hI a ha y)) (Ideal.mem_sup_right (hK b hb y))

theorem sup_map_mem (f : A →+* A) {I K : Ideal A} (hI : ∀ x ∈ I, f x ∈ I) (hK : ∀ x ∈ K, f x ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) : f x ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact add_mem (Ideal.mem_sup_left (hI a ha)) (Ideal.mem_sup_right (hK b hb))

end General

section Filt

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem fil_anti' {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, h.trans h2, h3⟩

theorem fil_mul_mem' {m n : ℕ} {a b : B} (ha : a ∈ fil δ m) (hb : b ∈ fil δ n) : a * b ∈ fil δ (m + n) := by
  have key : fil δ m * fil δ n ≤ fil δ (m + n) := by
    rw [fil, fil, Ideal.span_mul_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, ⟨l, hl, hs, rfl⟩, y, ⟨l', hl', hs', rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hp with hp | hp
      exacts [hl p hp, hl' p hp]
    · simp only [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.prod_append]
  exact key (Ideal.mul_mem_mul ha hb)

end Filt

section Main

variable (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

def relGen : Set (DR R B) :=
  {x | ∃ n : ℕ, ∃ a ∈ J, x = ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)}

theorem rel_eq_span : rel R δ = Ideal.span (relGen R δ) := rfl

theorem rel_mul_mem {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨n, a, ha, rfl⟩ := hs
  rw [ι_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem sgn_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨n, a, ha, rfl⟩ := hs
  change sgn (ι1 _) ∈ _
  rw [sgn_ι]
  exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem filSpan_mul_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n))
    (y : DR R B) : x * y ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨b, hb, rfl⟩ := hs
  rw [Algebra.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, hb, rfl⟩)

theorem filSpan_sgn_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    sgn x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨b, hb, rfl⟩ := hs
  change sgn (algebraMap B _ b) ∈ _
  rw [AlgHom.commutes]
  exact Ideal.subset_span ⟨b, hb, rfl⟩

theorem filSpan_smul_mem (m n : ℕ) {b : B} (hb : b ∈ fil δ m) {x : DR R B}
    (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    b • x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ (m + n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Algebra.smul_def, ← map_mul]
    exact Ideal.subset_span ⟨b * c, fil_mul_mem' δ hb hc, rfl⟩
  | zero => simp
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul r x _ ih =>
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, Algebra.commutes b r, mul_assoc, ← Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ ih

theorem rel_filDR_properties :
    (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
    (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
    filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
    ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n) := by
  refine ⟨fun x hx y ↦ rel_mul_mem R δ hx y, fun x hx ↦ sgn_mem_rel R δ hx, fun n x hx y ↦ ?_, fun n x hx ↦ ?_,
    ?_, fun m n h ↦ ?_, fun m n b hb x hx ↦ ?_⟩
  · exact sup_mul_mem (fun x hx y ↦ filSpan_mul_mem R δ n hx y) (fun x hx y ↦ rel_mul_mem R δ hx y) hx y
  · exact sup_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun x hx ↦ filSpan_sgn_mem R δ n hx)
      (fun x hx ↦ sgn_mem_rel R δ hx) hx
  · refine (Ideal.eq_top_iff_one _).2 (Ideal.mem_sup_left (Ideal.subset_span ⟨1, ?_, map_one _⟩))
    rw [fil_zero_eq_top]; trivial
  · exact sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_anti' δ h))) _
  · obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine add_mem (Ideal.mem_sup_left (filSpan_smul_mem R δ m n hb ha)) (Ideal.mem_sup_right ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hc


attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler in
theorem rel_eq_bot_of_map (I : Ideal R) (κ : DividedPowers I) (h : IsDPMorphism κ δ (algebraMap R B))
    (hJ : J ≤ I.map (algebraMap R B)) : rel R δ = ⊥ := by
  have hD := GlobalTheory.CrysConn.isDPDer_of_map h hJ (D R B)
  rw [rel, Ideal.span_eq_bot]
  rintro _ ⟨n, a, ha, rfl⟩
  rw [hD n a ha, sub_self, map_zero]

end Main

theorem rel_two_sided_and_bot :
    (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J),
      (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
      (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
      filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
      ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R)
      (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ :=
  ⟨fun R _ _ _ _ _ δ ↦ rel_filDR_properties R δ, fun R _ _ _ _ _ δ I κ h hJ ↦ rel_eq_bot_of_map R δ I κ h hJ⟩

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J), (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧ (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧ filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧ ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R) (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ := by
  first | exact @GlobalTheory.PDForm.rel_two_sided_and_bot | exact GlobalTheory.PDForm.rel_two_sided_and_bot | (intros; apply GlobalTheory.PDForm.rel_two_sided_and_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiples
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiples
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiplesStatement
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  first | exact @GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | exact GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples | (intros; apply GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorus
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_polarised_torus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧
      ∃ (L : LB A.left) (u : HolUnif A L g) (χ : u.Λ → ℂ), L.IsLB ∧ (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro g Λ Hm hd hf hH hpos hint
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd₁, hf₁, hE, hbij⟩ := GlobalTheory.T.exists_polarized_superlattice_of_riemann_form g Λ Hm hd hf hH hpos hint
  obtain ⟨P, u, χ, hPg, hu, hAH, -, -⟩ := GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd₁ hf₁ hH hpos hE hbij
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun z => u.ex ((N : ℂ)⁻¹ • z) with he
  have e_add : ∀ z w, e (z + w) = e z * e w := fun z w => by simp only [he, smul_add, u.ex_add]
  have e_zero : e 0 = 1 := by
    have h := e_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have e_nsmul : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => simp [e_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, e_add, ih, pow_succ]
  have e_N : ∀ z, e ((N : ℂ) • z) = u.ex z := fun z => by
    simp only [he, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  have e_sub : ∀ z w, e (z - w) * e w = e z := fun z w => by rw [← e_add, sub_add_cancel]
  let C : Subgroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { carrier := e '' (Λ : Set (Fin g → ℂ))
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Λ.add_mem ha hb, e_add a b⟩
      one_mem' := ⟨0, Λ.zero_mem, e_zero⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨-a, Λ.neg_mem ha, ?_⟩
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← e_add, neg_add_cancel, e_zero] }
  have hCfin : Finite C := by
    have := (GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples g Λ _ e N hd hf e_add hN fun l hl => by
      rw [e_N, u.ker, hu]; exact hle hl).to_subtype
    exact this
  have hA := P.isAb
  have := hA.proper
  have := hA.comm
  obtain ⟨A, _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ := GlobalTheory.exists_quotient_abelian_by_finite_points ℂ P.A hA C hCfin
  have := hA'.smooth
  have hmon : IsMonHom (𝟙 P.A ^ N) := GlobalTheory.GrpTangent.mulN_eq_pow P.A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN P.A _
  obtain ⟨⟨φ, hφ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ P.A A P.A ψ (𝟙 P.A ^ N) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine GlobalTheory.SS.PrincIsog.pow_eq_one_of_etale ψ N (fun y hy => ?_) T z hz
      obtain ⟨c, ⟨l, hl, rfl⟩, rfl⟩ := (hker ℂ (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← e_nsmul, e_N, (u.ker l).2 (hu ▸ hle hl), MonObj.comp_one]
  have htu : toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) := toUnit_unique _ _
  let exA : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => e z ≫ ψ
  have exA_add : ∀ z w, exA (z + w) = exA z * exA w := fun z w => by
    simp only [exA, e_add, MonObj.mul_comp]
  have exA_onto : Function.Surjective exA := by
    intro x
    obtain ⟨b, hb⟩ := GlobalTheory.SS.PrincIsog.exists_lift_point (F := ℂ) ψ.left x.left
    let b' : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = x := Over.OverMorphism.ext hb
    obtain ⟨w, hw⟩ := u.ex_onto b'
    exact ⟨(N : ℂ) • w, by simp only [exA, e_N, hw, hb']⟩
  have exA_ker : ∀ z, exA z = 1 ↔ z ∈ Λ := by
    intro z
    constructor
    · intro h
      obtain ⟨c, ⟨l, hl, rfl⟩, hc'⟩ := (hker ℂ (𝟙 _) (e z)).1 h
      rw [htu] at hc'
      replace hc' : e z = e l := hc'.trans (Category.id_comp _)
      have h1 : e (z - l) = 1 := by
        have := e_sub z l
        rw [hc'] at this
        exact mul_eq_right.1 this
      have h2 := (u.ker _).1 h1
      rw [hu] at h2
      have h3 := hNΛ _ h2
      rw [smul_smul, mul_inv_cancel₀ hNc, one_smul] at h3
      have := Λ.add_mem h3 hl
      rwa [sub_add_cancel] at this
    · intro hz
      exact (hker ℂ (𝟙 _) (e z)).2 ⟨e z, ⟨z, hz, rfl⟩, by rw [htu]; exact (Category.id_comp _).symm⟩
  have hcl : Continuous (fun z : Fin g → ℂ => (N : ℂ)⁻¹ • z) := continuous_const_smul _
  have exA_hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exA z).left U f) {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} := by
    intro U f
    have hs : {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} =
        (fun z => (N : ℂ)⁻¹ • z) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (ψ.left ⁻¹ᵁ U)} := by
      ext z
      simp only [exA, he, Over.comp_left, Scheme.Hom.comp_preimage, Set.mem_setOf_eq, Set.mem_preimage]
    have hv : (fun z => valAt' (exA z).left U f) =
        (fun w => valAt' (u.ex w).left (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)) ∘ (fun z => (N : ℂ)⁻¹ • z) := by
      funext z
      simp only [Function.comp, exA, he, Over.comp_left, GlobalTheory.valAt'_comp]
    refine ⟨hs ▸ (u.hol _ ((ψ.left.app U).hom f)).1.preimage hcl, ?_⟩
    rw [hs, hv]
    exact (u.hol _ _).2.comp ((differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).const_smul ((N : ℂ)⁻¹)).differentiableOn (fun z hz => hz)
  have hcomp : ∀ z, exA z ≫ φ = u.ex z := fun z => by
    simp only [exA, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
    rw [← e_nsmul, e_N]
  obtain ⟨uA, χA, hΛA, hAHA⟩ := GlobalTheory.T.exists_holUnif_pull_along_groupHom A P.A φ P.L g u exA Λ Hm χ exA_add exA_onto exA_ker hd hf
    exA_hol hcomp (hu ▸ hle) hAH
  have hsm : SmoothOfRelativeDimension g A.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover ℂ _ _ ψ.left A.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hPg ▸ P.smoothDim)
  exact ⟨A, inferInstance, hA', hsm, P.L.pull φ.left, uA, χA, pull_isLB P.isLB _, hΛA, hAHA⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorusStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_theorem_nonprincipal_polarised_torus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧
      ∃ (L : LB A.left) (u : HolUnif A L g) (χ : u.Λ → ℂ), L.IsLB ∧ (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  first | exact @GlobalTheory.riemann_polarised_torus | exact GlobalTheory.riemann_polarised_torus | (intros; apply GlobalTheory.riemann_polarised_torus <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMTypeRestrict

theorem exists_equiv_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := by
  intro E _ _ _ I _ φ hφ e₀
  have hreal : ∀ i, ComplexEmbedding.IsReal ((φ i).comp (algebraMap (FR E) E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  let g : Fin (Module.finrank ℚ (FR E)) → (FR E →+* ℝ) := fun j => (hreal (e₀ j)).embedding
  have hg : ∀ j (x : FR E), (g j x : ℂ) = φ (e₀ j) (x : E) := fun j x =>
    (hreal (e₀ j)).coe_embedding_apply x
  have hinj : Function.Injective g := by
    intro j k hjk
    have hc : (φ (e₀ j)).comp (algebraMap (FR E) E) = (φ (e₀ k)).comp (algebraMap (FR E) E) := by
      ext x
      have h1 := hg j x
      have h2 := hg k x
      rw [hjk] at h1
      simp only [RingHom.comp_apply]
      exact h1.symm.trans h2
    have hm : IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ j))) =
        IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ k))) := by
      rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
        InfinitePlace.comap_mk, InfinitePlace.comap_mk, hc]
    have := (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ).1 ((IsCMField.equivInfinitePlace E).injective hm)
    exact e₀.injective this
  have hcard : Fintype.card (Fin (Module.finrank ℚ (FR E))) = Fintype.card (FR E →+* ℝ) := by
    rw [Fintype.card_fin, GlobalTheory.card_realEmbeddings]
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩), fun j x => hg j x⟩

end GlobalTheory.CMTypeRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

end GlobalTheory.HodgeGenDesc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem Data.sec_smooth (D : Data) (U : D.X.affineOpens) : Algebra.Smooth D.R (Sec D.s U.1) := by
  haveI := D.smooth
  have h := HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

theorem Data.mono_i (D : Data) : Mono D.i := by
  obtain ⟨s₀, hpb, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›
  infer_instance

theorem Data.affine_inf (D : Data) {U V : D.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := D.sep
  haveI : IsSeparated (Limits.terminal.from D.X) := by
    rw [← Limits.terminal.comp_from D.s]; infer_instance
  exact hU.inf hV

theorem Data.smooth_mono_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧
    ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
  fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩

end GlobalTheory.SmoothLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInfStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_sections_mono_reduction_affine_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧ ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) := by
  first | exact @GlobalTheory.SmoothLift.Data.smooth_mono_inf | exact GlobalTheory.SmoothLift.Data.smooth_mono_inf | (intros; apply GlobalTheory.SmoothLift.Data.smooth_mono_inf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory


open TorusNil TorusLocal in
theorem splitTorus_hom_ext_of_forall_pow (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R)))
    (hB : IsSeparated B.hom) (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B)
    (hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) : f = g := by
  set t := torusPt R A (AddMonoidAlgebra.of R A) with ht
  have h1 : t ≫ f = t ≫ g := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map
          (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of R A
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R))), IsSeparated B.hom → ∀ (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B), (∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) → f = g := by
  first | exact @GlobalTheory.splitTorus_hom_ext_of_forall_pow | exact GlobalTheory.splitTorus_hom_ext_of_forall_pow | (intros; apply GlobalTheory.splitTorus_hom_ext_of_forall_pow <;> assumption)
end
end
