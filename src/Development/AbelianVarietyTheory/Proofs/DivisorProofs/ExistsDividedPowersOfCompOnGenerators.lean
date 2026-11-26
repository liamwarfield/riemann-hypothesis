module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDA

open MvPolynomial Finset

def dpBas2 (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • X 0 ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

theorem IsPreDP.eval_zero {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {n : ℕ} (hn : n ≠ 0) : γ n 0 = 0 := by
  have := h.mul n 0 0 J.zero_mem
  rwa [mul_zero, zero_pow hn, zero_mul] at this

theorem IsPreDP.comp_add {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {x y : B} (hx : x ∈ J) (hy : y ∈ J)
    (Px : ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x)
    (Py : ∀ m n : ℕ, n ≠ 0 → γ m (γ n y) = (m.uniformBell n : B) * γ (m * n) y)
    (m n : ℕ) (hn : n ≠ 0) : γ m (γ n (x + y)) = (m.uniformBell n : B) * γ (m * n) (x + y) := by
  classical
  set D := Submodule.span ℤ (Set.range dpBas2) with hD
  obtain ⟨φ, hφb, hφ2, hφz⟩ : ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (dpBas2 (a, c)) = γ a x * γ c y) ∧
      (∀ d ∈ D, ∀ e ∈ D, φ (d + e) = φ d + φ e ∧ d * e ∈ D ∧ φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ D, φ (z • d) = z • φ d) :=
    GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom B (fun a ↦ γ a x) (fun c ↦ γ c y) (h.zero x hx) (h.zero y hy)
      (fun a b ↦ h.mul_dpow a b x hx) (fun a b ↦ h.mul_dpow a b y hy)
  let Γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) := RatAlgebra.dividedPowers ⊤
  have top : ∀ q : MvPolynomial (Fin 2) ℚ, q ∈ (⊤ : Ideal _) := fun _ ↦ Submodule.mem_top
  have hΓ : ∀ (k : ℕ) (q : MvPolynomial (Fin 2) ℚ), Γ.dpow k q = (k.factorial : ℚ)⁻¹ • q ^ k := fun k q ↦ by
    rw [RatAlgebra.dpow_eq_inv_fact_smul _ Γ (top q), Ring.inverse_eq_inv']
  have hbasΓ : ∀ p : ℕ × ℕ, dpBas2 p = Γ.dpow p.1 (X 0) * Γ.dpow p.2 (X 1) := fun p ↦ by
    rw [dpBas2, hΓ, hΓ]
  have hX0 : ∀ a, Γ.dpow a (X 0) = dpBas2 (a, 0) := fun a ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), mul_one]
  have hX1 : ∀ c, Γ.dpow c (X 1) = dpBas2 (0, c) := fun c ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), one_mul]
  have hbasΓ' : ∀ a c, dpBas2 (a, c) = Γ.dpow a (X 0) * Γ.dpow c (X 1) := fun a c ↦ hbasΓ (a, c)
  have hDb : ∀ p, dpBas2 p ∈ D := fun p ↦ Submodule.subset_span ⟨p, rfl⟩
  have hone : dpBas2 (0, 0) = 1 := by simp [dpBas2]
  have hφ1 : φ 1 = 1 := by rw [← hone, hφb, h.zero x hx, h.zero y hy, one_mul]
  have hD1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ D := hone ▸ hDb _
  have hφ0 : φ 0 = 0 := by
    have := (hφ2 0 D.zero_mem 0 D.zero_mem).1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hpow : ∀ d ∈ D, ∀ k : ℕ, d ^ k ∈ D ∧ φ (d ^ k) = φ d ^ k := by
    intro d hd k
    induction k with
    | zero => simpa using ⟨hD1, hφ1⟩
    | succ k ih =>
      obtain ⟨_, h2, h3⟩ := hφ2 _ ih.1 d hd
      rw [pow_succ, pow_succ, h3, ih.2]
      exact ⟨h2, rfl⟩
  have hsum : ∀ (t : Finset (ℕ × ℕ)) (f : ℕ × ℕ → MvPolynomial (Fin 2) ℚ), (∀ i ∈ t, f i ∈ D) →
      (∑ i ∈ t, f i) ∈ D ∧ φ (∑ i ∈ t, f i) = ∑ i ∈ t, φ (f i) := by
    intro t f hf
    induction t using Finset.induction with
    | empty => simp [hφ0]
    | insert i t hi ih =>
      have ih' := ih fun j hj ↦ hf j (mem_insert_of_mem hj)
      have hfi := hf i (mem_insert_self i t)
      rw [sum_insert hi, sum_insert hi, (hφ2 _ hfi _ ih'.1).1, ih'.2]
      exact ⟨add_mem hfi ih'.1, rfl⟩
  have hnat : ∀ (N : ℕ), ∀ d ∈ D, (N : MvPolynomial (Fin 2) ℚ) * d ∈ D ∧ φ ((N : MvPolynomial (Fin 2) ℚ) * d) = N * φ d := by
    intro N d hd
    have e1 : (N : MvPolynomial (Fin 2) ℚ) * d = (N : ℤ) • d := by rw [zsmul_eq_mul, Int.cast_natCast]
    refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ hd, ?_⟩
    rw [e1, hφz _ _ hd, zsmul_eq_mul, Int.cast_natCast]
  have hsX : ∀ N : ℕ, Γ.dpow N (X 0 + X 1) ∈ D ∧ φ (Γ.dpow N (X 0 + X 1)) = γ N (x + y) := by
    intro N
    have e1 : Γ.dpow N (X 0 + X 1) = ∑ p ∈ antidiagonal N, dpBas2 p := by
      rw [Γ.dpow_add (top _) (top _)]
      exact sum_congr rfl fun p _ ↦ (hbasΓ p).symm
    rw [e1, (hsum _ _ fun p _ ↦ hDb p).2, h.add N x hx y hy]
    exact ⟨(hsum _ _ fun p _ ↦ hDb p).1, sum_congr rfl fun p _ ↦ hφb p.1 p.2⟩
  set Dp := Submodule.span ℤ (dpBas2 '' {p | p ≠ 0}) with hDp
  have T : ∀ d ∈ Dp, d ∈ D ∧ φ d ∈ J ∧ ∀ k, Γ.dpow k d ∈ D ∧ γ k (φ d) = φ (Γ.dpow k d) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, c⟩, hac, rfl⟩ := hd
      refine ⟨hDb _, ?_, fun k ↦ ?_⟩
      · rw [hφb]
        by_cases ha : a = 0
        · have hc : c ≠ 0 := by rintro rfl; exact hac (by simp [ha])
          exact J.mul_mem_left _ (h.mem c hc y hy)
        · exact J.mul_mem_right _ (h.mem a ha x hx)
      show Γ.dpow k (dpBas2 (a, c)) ∈ D ∧ γ k (φ (dpBas2 (a, c))) = φ (Γ.dpow k (dpBas2 (a, c)))
      rw [hφb a c]
      by_cases ha : a = 0
      · subst ha
        have hc : c ≠ 0 := by rintro rfl; exact hac rfl
        have e : Γ.dpow k (dpBas2 (0, c)) = ((k.uniformBell c : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (0, k * c) := by
          rw [← hX1 c, Γ.dpow_comp hc (top _), hX1 (k * c)]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell c) _ (hDb (0, k * c))
        rw [e]
        refine ⟨h1, ?_⟩
        rw [h2, hφb, h.zero x hx, one_mul, one_mul, Py k c hc]
      · have e : Γ.dpow k (dpBas2 (a, c)) =
            ((k.uniformBell a : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (k * a, 0) * dpBas2 (0, c) ^ k := by
          rw [hbasΓ' a c, Γ.dpow_mul_right (top _), Γ.dpow_comp ha (top _), hX0 (k * a), hX1 c]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell a) _ (hDb (k * a, 0))
        obtain ⟨h3, h4⟩ := hpow _ (hDb (0, c)) k
        obtain ⟨_, h5, h6⟩ := hφ2 _ h1 _ h3
        rw [e]
        refine ⟨h5, ?_⟩
        rw [h6, h2, h4, hφb, hφb, h.zero x hx, h.zero y hy, mul_comm (γ a x), h.mul k _ _ (h.mem a ha x hx),
          Px k a ha]
        ring
    | zero =>
      refine ⟨D.zero_mem, hφ0 ▸ J.zero_mem, fun k ↦ ?_⟩
      by_cases hk : k = 0
      · subst hk
        rw [Γ.dpow_zero (top _), hφ0, h.zero 0 J.zero_mem, hφ1]
        exact ⟨hD1, rfl⟩
      · rw [Γ.dpow_eval_zero hk, hφ0, h.eval_zero hk]
        exact ⟨D.zero_mem, rfl⟩
    | add d e _ _ hd he =>
      obtain ⟨dD, dJ, dk⟩ := hd
      obtain ⟨eD, eJ, ek⟩ := he
      obtain ⟨hde, -, -⟩ := hφ2 d dD e eD
      refine ⟨add_mem dD eD, hde ▸ add_mem dJ eJ, fun k ↦ ?_⟩
      have hm : ∀ p ∈ antidiagonal k, Γ.dpow p.1 d * Γ.dpow p.2 e ∈ D := fun p _ ↦
        (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.1
      rw [Γ.dpow_add (top _) (top _), hde, h.add k _ dJ _ eJ, (hsum _ _ hm).2]
      refine ⟨(hsum _ _ hm).1, sum_congr rfl fun p _ ↦ ?_⟩
      rw [(dk p.1).2, (ek p.2).2, (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.2]
    | smul z d _ hd =>
      obtain ⟨dD, dJ, dk⟩ := hd
      refine ⟨Submodule.smul_mem _ _ dD, (hφz z d dD) ▸ zsmul_mem dJ z, fun k ↦ ?_⟩
      have e1 : Γ.dpow k (z • d) = (z ^ k) • Γ.dpow k d := by
        rw [zsmul_eq_mul, Γ.dpow_mul (top _), zsmul_eq_mul, Int.cast_pow]
      refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ (dk k).1, ?_⟩
      rw [e1, hφz _ _ dD, hφz _ _ (dk k).1, zsmul_eq_mul, h.mul k _ _ dJ, (dk k).2, zsmul_eq_mul, Int.cast_pow]
  have hmem : Γ.dpow n (X 0 + X 1) ∈ Dp := by
    rw [Γ.dpow_add (top _) (top _)]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    rw [← hbasΓ]
    refine Submodule.subset_span ⟨p, fun h0 ↦ hn ?_, rfl⟩
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, h0]; rfl
  obtain ⟨_, _, hk⟩ := T _ hmem
  rw [← (hsX n).2, (hk m).2, Γ.dpow_comp hn (top _), (hnat _ _ (hsX _).1).2, (hsX _).2]

theorem exists_dividedPowers_of_comp_on_gens :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s →
      (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
      ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s h hJ hs
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    intro x hx
    subst hJ
    induction hx using Submodule.span_induction with
    | mem x hxs => exact hs x hxs
    | zero =>
      intro m n hn
      rw [h.eval_zero hn]
      by_cases hm : m = 0
      · subst hm
        rw [Nat.uniformBell_zero_left, zero_mul, h.zero 0 (Submodule.zero_mem _), Nat.cast_one, one_mul]
      · rw [h.eval_zero hm, h.eval_zero (mul_ne_zero hm hn), mul_zero]
    | add x y hx hy Px Py => exact fun m n hn ↦ h.comp_add hx hy Px Py m n hn
    | smul a x hx Px =>
      intro m n hn
      rw [smul_eq_mul, h.mul n a x hx, h.mul m _ _ (h.mem n hn x hx), Px m n hn, h.mul (m * n) a x hx, ← pow_mul,
        mul_comm n m]
      ring
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ h.null _ _ hx
           dpow_zero := fun hx ↦ h.zero _ hx
           dpow_one := fun hx ↦ h.one _ hx
           dpow_mem := fun hn hx ↦ h.mem _ hn _ hx
           dpow_add := fun hx hy ↦ h.add _ _ hx _ hy
           dpow_mul := fun hx ↦ h.mul _ _ _ hx
           mul_dpow := fun hx ↦ h.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end GlobalTheory.PDA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_of_comp_on_generators : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens | exact GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens | (intros; apply GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

open CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.NilThickIso

theorem appTop_spMap_eq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) :
    (spMap π).appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom π ≫
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc]; simp

theorem surjective_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) : Function.Surjective (spMap π).appTop := by
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso _).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso _).2

theorem isNilpotent_ker_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hn : IsNilpotent (RingHom.ker π)) : IsNilpotent (RingHom.ker (spMap π).appTop.hom) := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp]
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hk : RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom.comp
      (CommRingCat.ofHom π).hom).comp e) = (RingHom.ker π).comap e := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    constructor
    · intro h
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom h
      simpa using this
    · intro h; simp [h]
  rw [hk, Ideal.zero_eq_bot, ← le_bot_iff]
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hn, Ideal.zero_eq_bot]
  intro x hx
  simp only [Ideal.mem_comap, Ideal.mem_bot] at hx ⊢
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    (by rw [map_zero]; exact hx)

theorem surjective_of_sub_mem_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (h : ∀ c : C, ∃ b : B, c - φ b ∈ I.map (algebraMap A C)) : Function.Surjective φ := by
  obtain ⟨n, hn⟩ := hI
  let N : Submodule A C := LinearMap.range φ.toLinearMap
  have h1 : (⊤ : Submodule A C) ≤ N ⊔ I • ⊤ := by
    intro c _
    obtain ⟨b, hb⟩ := h c
    have hm : c - φ b ∈ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    have := Submodule.add_mem_sup (LinearMap.mem_range_self φ.toLinearMap b) hm
    simpa using this
  have h2 : ∀ k : ℕ, (⊤ : Submodule A C) ≤ N ⊔ I ^ k • ⊤ := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])
    | succ k ih =>
      calc ⊤ ≤ N ⊔ I ^ k • ⊤ := ih
        _ ≤ N ⊔ I ^ k • (N ⊔ I • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (k + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  have h3 := h2 n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at h3
  intro c
  obtain ⟨b, hb⟩ := h3 (Submodule.mem_top (x := c))
  exact ⟨b, hb⟩

theorem injective_of_flat_of_ker_le_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Flat A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (hs : Function.Surjective φ) (h : ∀ b : B, φ b = 0 → b ∈ I.map (algebraMap A B)) :
    Function.Injective φ := by
  obtain ⟨n, hn⟩ := hI
  set K := LinearMap.ker φ.toLinearMap with hKdef
  let mB : I ⊗[A] B →ₗ[A] B := (TensorProduct.lid A B).toLinearMap ∘ₗ I.subtype.rTensor B
  let mC : I ⊗[A] C →ₗ[A] C := (TensorProduct.lid A C).toLinearMap ∘ₗ I.subtype.rTensor C
  have hmC : Function.Injective mC := (TensorProduct.lid A C).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hcomm : ∀ t, φ (mB t) = mC (φ.toLinearMap.lTensor I t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mB, mC]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex := lTensor_exact I (LinearMap.exact_subtype_ker_map φ.toLinearMap) hs
  have hrange : ∀ b ∈ I • (⊤ : Submodule A B), ∃ t, mB t = b := by
    intro b hb
    refine Submodule.smul_induction_on (p := fun b ↦ ∃ t, mB t = b) hb ?_ ?_
    · intro a ha x _
      exact ⟨⟨a, ha⟩ ⊗ₜ x, by simp [mB]⟩
    · rintro x y ⟨t, rfl⟩ ⟨s, rfl⟩
      exact ⟨t + s, map_add _ _ _⟩
  have hK : ∀ s : I ⊗[A] K, mB (K.subtype.lTensor I s) ∈ I • K := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [mB, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, Submodule.subtype_apply]
      exact Submodule.smul_mem_smul a.2 x.2
    | add x y hx hy =>
      simp only [map_add]
      exact add_mem hx hy
  have hle : K ≤ I • K := by
    intro k hk
    have hk' : k ∈ I • (⊤ : Submodule A B) := by rw [Ideal.smul_top_eq_map]; exact h k hk
    obtain ⟨t, rfl⟩ := hrange k hk'
    have h0 : φ.toLinearMap.lTensor I t = 0 := hmC (by rw [← hcomm, map_zero]; exact hk)
    obtain ⟨s, rfl⟩ := (hex t).mp h0
    exact hK s
  have hle' : ∀ k : ℕ, K ≤ I ^ k • K := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih =>
      calc K ≤ I ^ k • K := ih
        _ ≤ I ^ k • (I • K) := Submodule.smul_mono le_rfl hle
        _ = I ^ (k + 1) • K := by rw [pow_succ, Submodule.mul_smul]
  have h3 := hle' n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul] at h3
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro b hb
  exact (Submodule.mem_bot A).mp (h3 hb)

theorem ring_step {A A₀ B C B₀ C₀ : CommRingCat.{0}} (ψ : A ⟶ A₀) (β : A ⟶ B) (ρ : A ⟶ C)
    (φ : B ⟶ C) (πB : B ⟶ B₀) (πC : C ⟶ C₀) (β₀ : A₀ ⟶ B₀) (ρ₀ : A₀ ⟶ C₀) (φ₀ : B₀ ⟶ C₀)
    (hψ : Function.Surjective ψ) (hn : IsNilpotent (RingHom.ker ψ.hom))
    (hB : IsPushout β ψ πB β₀) (hC : IsPushout ρ ψ πC ρ₀) (hflat : ρ.hom.Flat)
    (w : β ≫ φ = ρ) (w₀ : φ ≫ πC = πB ≫ φ₀) (hφ₀ : IsIso φ₀) : IsIso φ := by
  have hkB := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hB hψ
  have hkC := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hC hψ
  have hπB : Function.Surjective πB := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout hB, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨a, rfl⟩ := hψ y
      exact ⟨β a, congr($(hB.w).hom a)⟩
  have hφ₀ := ConcreteCategory.bijective_of_isIso φ₀
  have hw₀ (b : B) : πC (φ b) = φ₀ (πB b) := congr($(w₀).hom b)
  algebraize [β.hom, ρ.hom]
  let φA : B →ₐ[A] C := { φ.hom with commutes' := fun a ↦ congr($(w).hom a) }
  have hs : Function.Surjective φA := by
    refine surjective_of_sub_mem_map φA (RingHom.ker ψ.hom) hn fun c ↦ ?_
    obtain ⟨y, hy⟩ := hφ₀.2 (πC c)
    obtain ⟨b, rfl⟩ := hπB y
    refine ⟨b, ?_⟩
    have h0 : πC (c - φ b) = 0 := by rw [map_sub, hw₀, hy, sub_self]
    have h1 : c - φ b ∈ RingHom.ker πC.hom := h0
    rw [hkC] at h1
    exact h1
  have hi : Function.Injective φA := by
    refine injective_of_flat_of_ker_le_map φA (RingHom.ker ψ.hom) hn hs fun b hb ↦ ?_
    have h0 : πB b = 0 := hφ₀.1 (by rw [← hw₀, show φ b = 0 from hb, map_zero, map_zero])
    rw [← RingHom.mem_ker, hkB] at h0
    exact h0
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hi, hs⟩

theorem affine_case (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p] [IsAffine Y]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  have : IsAffine Y₀ := IsAffine.of_isPullback hY
  have : IsAffine X₀ := IsAffine.of_isIso f₀
  have : IsAffine X := GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker π) hn
    (CommRingCat.ofHom π) hπ rfl hX this
  have hψ := surjective_appTop_spMap π hπ
  have hψn := isNilpotent_ker_appTop_spMap π hn
  have hfl : (p.appTop).hom.Flat := HasRingHomProperty.iff_of_isAffine.mp ‹Flat p›
  have key : IsIso f.appTop := ring_step (spMap π).appTop q.appTop p.appTop f.appTop j.appTop i.appTop
    q₀.appTop p₀.appTop f₀.appTop hψ hψn (isPushout_appTop_of_isPullback hY)
    (isPushout_appTop_of_isPullback hX) hfl (by rw [← w]; simp) (by
      rw [← Scheme.Hom.comp_appTop, w₀, Scheme.Hom.comp_appTop]) ⟨⟨(inv f₀).appTop, by rw [← Scheme.Hom.comp_appTop]; simp, by rw [← Scheme.Hom.comp_appTop]; simp⟩⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop))))

theorem general (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    Y.affineCover (fun k ↦ ?_)
  change IsIso (pullback.snd f (Y.affineCover.f k))
  set u := Y.affineCover.f k
  have hU : IsPullback (pullback.snd j u) (pullback.fst j u ≫ q₀) (u ≫ q) (spMap π) :=
    (IsPullback.of_hasPullback j u).flip.paste_vert hY
  have hX' : IsPullback (pullback.snd i (pullback.fst f u)) (pullback.fst i (pullback.fst f u) ≫ p₀)
      (pullback.fst f u ≫ p) (spMap π) :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).flip.paste_vert hX
  have hP : IsPullback (pullback.fst i (pullback.fst f u))
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) (i ≫ f) u :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).paste_vert (IsPullback.of_hasPullback f u)
  have hP' : IsPullback (pullback.fst i (pullback.fst f u) ≫ f₀)
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) j u :=
    IsPullback.of_iso hP (Iso.refl _) (asIso f₀) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [w₀]) (by simp)
  exact affine_case R R₀ π hπ hn (pullback.fst f u ≫ p) (u ≫ q) _ _ _ _ hX' hU (pullback.snd f u)
    hP'.isoPullback.hom (by rw [← w, pullback.condition_assoc]) (by simp)

theorem isIso_of_flat_of_isIso_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  intro R R₀ _ _ π hπ hn X Y X₀ Y₀ i j hX hY hfl f f₀ w₀ hf₀
  have : IsIso f₀.left := (Over.forget _).map_isIso f₀
  have : IsIso f.left := general R R₀ π hπ hn X.hom Y.hom X₀.hom Y₀.hom i j hX hY f.left f₀.left
    (Over.w f) w₀
  have : IsIso ((Over.forget _).map f) := this
  exact isIso_of_reflects_iso f (Over.forget _)

end GlobalTheory.NilThickIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReductionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_flat_pullback_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  first | exact @GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction | exact GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction | (intros; apply GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsTranslationFamilyChartsThickeningsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W),
      ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    have hMove : ∃ φ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x,
        φ' x = φ x + ∑ a, φ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a :=
      GlobalTheory.SqZeroMove.gen_hom φ
        (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
        (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
        (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn2
    obtain ⟨φ', hφ'⟩ := hMove
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor :
    ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
      {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
      (ρ : Hol W →+* R ⊗[ℂ] Hol W₀),
      (∀ (a : Fin g) (h : Hol W),
        ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h)) →
      ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C,
        (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) →
        Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)
          (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) →
        Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_comp_of_close_includeRight : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  exact @GlobalTheory.CloseTen.close_tensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_tensorLift_of_DObj {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R]
    [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M) :
    ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)),
      ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  letI : Algebra ℂ S.T.C := ((algebraMap R S.T.C).comp (algebraMap ℂ R)).toAlgebra
  let fR : R →ₐ[ℂ] S.T.C := { algebraMap R S.T.C with commutes' := fun _ ↦ rfl }
  let fH : Hol (K₀.W S.T.k) →ₐ[ℂ] S.T.C :=
    { S.T.ρ with
      commutes' := fun a ↦ by
        have h1 : algebraMap ℂ (Hol (K₀.W S.T.k)) a = K₀.cst S.T.k (algebraMap ℂ (Hol F₀.V) a) :=
          ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K₀.base S.T.k)).commutes a).symm
        change S.T.ρ (algebraMap ℂ (Hol (K₀.W S.T.k)) a) = algebraMap R S.T.C (algebraMap ℂ R a)
        rw [h1, S.T.ρ_cst, S.compat]
        change algebraMap R S.T.C (et (algebraMap ℂ (Hol F₀.V) a)) = _
        rw [et.commutes] }
  refine ⟨(Algebra.TensorProduct.lift fR fH (fun _ _ ↦ Commute.all _ _)).toRingHom, fun d h ↦ ?_⟩
  exact Algebra.TensorProduct.lift_tmul _ _ _ d h

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLift_of_analyticThickening : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M), ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)), ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  first | exact @GlobalTheory.AnPer.exists_tensorLift_of_DObj | exact GlobalTheory.AnPer.exists_tensorLift_of_DObj | (intros; apply GlobalTheory.AnPer.exists_tensorLift_of_DObj <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_translationFamilyCharts_thickenings : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw (W := K.W (ka k)) a h) = LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using GlobalTheory.T.exists_tensorLift_of_analyticThickening K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, _root_.mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, _root_.one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.CloseTen.close_tensor S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2
end
