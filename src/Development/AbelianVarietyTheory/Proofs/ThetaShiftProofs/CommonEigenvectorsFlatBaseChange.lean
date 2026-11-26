module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
open Matrix TensorProduct

namespace GlobalTheory

namespace EigFlat

variable {A : Type} [CommRing A]

theorem piScalarRight_lTensor_vecMul {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B]
    (x : B ⊗[A] (a → A)) :
    TensorProduct.piScalarRight A B B b (LinearMap.lTensor B U.vecMulLinear x)
      = (TensorProduct.piScalarRight A B B a x) ᵥ* U.map (algebraMap A B) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.add_vecMul]
  | tmul s v =>
    ext j
    simp [Matrix.vecMul, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_right_comm]

theorem exact_iff {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    [DecidableEq b] [DecidableEq c] (U : Matrix a b A) (H : Matrix b c A)
    (B : Type) [CommRing B] [Algebra A B] :
    Function.Exact (LinearMap.lTensor B U.vecMulLinear) (LinearMap.lTensor B H.vecMulLinear) ↔
      ∀ w : b → B, w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∃ cf : a → B, cf ᵥ* U.map (algebraMap A B) = w := by
  constructor
  · intro h w
    obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight A B B b).surjective w
    rw [← piScalarRight_lTensor_vecMul, LinearEquiv.map_eq_zero_iff, h y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
  · intro h y
    rw [← (TensorProduct.piScalarRight A B B c).map_eq_zero_iff, piScalarRight_lTensor_vecMul, h]
    constructor
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩

theorem injective_iff {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B] :
    Function.Injective (LinearMap.lTensor B U.vecMulLinear) ↔
      Function.Injective (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) := by
  have h : (TensorProduct.piScalarRight A B B b) ∘ (LinearMap.lTensor B U.vecMulLinear)
      = (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) ∘ (TensorProduct.piScalarRight A B B a) :=
    funext fun x => piScalarRight_lTensor_vecMul U B x
  rw [← Function.Injective.of_comp_iff (TensorProduct.piScalarRight A B B b).injective, h,
    Function.Injective.of_comp_iff' _ (TensorProduct.piScalarRight A B B a).bijective]

theorem exists_matrix [IsNoetherianRing A] {I : Type} {g : ℕ} (D : I → Matrix (Fin g) (Fin g) A) :
    ∃ (n : ℕ) (H : Matrix (Fin g) (Fin n × Fin g) A), ∀ (B : Type) [CommRing B] [Algebra A B]
      (w : Fin g → B), w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∀ i, w ᵥ* (D i).map (algebraMap A B) = 0 := by
  have hfg : (Submodule.span A (Set.range D)).FG := IsNoetherian.noetherian _
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨n, Matrix.of fun j p => s p.1 j p.2, fun B _ _ w => ?_⟩
  let K : Submodule A (Matrix (Fin g) (Fin g) A) :=
    { carrier := {X | w ᵥ* X.map (algebraMap A B) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro X Y hX hY
        simp only [Set.mem_setOf_eq] at hX hY ⊢
        rw [Matrix.map_add _ (map_add _), Matrix.vecMul_add, hX, hY, add_zero]
      smul_mem' := by
        intro r X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have : (r • X).map (algebraMap A B) = algebraMap A B r • X.map (algebraMap A B) := by
          ext i j; simp
        rw [this, Matrix.vecMul_smul, hX, smul_zero] }
  have h1 : (∀ i, w ᵥ* (D i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range D) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  have h2 : (∀ i, w ᵥ* (s i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range s) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  rw [h1, ← hs, ← h2]
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

theorem eig_iff {g : ℕ} (M : Matrix (Fin g) (Fin g) A) (ρ : A) (B : Type) [CommRing B]
    [Algebra A B] (w : Fin g → B) :
    w ᵥ* (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B) = 0 ↔
      w ᵥ* M.map (algebraMap A B) = algebraMap A B ρ • w := by
  have : (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B)
      = M.map (algebraMap A B) - algebraMap A B ρ • (1 : Matrix (Fin g) (Fin g) B) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Algebra.algebraMap_eq_smul_one, sub_smul]
  rw [this, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero]

theorem sum_eq {g m : ℕ} (u : Fin m → Fin g → A) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (∑ k, cf k • (fun j => algebraMap A B (u k j)))
      = cf ᵥ* (Matrix.of u).map (algebraMap A B) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem eig_map {g m : ℕ} (u : Fin m → Fin g → A) (M : Matrix (Fin g) (Fin g) A) (ρ : A)
    (hu : ∀ k, u k ᵥ* M = ρ • u k) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (cf ᵥ* (Matrix.of u).map (algebraMap A B)) ᵥ* M.map (algebraMap A B)
      = algebraMap A B ρ • (cf ᵥ* (Matrix.of u).map (algebraMap A B)) := by
  have h : Matrix.of u * M = ρ • Matrix.of u := by
    ext k j
    exact congrFun (hu k) j
  have h2 : (ρ • Matrix.of u).map (algebraMap A B)
      = algebraMap A B ρ • (Matrix.of u).map (algebraMap A B) := by
    ext i j; simp
  rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, h, h2, Matrix.vecMul_smul]

end EigFlat


open EigFlat in
theorem commonEigenvectors_flat_baseChange :
    ∀ (A : Type) [CommRing A] (I : Type) (g m : ℕ) (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A), (∀ (R : Type) [CommRing R] [Algebra A R] [Module.FaithfullyFlat A R] [IsNoetherianRing A] (u : Fin m → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) → (∀ w : Fin g → R, (∀ i, w ᵥ* (M i).map (algebraMap A R) = algebraMap A R (ρ i) • w) → ∃! cf : Fin m → R, w = ∑ k, cf k • (fun j => algebraMap A R (u k j))) → ∀ (S : Type) [CommRing S] [Algebra A S] [Module.Flat A S] (w : Fin g → S), (∀ i, w ᵥ* (M i).map (algebraMap A S) = algebraMap A S (ρ i) • w) → ∃! cf : Fin m → S, w = ∑ k, cf k • (fun j => algebraMap A S (u k j))) ∧ ∀ [IsDomain A] [IsPrincipalIdealRing A], ∃ (n : ℕ) (u : Fin n → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) ∧ ∀ w : Fin g → A, (∀ i, w ᵥ* M i = ρ i • w) → ∃! cf : Fin n → A, w = ∑ k, cf k • u k := by
  intro A _ I g m M ρ
  constructor
  · intro R _ _ _ _ u hu hR S _ _ _ w hw
    obtain ⟨n, H, hH⟩ := exists_matrix (fun i => M i - ρ i • (1 : Matrix (Fin g) (Fin g) A))
    simp only [eig_iff] at hH
    simp only [sum_eq] at hR ⊢
    have hexR : Function.Exact (LinearMap.lTensor R (Matrix.of u).vecMulLinear)
        (LinearMap.lTensor R H.vecMulLinear) := by
      rw [exact_iff]
      intro v
      rw [hH]
      constructor
      · intro hv
        obtain ⟨cf, hcf, -⟩ := hR v hv
        exact ⟨cf, hcf.symm⟩
      · rintro ⟨cf, rfl⟩ i
        exact eig_map u (M i) (ρ i) (fun k => hu k i) R cf
    have hinjR : Function.Injective (LinearMap.lTensor R (Matrix.of u).vecMulLinear) := by
      rw [injective_iff]
      intro c₁ c₂ hc
      exact (hR _ (fun i => eig_map u (M i) (ρ i) (fun k => hu k i) R c₁)).unique rfl hc
    have hex := (Module.FaithfullyFlat.lTensor_exact_iff_exact A R _ _).mp hexR
    have hinj := (Module.FaithfullyFlat.lTensor_injective_iff_injective A R _).mp hinjR
    have hexS := (exact_iff _ _ S).mp (Module.Flat.lTensor_exact S hex)
    have hinjS := (injective_iff _ S).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hinj)
    obtain ⟨cf, hcf⟩ := (hexS w).mp ((hH S w).mpr hw)
    exact ⟨cf, hcf.symm, fun c' hc' => hinjS (hc'.symm.trans hcf.symm)⟩
  · intro _ _
    let N : Submodule A (Fin g → A) :=
      { carrier := {w | ∀ i, w ᵥ* M i = ρ i • w}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy i
          rw [Matrix.add_vecMul, hx i, hy i, smul_add]
        smul_mem' := by
          intro r x hx i
          rw [Matrix.smul_vecMul, hx i, smul_comm] }
    obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin g)) N
    refine ⟨n, fun k => (b k : Fin g → A), fun k i => (b k).2 i, fun w hw => ?_⟩
    have key : ∀ cf : Fin n → A, (∑ k, cf k • (b k : Fin g → A))
        = ((b.equivFun.symm cf : N) : Fin g → A) := by
      intro cf
      rw [Module.Basis.equivFun_symm_apply]
      simp
    refine ⟨b.equivFun ⟨w, hw⟩, ?_, fun cf hcf => ?_⟩
    · beta_reduce
      rw [key]; simp
    · beta_reduce at hcf
      rw [key] at hcf
      have : (⟨w, hw⟩ : N) = b.equivFun.symm cf := Subtype.ext hcf
      exact ((congrArg b.equivFun this).trans (b.equivFun.apply_symm_apply cf)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IrreducibleDetOfIsRelPrime
open MvPolynomial

namespace GlobalTheory.RowDet

theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type*} [Fintype m] [DecidableEq m] (S : Subalgebra R A) (M : Matrix m m A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem notMem_vars_det {R σ : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (a : σ) (M : Matrix m m (MvPolynomial σ R)) (h : ∀ i j, a ∉ (M i j).vars) :
    a ∉ M.det.vars := by
  have : M.det ∈ supported R ({a}ᶜ : Set σ) := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    rw [mem_supported]
    intro b hb hba
    rw [Set.mem_singleton_iff] at hba
    exact h i j (hba ▸ hb)
  rw [mem_supported] at this
  intro ha
  exact this ha rfl

theorem det_updateRow_single {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    (M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have : (-1 : A) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, Matrix.updateRow_self, Pi.single_eq_same, one_mul, one_mul, Fin.succAbove_last]
    congr 1
    ext i j
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem minor_not_dvd {R σ : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (e : Fin (n + 2) × Fin (n + 2) → σ) (he : Function.Injective e) :
    ¬ ((Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ∣
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  intro h
  let w : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix (Equiv.swap 0 (Fin.last (n + 1))) id
  let v : σ → R := Function.extend e (fun p => w p.1 p.2) 0
  have hv : ∀ i k, v (e (i, k)) = w i k := fun i k => he.extend_apply _ _ _
  have h2 := map_dvd (eval v) h
  rw [RingHom.map_det, RingHom.map_det] at h2
  have e1 : (eval v).mapMatrix
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)) = w := by
    ext i k; simp [hv]
  have e2 : ((eval v).mapMatrix ((Matrix.of fun i k : Fin (n + 2) =>
      (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc)).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    simp [hv, w, Matrix.one_apply, (Fin.castSucc_lt_last j).ne']
  rw [e1, e2, zero_dvd_iff] at h2
  have hu : IsUnit w.det := by
    rw [Matrix.det_permute, Matrix.det_one, mul_one]
    exact (Units.isUnit _).map (Int.castRingHom R)
  exact hu.ne_zero h2

theorem irreducible_det_of_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e)
    (h0 : ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0)
    (h : IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det) :
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  set A := (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)) with hA
  let r : Fin (n + 1) → MvPolynomial σ R := fun k => if k = Fin.last n then 0 else A (Fin.last n) k
  have hD : A.det = (A.submatrix Fin.castSucc Fin.castSucc).det * X (e (Fin.last n, Fin.last n))
      + (A.updateRow (Fin.last n) r).det := by
    rw [← det_updateRow_single, mul_comm, ← Matrix.det_updateRow_smul,
      ← Matrix.det_updateRow_add]
    congr 1
    rw [eq_comm]
    convert Matrix.updateRow_eq_self A (Fin.last n)
    ext1 k
    by_cases hk : k = Fin.last n
    · subst hk; simp [r, A]
    · simp [r, hk]
  rw [hD] at h ⊢
  refine irreducible_mul_X_add _ _ _ h0 ?_ ?_ ?_
  · refine notMem_vars_det _ _ fun i j => ?_
    simp [A, vars_X, he.eq_iff, (Fin.castSucc_lt_last j).ne']
  · refine notMem_vars_det _ _ fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      by_cases hj : j = Fin.last n
      · simp [r, hj]
      · simp [r, hj, A, vars_X, he.eq_iff, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, A, vars_X, he.eq_iff, Ne.symm hi]
  · intro c hc1 hc2
    exact h hc1 (dvd_add (hc1.mul_right _) hc2)

theorem irreducible_det {R σ : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    ∀ (e : Fin (n + 1) × Fin (n + 1) → σ), Function.Injective e →
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  induction n with
  | zero =>
    intro e he
    refine irreducible_det_of_isRelPrime e he ?_ ?_
    · simp
    · rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  | succ n ih =>
    intro e he
    have h := ih (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by
      have := he hpq
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
      exact Prod.ext this.1 this.2)
    exact irreducible_det_of_isRelPrime e he h.ne_zero
      (h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he))

theorem minor_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e) :
    ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  cases n with
  | zero => rw [Matrix.det_isEmpty]; exact ⟨one_ne_zero, isRelPrime_one_left⟩
  | succ n =>
    have h := irreducible_det (R := R) n (fun p => e (p.1.castSucc, p.2.castSucc))
      (fun p q hpq => by
        have := he hpq
        simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
        exact Prod.ext this.1 this.2)
    exact ⟨h.ne_zero, h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he)⟩

end GlobalTheory.RowDet
end
