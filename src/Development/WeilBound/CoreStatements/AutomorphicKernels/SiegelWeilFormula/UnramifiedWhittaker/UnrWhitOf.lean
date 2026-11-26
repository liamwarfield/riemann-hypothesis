module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramified
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFibreGramDifferential
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCard
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem card_hermitian_resAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (n : ℕ) :
    Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  have hq : q ≠ 0 := by have := hE.one_lt; omega
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hq)
  obtain ⟨u, hu, -⟩ := hE.basis
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq τ hE.inv u hu 1 (map_one τ) n
  have hiff : ∀ H : Matrix (Fin n) (Fin n) E,
      cT τ H = H ↔ ((∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b) := by
    intro H
    constructor
    · intro h
      refine ⟨fun a b => ?_, fun a b => one_dvd _⟩
      have := congrFun (congrFun h a) b
      simpa [cT] using this
    · rintro ⟨h, -⟩
      ext a b
      simpa [cT] using h a b
  have e1 : Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H}
      = Nat.card {H : Matrix (Fin n) (Fin n) E //
          (∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have e2 : Nat.card {x : E // (1 : E) ∣ x} = q ^ 2 := by
    rw [← hE.card]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  rw [e2] at key
  have hsq : (q ^ (n ^ 2)) ^ 2 = (q ^ 2) ^ (n * n) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e1]
  exact Nat.pow_left_injective (by norm_num) (key.trans hsq.symm)

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrices_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ n : ℕ, Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | exact GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg <;> assumption)
end
end

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff

variable {E : Type} [CommRing E] (τ : E →+* E)

theorem cT_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i j
  simp [cT]

theorem cT_zero {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i j
  simp [cT]

theorem cT_neg {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : cT τ (-A) = -cT τ A := by
  ext i j
  simp [cT]

theorem cT_smul {a b : ℕ} (c : E) (A : Matrix (Fin a) (Fin b) E) :
    cT τ (c • A) = τ c • cT τ A := by
  ext i j
  simp [cT]

theorem cT_cT (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i j
  simp [cT, hτ]

theorem cT_cross (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) E} (hS : cT τ S = S)
    (x y : Matrix (Fin m) (Fin n) E) : cT τ (cT τ x * S * y) = cT τ y * S * x := by
  rw [cT_mul, cT_mul, cT_cT τ hτ, hS, Matrix.mul_assoc]

def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) E) where
  carrier := {H | cT τ H = H}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [cT_add, ha, hb]
  zero_mem' := cT_zero τ
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [cT_neg, ha]

def diffMap (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S)
    (x : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin n) E →+ hermSub τ n :=
  AddMonoidHom.mk'
    (fun y => ⟨cT τ y * S * x + cT τ x * S * y, by
      change cT τ (cT τ y * S * x + cT τ x * S * y) = cT τ y * S * x + cT τ x * S * y
      rw [cT_add, cT_cross τ hτ hS, cT_cross τ hτ hS, add_comm]⟩)
    (by
      intro a b
      apply Subtype.ext
      change cT τ (a + b) * S * x + cT τ x * S * (a + b) =
        (cT τ a * S * x + cT τ x * S * a) + (cT τ b * S * x + cT τ x * S * b)
      rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add]
      abel)

theorem exists_trace_one {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) : ∃ θ : E, θ + τ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - τ u) * τ v = -1 := by
    have := congrArg τ hv
    rw [map_mul, map_sub, h.inv, map_one] at this
    linear_combination -this
  have h2 : τ v = -v := by
    linear_combination (-(τ v)) * hv + v * h1
  refine ⟨u * v, ?_⟩
  rw [map_mul, h2]
  linear_combination hv

theorem diffMap_surjective {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S) (T : Matrix (Fin n) (Fin n) E)
    (x : Matrix (Fin m) (Fin n) E) (hT : IsUnit T.det) (hx : cT τ x * S * x = T) :
    Function.Surjective (diffMap τ h.inv S hS x) := by
  rintro ⟨H, hH⟩
  have hH' : cT τ H = H := hH
  obtain ⟨θ, hθ⟩ := exists_trace_one τ h
  have hW : cT τ x * S * (x * T⁻¹ * (θ • H)) = θ • H := by
    calc cT τ x * S * (x * T⁻¹ * (θ • H)) = (cT τ x * S * x) * T⁻¹ * (θ • H) := by
          simp only [Matrix.mul_assoc]
      _ = θ • H := by rw [hx, Matrix.mul_nonsing_inv T hT, Matrix.one_mul]
  refine ⟨x * T⁻¹ * (θ • H), ?_⟩
  apply Subtype.ext
  change cT τ (x * T⁻¹ * (θ • H)) * S * x + cT τ x * S * (x * T⁻¹ * (θ • H)) = H
  rw [← cT_cross τ h.inv hS x (x * T⁻¹ * (θ • H)), hW, cT_smul, hH', ← add_smul, add_comm, hθ, one_smul]

theorem card_fibre_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] (f : A →+ B)
    (hf : Function.Surjective f) (b : B) : Nat.card {a // f a = b} * Nat.card B = Nat.card A := by
  obtain ⟨y, rfl⟩ := hf b
  have e : {a // f a = f y} ≃ f.ker :=
    { toFun := fun a => ⟨a.1 - y, by simp [AddMonoidHom.mem_ker, a.2]⟩
      invFun := fun k => ⟨k.1 + y, by
        have : f k.1 = 0 := k.2
        simp [this]⟩
      left_inv := fun a => by simp
      right_inv := fun k => by simp }
  have hi : f.ker.index = Nat.card B := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [Nat.card_congr e, ← hi]
  exact AddSubgroup.card_mul_index f.ker

theorem card_fibre_gram_differential : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by
  intro E _ τ q ε h m n hnm S T x H hS _ hT hx hH
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  have hM : Nat.card (Matrix (Fin m) (Fin n) E) = ((q ^ 2) ^ n) ^ m := by
    change Nat.card (Fin m → Fin n → E) = _
    rw [Nat.card_fun, Nat.card_fun, h.card]
    simp
  have hHerm : Nat.card (hermSub τ n) = q ^ (n ^ 2) := GlobalTheory.T.hermitian_matrices_card E τ q ε h n
  have hfib := card_fibre_mul (diffMap τ h.inv S hS x)
    (diffMap_surjective τ h S hS T x hT hx) ⟨H, hH⟩
  have hc : Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} =
      Nat.card {y // diffMap τ h.inv S hS x y = ⟨H, hH⟩} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Subtype.ext_iff]
      rfl)
  have hle : n ^ 2 ≤ 2 * m * n := by nlinarith
  have hpow : ((q ^ 2) ^ n) ^ m = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hle, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hc]
  rw [hHerm, hM, hpow, mul_comm] at hfib
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq _) hfib

end GlobalTheory.CompanionTheory.UnrDens.GramDiff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep

section Generic

theorem card_of_fibres {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp [h, Nat.card_eq_fintype_card, mul_comm]

theorem card_eq_of_surj {W A B : Type*} (a : W → A) (b : W → B) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (hab : ∀ w w', a w = a w' ↔ b w = b w') :
    Nat.card A = Nat.card B := by
  refine Nat.card_congr (Equiv.ofBijective (fun y => b (Function.surjInv ha y)) ⟨?_, ?_⟩)
  · intro y y' h
    have := (hab _ _).2 h
    simpa [Function.surjInv_eq] using this
  · intro z
    obtain ⟨w, rfl⟩ := hb z
    exact ⟨a w, (hab _ _).1 (Function.surjInv_eq ha _)⟩

end Generic

variable {R : Type} [CommRing R] {a b c : ℕ}

theorem cT_add (σ : R →+* R) (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j; simp [cT]

theorem cT_smul (σ : R →+* R) (r : R) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (r • x) = σ r • cT σ x := by
  ext i j; simp [cT]

theorem cT_mul (σ : R →+* R) (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ r, σ (σ r) = r) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j; simp [cT, h]

theorem red_add (ϖ : R) (k : ℕ) (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j; simp [red]

theorem red_mul (ϖ : R) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  simp [red, Matrix.map_mul]

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j; simp [red, cT]

theorem red_surjective (ϖ : R) (k : ℕ) :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := fun t =>
  ⟨fun i j => Function.surjInv Ideal.Quotient.mk_surjective (t i j), by
    ext i j; exact Function.surjInv_eq _ _⟩

theorem red_eq_iff (ϖ : R) (k : ℕ) (M N : Matrix (Fin a) (Fin b) R) :
    red ϖ k M = red ϖ k N ↔ ∃ D : Matrix (Fin a) (Fin b) R, M = N + ϖ ^ k • D := by
  constructor
  · intro h
    have h1 : ∀ i j, ∃ d, M i j = N i j + ϖ ^ k * d := by
      intro i j
      have h2 : Ideal.Quotient.mk (lev ϖ k) (M i j) = Ideal.Quotient.mk (lev ϖ k) (N i j) :=
        congrFun (congrFun h i) j
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
      exact ⟨d, by linear_combination -hd⟩
    choose D hD using h1
    exact ⟨Matrix.of D, by ext i j; simp [hD i j]⟩
  · rintro ⟨D, rfl⟩
    ext i j
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨D i j, ?_⟩)
    simp [mul_comm]

theorem smul_cancel {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) {A B : Matrix (Fin a) (Fin b) R}
    (h : ϖ ^ k • A = ϖ ^ k • B) : A = B := by
  ext i j
  have h1 : ϖ ^ k • A i j = ϖ ^ k • B i j := by
    simpa using congrFun (congrFun h i) j
  exact (hr.pow k) h1

theorem red_smul_iff {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) (A B : Matrix (Fin a) (Fin b) R) :
    red ϖ (k + 1) (ϖ ^ k • A) = red ϖ (k + 1) (ϖ ^ k • B) ↔ red ϖ 1 A = red ϖ 1 B := by
  rw [red_eq_iff, red_eq_iff]
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, smul_cancel hr k ?_⟩
    rw [hD, smul_add, smul_smul, pow_one, pow_succ]
  · rintro ⟨D, rfl⟩
    refine ⟨D, ?_⟩
    rw [smul_add, smul_smul, pow_one, pow_succ]

theorem gram_expand (σ : R →+* R) {r : R} (hc : σ r = r) (S : Matrix (Fin a) (Fin a) R)
    (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + r • y) * S * (x + r • y) =
      cT σ x * S * x + r • (cT σ y * S * x + cT σ x * S * y) + (r * r) • (cT σ y * S * y) := by
  rw [cT_add, cT_smul, hc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel

theorem lift_iff {σ : R →+* R} {ϖ : R} (hf : σ ϖ = ϖ) (hr : IsSMulRegular R ϖ) {k : ℕ} (hk : 1 ≤ k)
    (S : Matrix (Fin a) (Fin a) R) (T H : Matrix (Fin b) (Fin b) R)
    (x y : Matrix (Fin a) (Fin b) R) (hH : cT σ x * S * x + ϖ ^ k • H = T) :
    red ϖ (k + 1) (cT σ (x + ϖ ^ k • y) * S * (x + ϖ ^ k • y)) = red ϖ (k + 1) T ↔
      red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 H := by
  have hc : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hf]
  have hq : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = 0 := by
    have : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = red ϖ (k + 1) 0 := by
      refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • (cT σ y * S * y), ?_⟩
      rw [smul_smul, zero_add, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [this]
    ext i j; simp [red]
  rw [gram_expand σ hc, red_add, hq, add_zero, ← hH, red_add, red_add]
  rw [add_right_inj, red_smul_iff hr]

section Main

variable {σ : R →+* R} {ϖ : R}

abbrev solSet (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R)
    (k : ℕ) : Set (Matrix (Fin a) (Fin b) R) :=
  {x | red ϖ k (cT σ x * S * x) = red ϖ k T}

theorem lev_succ_le_lev (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ k))

def proj (ϖ : R) (k : ℕ) (t : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ (k + 1))) :
    Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  t.map (Ideal.Quotient.factor (lev_succ_le_lev ϖ k))

theorem proj_red (ϖ : R) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) :
    proj ϖ k (red ϖ (k + 1) x) = red ϖ k x := by
  ext i j; simp [proj, red]

theorem solSet_succ {S : Matrix (Fin a) (Fin a) R} {T : Matrix (Fin b) (Fin b) R} {k : ℕ}
    {x : Matrix (Fin a) (Fin b) R} (hx : x ∈ solSet σ ϖ S T (k + 1)) : x ∈ solSet σ ϖ S T k := by
  have h1 := congrArg (proj ϖ k) hx
  simp only [proj_red] at h1
  exact h1

def down (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R) (k : ℕ)
    (t : red ϖ (k + 1) '' solSet σ ϖ S T (k + 1)) : red ϖ k '' solSet σ ϖ S T k :=
  ⟨proj ϖ k t.1, by
    obtain ⟨x, hx, e⟩ := t.2
    exact ⟨x, solSet_succ hx, by rw [← e, proj_red]⟩⟩

theorem red_diff (hf : σ ϖ = ϖ) (S : Matrix (Fin a) (Fin a) R) (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) =
      cT (barσ σ ϖ hf 1) (red ϖ 1 y) * red ϖ 1 S * red ϖ 1 x +
        cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 y := by
  simp only [red_add, red_mul, red_cT σ ϖ hf]

theorem fibre_card {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {m n : ℕ} (hnm : n ≤ m)
    {S : Matrix (Fin m) (Fin m) R} {T : Matrix (Fin n) (Fin n) R} (hS : IsUnimod σ S)
    (hT : IsUnimod σ T) {k : ℕ} (hk : 1 ≤ k) {x : Matrix (Fin m) (Fin n) R}
    (hx : x ∈ solSet σ ϖ S T k) (s : red ϖ k '' solSet σ ϖ S T k) (hs : s.1 = red ϖ k x) :
    Nat.card {t // down σ ϖ S T k t = s} = q ^ (2 * m * n - n ^ 2) := by
  obtain ⟨D, hD⟩ := (red_eq_iff _ _ _ _).1 hx
  have hH : cT σ x * S * x + ϖ ^ k • (-D) = T := by
    rw [hD, smul_neg]; abel
  have hG : cT σ (cT σ x * S * x) = cT σ x * S * x := by
    rw [cT_mul, cT_mul, cT_cT σ h.inv, hS.1, Matrix.mul_assoc]
  have hherm : cT σ (-D) = -D := by
    apply smul_cancel h.reg k
    have h1 := congrArg (cT σ) hH
    rw [cT_add, cT_smul, map_pow, h.fix_ϖ, hG, hT.1] at h1
    exact add_left_cancel (h1.trans hH.symm)
  have hf := h.fix_ϖ
  have hgram : cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 x = red ϖ 1 T := by
    rw [← red_cT σ ϖ hf, ← red_mul, ← red_mul]
    refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • D, ?_⟩
    rw [hD, smul_smul, ← pow_add]
    congr 3
    omega
  have hdet : IsUnit (red ϖ 1 T).det := by
    have h1 := hT.2.map (Ideal.Quotient.mk (lev ϖ 1))
    rw [RingHom.map_det] at h1
    exact h1
  have hcard := GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential _ (barσ σ ϖ hf 1) q ε (GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad R σ ϖ q ε h) m n hnm
    (red ϖ 1 S) (red ϖ 1 T) (red ϖ 1 x) (red ϖ 1 (-D))
    (by rw [← red_cT σ ϖ hf, hS.1]) (by rw [← red_cT σ ϖ hf, hT.1]) hdet hgram
    (by rw [← red_cT σ ϖ hf, hherm])
  rw [← hcard]
  symm
  let W := {y : Matrix (Fin m) (Fin n) R //
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 (-D)}
  refine card_eq_of_surj (W := W)
    (fun w => ⟨red ϖ 1 w.1, by rw [← red_diff hf]; exact w.2⟩)
    (fun w => ⟨⟨red ϖ (k + 1) (x + ϖ ^ k • w.1), x + ϖ ^ k • w.1,
        (lift_iff hf h.reg hk S T (-D) x w.1 hH).2 w.2, rfl⟩, Subtype.ext (by
          show proj ϖ k (red ϖ (k + 1) (x + ϖ ^ k • w.1)) = s.1
          rw [proj_red, hs]
          exact (red_eq_iff _ _ _ _).2 ⟨w.1, rfl⟩)⟩) ?_ ?_ ?_
  · rintro ⟨ybar, hy⟩
    obtain ⟨y, rfl⟩ := red_surjective ϖ 1 ybar
    exact ⟨⟨y, by rw [red_diff hf]; exact hy⟩, rfl⟩
  · rintro ⟨⟨t, x', hx', rfl⟩, ht⟩
    have h1 : red ϖ k x' = red ϖ k x := by
      have h2 : proj ϖ k (red ϖ (k + 1) x') = s.1 := congrArg Subtype.val ht
      rwa [proj_red, hs] at h2
    obtain ⟨y, rfl⟩ := (red_eq_iff _ _ _ _).1 h1
    exact ⟨⟨y, (lift_iff hf h.reg hk S T (-D) x y hH).1 hx'⟩, rfl⟩
  · intro w w'
    rw [Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
    show red ϖ 1 w.1 = red ϖ 1 w'.1 ↔
      red ϖ (k + 1) (x + ϖ ^ k • w.1) = red ϖ (k + 1) (x + ϖ ^ k • w'.1)
    rw [red_add, red_add, add_right_inj, red_smul_iff h.reg]

end Main

end GlobalTheory.CompanionTheory.UnrDens.HenselStep


open GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep in
theorem GlobalTheory.CompanionTheory.UnrDens.solCount_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k →
    solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  intro R _ σ ϖ q ε h m n hnm S T hS hT k hk
  have hfin : ∀ j, Finite (R ⧸ lev ϖ j) := fun j =>
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε h j]
      exact pow_ne_zero _ (by have := h.one_lt; omega))
  haveI := hfin k
  haveI := hfin (k + 1)
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := by unfold Matrix; infer_instance
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1))) := by unfold Matrix; infer_instance
  unfold solCount
  refine card_of_fibres (down σ ϖ S T k) _ ?_
  rintro ⟨s, x, hx, rfl⟩
  exact fibre_card h hnm hS hT hk hx _ rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSuccStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_reps_count_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_succ | exact GlobalTheory.CompanionTheory.UnrDens.solCount_succ | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_succ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens Filter Topology

namespace GlobalTheory.CompanionTheory.UnrDens

theorem unrFormula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  have hsq : n ^ 2 ≤ 2 * m * n := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by omega
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := by
    intro j
    induction j with
    | zero =>
      rw [GlobalTheory.T.card_unimodular_hermitian_reps_level_one R σ ϖ q ε hR m n hnm S T hS hT, ha]
      simp
    | succ j ih =>
      rw [GlobalTheory.T.unimodular_hermitian_reps_count_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]
      push_cast
      rw [ih, add_mul, one_mul, pow_add]
      ring
  have hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
    intro j
    unfold densAt
    have hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1), ← pow_mul,
        ← pow_mul]
      ring_nf
    rw [hsol j, GlobalTheory.T.card_hermitian_matrices_mod_pow R σ ϖ q ε hR n (j + 1), hM]
    have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
      calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
        _ = (j + 1) * (2 * m * n) := by rw [ha']
        _ = 2 * (j + 1) * (m * n) := by ring
    have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n)) := pow_pos hq _
    push_cast
    rw [div_eq_iff hpos.ne', ← he, pow_add, pow_add]
    ring
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hdens j).symm

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormulaStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CFinal
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.LocCMain
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.LocCAsm
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

theorem coe_pS : ((hG.pS : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := rfl

theorem cT_smul_pS (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    PositivityTheory.PfSWUS.Loc.cT σS (hG.pS • X) = hG.pS • X := by
  ext a b
  have h1 := congrFun (congrFun hX a) b
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul] at h1 ⊢
  have h2 : σS hG.pS = hG.pS := hG.quad.fix_ϖ
  rw [h2, h1]

theorem hermLev_succ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    hG.hermLev (k + 1) (hG.pS • X) (hG.cT_smul_pS k X hX) = hG.hermLev k X hX := by
  apply Subtype.ext
  funext a b
  show (ϖ ^ (k + 1))⁻¹ • (((hG.pS • X) a b : S) : Fv F v ⊗[F] E) = (ϖ ^ k)⁻¹ • ((X a b : S) : Fv F v ⊗[F] E)
  rw [Matrix.smul_apply, smul_eq_mul, Subring.coe_mul, coe_pS, ← Algebra.smul_def, smul_smul, pow_succ, mul_inv,
    mul_assoc, inv_mul_cancel₀ hG.unif_ne, mul_one]

def liftH {k : ℕ} (B : hermMod σS hG.pS n k) : Matrix (Fin n) (Fin n) S := Classical.choose B.2

theorem liftH_herm {k : ℕ} (B : hermMod σS hG.pS n k) : PositivityTheory.PfSWUS.Loc.cT σS (hG.liftH B) = hG.liftH B :=
  (Classical.choose_spec B.2).1

theorem red_liftH {k : ℕ} (B : hermMod σS hG.pS n k) : red hG.pS k (hG.liftH B) = B.1 :=
  (Classical.choose_spec B.2).2

def iota (k : ℕ) (B : hermMod σS hG.pS n k) : HermR (Fv F v) σ n ⧸ H0 S σ n :=
  QuotientAddGroup.mk (hG.hermLev k (hG.liftH B) (hG.liftH_herm B))

theorem iota_eq (hCL : ClassLev) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (B : hermMod σS hG.pS n k) (hB : red hG.pS k X = B.1) :
    hG.iota k B = QuotientAddGroup.mk (hG.hermLev k X hX) := by
  unfold iota
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k X (hG.liftH B) hX (hG.liftH_herm B)).2 (by rw [hB, hG.red_liftH])

theorem iota_inj (hCL : ClassLev) (k : ℕ) : Function.Injective (hG.iota k) := by
  intro B B' h
  unfold iota at h
  rw [QuotientAddGroup.eq, neg_add_eq_sub] at h
  have := (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k (hG.liftH B') (hG.liftH B) (hG.liftH_herm B') (hG.liftH_herm B)).1 h
  rw [hG.red_liftH, hG.red_liftH] at this
  exact Subtype.ext this.symm

theorem iota_succ (hCL : ClassLev) (k : ℕ) (B : hermMod σS hG.pS n k) :
    ∃ B' : hermMod σS hG.pS n (k + 1), hG.iota (k + 1) B' = hG.iota k B := by
  refine ⟨⟨red hG.pS (k + 1) (hG.pS • hG.liftH B), hG.pS • hG.liftH B, hG.cT_smul_pS k _ (hG.liftH_herm B), rfl⟩, ?_⟩
  rw [hG.iota_eq hCL (k + 1) (hG.pS • hG.liftH B) (hG.cT_smul_pS k _ (hG.liftH_herm B)) _ rfl, hG.hermLev_succ]
  rfl

theorem iota_surj (hCL : ClassLev) (hEx : Exhaust) (c : HermR (Fv F v) σ n ⧸ H0 S σ n) :
    ∃ k B, hG.iota k B = c := by
  induction c using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨k, X, hX, rfl⟩ := hEx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG b
    exact ⟨k, ⟨red hG.pS k X, X, hX, rfl⟩, hG.iota_eq hCL k X hX _ rfl⟩

theorem f_lev (hNP : NuPow) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hT : ∀ a b, σ (T b a) = T a b)
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (hμ : SdW F E σ M J (Fv F v) ψv n μv)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure)
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (z : ℂ) (k : ℕ) (B : hermMod σS hG.pS n k) :
    whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z
      (hG.hermLev k (hG.liftH B) (hG.liftH_herm B)) =
    ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) *
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
  have e1 := hNL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG lam L hlam hL k (hG.liftH B) (hG.liftH_herm B)
  have e2 := hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG μv hμ k (hG.liftH B) (hG.liftH_herm B)
  have e3 := hPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hT k (hG.liftH B) (hG.liftH_herm B)
  rw [hG.red_liftH] at e1 e2 e3
  have e4 : nuAt hG.pS B.1 = (Ideal.absNorm v.asIdeal ^ 2) ^ Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) :=
    hNP S σS hG.pS _ ε hG.quad n k B.1 B.2
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have := hG.quad.one_lt
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  simp only [whI]
  rw [e1, e2, e3]
  congr 1
  set D := Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1)
  set q := Ideal.absNorm v.asIdeal
  rw [e4]
  have h5 : ((((q ^ 2) ^ D : ℕ) : ℝ) : ℂ) = ((q : ℂ) ^ (2 * D : ℕ)) := by push_cast; ring
  rw [h5, ← Complex.natCast_cpow_natCast_mul]
  have h6 : ((2 * D : ℕ) : ℂ) * -(z - ((M : ℂ) - n) / 2) = (D : ℂ) * (2 * -(z - ((M : ℂ) - n) / 2)) := by push_cast; ring
  rw [h6, Complex.cpow_nat_mul, ← mul_pow]
  congr 1
  rw [← Complex.cpow_intCast, mul_left_comm, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

end GoodLoc

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

theorem locC_of_steps (hP : UnrPoly) (hCI : CosetInt) (hTE : TsumExhaust) (hNP : NuPow) (hNB : NuBound)
    (hLC : LevChars) (hVH : HermitianLatticeVolumeOne) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hEx : Exhaust) (hCL : ClassLev)
    (hInv : HermitianLatticeInvariance) (hCM : CosetMeas) : LocC := by
  classical
  intro F E _ _ _ _ _ σ M n d J T hT bs v ψv S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hR : IsUnrQuad S σS hG.pS q ε := hG.quad
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hfin : ∀ k, Finite (S ⧸ lev hG.pS k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card S σS hG.pS q ε hR k]; exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (S ⧸ lev hG.pS k) := fun k => Fintype.ofFinite _
  letI : ∀ k, Fintype (hermMod σS hG.pS n k) := fun k => Fintype.ofFinite _
  have hε1 : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

  set f := whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z with hf
  have hinv : ∀ b h, h ∈ H0 S σ n → f (b + h) = f b := fun b h hh =>
    hInv F E σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  let fbar : HermR (Fv F v) σ n ⧸ H0 S σ n → ℂ := fun c => f (Quotient.out c)
  have hfbar : ∀ g, f g = fbar (QuotientAddGroup.mk g) := by
    intro g
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) :
        HermR (Fv F v) σ n ⧸ H0 S σ n) = QuotientAddGroup.mk g := Quotient.out_eq' _
    rw [QuotientAddGroup.eq] at h1
    have := hinv (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) _ h1
    rw [add_neg_cancel_left] at this
    exact this

  set t : ℂ := (ε : ℂ) ^ M * (q : ℂ) ^ (-(2 * z + n)) with ht
  have hval : ∀ k (B : hermMod σS hG.pS n k), fbar (hG.iota k B) =
      t ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) *
        hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
    intro k B
    rw [GoodLoc.iota, ← hfbar]
    exact hG.f_lev hNP hJ hNL hPL hT μv hμ lam L hlam hL z k B

  let C : ℕ → Finset (HermR (Fv F v) σ n ⧸ H0 S σ n) := fun k => Finset.univ.image (hG.iota k)
  have hCmono : Monotone C := by
    refine monotone_nat_of_le_succ fun k => ?_
    intro c hc
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨B', hB'⟩ := hG.iota_succ hCL k B
    exact Finset.mem_image.2 ⟨B', Finset.mem_univ _, hB'⟩
  have hCcov : ∀ c, ∃ k, c ∈ C k := by
    intro c
    obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
    exact ⟨k, Finset.mem_image.2 ⟨B, Finset.mem_univ _, rfl⟩⟩
  have hsumC : ∀ k, ∑ c ∈ C k, fbar c = ∑ B : hermMod σS hG.pS n k, fbar (hG.iota k B) := fun k =>
    Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h
  have hnormC : ∀ k, ∑ c ∈ C k, ‖fbar c‖ = ∑ B : hermMod σS hG.pS n k, ‖t‖ ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) := by
    intro k
    rw [Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, norm_mul, norm_pow, AddChar.norm_apply, mul_one]

  have htn : ‖t‖ = (q : ℝ) ^ (-(2 * z.re + n)) := by
    rw [ht, norm_mul, norm_pow, hε1, one_pow, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have hlt : (q : ℝ) ^ (n ^ 2) * ‖t‖ < 1 := by
    rw [htn, ← Real.rpow_natCast, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < q))]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq1)
    push_cast
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbound : ∀ k, ∑ c ∈ C k, ‖fbar c‖ ≤ 1 / (1 - (q : ℝ) ^ (n ^ 2) * ‖t‖) := by
    intro k
    rw [hnormC]
    have := hNB S σS hG.pS q ε hR n k ‖t‖ (norm_nonneg _) hlt
    rwa [tsum_fintype] at this

  have hlc : IsLevelChars σS hG.pS (hG.psiLev (c := -1) (neg_mem (one_mem _))) :=
    hLC F E σ M n d J T bs v ψv S σS ϖ ε hG (-1) (neg_mem (one_mem _)) (by simp)
  have hpoly : ∀ k, 1 ≤ k → ∑ c ∈ C k, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro k hk
    rw [hsumC, ← hP S σS hG.pS q ε hR _ hlc n (matS S T hG.T_int) hG.T_unimod k hk t, tsum_fintype]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, mul_comm]

  obtain ⟨hsum, htend⟩ := hTE _ fbar C hCmono hCcov ⟨_, hbound⟩
  have htsum : ∑' c, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    refine tendsto_nhds_unique htend ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact (hpoly k hk).symm

  haveI := hν.1
  haveI := hCM F E σ M n d J T bs v ψv S σS ϖ ε hG |>.1
  have hcount : Countable (HermR (Fv F v) σ n ⧸ H0 S σ n) := by
    have : (Set.univ : Set (HermR (Fv F v) σ n ⧸ H0 S σ n)) ⊆ ⋃ k, Set.range (hG.iota k) := fun c _ => by
      obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
      exact Set.mem_iUnion.2 ⟨k, B, rfl⟩
    exact Set.countable_univ_iff.1 ((Set.countable_iUnion fun k => (Set.finite_range _).countable).mono this)
  obtain ⟨hI1, hI2⟩ := hCI _ νv (H0 S σ n) (hCM F E σ M n d J T bs v ψv S σS ϖ ε hG).2
    (hVH F E σ M n d J T bs v ψv S σS ϖ ε hG νv hν) hcount f fbar hfbar
  refine ⟨hI1.2 hsum, ?_⟩
  rw [hI2 hsum, htsum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [ht, mul_pow, mul_mul_mul_comm, ← pow_add, ← Complex.cpow_natCast (q : ℂ) (i : ℕ), ← Complex.cpow_add _ _ hq0]
  congr 2
  ring

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem unrPoly : PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := GlobalTheory.T.unramified_formula_polynomial_gen GlobalTheory.T.unramified_local_formula

theorem locC : LocC :=
  locC_of_steps unrPoly GlobalTheory.T.coset_integral_unramified GlobalTheory.T.tsum_exhaustion_unramified GlobalTheory.T.multiplicity_power_formula GlobalTheory.T.multiplicity_bound_unramified GlobalTheory.T.level_characters_unramified GlobalTheory.T.integral_hermitian_volume_one GlobalTheory.T.level_joint_reduction GlobalTheory.T.multiplicity_level_formula GlobalTheory.T.character_level_formula GlobalTheory.T.level_exhaustion GlobalTheory.T.class_level_formula GlobalTheory.T.integral_hermitian_invariance GlobalTheory.T.coset_measure_formula

end PositivityTheory.SiegelWeilFormula.Gunr
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGood
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.NormLeOneIffMem
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_le_one_iff_mem' (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_two (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : (2 : F)⁻¹ ∈ basisSet σ bs := by
  classical
  simp [basisSet]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_one (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (k : Fin d) :
    bs.repr 1 k ∈ basisSet σ bs := by
  unfold basisSet
  simp

theorem two_of {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) : ‖(2 : Fv F v)‖ = 1 := by
  have h1 := hB _ (mem_basisSet_two σ bs)
  rw [map_inv₀, map_ofNat, ← norm_le_one_iff_mem', norm_inv] at h1
  have h2 : ‖(2 : Fv F v)‖ ≤ 1 := by
    rw [norm_le_one_iff_mem', show (2 : Fv F v) = 1 + 1 by norm_num]
    exact add_mem (one_mem _) (one_mem _)
  have h0 : (2 : Fv F v) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero_iff _ (algebraMap F (Fv F v)).injective).mpr two_ne_zero
  have hpos : 0 < ‖(2 : Fv F v)‖ := norm_pos_iff.mpr h0
  have h3 := (inv_le_one₀ hpos).mp h1
  linarith

theorem unif_mem_Rv {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ Rv bs v := by
  intro k
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.basis_repr_tmul]
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact mul_mem hϖ (hB _ (mem_basisSet_one σ bs k))

theorem locRingE_of (h1 : RvRing) (h2 : FixedK) (h3 : UnifEx) (h4 : QuadAt) (h6 : TraceDualAt) : LocRingE := by
  intro F E i1 i2 i3 i4 i5 σ hCM d bs v hB
  obtain ⟨S, σS, hS, hσS⟩ := h1 F E σ d bs v hB
  obtain ⟨ϖ, hϖ0, hϖ1, hϖd, hϖc⟩ := h3 F v
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε : ℂ) = eSp E v := by
    unfold eSp
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  have hϖS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v) ∈ S := by
    have := unif_mem_Rv hB ϖ.2
    rw [← hS] at this
    exact this
  have htr := h6 F E σ hCM d bs v hB
  rw [← hS] at htr
  exact ⟨S, σS, ϖ, ε, hϖS, hε, hS, hσS, h2 F E σ hCM v, ϖ.2, hϖ0, hϖ1,
    h4 F E σ hCM d bs v hB S σS hS hσS ϖ hϖ0 hϖ1 hϖd hϖc hϖS ε hε, two_of hB, htr⟩

theorem almostGood_ofE (h1 : FinInt) (h2 : PsiBasic) (h3 : PsiCond) (h4 : LocRingE) (h5 : LocMat) : AlmostGood := by
  classical
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  filter_upwards [h1 F (basisSet σ bs ∪ matSet bs J ∪ matSet bs T), h3 F ψ hψ] with v hv hc
  have hB : IntAt v (basisSet σ bs) := fun x hx => hv x (by simp [hx])
  have hMJ : IntAt v (matSet bs J) := fun x hx => hv x (by simp [hx])
  have hMT : IntAt v (matSet bs T) := fun x hx => hv x (by simp [hx])
  obtain ⟨S, σS, ϖ, ε, hϖ, hε, hcar, hsig, hfix, hϖO, hϖ0, hϖ1, hquad, htwo, htr⟩ := h4 F E σ hσ d bs v hB
  obtain ⟨hJi, hJu⟩ := h5 F E σ d bs v S σS hcar hsig M J hJ.1 hJ.2 hMJ
  obtain ⟨hTi, hTu⟩ := h5 F E σ d bs v S σS hcar hsig n T hT hdet hMT
  obtain ⟨pa, p0, pc⟩ := h2 F ψ hψ v
  exact ⟨S, σS, ϖ, ε, hε,
    { carrier := hcar, sig := hsig, fixed := hfix, unif_mem := hϖO, unif_ne := hϖ0, unif_lt := hϖ1, unif_S := hϖ,
      quad := hquad, two := htwo, trace_dual := htr, J_int := hJi, J_unimod := hJu, T_int := hTi, T_unimod := hTu,
      psi_add := pa, psi_zero := p0, psi_cont := pc, psi_cond := hc }⟩

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem almostGood : AlmostGood :=
  almostGood_ofE GlobalTheory.T.unramified_finite_integral GlobalTheory.T.basic_character_unramified GlobalTheory.T.character_conductor_condition
    (locRingE_of GlobalTheory.T.residue_ring_structure GlobalTheory.T.fixed_field_structure GlobalTheory.T.uniformizer_existence
      (quadAt_of GlobalTheory.T.unramified_quadratic_condition_one GlobalTheory.T.unramified_quadratic_condition_two GlobalTheory.T.unramified_quadratic_condition_three GlobalTheory.T.unramified_quadratic_condition_four GlobalTheory.T.unramified_quadratic_condition_five) GlobalTheory.T.trace_dual_at_place) GlobalTheory.T.local_matrix_integral

end PositivityTheory.SiegelWeilFormula.Gunr
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Assemble
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

variable {F : Type} [Field F] [NumberField F]

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

theorem unrWhitX_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitX := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨(n : ℝ) ^ 2, ?_⟩
  filter_upwards [hA F E σ hσ M J hJ n T hT hdet d bs ψ hψ] with v hv
  obtain ⟨S, σS, ϖ, ε, hε, hG⟩ := hv
  intro μv νv lam L hμ hν hlam hL z hz
  rw [← hε]
  exact hC F E σ M n d J T hT bs v (psiV F ψ v) S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz

theorem eSp_eq (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℤˣ, ((e : ℤ) : ℂ) = eSp E v := by
  unfold eSp
  split_ifs
  · exact ⟨-1, by simp⟩
  · exact ⟨1, by simp⟩

theorem unrWhitAll_of_X (h : UnrWhitX) : UnrWhitAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  obtain ⟨t, ht⟩ := h F E σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨t, ?_⟩
  filter_upwards [ht] with v hv
  obtain ⟨e, he⟩ := eSp_eq E v
  exact ⟨e, fun μv νv lam L hμ hν hlam hL z hz => by rw [he]; exact hv μv νv lam L hμ hν hlam hL z hz⟩

theorem unrWhitAll_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitAll := unrWhitAll_of_X (unrWhitX_of_parts hC hA)

theorem unrWhit_of_all (h : UnrWhitAll) : UnrWhit :=
  fun F E _ _ _ _ _ σ hσ M J hJ n _ T hT hdet d bs ψ hψ => h F E σ hσ M J hJ n T hT hdet d bs ψ hψ

theorem unrWhit_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhit := unrWhit_of_all (unrWhitAll_of_parts hC hA)

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem unrWhitX : PositivityTheory.SiegelWeilFormula.Gen.UnrWhitX := unrWhitX_of_parts locC almostGood

theorem unrWhit : PositivityTheory.SiegelWeilFormula.Gen.UnrWhit := unrWhit_of_parts locC almostGood

end PositivityTheory.SiegelWeilFormula.Gunr
