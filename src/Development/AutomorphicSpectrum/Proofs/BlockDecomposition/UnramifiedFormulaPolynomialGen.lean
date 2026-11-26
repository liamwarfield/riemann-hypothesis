module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardPreimageHom
open Filter Topology

namespace GlobalTheory.CompanionTheory.LocalDens

open PositivityTheory.PfSWUS.Loc

variable {R : Type} [CommRing R]

theorem cT_mul (σ : R →+* R) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j; simp [cT]

theorem cT_smul (σ : R →+* R) {a b : ℕ} (r : R) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (r • x) = σ r • cT σ x := by
  ext i j; simp [cT]

theorem cT_one (σ : R →+* R) {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  simp [red, Matrix.map_mul]

theorem red_add (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j; simp [red]

theorem red_one (ϖ : R) (k : ℕ) {a : ℕ} : red ϖ k (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  simp [red]

theorem red_eq_iff (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k x = red ϖ k y ↔ ∀ i j, ϖ ^ k ∣ x i j - y i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [red, Matrix.map_apply] at this
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 this)
  · intro h
    ext i j
    simp only [red, Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h i j))

theorem red_pow_smul (ϖ : R) (k j : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (ϖ ^ (k + j) • x) = 0 := by
  have : red ϖ k (ϖ ^ (k + j) • x) = red ϖ k 0 := by
    rw [red_eq_iff]
    intro i l
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, sub_zero, pow_add]
    exact ⟨ϖ ^ j * x i l, by ring⟩
  rw [this]; ext i l; simp [red]

theorem red_cT_congr {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    {x y : Matrix (Fin a) (Fin b) R} (h : red ϖ k x = red ϖ k y) :
    red ϖ k (cT σ x) = red ϖ k (cT σ y) := by
  rw [red_eq_iff] at h ⊢
  intro i j
  have := map_dvd σ (h j i)
  simpa [cT, hσ, map_sub] using this

theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} : Function.Surjective (red ϖ k (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem finite_lev {ϖ : R} (h : Finite (R ⧸ lev ϖ 1)) (k : ℕ) : Finite (R ⧸ lev ϖ k) := by
  have h1 : lev ϖ k = (lev ϖ 1) ^ k := by simp [lev, Ideal.span_singleton_pow]
  rw [h1]
  exact Ideal.finite_quotient_pow ⟨{ϖ ^ 1}, by simp [lev]⟩ k

theorem inv_mod (ϖ : R) (k : ℕ) {a : ℕ} (N : Matrix (Fin a) (Fin a) R) :
    ∃ h, red ϖ k ((1 + ϖ • N) * h) = 1 ∧ red ϖ k (h * (1 + ϖ • N)) = 1 := by
  refine ⟨∑ i ∈ Finset.range k, (ϖ • (-N)) ^ i, ?_, ?_⟩
  · have h1 : (1 + ϖ • N) = 1 - ϖ • (-N) := by simp
    rw [h1, mul_neg_geom_sum, smul_pow]
    have : (1 - ϖ ^ k • (-N) ^ k : Matrix (Fin a) (Fin a) R) = 1 + ϖ ^ (k + 0) • (-(-N) ^ k) := by
      simp [sub_eq_add_neg]
    rw [this, red_add, red_pow_smul, red_one, add_zero]
  · have h1 : (1 + ϖ • N) = 1 - ϖ • (-N) := by simp
    rw [h1, geom_sum_mul_neg, smul_pow]
    have : (1 - ϖ ^ k • (-N) ^ k : Matrix (Fin a) (Fin a) R) = 1 + ϖ ^ (k + 0) • (-(-N) ^ k) := by
      simp [sub_eq_add_neg]
    rw [this, red_add, red_pow_smul, red_one, add_zero]

def gr (σ : R →+* R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin n) (Fin n) R := cT σ x * S * x

theorem gr_congr {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) (k : ℕ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    {x y : Matrix (Fin m) (Fin n) R} (h : red ϖ k x = red ϖ k y) :
    red ϖ k (gr σ S x) = red ϖ k (gr σ S y) := by
  rw [gr, gr, red_mul, red_mul, red_mul, red_mul, red_cT_congr hσ k h, h]

theorem gr_mul (σ : R →+* R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R)
    (g : Matrix (Fin n) (Fin n) R) : gr σ S (x * g) = cT σ g * gr σ S x * g := by
  simp only [gr, cT_mul, Matrix.mul_assoc]

def sol (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Set (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :=
  red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (gr σ S x) = red ϖ k T}

theorem solCount_eq (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) : solCount σ ϖ S T k = Nat.card (sol σ ϖ S T k) := rfl

theorem sol_congr (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    {T₁ T₂ : Matrix (Fin n) (Fin n) R} (k : ℕ) (h : red ϖ k T₁ = red ϖ k T₂) :
    sol σ ϖ S T₁ k = sol σ ϖ S T₂ k := by
  simp only [sol, h]

theorem solCount_congr {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T g h : Matrix (Fin n) (Fin n) R) (k : ℕ) (hgh : red ϖ k (g * h) = 1) (hhg : red ϖ k (h * g) = 1) :
    solCount σ ϖ S (cT σ g * T * g) k = solCount σ ϖ S T k := by
  have hc : red ϖ k (cT σ (g * h)) = 1 := by
    have h1 : red ϖ k (g * h) = red ϖ k 1 := by rw [hgh, red_one]
    rw [red_cT_congr hσ k h1, cT_one, red_one]
  have himg : sol σ ϖ S (cT σ g * T * g) k = (fun y => y * red ϖ k g) '' sol σ ϖ S T k := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨red ϖ k (x * h), ⟨x * h, ?_, rfl⟩, ?_⟩
      · have hx' : red ϖ k (gr σ S x) = red ϖ k (cT σ g * T * g) := hx
        show red ϖ k (gr σ S (x * h)) = red ϖ k T
        rw [gr_mul, red_mul, red_mul, hx', red_mul, red_mul]
        rw [cT_mul, red_mul] at hc
        rw [red_mul] at hgh
        calc red ϖ k (cT σ h) * (red ϖ k (cT σ g) * red ϖ k T * red ϖ k g) * red ϖ k h
            = (red ϖ k (cT σ h) * red ϖ k (cT σ g)) * red ϖ k T * (red ϖ k g * red ϖ k h) := by
              simp only [Matrix.mul_assoc]
          _ = red ϖ k T := by rw [hc, hgh, Matrix.one_mul, Matrix.mul_one]
      · show red ϖ k (x * h) * red ϖ k g = red ϖ k x
        rw [red_mul, Matrix.mul_assoc, ← red_mul ϖ k h g, hhg, Matrix.mul_one]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : red ϖ k (gr σ S x) = red ϖ k T := hx
      refine ⟨x * g, ?_, red_mul _ _ _ _⟩
      show red ϖ k (gr σ S (x * g)) = red ϖ k (cT σ g * T * g)
      rw [gr_mul, red_mul, red_mul, hx', red_mul, red_mul]
  have hinj : Function.Injective (fun y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k) => y * red ϖ k g) := by
    intro y y' hyy
    have h2 : y * red ϖ k g * red ϖ k h = y' * red ϖ k g * red ϖ k h := by
      simp only at hyy
      rw [hyy]
    rw [red_mul] at hgh
    simpa [Matrix.mul_assoc, hgh] using h2
  rw [solCount_eq, solCount_eq, himg]
  exact Nat.card_image_of_injective hinj _

theorem twist {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {n : ℕ} {T T' H : Matrix (Fin n) (Fin n) R} {t : R}
    (ht : t + σ t = 1) (hH : cT σ H = H) (e b : ℕ)
    (h1 : T * T' = ϖ ^ e • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : cT σ T' * T = ϖ ^ e • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ g h : Matrix (Fin n) (Fin n) R, red ϖ (e + b + 1 + 1) (g * h) = 1 ∧ red ϖ (e + b + 1 + 1) (h * g) = 1 ∧
      red ϖ (e + b + 1 + 1) (cT σ g * T * g) = red ϖ (e + b + 1 + 1) (T + ϖ ^ (e + b + 1) • H) := by
  obtain ⟨h, hgh, hhg⟩ := inv_mod ϖ (e + b + 1 + 1) ((ϖ ^ b * t) • (T' * H))
  refine ⟨_, h, hgh, hhg, ?_⟩
  have hs : σ t = 1 - t := by rw [← ht]; ring
  have hcg : cT σ (1 + ϖ • (ϖ ^ b * t) • (T' * H)) = 1 + (ϖ ^ (b + 1) * (1 - t)) • (H * cT σ T') := by
    rw [cT_add, cT_one, cT_smul, cT_smul, cT_mul, hH, hσ, map_mul, map_pow, hσ, hs, smul_smul, pow_succ]
    congr 2
    ring
  have e1 : (1 + (ϖ ^ (b + 1) * (1 - t)) • (H * cT σ T')) * T
      = T + (ϖ ^ (b + 1) * (1 - t) * ϖ ^ e) • H := by
    rw [add_mul, one_mul, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have e2 : T * (T' * H) = ϖ ^ e • H := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  have e3 : cT σ (1 + ϖ • (ϖ ^ b * t) • (T' * H)) * T * (1 + ϖ • (ϖ ^ b * t) • (T' * H))
      = (T + ϖ ^ (e + b + 1) • H) + ϖ ^ ((e + b + 1 + 1) + b) • ((t * (1 - t)) • (H * (T' * H))) := by
    rw [hcg, e1, mul_add, add_mul, add_mul, Matrix.mul_one, Matrix.mul_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, e2]
    simp only [smul_smul]
    have c1 : ϖ ^ ((e + b + 1 + 1) + b) = ϖ ^ (b + 1) * ϖ ^ (b + 1) * ϖ ^ e := by ring
    have c2 : ϖ ^ (e + b + 1) = ϖ ^ (b + 1) * ϖ ^ e := by ring
    rw [c1, c2]
    module
  rw [e3, red_add, red_pow_smul, add_zero]

theorem card_fibers {α β : Type} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (hf : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp [hf, Nat.card_eq_fintype_card]

theorem card_preimage_hom {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B] (f : A →+ B)
    (hf : Function.Surjective f) (U : Set B) :
    Nat.card (f ⁻¹' U) * Nat.card B = Nat.card U * Nat.card A := by
  have fib : ∀ b, Nat.card {a // f a = b} = Nat.card f.ker := by
    intro b
    obtain ⟨a0, rfl⟩ := hf b
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1 - a0, by simp [AddMonoidHom.mem_ker, a.2]⟩
        invFun := fun z => ⟨z.1 + a0, by have := z.2; simp only [AddMonoidHom.mem_ker] at this; simp [this]⟩
        left_inv := fun a => by simp
        right_inv := fun z => by simp }
  have hA := card_fibers f _ fib
  have hU : Nat.card (f ⁻¹' U) = Nat.card U * Nat.card f.ker := by
    refine card_fibers (fun a : f ⁻¹' U => (⟨f a.1, a.2⟩ : U)) _ (fun b => ?_)
    rw [← fib b.1]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, by simpa [Subtype.ext_iff] using a.2⟩
        invFun := fun a => ⟨⟨a.1, by show f a.1 ∈ U; rw [a.2]; exact b.2⟩, Subtype.ext a.2⟩
        left_inv := fun a => by simp
        right_inv := fun a => by simp }
  rw [hA, hU]
  ring

theorem lev_le (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ k))

def piM (ϖ : R) (k a b : ℕ) :
    Matrix (Fin a) (Fin b) (R ⧸ lev ϖ (k + 1)) →+ Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  (Ideal.Quotient.factor (lev_le ϖ k)).toAddMonoidHom.mapMatrix

theorem piM_red (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    piM ϖ k a b (red ϖ (k + 1) x) = red ϖ k x := by
  ext i j
  simp [piM, red]

theorem piM_surj (ϖ : R) (k a b : ℕ) : Function.Surjective (piM ϖ k a b) := by
  intro y
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  exact ⟨red ϖ (k + 1) x, piM_red ϖ k x⟩

theorem cT_neg (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : cT σ (-x) = - cT σ x := by
  ext i j; simp [cT]

theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : red ϖ k (-x) = - red ϖ k x := by
  ext i j; simp [red]

def hermSub (σ : R →+* R) (ϖ : R) (n k : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) where
  carrier := hermMod σ ϖ n k
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hx' : cT σ x = x := hx
    have hy' : cT σ y = y := hy
    exact ⟨x + y, by show cT σ (x + y) = x + y; rw [cT_add, hx', hy'], red_add _ _ _ _⟩
  zero_mem' := ⟨0, by show cT σ 0 = 0; ext i j; simp [cT], by ext i j; simp [red]⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : cT σ x = x := hx
    exact ⟨-x, by show cT σ (-x) = -x; rw [cT_neg, hx'], red_neg _ _ _⟩

def piH (σ : R →+* R) (ϖ : R) (n k : ℕ) : hermSub σ ϖ n (k + 1) →+ hermSub σ ϖ n k :=
  ((piM ϖ k n n).comp (hermSub σ ϖ n (k + 1)).subtype).codRestrict (hermSub σ ϖ n k) (by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨x, hx, (piM_red ϖ k x).symm⟩)

theorem piH_surj (σ : R →+* R) (ϖ : R) (n k : ℕ) : Function.Surjective (piH σ ϖ n k) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨red ϖ (k + 1) x, x, hx, rfl⟩, Subtype.ext (piM_red ϖ k x)⟩

noncomputable def gb (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (k : ℕ)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k) :=
  red ϖ k (gr σ S (Function.surjInv (red_surj ϖ k) y))

theorem gb_red {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (k : ℕ)
    (x : Matrix (Fin m) (Fin n) R) : gb σ ϖ S k (red ϖ k x) = red ϖ k (gr σ S x) :=
  gr_congr hσ k S (Function.surjInv_eq _ _)

theorem mem_sol {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    y ∈ sol σ ϖ S T k ↔ gb σ ϖ S k y = red ϖ k T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [gb_red hσ]
    exact hx
  · intro h
    exact ⟨_, h, Function.surjInv_eq _ _⟩

theorem gr_herm {σ : R →+* R} (hinv : ∀ a, σ (σ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) R}
    (hS : cT σ S = S) (x : Matrix (Fin m) (Fin n) R) : cT σ (gr σ S x) = gr σ S x := by
  have : cT σ (cT σ x) = x := by ext i j; simp [cT, hinv]
  rw [gr, cT_mul, cT_mul, this, hS, Matrix.mul_assoc]

theorem dens_step {σ : R →+* R} {ϖ : R} (hfin : ∀ k, Finite (R ⧸ lev ϖ k)) (hinv : ∀ a, σ (σ a) = a)
    (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ)
    (hS : cT σ S = S) (hT : cT σ T = T)
    (hfib : ∀ h : Matrix (Fin n) (Fin n) R, cT σ h = h → red ϖ k h = red ϖ k T →
      solCount σ ϖ S h (k + 1) = solCount σ ϖ S T (k + 1)) :
    densAt σ ϖ S T k = densAt σ ϖ S T (k + 1) := by
  haveI := hfin
  haveI : ∀ k a b, Finite (Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k)) := fun k a b =>
    inferInstanceAs (Finite (Fin a → Fin b → R ⧸ lev ϖ k))
  have hTm : red ϖ k T ∈ hermSub σ ϖ n k := ⟨T, hT, rfl⟩
  have h1 := card_preimage_hom (piM ϖ k m n) (piM_surj ϖ k m n) (sol σ ϖ S T k)
  have h2 := card_preimage_hom (piH σ ϖ n k) (piH_surj σ ϖ n k) {⟨red ϖ k T, hTm⟩}
  have hmem : ∀ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)), gb σ ϖ S (k + 1) y ∈ hermSub σ ϖ n (k + 1) := by
    intro y
    obtain ⟨x, rfl⟩ := red_surj ϖ (k + 1) y
    rw [gb_red hσ]
    exact ⟨_, gr_herm hinv hS x, rfl⟩
  have hpi : ∀ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)),
      gb σ ϖ S k (piM ϖ k m n y) = piM ϖ k n n (gb σ ϖ S (k + 1) y) := by
    intro y
    obtain ⟨x, rfl⟩ := red_surj ϖ (k + 1) y
    rw [gb_red hσ, piM_red, gb_red hσ, piM_red]
  have h3 : Nat.card ((piM ϖ k m n) ⁻¹' (sol σ ϖ S T k))
      = Nat.card ((piH σ ϖ n k) ⁻¹' {⟨red ϖ k T, hTm⟩}) * solCount σ ϖ S T (k + 1) := by
    have hD : ∀ y : (piM ϖ k m n) ⁻¹' (sol σ ϖ S T k), (⟨gb σ ϖ S (k + 1) y.1, hmem y.1⟩ : hermSub σ ϖ n (k + 1)) ∈
        (piH σ ϖ n k) ⁻¹' {⟨red ϖ k T, hTm⟩} := by
      intro y
      have := (mem_sol hσ S T k _).1 y.2
      rw [hpi] at this
      exact Subtype.ext this
    refine card_fibers (fun y => ⟨⟨gb σ ϖ S (k + 1) y.1, hmem y.1⟩, hD y⟩) _ (fun d => ?_)
    obtain ⟨⟨_, h, hh, rfl⟩, hd⟩ := d
    have hk : red ϖ k h = red ϖ k T := by
      have := congrArg Subtype.val (Set.mem_singleton_iff.1 hd)
      simpa [piH, piM_red] using this
    rw [← hfib h hh hk, solCount_eq]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, (mem_sol hσ S h (k + 1) _).2 (by
          have := congrArg (fun w => w.1.1) y.2
          simpa using this)⟩
        invFun := fun z => ⟨⟨z.1, by
          show piM ϖ k m n z.1 ∈ sol σ ϖ S T k
          rw [mem_sol hσ, hpi, (mem_sol hσ S h (k + 1) _).1 z.2, piM_red, hk]⟩,
          Subtype.ext (Subtype.ext ((mem_sol hσ S h (k + 1) _).1 z.2))⟩
        left_inv := fun y => by simp
        right_inv := fun z => by simp }
  have hH : ∀ k, Nat.card (hermMod σ ϖ n k) = Nat.card (hermSub σ ϖ n k) := fun _ => rfl
  have hM : ∀ k, 0 < Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := fun k => Nat.card_pos
  have hone : Nat.card ({⟨red ϖ k T, hTm⟩} : Set (hermSub σ ϖ n k)) = 1 := by simp
  rw [hone, one_mul] at h2
  rw [h3] at h1
  unfold densAt
  rw [hH, hH, div_eq_div_iff (by exact_mod_cast (hM k).ne') (by exact_mod_cast (hM (k + 1)).ne')]
  have key : solCount σ ϖ S T k * Nat.card (hermSub σ ϖ n k) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)))
      = solCount σ ϖ S T (k + 1) * Nat.card (hermSub σ ϖ n (k + 1)) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := by
    rw [← h2]
    rw [solCount_eq σ ϖ S T k]
    calc _ = (Nat.card (sol σ ϖ S T k) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)))) * Nat.card (hermSub σ ϖ n k) := by ring
      _ = _ := by rw [← h1]; ring
  exact_mod_cast key

end GlobalTheory.CompanionTheory.LocalDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.LocalDens Filter Topology Polynomial

namespace GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

variable {R : Type} [CommRing R]

theorem densAt_succ {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) (b : ℕ) :
    densAt σ ϖ S T (0 + b + 1) = densAt σ ϖ S T (0 + b + 1 + 1) := by
  obtain ⟨hTc, hdet⟩ := hT
  obtain ⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by
    obtain ⟨w, hw⟩ := hdet.exists_left_inv
    exact ⟨w, by simpa using hw⟩
  have hσ := hU.fix_ϖ
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hU.card]
    exact pow_ne_zero _ (by have := hU.one_lt; omega)) k
  have h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]
  have h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    have := congrArg (cT σ) h1
    rw [cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t, t + σ t = 1 := by
    obtain ⟨u, hu, -⟩ := hU.basis
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : (u - σ u) * σ w = -1 := by
      have := congrArg σ hw
      simp only [map_mul, map_sub, hU.inv, map_one] at this
      linear_combination -this
    have h4 : σ w = -w := by linear_combination (-σ w) * hw + w * h3
    refine ⟨u * w, ?_⟩
    rw [map_mul, h4]
    linear_combination hw
  refine dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)
  rw [red_eq_iff] at hk
  choose C hC using hk
  have hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hCh : cT σ (Matrix.of C) = Matrix.of C := by
    ext i j
    have e1 := congrFun (congrFun (hh) i) j
    have e2 := congrArg σ (hC j i)
    have e3 := congrFun (congrFun hTc i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3
    simp only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2
    have := (hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by
      simp only [smul_eq_mul]
      rw [← e2, hC i j])
    simpa [cT] using this
  obtain ⟨g, h', hgh, hhg, hg⟩ := GlobalTheory.CompanionTheory.LocalDens.twist hσ ht hCh 0 b h1 h2
  rw [← hhT] at hg
  rw [solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]
  exact solCount_congr hσ S T g h' _ hgh hhg

theorem densAt_eq_densAt_one_of_isUnimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = densAt σ ϖ S T 1 := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 0 + b + 1 := ⟨k - 1, by omega⟩
    rw [← densAt_succ hU S T hS hT b, ih]

theorem densAt_eq_of_isDens {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    {α : ℝ} (hα : IsDens σ ϖ S T α) (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = α := by
  have h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm
  rw [densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]
  exact tendsto_nhds_unique h1 hα

theorem isUnimod_one (σ : R →+* R) (m : ℕ) : IsUnimod σ (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨cT_one σ, by simp⟩

theorem unrPoly : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  intro hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t
  classical
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hR.card]
    exact pow_ne_zero _ (by have := hR.one_lt; omega)) k
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))
  haveI : Finite (hermMod σ ϖ n k) := Subtype.finite
  letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _
  have hq1 : 1 < q := hR.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  let P : ℂ[X] := ∑ B : hermMod σ ϖ n k,
    C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
  let Q : ℂ[X] := ∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))
  have hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k,
      ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro x
    rw [tsum_fintype]
    simp [P, Polynomial.eval_finsetSum]
  have hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro x
    simp [Q, Polynomial.eval_prod]
  have hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m) := by
    intro m hm
    have hS := isUnimod_one σ m
    have hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ) :=
      GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1
        (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k)
        (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)
    have hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
      rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hP, hQ]
    unfold siegAt at hs
    rw [hc] at hs
    rw [hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := by have := i.2; omega
    have e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      have : (ε : ℂ) / q * ((ε : ℂ) * q) = 1 := by
        field_simp
        simpa using hε
      rw [this, one_pow]
    rw [e1, mul_assoc, e2, mul_one]
  have hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j)) := by
    intro a b hab
    have h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖ := congrArg norm hab
    have hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹ := by
      rw [norm_div, hnε]
      simp
    rw [norm_pow, norm_pow, hnorm] at h1
    have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hq2 : (q : ℝ)⁻¹ ≠ 1 := by
      have : (1 : ℝ) < q := by exact_mod_cast hq1
      exact (inv_lt_one_of_one_lt₀ this).ne
    have := pow_right_injective₀ hq0 hq2 h1
    omega
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))
  have := congrArg (Polynomial.eval t) hPQ
  rw [hP, hQ] at this
  exact this

end GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGenStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_formula_polynomial_gen : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | exact GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly <;> assumption)
end
