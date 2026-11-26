module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import Formalism.DegreeFormula.FlagDegFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

section Formal

variable {R : Type*} [CommRing R]

def Uo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (l * n)

def Vo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then a (n / l) else 0

def dep (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then 0 else a n

def To (k : ℕ) (c : R) (q : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (q * n) + c * (q : R) ^ (k - 1) * Vo q a n

def mul (a b : ℕ → R) : ℕ → R := fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def eis (j : ℕ) (c : R) (a b : ℤ → R) : ℕ → R := fun n =>
  if n = 0 then c else ∑ p ∈ n.divisorsAntidiagonal, a p.1 * (p.1 : R) ^ (j - 1) * b p.2

def Zs (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.2 * v y.1 * F x.1 y.1

def quo {M : ℕ} (f : ZMod M → R) : ℕ → ℕ → R := fun x x' => f ((x : ZMod M) * (x' : ZMod M)⁻¹)

def lam (B : ℕ) (c a : ℕ → R) : R := ∑ n ∈ Finset.range B, c n * a n

end Formal

section Level

variable {K : Type*} [Field K]

def val (B : ℕ) (c : ℕ → K) (l : ℕ) (α : K) (r : ℕ) (a : ℕ → K) : K := (α ^ r)⁻¹ * lam B c ((Uo l)^[r] a)

def Fser (j M : ℕ) (ζ : K) (b : ℤ → K) (c : K) (u w : ZMod M) : ℕ → K := fun s =>
  if s = 0 then c else ∑ p ∈ s.divisorsAntidiagonal,
    ((if (p.1 : ZMod M) = u then ((p.1 : K) / M) ^ (j - 1) * ζ ^ (w.val * p.2) * b p.2 else 0) -
      (if -(p.1 : ZMod M) = u then (-(p.1 : K) / M) ^ (j - 1) * (ζ ^ (w.val * p.2))⁻¹ * b (-(p.2 : ℤ)) else 0))

end Level

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem mul_eq_cmul (f g : ℕ → K) : mul f g = GlobalTheory.KummerEisensteinGalois.cmul f g := by
  funext n
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j) n

end Bridge

def hat {N : ℕ} (φ : ZMod N → ℂ) (d : ℤ) : ℂ := ∑ y ∈ Finset.range N, φ y * cexp (2 * π * Complex.I * (y * d) / N)

def qs (a : ℕ → ℂ) (τ : ℍ) : ℂ := ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)

def PolyB (a : ℕ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A

def Inv (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1) * (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ

def MF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := PolyB a ∧ Inv k L χ (qs a)

def CF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := MF k L χ a ∧ ∃ C : ℝ, ∀ τ : ℍ, ‖qs a τ‖ ^ 2 * τ.im ^ k ≤ C

def ch {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ → ℂ := fun d => χ (d : ZMod N)

structure Prim (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) : Prop where
  cf : CF k N (ch χ) g
  one : g 1 = 1
  zero : ∀ n : ℕ, ¬ n.Coprime N → g n = 0
  eig : ∀ q : ℕ, q.Prime → ¬ q ∣ N → To k (ch χ q) q g = fun n => g q * g n

structure Wt (L : ℕ) (ρ : ℍ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ τ, 0 ≤ ρ τ
  sum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ)) • τ)) 1
  supp : ∃ S : Finset SL(2, ℤ), ∀ τ, ρ τ ≠ 0 → ∃ γ ∈ S, γ • τ ∈ ModularGroup.fd

def pet (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) : ℂ := ∫ τ : ℍ, (ρ τ : ℂ) * (conj (h τ) * f τ * (τ.im : ℂ) ^ k)

structure EigF (k N l : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop where
  T : ∀ a, MF k (N * l) (ch ε) a → ∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam B c (To k (ch ε q) q a) = t q * lam B c a
  U : ∀ a, MF k (N * l) (ch ε) a → lam B c (Uo l a) = α * lam B c a

def trm (j : ℕ) (s : ℝ) (z : ℂ) : ℂ := (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)

def dif (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) : ℤ × ℤ → ℂ := fun x =>
  F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)

def lat (j : ℕ) (s : ℝ) (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) : ℂ :=
  ∑' x : ℤ × ℤ, Φ x * dif L v (dif L v fun y => trm j s ((y.1 : ℂ) * τ + y.2)) x

end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitWeil.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountable_and_t2_local_field : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem nabs_pos (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast distribHaarChar_pos

theorem nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by
  simp [nabs]

theorem nabs_one : nabs k 1 = 1 := by simp [nabs]

theorem om_one {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x; simp [om, nabs_one]

theorem om_mul {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos _).le (nabs_pos _).le,
    _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Complex.ofReal_mul]
  ring

theorem not_hasConductor_one (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by
  intro h
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have := (h (c / r)).1 (fun y _ => rfl)
  have hc : valuation k (c : k) ≠ 0 := by simp
  have hr' : valuation k r ≠ 0 := by simpa using hr
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 hr')] at this
  have h2 : valuation k (c : k) * valuation k r < valuation k (c : k) * 1 :=
    mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hc)
  rw [mul_one] at h2
  exact absurd this (not_le.2 h2)

def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem ratCircle_eq_zero (x : AddCircle (1 : ℚ)) (h : ratCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h' : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
    refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this : (n : ℚ) = q)

theorem exists_hasConductor : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)⁻¹
  have ht1 : 1 < valuation k t := by
    rw [ht]; exact uniformizer_inv_le_iff.1 le_rfl
  let O : AddSubgroup k := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk t : k ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact not_le.2 ht1
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : (k ⧸ O) →+ AddCircle (1 : ℚ) := c
  let f : k →+ AddCircle (1 : ℝ) := ratCircle.comp (c'.comp (QuotientAddGroup.mk' O))
  refine ⟨(AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom f, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    have hx' : 1 < valuation k x := by simpa using hx
    have h1 := h t (ht ▸ uniformizer_inv_le_iff.2 hx')
    have h2 : AddCircle.toCircle (f t) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero h2))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ O) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hy.trans (by simpa using h)
    show AddCircle.toCircle (ratCircle (c' (QuotientAddGroup.mk y))) = 1
    rw [hy']; simp

theorem KOne_le_KO (n : Type*) [Fintype n] [DecidableEq n] : KOne k n ≤ KO k n :=
  Subgroup.map_le_range _ _

theorem isOpen_int : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[k] : Set k) :=
  IsNonarchimedeanLocalField.isCompact_closedBall k 1

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_isUnitVol : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), isCompact_int⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), isCompact_int⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from isOpen_int.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

theorem nabs_vol (ν : Measure k) (h : IsUnitVol ν) (x : kˣ) :
    ν (x • (𝒪[k] : Set k)) = ENNReal.ofReal (nabs k x) := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  rw [← distribHaarChar_mul ν x, h.2]; simp [nabs]

theorem nabs_le_one (x : kˣ) (hx : valuation k (x : k) ≤ 1) : nabs k x ≤ 1 := by
  obtain ⟨ν, h⟩ := exists_isUnitVol (k := k)
  have : ν (x • (𝒪[k] : Set k)) ≤ ν (𝒪[k] : Set k) := by
    apply measure_mono
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (show (x : k) ∈ 𝒪[k] from hx) hy
  rw [nabs_vol ν h, h.2] at this
  exact ENNReal.ofReal_le_one.1 this

theorem measurableEmbedding_val (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine MeasurableEmbedding.iff_comap_eq.2 ⟨Units.val_injective, rfl, ?_⟩
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    rfl
  rw [this]
  exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).measurableSet




omit [MeasurableSpace k] [BorelSpace k] in
theorem om_mem_SB {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  let e : Matrix b a k ≃ₜ Matrix b a k :=
    { toFun := fun x => (h⁻¹ : GL b k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL a k).val
      left_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have h1 : (Φ ∘ e) ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  exact (SB (Matrix b a k)).smul_mem _ h1

end GlobalTheory.SplitWeil.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.RootEx
open GlobalTheory.SplitWeil

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def lev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => p) (fun i => i.val + 1)

def InN (p : ℕ) (g : GL (n ⊕ Fin c) k) : Prop :=
  ∀ r s, lev p s ≤ lev p r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

def N (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  Subgroup.closure {g | InN p g}

def embX (c : ℕ) : GL n k →* GL (n ⊕ Fin c) k :=
  Units.map
    { toFun := fun g : Matrix n n k => (fromBlocks g 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }

def embA (n : Type*) [Fintype n] [DecidableEq n] : GL (Fin c) k →* GL (n ⊕ Fin c) k :=
  Units.map
    { toFun := fun g : Matrix (Fin c) (Fin c) k => (fromBlocks 1 0 0 g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      map_one' := fromBlocks_one
      map_mul' := fun g h => by simp [fromBlocks_multiply] }

def R (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  (embX c).range ⊔ N k n c p

def lowU (C : Matrix (Fin c) n k) : GL (n ⊕ Fin c) k :=
  ⟨fromBlocks 1 0 C 1, fromBlocks 1 0 (-C) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

def upU (B : Matrix n (Fin c) k) : GL (n ⊕ Fin c) k :=
  ⟨fromBlocks 1 B 0 1, fromBlocks 1 (-B) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

def rowE (c p : ℕ) (u : n → k) : GL (n ⊕ Fin c) k :=
  lowU (Matrix.of fun l s => if l.val + 1 = p then u s else 0)

def colE (c p : ℕ) (β : n → k) : GL (n ⊕ Fin c) k :=
  upU (Matrix.of fun r i => if i.val + 1 = p then β r else 0)

def simpleSum (g : GL (n ⊕ Fin c) k) : k :=
  ∑ i : Fin c, ∑ j : Fin c, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0

variable {n' : Type*} [Fintype n'] [DecidableEq n']

def Free (p : ℕ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (Sum.inl _, Sum.inl _) => False
  | (Sum.inr l, Sum.inl _) => l.val + 1 < p
  | (Sum.inl _, Sum.inr i) => p < i.val + 1
  | (Sum.inr l, Sum.inr i) => l.val < i.val

def basePt (c : ℕ) (x₀ : Matrix n n' k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x₀ 0 0 (Matrix.of fun l i => if l.val = i.val then 1 else 0)


open Classical in
def affPt (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  by
    classical
    exact basePt c x₀ + Matrix.of fun r s => if h : Free p (r, s) then e ⟨(r, s), h⟩ else 0

def ch (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : k := ∑ i : Fin c, x (Sum.inr i) (Sum.inr i.succ)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {P A : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]

def IsNEquiv (ψ : AddChar k Circle) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) : Prop :=
  ∀ g ∈ N k n c p, ∀ v, l (σ g v) = (ψ (simpleSum g) : ℂ) * l v

def IsPos (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ p σ (b φ)) ∧ ∀ (g : GL n k) φ v, b (π g φ) (σ (embX c g) v) =
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b φ v

variable [MeasurableSpace k] [BorelSpace k]

def exUp (ν : Measure k) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) (v : A) : ℂ :=
  ∫ u : n → k, l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)

def exDown (ν : Measure k) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) (v : A) : ℂ :=
  ∫ β : n → k, l (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν)


open Classical in
def opE (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x₀ : Matrix n n' k) : ℂ :=
  by
    classical
    exact ∫ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) ∂(Measure.pi fun _ => ν)


open Classical in
def volN (ν : Measure k) (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Measure (N k n c p) :=
  (Measure.pi fun _ : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} => ν).comap
    fun g rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2

def IsQuotInt (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (p : ℕ)
    (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) : Prop :=
  ∃ F ∈ SB (GL (n ⊕ Fin c) k),
    (∀ h, f h = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) ∂μX) ∧ z = ∫ h, F h ∂μG

end GlobalTheory.RootEx
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
noncomputable section

namespace GlobalTheory.K4

open GlobalTheory.KEdge GlobalTheory.NeedB

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def geo (F K Ω : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] :
    Subgroup (Ω ≃ₐ[F] Ω) :=
  (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup

def IsTopW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) (w : K) :
    Prop :=
  w ≠ 0 ∧ ∃ θ : Ω, θ ^ N = algebraMap K Ω w ∧ ∀ g ∈ geo F K Ω, kum (K := F) (N := N) ζ θ g = edge x y η σ g


open Classical in
def topW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K := by
  classical
  exact if h : ∃ w : K, IsTopW ζ x y η σ w then h.choose else 1

namespace TopW

variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

theorem mem_geo (g : Ω ≃ₐ[F] Ω) : g ∈ geo F K Ω ↔ ∀ z : K, g (algebraMap K Ω z) = algebraMap K Ω z := by
  unfold geo
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z
    exact h _ ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

theorem conj_mem_geo [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _

theorem exists_of_fixed [IsGalois K Ω] {z : Ω} (hz : ∀ g ∈ geo F K Ω, g z = z) : ∃ c : K, algebraMap K Ω c = z :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g =>
    hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)

theorem apply_eq_kum [NeZero N] (hζ : IsPrimitiveRoot ζ N) {θ : Ω} {w : K} (hw0 : w ≠ 0)
    (hw : θ ^ N = algebraMap K Ω w) {g : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) :
    g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := by
  have hw1 : algebraMap K Ω w ≠ 0 := by simpa using hw0
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw1 hw.symm
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine kum_choose_spec ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]

theorem pow_val_add [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem pow_val_mul [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, mul_comm b.val, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring

theorem edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring

theorem isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by
  unfold topW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem topW_ne_zero (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dite_eq_right h]
    exact one_ne_zero

theorem unique [NeZero N] [IsGalois K Ω] (hζ : IsPrimitiveRoot ζ N) {σ : Ω ≃ₐ[F] Ω} {w v : K}
    (hw : IsTopW ζ x y η σ w) (hv : IsTopW ζ x y η σ v) : ∃ c : K, c ≠ 0 ∧ w = v * c ^ N := by
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  obtain ⟨hv0, ψ, hψ, hψk⟩ := hv
  have hv1 : algebraMap K Ω v ≠ 0 := by simpa using hv0
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  obtain ⟨c, hc⟩ := exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by
    rw [map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg,
      mul_div_mul_left _ _ (pow_ne_zero _ hz)]
  have key : w = v * c ^ N := by
    apply (algebraMap K Ω).injective
    rw [map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]
  refine ⟨c, ?_, key⟩
  rintro rfl
  rw [zero_pow (NeZero.ne N), mul_zero] at key
  exact hw0 key

end TopW

end GlobalTheory.K4
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)

def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j

end GlobalTheory.FlagPoly
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt (p := p) (w g)) ∧
    ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (w h) (w g)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong (p := p) k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt (p := p) x ∧ ∀ g ∈ H, Cong (p := p) k (c g) (((χ g).val : Ω) ^ j * g x - x)

end GlobalTheory.K5
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.Imports
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)

def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)

end GlobalTheory.Sieg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
noncomputable section

namespace GlobalTheory.AlmostEt

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

structure IsDerOn (B : Subalgebra A S) (D : S → M) : Prop where
  add : ∀ x ∈ B, ∀ y ∈ B, D (x + y) = D x + D y
  mul : ∀ x ∈ B, ∀ y ∈ B, D (x * y) = x • D y + y • D x
  alg : ∀ a : A, D (algebraMap A S a) = 0

structure IsTrData (B C : Subalgebra A S) (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) : Prop where
  le : B ≤ C
  e_mem : e ∈ B
  a_mem : ∀ i, a i ∈ C
  b_mem : ∀ i, b i ∈ C
  tr_mem : ∀ x ∈ C, tr x ∈ B
  tr_add : ∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y
  tr_mul : ∀ β ∈ B, ∀ x ∈ C, tr (β * x) = β * tr x
  left : ∀ x ∈ C, ∑ i, a i * tr (b i * x) = e * x
  right : ∀ x ∈ C, ∑ i, b i * tr (a i * x) = e * x
  sum : ∑ i, a i * b i = e

end General

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simpa using T.q0
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

def zS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.ζ n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [(T.prim n).pow_eq_one]; exact isIntegral_one)⟩

def qS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.qq n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [qq_pow]; exact isIntegral_algebraMap)⟩

def levelAlg (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) {zS T n, qS T n}

def towerAlg (T : Tower p Ω) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) (Set.range (zS T) ∪ Set.range (qS T))

abbrev Frac (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ :=
  Ω ⧸ LinearMap.range (Algebra.linearMap (integralClosure (O0 p) Ω) Ω)

end Tower

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.Inhab

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

end General

section Examples

end Examples

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

end Tower

end GlobalTheory.AlmostEt.Inhab
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.Letter
noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.OverY (X : Tower Ω ε) (W : ValuationSubring X.K) : Prop :=
  (∀ c : Ω, algebraMap Ω X.K c ∈ W) ∧ X.jK ∈ W

def Tower.Un (X : Tower Ω ε) (m : ℕ) : Set X.Kˣ :=
  {f | ∀ W, X.OverY W → ∃ g : X.Kˣ, W.valuation ((f : X.K) / (g : X.K) ^ m) = 1}

abbrev Tower.Kl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := TensorProduct ℤ ℤ_[l] (Additive X.Kˣ)

abbrev idl (l : ℕ) [Fact l.Prime] : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])}

abbrev Tower.Khat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := AdicCompletion (idl l) (X.Kl l)

def Tower.cls (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) :
    X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l))) :=
  Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul f)

def Tower.ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Set (X.Khat l) :=
  {a | ∀ n : ℕ, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f}

def Tower.A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Khat l) := Submodule.span ℤ_[l] (X.ASet l)

def Tower.kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))))

abbrev Tower.Fn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := (Fin 2 → ℤ_[l]) → X.Khat l

def Tower.Pol (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) : Set (X.Fn l) :=
  {b | ∃ c : Fin (w + 1) → X.Khat l, (∀ i, c i ∈ X.A l) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}

def mZl (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ_[l] := m.map (Int.castRingHom ℤ_[l])

def Tower.act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

def Gam (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def Tower.BSet (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Set (X.Fn l) :=
  {b | b ∈ X.Pol l w ∧ ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b}

def Tower.B (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Fn l) := Submodule.span ℤ_[l] (X.BSet N l w)

def IsDiam (N l d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ (en γ 1 1 : ZMod N) = d

def sgD (N l d : ℕ) : SL(2, ℤ) := Classical.epsilon (IsDiam N l d)

def Tower.diam (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (d : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def Tower.heckeT (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) +
    X.act l ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])

def Tower.heckeU (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  ∑ j ∈ Finset.range l, X.act l !![1, (j : ℤ); 0, (l : ℤ)]

def Tower.galB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1])
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

inductive Letter
  | T (q : ℕ)
  | U
  | D (d : ℕ)

def Tower.op (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : Letter → (X.Fn l →ₗ[ℤ_[l]] X.Fn l)
  | Letter.T q => X.heckeT N l q
  | Letter.U => X.heckeU l
  | Letter.D d => X.diam N l d

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)

def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

end GlobalTheory.KummerEisensteinGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Subfield X.K :=
  ⨅ γ ∈ Γ', RingHom.eqLocusField (X.sl (ofSL γ)).toRingEquiv.toRingHom (RingHom.id X.K)

def mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Subfield X.K :=
  lev X Γ' ⊓ ⨅ s ∈ S, RingHom.eqLocusField (X.gal s).toRingHom (RingHom.id X.K)

end GlobalTheory.K4
end
end
