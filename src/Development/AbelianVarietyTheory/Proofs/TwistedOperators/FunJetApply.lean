module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix Formalism.REAL Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

variable {n : ℕ}

def actM {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, Z a b • E a b

def thE (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  -((sgn ε p.1 p.2 : ℝ) : ℂ) • Matrix.single p.2 p.1 (1 : ℂ)

def thM (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : Fin n × Fin n, Z p.1 p.2 • thE ε p

def arr1 {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (j : W →ₗᵢ[ℂ] V) (G : Fin n × Fin n → W) : Arr V n 1 :=
  arrTo V n 1 fun α => j (G (α 0))

def Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  fun z => fderiv ℂ f z (z * Z)

def Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool) (l : List (Fin n × Fin n))
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  l.foldr (fun p g => Rz (thE ε p) g) f

def formOf {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : W →ₗ[ℂ] W) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ).compl₂ T

def funJet {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  formOf (Rw ε l f 1 : W →L[ℂ] W).toLinearMap

theorem funJet_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) (y x : W) :
    funJet ε f l y x = ⟪y, Rw ε l f 1 x⟫_ℂ := rfl

def modJet {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n)) :
    W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).compl₂ (ew E l ∘ₗ j.toLinearMap)) ∘ₛₗ j.toLinearMap

theorem modJet_apply {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n))
    (y x : W) : modJet E j l y x = ⟪j y, ew E l (j x)⟫_ℂ := rfl

section Rel

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]

def JetRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
    B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
      (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0)) ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y x x' : W, j x' = E a b (j x) →
    B (l ++ [(a, b)]) y x = B l y x') ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y y' x : W, j y' = E b a (j y) →
    B ((a, b) :: l) y x = B l y' x) ∧
  ∀ (l : List (Fin n × Fin n)) (G : Fin n × Fin n → W), arr1 j G ∈ Vminus ε E Λ u →
    ∀ y : W, ∑ p, B (l ++ [p]) y (G p) = 0

theorem JetRel.sub {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V}
    {j : W →ₗᵢ[ℂ] V} {B B' : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (h : JetRel ε E Λ u j B)
    (h' : JetRel ε E Λ u j B') : JetRel ε E Λ u j (fun l => B l - B' l) := by
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b hab y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have h1 := h.1 l₁ l₂ a b c d
    have h2 := h'.1 l₁ l₂ a b c d
    rw [sub_sub_sub_comm, h1, h2]
    split_ifs <;> (ext y x; simp only [LinearMap.sub_apply, LinearMap.zero_apply]; ring)
  · simp only [LinearMap.sub_apply, h.2.1 l a b hab y x x' hx, h'.2.1 l a b hab y x x' hx]
  · simp only [LinearMap.sub_apply, h.2.2.1 l a b hab y y' x hy, h'.2.2.1 l a b hab y y' x hy]
  · simp only [LinearMap.sub_apply, Finset.sum_sub_distrib, h.2.2.2 l G hG y, h'.2.2.2 l G hG y, sub_self]

def FunEquiv (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    (∀ x x' : W, j x' = E a b (j x) → fderiv ℂ f z (z * thE ε (a, b)) x = f z x') ∧
    ∀ y y' x : W, j y' = E b a (j y) → ⟪y, fderiv ℂ f z (thE ε (a, b) * z) x⟫_ℂ = ⟪y', f z x⟫_ℂ

def FunSchmid (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    ∑ p, fderiv ℂ f z (z * thE ε p) (G p) = 0

def TauTie (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ Y, inK ε Y → ∀ v v' : W, j v' = actM E (Y.map star) (j v) →
    HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v) v' 0

def LowData (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) :
    Prop :=
  GlRel E ∧ IsUnitary ε E ∧ KHighest ε E Λ u ∧ FiniteDimensional ℂ (kSpan ε E u) ∧
    LinearMap.range j.toLinearMap = kSpan ε E u

def DerTie {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) : Prop :=
  ∀ X, inG ε X → ∀ v : V,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (ι v)) (ι (actM E X v)) 0

end Rel

end GlobalTheory.SphJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionSmooth
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SepReal.ProjSm

variable {m : ℕ}

theorem mem_iff (ε : Fin m → Bool) (g : Mat m) : g ∈ UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem mul_mem' {ε : Fin m → Bool} {g h : Mat m} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  rw [mem_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem one_mem' (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := by
  rw [mem_iff]; simp

theorem exp_mem {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ lieOf (Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have JJ := Formalism.REAL.Jm_mul_self ε
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  set Y : Mat m := t • X with hY
  have hYh : Yᴴ = Formalism.REAL.Jm ε * (-Y) * Formalism.REAL.Jm ε := by
    have : Xᴴ = -(Formalism.REAL.Jm ε * X) * Formalism.REAL.Jm ε := by
      have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
      calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, JJ, Matrix.mul_one]
        _ = _ := by rw [h1]
    rw [hY, Matrix.conjTranspose_smul, this]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg]
  have hc : NormedSpace.exp Yᴴ = Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε := by
    have hJi : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv JJ
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) (-Y) ⟨⟨_, _, JJ, JJ⟩, rfl⟩
    rw [hJi] at this
    rw [hYh, this]
  rw [mem_iff, ← Matrix.exp_conjTranspose, hc]
  have he : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp Y
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-Y) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [JJ, Matrix.mul_one, he, Matrix.mul_one]

theorem list_mem {m : ℕ} {ε : Fin m → Bool} : ∀ l : List (Mat m), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => by simpa using one_mem' ε
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))

theorem embH_list {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) : ∀ l : List (Mat n), embH e l.prod = (l.map (embH e)).prod
  | [] => by simp [embH_one]
  | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]

variable {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Mat (n + 1) → (H →L[ℂ] H)} {σ : Mat n → (H' →L[ℂ] H')} {j : H' →L[ℂ] H} {P : H →L[ℂ] H'}

end GlobalTheory.SepReal.ProjSm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolume
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.powerIntegrability

theorem one_le_hsn {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hsn (umat g) := by
  set a : Fin m := ⟨0, hm⟩
  have h : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h2 := congrFun (congrFun h a) a
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2
  have hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2 := by
    have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
    rw [← e1, ← h2]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [sq]
  have hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2 :=
    Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  unfold hsn
  exact Real.one_le_sqrt.mpr (hn.trans hc)

theorem continuous_hsn_umat {m : ℕ} (ε : Fin m → Bool) : Continuous fun g : UJ ε => hsn (umat g) := by
  unfold hsn
  have hu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  refine Real.continuous_sqrt.comp ?_
  fun_prop

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal.powerIntegrability

theorem const_le (m : ℕ) (hm : 1 ≤ m) : 2 * (33 : ℝ) ^ (2 * m ^ 2) ≤ Real.exp (10 * (m : ℝ) ^ 2) := by
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e10 : (2178 : ℝ) ≤ Real.exp 10 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (2178 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  have e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2) := by rw [pow_mul]; norm_num
  rw [e1, e2]
  calc 2 * (1089 : ℝ) ^ (m ^ 2) ≤ 2 ^ (m ^ 2) * 1089 ^ (m ^ 2) := by
        gcongr; exact le_self_pow₀ (by norm_num) (by omega)
    _ = 2178 ^ (m ^ 2) := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 10 ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) e10 _

theorem term_le (m : ℕ) (A : ℝ) (hA : 4 * (m : ℝ) ^ 2 + 1 ≤ A) (j : ℕ) :
    ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2) ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j := by
    have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring
    rw [this]; linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (-A) := by positivity
  have hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2 := by
    have e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [e, ← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-A + ((4 * m ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  calc ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)
      ≤ ((2 : ℝ) ^ (-A)) ^ j * (33 * 4 ^ j) ^ (2 * m ^ 2) := by
        gcongr
    _ = 33 ^ (2 * m ^ 2) * ((2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2)) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]; ring
    _ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
        gcongr

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.powerIntegrability in
theorem powInt_of_volBall : VolBall → PowInt := by
  intro hV m ε A hm hA
  obtain ⟨-, hfin, -⟩ := hV m ε (1 / 4) 1 (by norm_num) one_pos
  set μN := muG ε (nbh ε (1 / 4)) with hμN
  set r : ℝ := (2 : ℝ) ^ (-A) with hr
  have hcont := continuous_hsn_umat ε
  have hpos : ∀ g : UJ ε, 0 < hsn (umat g) := fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)
  have hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A) :=
    hcont.rpow_const fun g => Or.inl (hpos g).ne'
  have hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A) := fun g => (Real.rpow_pos_of_pos (hpos g) _).le
  let S : ℕ → Set (UJ ε) := fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hcont.measurable measurable_const
  have hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g := by
    intro g
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show g ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    have key : r ^ j = ((2 : ℝ) ^ j) ^ (-A) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [key]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])
  have hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
    calc ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε
        ≤ ∫⁻ g, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε := lintegral_mono hpt
      _ = ∑' j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε :=
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (r ^ j) * muG ε (S j) := by
          congr 1; funext j; exact lintegral_indicator_const (hS j) _
      _ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hb := (hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2
          calc ENNReal.ofReal (r ^ j) * muG ε (S j)
              ≤ ENNReal.ofReal (r ^ j) * (ENNReal.ofReal ((1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN) :=
                by gcongr
            _ = ENNReal.ofReal (r ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')
            _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
                have h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_mul (by positivity), h2]
      _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]
  have hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A) := Filter.Eventually.of_forall hf_nn
  refine ⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]
  calc (∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε).toReal
      ≤ (ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hL
    _ = 2 * 33 ^ (2 * m ^ 2) * μN.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal :=
        mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg

end GlobalTheory.SepReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolumeStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume : VolBall → PowInt := by
  first | exact @GlobalTheory.SepReal.powInt_of_volBall | exact GlobalTheory.SepReal.powInt_of_volBall | (intros; apply GlobalTheory.SepReal.powInt_of_volBall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolume
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

open scoped ContDiff

namespace GlobalTheory.SepReal

theorem expS_mem_UJset {m : ℕ} {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.MainNotions.S.UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, neg_mul]
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  have hc : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hJu, hJinv]
  have hcomm : Commute (-(t • X)) (t • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-(t • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp (t • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem orbit_sub_le {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π) {X : Mat m}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) {v : H} (hv : SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v) :
    ‖π (NormedSpace.exp X) v - v‖ ≤ ‖dR π X v‖ := by
  set f : ℝ → H := fun s => π (NormedSpace.exp (s • X)) v with hf
  have hcd : ContDiff ℝ ∞ f := by
    have h1 := hv 1 (fun _ => X) (fun _ => hX)
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    have h3 := h1.comp h2
    convert h3 using 1
    funext s
    simp [f, List.ofFn_succ]
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt f (π (NormedSpace.exp (t • X)) (dR π X v)) t := by
    intro t
    set Lt := π (NormedSpace.exp (t • X)) with hLt
    have h0 : HasDerivAt f (dR π X v) 0 := (hdiff 0).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (Lt.restrictScalars ℝ) (f u)) ((Lt.restrictScalars ℝ) (dR π X v)) (t - t) := by
      rw [sub_self]; exact (Lt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := h1.comp_sub_const t t
    have hfun : f = fun s : ℝ => (Lt.restrictScalars ℝ) (f (s - t)) := by
      funext s
      have he : NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
        congr 2; ring
      simp only [f, he, hπ.1.2 _ (expS_mem_UJset hX t) _ (expS_mem_UJset hX (s - t))]
      rfl
    rw [hfun]
    exact h2
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => π (NormedSpace.exp (t • X)) (dR π X v)) (C := ‖dR π X v‖)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hπ.2.1 _ (expS_mem_UJset hX t) _))
  simpa [f, hπ.1.1] using hb

end GlobalTheory.SepReal

namespace GlobalTheory.SepReal

theorem exists_lowUnit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)} (hds : IsDS ε lam π) : ∃ v, IsLowUnit ε lam π v := by
  obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    simp [norm_smul, this]
  · exact (le_sSup hS : S ≤ lowKSub ε lam π) (S.smul_mem _ hvS)

theorem one_le_eightMB {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 3 ≤ m) (hlam : IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ 8 * (m : ℝ) * B := by
  have i0 : 0 < m := by omega
  have i1 : 1 < m := by omega
  have hlt : lam ⟨1, i1⟩ < lam ⟨0, i0⟩ := hlam.1 (show (⟨0, i0⟩ : Fin m) < ⟨1, i1⟩ from by simp [Fin.lt_def])
  obtain ⟨k0, hk0⟩ := hlam.2 ⟨0, i0⟩
  obtain ⟨k1, hk1⟩ := hlam.2 ⟨1, i1⟩
  have hk : (k1 : ℝ) < k0 := by linarith
  have hk' : k1 < k0 := by exact_mod_cast hk
  have hk'' : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hk'
  have h0 := hB ⟨0, i0⟩
  have h1 := hB ⟨1, i1⟩
  rw [abs_le] at h0 h1
  have hB2 : 1 / 2 ≤ B := by linarith
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem degUpper_of (hlog : LogNear) (hlie : LieBound) (_hvol : VolBall) : DegUpper := by
  unfold DegUpper ForDS
  intro m ε lam B hm hlam hgap hB H _ _ π hds d hd
  obtain ⟨v₀, hv₀⟩ := exists_lowUnit hds
  obtain ⟨hsm, hbd⟩ := hlie m ε lam B hm hlam hgap hB H π hds v₀ hv₀
  have hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π := hds.2.2.1
  have hB1 := one_le_eightMB hm hlam hB
  set c : ℝ := (8 * (m : ℝ) * B) ^ 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by linarith
  set δ : ℝ := 1 / (4 * c) with hδ
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hv1 : ‖v₀‖ = 1 := hv₀.1

  have key : ∀ g ∈ nbh ε δ, (1 / 4 : ℝ) ≤ ‖coefOn π v₀ v₀ g‖ ^ 2 := by
    intro g hg
    have hgU : umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
    obtain ⟨X, hX, hXn, hXe⟩ := hlog m ε δ hδ4 (umat g) hgU hg
    have h1 := hbd [X] (by simpa using hX) (by simp)
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1
    have h2 : ‖dR π X v₀‖ ≤ 1 / 2 := by
      calc ‖dR π X v₀‖ ≤ c * hsn X := h1
        _ ≤ c * (2 * δ) := by gcongr
        _ = 1 / 2 := by rw [hδ]; field_simp; ring
    have h3 : ‖π (umat g) v₀ - v₀‖ ≤ 1 / 2 := by
      rw [← hXe]; exact (orbit_sub_le hπ hX hsm).trans h2
    have h4 : coefOn π v₀ v₀ g = 1 + ⟪v₀, π (umat g) v₀ - v₀⟫_ℂ := by
      simp only [coefOn, inner_sub_right, inner_self_eq_norm_sq_to_K, hv1]
      push_cast; ring
    have h5 : ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ 1 / 2 := by
      calc ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ ‖v₀‖ * ‖π (umat g) v₀ - v₀‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 := by rw [hv1, one_mul]; exact h3
    have h6 : 1 / 2 ≤ ‖coefOn π v₀ v₀ g‖ := by
      rw [h4]
      have := norm_sub_norm_le (1 : ℂ) (-⟪v₀, π (umat g) v₀ - v₀⟫_ℂ)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    nlinarith

  obtain ⟨hdpos, hI⟩ := hd
  obtain ⟨hint, hval⟩ := hI v₀ v₀ v₀ v₀
  have hpt : ∀ g : UJ ε, coefOn π v₀ v₀ g * star (coefOn π v₀ v₀ g) = ((‖coefOn π v₀ v₀ g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint' : Integrable (fun g => ‖coefOn π v₀ v₀ g‖ ^ 2) (muG ε) := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  have hval' : ∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε = 1 / d := by
    have h := hval
    simp only [hpt, inner_self_eq_norm_sq_to_K, hv1] at h
    rw [integral_complex_ofReal] at h
    have h' : ((∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hlint : ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ) ≤ ENNReal.ofReal (1 / d) := by
    calc ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ)
        ≤ ENNReal.ofReal (1 / 4) * muG ε {g | ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2)} := by
          gcongr
          intro g hg
          exact ENNReal.ofReal_le_ofReal (key g hg)
      _ ≤ ∫⁻ g, ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2) ∂muG ε :=
          mul_meas_ge_le_lintegral₀ hint'.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
      _ = ENNReal.ofReal (1 / d) := by
          rw [← hval', ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun g => by positivity)]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)] at ht
  have : (muG ε (nbh ε δ)).toReal ≤ 4 * (1 / d) := by linarith
  rwa [mul_one_div] at this

end GlobalTheory.SepReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolumeStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume : LogNear → LieBound → VolBall → DegUpper := by
  first | exact @GlobalTheory.SepReal.degUpper_of | exact GlobalTheory.SepReal.degUpper_of | (intros; apply GlobalTheory.SepReal.degUpper_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardLeOfSeparated
open MeasureTheory

namespace GlobalTheory.SeparatedSetCardBound

theorem card_le_of_separated {G E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : G → E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (T : Finset G)
    (hT : ∀ h ∈ T, ‖φ h‖ ≤ R) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖) :
    (T.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  haveI := hμ
  set d := Module.finrank ℝ E
  have hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_iff]
    rintro z ⟨hza, hzb⟩
    have hs := hsep a ha b hb hab
    rw [Metric.mem_ball, dist_eq_norm] at hza hzb
    have h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖ := by
      calc ‖φ a - φ b‖ = ‖(z - φ b) - (z - φ a)‖ := by congr 1; abel
        _ ≤ ‖z - φ b‖ + ‖z - φ a‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖ := by
      calc ‖z‖ = ‖(z - φ h) + φ h‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - φ h‖ + ‖φ h‖ := norm_add_le _ _
    linarith [hT h hh]
  have hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [div_pow, le_div_iff₀ hrd]
  exact hle

theorem main : ∀ {G E : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.SFinite μ] [inst_8 : NormedAddCommGroup E] [inst_9 : NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E), Continuous φ → ∀ (W : Set G) (R r : ℝ), (0 : ℝ) ≤ R → (0 : ℝ) < r → (∀ (g h : G), ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ (2 : ℝ) * r → h⁻¹ * g ∈ W) → (μ : Set G → ENNReal) {g : G | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * (μ : Set G → ENNReal) W := by
  intro G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW
  classical
  let P : Finset G → Prop := fun T =>
    (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖
  let A : Set ℕ := {n | ∃ T, P T ∧ T.card = n}
  have hA0 : A.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hAb : BddAbove A := by
    refine ⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨T, hT, rfl⟩
    have h1 := card_le_of_separated φ R r hR hr T hT.1 hT.2
    have h2 := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨T, hT, hTc⟩ := Nat.sSup_mem hA0 hAb
  have hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W := by
    intro g hg
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne
    have hg' : ‖φ g‖ ≤ R := hg
    have hgT : g ∉ T := fun hgT => hne g hgT (hW g g hg' (by simp; positivity))
    have far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖ := by
      intro h hh
      by_contra hle
      push_neg at hle
      exact hne h hh (hW g h (hT.1 h hh) hle)
    have hP : P (insert g T) := by
      refine ⟨?_, ?_⟩
      · intro h hh
        rw [Finset.mem_insert] at hh
        rcases hh with rfl | hh
        · exact hg'
        · exact hT.1 h hh
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact far b hb
        · rw [norm_sub_rev]; exact far a ha
        · exact hT.2 a ha b hb hab
    have hmem : (insert g T).card ∈ A := ⟨_, hP, rfl⟩
    have hle := le_csSup hAb hmem
    rw [Finset.card_insert_of_notMem hgT, ← hTc] at hle
    omega
  calc μ {g : G | ‖φ g‖ ≤ R} ≤ μ (⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W) := measure_mono hcover
    _ ≤ ∑ h ∈ T, μ ((fun x => h⁻¹ * x) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = T.card * μ W := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)

end GlobalTheory.SeparatedSetCardBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBound
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.VolBallPf

theorem double_count {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E) (hφ : Continuous φ) (W : Set G) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 < r) (hW : ∀ g h, ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ 2 * r → h⁻¹ * g ∈ W) :
    μ {g | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
  first
  | exact @_root_.GlobalTheory.SeparatedSetCardBound.main
  | exact _root_.GlobalTheory.SeparatedSetCardBound.main
  | (apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)

def toEuc {m : ℕ} (A : Mat m) : EuclideanSpace ℂ (Fin m × Fin m) := WithLp.toLp 2 fun p => A p.1 p.2

theorem norm_vec {m : ℕ} (A : Mat m) : ‖toEuc A‖ = hsn A := by
  simp [toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem toEuc_sub {m : ℕ} (A B : Mat m) : toEuc A - toEuc B = toEuc (A - B) := by
  ext p; simp [toEuc]

theorem continuous_vec {m : ℕ} : Continuous (toEuc : Mat m → _) := by
  unfold toEuc
  fun_prop

theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hsn (umat g⁻¹) = hsn (umat g) := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := determinant_character_mul_inv g
  have h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
    calc umat g⁻¹ = Jm ε * Jm ε * umat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
      _ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg]
      _ = Jm ε * (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [h2]
  unfold hsn
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem hsn_mul {m : ℕ} (A B : Mat m) : hsn (A * B) ≤ hsn A * hsn B := sqrt_frobenius_mul_le A B

theorem hsn_add {m : ℕ} (A B : Mat m) : hsn (A + B) ≤ hsn A + hsn B := sqrt_frobenius_add_le A B

end GlobalTheory.SepReal.VolBallPf

namespace GlobalTheory.SepReal

open VolBallPf

theorem volBall : VolBall := by
  intro m ε δ R hδ hR
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix m ε).1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ} :=
      isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const
    refine lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)
    · simpa [norm_vec, hsn, umat] using hδ
    · have : ‖toEuc (umat g - 1)‖ < δ := hg
      rw [norm_vec] at this
      exact this.le
  · refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))
    have h1 : hsn (umat g - 1) ≤ δ := hg
    have h2 := hsn_add (umat g - 1) 1
    rw [sub_add_cancel] at h2
    have h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m) := by linarith
    exact (Real.sqrt_le_iff.1 h3).2
  · have key := double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le
      (by positivity) (fun g h hh hgh => by
        rw [norm_vec] at hh
        rw [toEuc_sub, norm_vec] at hgh
        show hsn (umat (h⁻¹ * g) - 1) ≤ δ
        have h1 : umat h⁻¹ * umat h = 1 := by
          have := determinant_character_mul_inv h⁻¹
          rw [inv_inv] at this
          exact this
        have h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h) := by
          rw [Matrix.mul_sub, h1]; rfl
        rw [h2]
        refine (hsn_mul _ _).trans ?_
        rw [hsn_inv]
        calc hsn (umat h) * hsn (umat g - umat h) ≤ R * (2 * (δ / (2 * R))) :=
              mul_le_mul hh hgh (Real.sqrt_nonneg _) hR.le
          _ = δ := by field_simp)
    have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2 := by
      rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [sq]
    have hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ := by field_simp; ring
    simp only [norm_vec, hfr, hq] at key
    exact key

end GlobalTheory.SepReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBoundStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_of_ball_bound : VolBall := by
  first | exact @GlobalTheory.SepReal.volBall | exact GlobalTheory.SepReal.volBall | (intros; apply GlobalTheory.SepReal.volBall <;> assumption)
end
end
