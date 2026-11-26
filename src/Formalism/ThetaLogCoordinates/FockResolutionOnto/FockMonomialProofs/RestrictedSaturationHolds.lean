module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKillsDegreeZero
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedLatticeDividedPower
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.WmMulWmComm

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeDividedIntegral
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section D
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem coeff_pderiv_pow (v : σ) (k : ℕ) (f : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff ((((pderiv v).toLinearMap : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) ^ k) f) m =
      (((m v + k).descFactorial k : ℕ) : ℚ_[p]) * AddMonoidAlgebra.coeff f (m + Finsupp.single v k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show AddMonoidAlgebra.coeff (pderiv v _) m = _
    rw [coeff_pderiv, ih, Nat.descFactorial_succ]
    have h1 : (m + Finsupp.single v 1 : σ →₀ ℕ) v = m v + 1 := by simp
    have h2 : m + Finsupp.single v 1 + Finsupp.single v k = m + Finsupp.single v (k + 1) := by
      rw [add_assoc, ← Finsupp.single_add, add_comm 1 k]
    rw [h1, h2, show m v + 1 + k = m v + (k + 1) by omega, show m v + (k + 1) - k = m v + 1 by omega]
    push_cast
    ring

private theorem norm_natCast_padic_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (n : ℤ)

theorem pderiv_div_int (v : σ) (k : ℕ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p]))⁻¹ •
      ((((pderiv v).toLinearMap : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) ^ k) x) ∈ IntPol p σ := by
  rw [intPol_iff_norm] at hx ⊢
  intro m
  rw [coeff_smul, smul_eq_mul, coeff_pderiv_pow, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul, norm_mul]
  exact mul_le_one₀ (norm_natCast_padic_le_one _) (norm_nonneg _) (hx _)

end D

theorem derivative_divided_integral : DWDivInt := by
  intro p _ K r a k x hx
  exact pderiv_div_int _ k x hx

theorem fact_choose_succ (c : ℤ) (k : ℕ) :
    ((k + 1).factorial : ℤ) * Ring.choose c (k + 1) = c * ((k.factorial : ℤ) * Ring.choose (c - 1) k) := by
  have e1 := Ring.descPochhammer_eq_factorial_smul_choose c (k + 1)
  have e2 := Ring.descPochhammer_eq_factorial_smul_choose (c - 1) k
  rw [← Polynomial.eval_eq_smeval, nsmul_eq_mul] at e1 e2
  rw [← e1, ← e2, descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]

section U
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

noncomputable def DDop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  Wm p K a ∘ₗ eulW p K r + ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b

variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)

theorem DDop_apply (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    DDop p LL Cs a F = X (Fin.last K, a) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F +
        ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by
  simp only [DDop, eulW, Wm, dW, ProjS.eulL, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.mulLeft_apply]

theorem Uop_eq (c : ℤ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL c Cs a F = ((c : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * F) - DDop p LL Cs a F := by
  simp only [Uop, DDop, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Wm, LinearMap.mulLeft_apply, mul_sub, mul_smul_comm]
  abel

private theorem sum_linearMaps_leibniz_of_leibniz {σ ι : Type} (s : Finset ι)
    (L : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, ∀ f g, L i (f * g) = L i f * g + f * L i g) (f g : MvPolynomial σ ℚ_[p]) :
    (∑ i ∈ s, L i) (f * g) = (∑ i ∈ s, L i) f * g + f * (∑ i ∈ s, L i) g := by
  simp only [LinearMap.sum_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => h i hi f g)

private theorem mulLeft_comp_leibniz_of_leibniz {σ : Type} (q : MvPolynomial σ ℚ_[p])
    (L : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (h : ∀ f g, L (f * g) = L f * g + f * L g) (f g : MvPolynomial σ ℚ_[p]) :
    (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) (f * g) =
      (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) f * g + f * (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) g := by
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, h]
  ring

private theorem pderiv_toLinearMap_mul {σ : Type} (v : σ) (f g : MvPolynomial σ ℚ_[p]) :
    (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (f * g) =
    (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) f * g +
    f * (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) g := by
  simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  ring

theorem DDop_mul (f g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    DDop p LL Cs a (f * g) = DDop p LL Cs a f * g + f * DDop p LL Cs a g := by
  have hg : ∀ b, ∀ f g, glAct p LL K a b (f * g) = glAct p LL K a b f * g + f * glAct p LL K a b g := by
    intro b
    unfold glAct
    apply sum_linearMaps_leibniz_of_leibniz
    intro i _
    split_ifs
    · exact mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)
    · intro f g
      rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.neg_apply, mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)]
      ring
    · intro f g
      simp
  have he : ∀ f g, eulW p K r (f * g) = eulW p K r f * g + f * eulW p K r g := by
    unfold eulW
    apply sum_linearMaps_leibniz_of_leibniz
    intro i _
    exact mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)
  have hA : (Wm p K a ∘ₗ eulW p K r) (f * g) =
      (Wm p K a ∘ₗ eulW p K r) f * g + f * (Wm p K a ∘ₗ eulW p K r) g := mulLeft_comp_leibniz_of_leibniz _ _ he f g
  have hs : (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) (f * g) =
      (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) f * g + f * (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) g :=
    sum_linearMaps_leibniz_of_leibniz Cs (fun b => Wm p K b ∘ₗ glAct p LL K a b) (fun b _ => mulLeft_comp_leibniz_of_leibniz _ _ (hg b)) f g
  unfold DDop
  simp only [LinearMap.add_apply]
  rw [hA, hs]
  ring

theorem Uop_shift (c n : ℤ) (q : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hq : DDop p LL Cs a q = ((n : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * q))
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL (c + n) Cs a (q * G) = q * Uop p LL c Cs a G := by
  rw [Uop_eq, Uop_eq, DDop_mul, hq]
  simp only [MvPolynomial.smul_eq_C_mul]
  push_cast
  simp only [map_add (f := _)]
  ring

theorem Uop_shift_pow (c n : ℤ) (q : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hq : DDop p LL Cs a q = ((n : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * q)) (k : ℕ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ((Uop p LL (c + n) Cs a) ^ k) (q * G) = q * ((Uop p LL c Cs a) ^ k) G := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, Uop_shift LL Cs a c n q hq, ih, pow_succ, Module.End.mul_apply]

theorem Uop_comm_pow (c : ℤ) (q : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hq : DDop p LL Cs a q = 0) (k : ℕ) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ((Uop p LL c Cs a) ^ k) (q * G) = q * ((Uop p LL c Cs a) ^ k) G := by
  have hq' : DDop p LL Cs a q = ((0 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * q) := by
    rw [hq]
    simp
  have key := Uop_shift_pow LL Cs a c 0 q hq' k G
  rwa [add_zero] at key

theorem Uop_step_pow (c : ℤ) (x w : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : DDop p LL Cs a x = -w) (hw : DDop p LL Cs a w = 0) (k : ℕ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ((Uop p LL c Cs a) ^ (k + 1)) (x * G) = x * ((Uop p LL c Cs a) ^ (k + 1)) G +
      ((k + 1 : ℕ) : ℚ_[p]) • (w * ((Uop p LL c Cs a) ^ k) G) := by
  have h1 : ∀ G, Uop p LL c Cs a (x * G) = x * Uop p LL c Cs a G + w * G := by
    intro G
    rw [Uop_eq, Uop_eq, DDop_mul, hx]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  induction k generalizing G with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_smul]
    exact h1 G
  | succ k ih =>
    have e0 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) (x * G) =
        ((Uop p LL c Cs a) ^ (k + 1)) (Uop p LL c Cs a (x * G)) := by
      rw [pow_succ, Module.End.mul_apply]
    have e1 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) G =
        ((Uop p LL c Cs a) ^ (k + 1)) (Uop p LL c Cs a G) := by
      rw [pow_succ, Module.End.mul_apply]
    have e2 : ((Uop p LL c Cs a) ^ (k + 1)) G = ((Uop p LL c Cs a) ^ k) (Uop p LL c Cs a G) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [e0, h1, map_add (f := _), ih, Uop_comm_pow LL Cs a c w hw (k + 1), ← e1, ← e2]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add (f := _), map_one, map_natCast]
    ring

theorem eulL_X (i : Fin (K + 1)) (d : Fin r) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (X (i, d) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) =
      if i = Fin.last K then X (i, d) else 0 := by
  unfold ProjS.eulL
  rw [LinearMap.sum_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single d]
    · simp [pderiv_X]
    · intro b _ hb
      simp [pderiv_X, Pi.single_apply, Ne.symm hb]
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    simp [pderiv_X, Pi.single_apply, h]

private theorem glAct_X_eq_ite (b : Fin r) (i : Fin (K + 1)) (d : Fin r) :
    glAct p LL K a b (X (i, d)) =
      if (i : ℕ) < K then
        (if LL.vec i = true then (if b = d then X (i, a) else 0) else (if a = d then -X (i, b) else 0))
      else 0 := by
  unfold glAct
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro j _ hj
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hj]
  · simp

theorem DDop_last (d : Fin r) :
    DDop p LL Cs a (X (Fin.last K, d)) = ((1 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * X (Fin.last K, d)) := by
  rw [DDop_apply, eulL_X, if_pos rfl]
  have hz : ∀ b, glAct p LL K a b (X (Fin.last K, d)) = 0 := by
    intro b
    rw [glAct_X_eq_ite]
    simp
  simp [hz]

theorem DDop_vec (i : Fin (K + 1)) (hi : i ≠ Fin.last K) (hv : LL.vec i = true) (d : Fin r) :
    DDop p LL Cs a (X (i, d)) = if d ∈ Cs then X (Fin.last K, d) * X (i, a) else 0 := by
  rw [DDop_apply, eulL_X, if_neg hi, mul_zero, zero_add]
  simp only [glAct_X_eq_ite, if_pos (Fin.val_lt_last hi), hv, if_true]
  simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem DDop_cov (i : Fin (K + 1)) (hi : i ≠ Fin.last K) (hv : LL.vec i = false) (d : Fin r) :
    DDop p LL Cs a (X (i, d)) = if a = d then -∑ b ∈ Cs, X (Fin.last K, b) * X (i, b) else 0 := by
  rw [DDop_apply, eulL_X, if_neg hi, mul_zero, zero_add]
  simp only [glAct_X_eq_ite, if_pos (Fin.val_lt_last hi), hv, Bool.false_eq_true, if_false]
  split_ifs with h
  · simp [h, Finset.sum_neg_distrib]
  · simp [h]

theorem DDop_pair (ha : a ∈ Cs) (i : Fin (K + 1)) (hi : i ≠ Fin.last K) (hv : LL.vec i = false) :
    DDop p LL Cs a (∑ b ∈ Cs, X (Fin.last K, b) * X (i, b)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [DDop_mul, DDop_last, DDop_cov LL Cs a i hi hv]
  simp [Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq, ha]
  rw [Finset.mul_sum, ← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl (fun b _ => by ring)

theorem Uop_pow_one (c : ℤ) (k : ℕ) :
    ((Uop p LL c Cs a) ^ k) 1 =
      (((k.factorial : ℤ) * Ring.choose c k : ℤ) : ℚ_[p]) • (X (Fin.last K, a) ^ k) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have hU1 : Uop p LL c Cs a 1 = ((c : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * 1) := by
      rw [Uop_eq]
      have h0 : DDop p LL Cs a 1 = 0 := by
        have h2 := DDop_mul (p := p) LL Cs a 1 1
        rw [one_mul, one_mul, mul_one] at h2
        linear_combination -h2
      rw [h0, sub_zero]
    have hq := DDop_last (p := p) LL Cs a a
    have key := Uop_shift_pow LL Cs a (c - 1) 1 (X (Fin.last K, a)) hq k 1
    rw [sub_add_cancel] at key
    rw [pow_succ (Uop p LL c Cs a) k, Module.End.mul_apply, hU1, map_smul, key, ih (c - 1), fact_choose_succ]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_mul]
    ring

private theorem Uop_add_one_apply (c : ℤ) (H : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL (c + 1) Cs a H = Uop p LL c Cs a H + X (Fin.last K, a) * H := by
  rw [Uop_eq, Uop_eq]
  push_cast
  rw [add_smul, one_smul]
  abel

private theorem Uop_pow_succ_apply_eq (c : ℤ) (H : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((Uop p LL c Cs a) ^ (k + 1)) H = ((Uop p LL (c - 1) Cs a) ^ (k + 1)) H +
      ((k + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, a) * ((Uop p LL (c - 1) Cs a) ^ k) H) := by
  have hUV : ∀ Z, Uop p LL c Cs a Z = Uop p LL (c - 1) Cs a Z + X (Fin.last K, a) * Z := by
    intro Z
    have h := Uop_add_one_apply LL Cs a (c - 1) Z
    rwa [sub_add_cancel] at h
  have hsh : ∀ Z, Uop p LL c Cs a (X (Fin.last K, a) * Z) = X (Fin.last K, a) * Uop p LL (c - 1) Cs a Z := by
    intro Z
    have h := Uop_shift LL Cs a (c - 1) 1 _ (DDop_last (p := p) LL Cs a a) Z
    rwa [sub_add_cancel] at h
  induction k with
  | zero => simp [hUV]
  | succ k ih =>
    have e1 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ (k + 1)) H) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1 + 1)) H := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e2 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ k) H) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1)) H := by
      rw [pow_succ' _ k, Module.End.mul_apply]
    rw [pow_succ' (Uop p LL c Cs a) (k + 1), Module.End.mul_apply, ih, map_add (f := _), map_smul, hUV, hsh, e1, e2]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add (f := _), map_one, map_natCast]
    ring

private theorem Uop_pow_succ_mul_apply (c : ℤ) (x w : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : DDop p LL Cs a x = w) (hw : DDop p LL Cs a w = ((2 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * w))
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((Uop p LL c Cs a) ^ (k + 1)) (x * G) = x * ((Uop p LL c Cs a) ^ (k + 1)) G -
      ((k + 1 : ℕ) : ℚ_[p]) • (w * ((Uop p LL (c - 1) Cs a) ^ k) G) := by
  have h1 : ∀ G, Uop p LL c Cs a (x * G) = x * Uop p LL c Cs a G - w * G := by
    intro G
    rw [Uop_eq, Uop_eq, DDop_mul, hx]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  have hw' : ∀ Y, Uop p LL c Cs a (w * Y) = w * Uop p LL (c - 2) Cs a Y := by
    intro Y
    have h := Uop_shift LL Cs a (c - 2) 2 w hw Y
    rwa [sub_add_cancel] at h
  have hV : ∀ Y, Uop p LL (c - 2) Cs a Y = Uop p LL (c - 1) Cs a Y - X (Fin.last K, a) * Y := by
    intro Y
    have h := Uop_add_one_apply LL Cs a (c - 2) Y
    rw [show c - 2 + 1 = c - 1 by ring] at h
    rw [h]
    abel
  induction k with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_smul]
    exact h1 G
  | succ k ih =>
    have e0 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) (x * G) =
        Uop p LL c Cs a (((Uop p LL c Cs a) ^ (k + 1)) (x * G)) := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e1 : Uop p LL c Cs a (((Uop p LL c Cs a) ^ (k + 1)) G) = ((Uop p LL c Cs a) ^ (k + 1 + 1)) G := by
      rw [pow_succ' _ (k + 1), Module.End.mul_apply]
    have e2 : Uop p LL (c - 1) Cs a (((Uop p LL (c - 1) Cs a) ^ k) G) =
        ((Uop p LL (c - 1) Cs a) ^ (k + 1)) G := by
      rw [pow_succ' _ k, Module.End.mul_apply]
    rw [e0, ih, map_sub, map_smul, h1, hw', hV, e1, e2, Uop_pow_succ_apply_eq LL Cs a c G k]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add (f := _), map_one, map_natCast]
    ring

private theorem inv_factorial_succ_mul_succ_eq (k : ℕ) :
    (((k + 1).factorial : ℚ_[p]))⁻¹ * ((k + 1 : ℕ) : ℚ_[p]) = ((k.factorial : ℚ_[p]))⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k), one_mul]

theorem udiv_map (ha : a ∈ Cs) (P : MvPolynomial (Fin (K + 1) × Fin r) ℤ_[p]) :
    ∀ (c : ℤ) (k : ℕ), ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈
      IntPol p (Fin (K + 1) × Fin r) := by
  have hX : ∀ v, (X v : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun v => FrozenVariableLemmas.intPol_X p v
  have hM : ∀ {F G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]}, F ∈ IntPol p (Fin (K + 1) × Fin r) →
      G ∈ IntPol p (Fin (K + 1) × Fin r) → F * G ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun hF hG => FrozenVariableLemmas.intPol_mul p hF hG
  refine MvPolynomial.induction_on (motive := fun P => ∀ (c : ℤ) (k : ℕ),
    ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈
      IntPol p (Fin (K + 1) × Fin r)) P ?_ ?_ ?_
  · intro z c k
    beta_reduce
    rw [map_C]
    have hC : (C (algebraMap ℤ_[p] ℚ_[p] z) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) =
        (algebraMap ℤ_[p] ℚ_[p] z) • (1 : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    have hs : ((k.factorial : ℚ_[p]))⁻¹ * ((((k.factorial : ℤ) * Ring.choose c k : ℤ)) : ℚ_[p]) =
        ((Ring.choose c k : ℤ) : ℚ_[p]) := by
      push_cast
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]
    have hT : ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) 1 =
        ((Ring.choose c k : ℤ) : ℚ_[p]) • X (Fin.last K, a) ^ k := by
      rw [Uop_pow_one, smul_smul, hs]
    rw [hC, map_smul, smul_comm, hT, algebraMap_smul, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ z (zsmul_mem (FrozenVariableLemmas.intPol_pow p (hX _) k) _)
  · intro P Q hP hQ c k
    beta_reduce
    rw [map_add (f := _), map_add (f := _), smul_add]
    exact add_mem (hP c k) (hQ c k)
  · intro P n hP c k
    beta_reduce
    obtain ⟨j, d⟩ := n
    rw [map_mul, map_X, mul_comm]
    have hF0 : map (algebraMap ℤ_[p] ℚ_[p]) P ∈ IntPol p (Fin (K + 1) × Fin r) := by
      simpa using hP c 0
    by_cases hj : j = Fin.last K
    · subst hj
      have key := Uop_shift_pow LL Cs a (c - 1) 1 (X (Fin.last K, d)) (DDop_last LL Cs a d) k
        (map (algebraMap ℤ_[p] ℚ_[p]) P)
      rw [sub_add_cancel] at key
      rw [key, ← mul_smul_comm]
      exact hM (hX _) (hP (c - 1) k)
    · cases hv : LL.vec j with
      | false =>
        by_cases hd : d = a
        · rw [hd]
          have hx : DDop p LL Cs a (X (j, a)) = -(∑ b ∈ Cs, X (Fin.last K, b) * X (j, b)) := by
            rw [DDop_cov LL Cs a j hj hv a, if_pos rfl]
          have hw := DDop_pair (p := p) LL Cs a ha j hj hv
          have hwI : (∑ b ∈ Cs, X (Fin.last K, b) * X (j, b) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈
              IntPol p (Fin (K + 1) × Fin r) :=
            Submodule.sum_mem _ (fun b _ => hM (hX _) (hX _))
          cases k with
          | zero => simpa using hM (hX (j, a)) hF0
          | succ k =>
            rw [Uop_step_pow LL Cs a c _ _ hx hw k, smul_add, smul_smul, inv_factorial_succ_mul_succ_eq]
            simp only [← mul_smul_comm]
            exact add_mem (hM (hX _) (hP c (k + 1))) (hM hwI (hP c k))
        · have hD : DDop p LL Cs a (X (j, d)) = 0 := by
            rw [DDop_cov LL Cs a j hj hv d, if_neg (Ne.symm hd)]
          rw [Uop_comm_pow LL Cs a c _ hD k, ← mul_smul_comm]
          exact hM (hX _) (hP c k)
      | true =>
        by_cases hd : d ∈ Cs
        · have hx : DDop p LL Cs a (X (j, d)) = X (Fin.last K, d) * X (j, a) := by
            rw [DDop_vec LL Cs a j hj hv d, if_pos hd]
          have hw : DDop p LL Cs a (X (Fin.last K, d) * X (j, a)) =
              ((2 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * (X (Fin.last K, d) * X (j, a))) := by
            rw [DDop_mul, DDop_last, DDop_vec LL Cs a j hj hv a, if_pos ha]
            push_cast
            rw [two_smul, one_smul]
            ring
          have hwI : (X (Fin.last K, d) * X (j, a) : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) ∈
              IntPol p (Fin (K + 1) × Fin r) := hM (hX _) (hX _)
          cases k with
          | zero => simpa using hM (hX (j, d)) hF0
          | succ k =>
            rw [Uop_pow_succ_mul_apply LL Cs a c _ _ hx hw, smul_sub, smul_smul, inv_factorial_succ_mul_succ_eq]
            simp only [← mul_smul_comm]
            exact sub_mem (hM (hX _) (hP c (k + 1))) (hM hwI (hP (c - 1) k))
        · have hD : DDop p LL Cs a (X (j, d)) = 0 := by
            rw [DDop_vec LL Cs a j hj hv d, if_neg hd]
          rw [Uop_comm_pow LL Cs a c _ hD k, ← mul_smul_comm]
          exact hM (hX _) (hP c k)

end U

theorem raising_divided_integral : UDivInt := by
  intro p _ K r LL c Cs a k ha x hx
  obtain ⟨P, rfl⟩ := (FrozenVariableLemmas.intPol_iff p x).mp hx
  exact udiv_map LL Cs a ha P c k

end Formalism.InvariantFactorPaths.L4
end

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section Lat
variable {p : ℕ} [Fact p.Prime] {K : ℕ}

theorem sat_of_mem_y {r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (n : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ n) • x := by
  have key : ∀ y ∈ FreeOf p (Fin.last K, ρ), initPart (Fin.last K, ρ) 0 y = y := by
    intro y hy
    unfold initPart
    conv_rhs => rw [y.as_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m (Fin.last K, ρ) = 0 := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hy hm
    rw [if_pos hm0]
  refine ⟨((p : ℚ_[p]) ^ n) • x, Submodule.smul_mem _ _ hY, ?_, key _ (Submodule.smul_mem _ _ hF)⟩
  rw [show ((p : ℚ_[p]) ^ n) = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n) by simp, algebraMap_smul]
  exact Submodule.smul_mem _ _ hi

theorem pol_le_ycond {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  unfold YCond
  apply le_sSup
  refine ⟨?_, fun c d x hx => Formalism.CountingSumsFrames.glAct_pol (p := p) LL j c d x hx⟩
  intro x hx
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hd := hx hm
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  refine le_trans ?_ hc
  calc wt LL j 0 m ≤ ∑ i, (LL.deg i : ℤ) := Finset.sum_le_sum fun i _ => by
        have h1 : (m (i, 0) : ℤ) ≤ LL.deg i := by
          rw [← hd i]
          exact_mod_cast Finset.single_le_sum (fun c _ => Nat.zero_le (m (i, c))) (Finset.mem_univ 0)
        split_ifs <;> omega
    _ = (LL.total : ℤ) := by unfold Letters.total; push_cast; rfl

theorem sat_main {s : ℕ} (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
    (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (hcd : c < LL.total)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hx : x ∈ XSp p LL J M (Fin.last s))
    (hxi : x ∈ IntPol p (Fin (K + 1) × Fin (s + 1))) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin (s + 1)) ∧
      initPart (Fin.last K, Fin.last s) 0 h =
        ((p : ℚ_[p]) ^ (2 * ((s + 1).choose 2 * Nat.log p (4 * LL.total + (s + 1) - 1)))) • x := by
  obtain ⟨G, hE, hcomp⟩ := gl_action_exists p K s LL c hv
  have L := latData LL J M c raising_divided_integral derivative_divided_integral hs hv k0 hk0 hc hmin hcd G hE hcomp
  have hxW : x ∈ Wtot p LL J M (Fin.last s) :=
    mem_wtot LL J M (LL.deg (Fin.last K)) x (by rw [setLast_self]; exact hx)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp
    (wtot_le_iso LL J M c hs hv k0 hk0 hc hmin G hE hcomp hxW)
  generalize hD : (s + 1).choose 2 * Nat.log p (4 * LL.total + (s + 1) - 1) = D
  have hpiece : ∀ la, ((p : ℚ_[p]) ^ D) • (((p : ℚ_[p]) ^ D) • f la) ∈ M2 p LL J M (Fin.last s) := by
    intro la
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := Formalism.InvariantFactorPaths.PW.Top.typeInt p _ (s + 1) G _ _ (4 * LL.total) L la
    have hQx : Q x = f la := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsum, Finsupp.sum, map_sum]
      by_cases hla : la ∈ f.support
      · rw [Finset.sum_eq_single_of_mem la hla (fun mu _ hne => hQ2 mu hne _ (hf mu)), hQ1 _ (hf la)]
      · rw [Finset.sum_eq_zero (fun mu hmu => hQ2 mu (fun h => hla (h ▸ hmu)) _ (hf mu)),
          Finsupp.notMem_support_iff.mp hla]
    have h1 := hQ3 x hxi hxW
    rw [hQx, hD] at h1
    have h2 := Formalism.InvariantFactorPaths.PW.Top.weylInt p _ (s + 1) G _ _ (4 * LL.total) L la _
      (Submodule.smul_mem _ _ (hf la)) h1
    rw [hD] at h2
    refine span_le_restrictedLattice raising_divided_integral derivative_divided_integral LL hv J M c k0 hk0 hc hmin G hE _ ?_ h2
    intro h hh
    exact restrictedLattice_of_deg_zero LL hv J M _ h (hw_deg_zero LL J M c G hE hcomp la h hh.1 hh.2.1) hh.2.2
  have hM2 : ((p : ℚ_[p]) ^ (2 * D)) • x ∈ M2 p LL J M (Fin.last s) := by
    rw [two_mul, pow_add, ← smul_smul, ← hsum, Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
    exact Submodule.sum_mem _ fun la _ => hpiece la
  have hP : ((p : ℚ_[p]) ^ (2 * D)) • x ∈ Pol p (s + 1) (setLast LL (LL.deg (Fin.last K))) := by
    rw [setLast_self]
    exact Submodule.smul_mem _ _ ((mem_xsp LL J M _ x).mp hx).1
  have h3 := restrictedLattice_exists_lift LL J M (Fin.last s) (LL.deg (Fin.last K)) _ hM2 hP
  rwa [setLast_self] at h3

end Lat

theorem restricted_saturation_holds : ResSatLThm := by
  intro p _ K r _ LL q J M ρ hr hρ hv x hx hi
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hρ' : ρ = Fin.last s := Fin.ext (by simp [hρ])
  subst hρ'
  have hs : 1 ≤ s := by omega
  by_cases hex : ∃ k, K + 1 ≤ J k ∧ M k < ((LL.total : ℤ) : WithTop ℤ)
  · obtain ⟨k1, hk1, hk1M⟩ := hex
    obtain ⟨k0, hk0mem, hk0min⟩ := Finset.exists_min_image (univ.filter fun k => K + 1 ≤ J k) M
      ⟨k1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk1⟩⟩
    have hk0 : K + 1 ≤ J k0 := (Finset.mem_filter.1 hk0mem).2
    have hlt : M k0 < ((LL.total : ℤ) : WithTop ℤ) := lt_of_le_of_lt (hk0min k1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk1⟩)) hk1M
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    refine sat_main LL J M c hs hv k0 hk0 hc.symm (fun k hk => hk0min k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)) ?_ x hx hi
    rw [← hc] at hlt
    exact_mod_cast hlt
  · push_neg at hex
    have hx1 := Submodule.mem_inf.1 hx
    have hP := (Submodule.mem_inf.1 hx1.1).1
    have hF := (Submodule.mem_inf.1 hx1.1).2
    have hK := (Submodule.mem_iInf _).1 hx1.2
    have hxY : x ∈ Y p LL J M := by
      refine Submodule.mem_inf.2 ⟨hP, (Submodule.mem_iInf _).2 fun k => ?_⟩
      by_cases hJ : K + 1 ≤ J k
      · have hMk := hex k hJ
        have h1 := pol_le_ycond (p := p) (r := s + 1) LL (J k) (LL.total : ℤ) le_rfl hP
        have hmono : YCond p (r := s + 1) LL (J k) (((LL.total : ℤ) : ℤ) : WithTop ℤ) ≤
            YCond p (r := s + 1) LL (J k) (M k) := by
          unfold YCond
          apply sSup_le_sSup
          rintro S ⟨hS1, hS2⟩
          refine ⟨hS1.trans ?_, hS2⟩
          intro y hy
          rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
          intro m hm
          exact le_trans (hy hm) hMk
        exact hmono h1
      · have := hK k
        rw [if_neg hJ] at this
        exact this
    exact sat_of_mem_y LL J M (Fin.last s) _ x hF hxY hi

end Formalism.InvariantFactorPaths.L4
