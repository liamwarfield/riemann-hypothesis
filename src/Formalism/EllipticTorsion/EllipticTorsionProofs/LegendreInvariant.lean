module

public import Formalism.EllipticTorsion.Statement

@[expose] public section

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
namespace Formalism.ELL

theorem legendre_invariant : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

theorem deuring_invariant : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring

end Formalism.ELL
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
section -- merged from Formalism.EllipticTorsion.CompExpWeight
open PowerSeries

universe u

namespace Formalism.ELL

open Formalism.G

def CompExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (σ : Type) [Finite σ] (c : ℝ),
    0 < c → c ≤ 1 →
    ∀ E : PowerSeries K, constantCoeff E = 0 →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) →
    ∀ G : MvPowerSeries σ K, IntegralMv G → ∀ α : σ →₀ ℕ,
      ‖MvPowerSeries.coeff α
          (MvPowerSeries.subst (fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) G)‖
        ≤ c ^ (-(α.degree : ℤ))

end Formalism.ELL
end

open PowerSeries IsUltrametricDist

universe u

namespace Formalism.ELL.MultiplicativeWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)

def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))

variable {c}

theorem W_one (hc : 0 < c) (_hc1 : c ≤ 1) : W c 0 (1 : MvPowerSeries σ K) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

theorem W_mul (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add (f := _)]; push_cast; ring_nf

theorem W_pow (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf

theorem W_E (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity

theorem W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih

theorem comp_exp_coeff_weight_of : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)

end Formalism.ELL.MultiplicativeWeight

namespace Formalism.ELL

theorem comp_exp_coeff_weight : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of

end Formalism.ELL
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
noncomputable section

open PowerSeries

namespace Formalism.ELL.SubstitutionCoefficientCongruence

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_subst_congr_lemma {R : Type*} [CommRing R] {σ : Type*}
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (n : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a ^ n) = 0 := by
  classical
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : x.2 = 0
    · have h0 : MvPowerSeries.coeff 0 a = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
      rw [h2, h0, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
      have hsum : x.1.degree + x.2.degree = e.degree := by rw [← map_add (f := _), hx]
      have h1 : x.1.degree < n := by omega
      rw [ih x.1 h1, zero_mul]

theorem coeff_subst_congr {g h : PowerSeries R} {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  classical
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  · rw [hgh k hk]
  · rw [coeff_subst_congr_lemma ha k e (by omega), smul_zero, smul_zero]

theorem pderiv_subst_coe (p : Polynomial R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv (R := R) i ((p : PowerSeries R).subst a) =
      (derivative (p : PowerSeries R)).subst a * MvPowerSeries.pderiv (R := R) i a := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  suffices H : ∀ P : Polynomial R, MvPowerSeries.pderiv (R := R) i (PowerSeries.substAlgHom hs (P : PowerSeries R)) =
      PowerSeries.substAlgHom hs (derivative (P : PowerSeries R)) * MvPowerSeries.pderiv (R := R) i a by
    simpa only [PowerSeries.coe_substAlgHom] using H p
  intro P
  induction P using Polynomial.induction_on'
  next P Q hP hQ =>
    rw [Polynomial.coe_add, map_add (f := _), map_add (f := _), hP, hQ, map_add (f := _), map_add (f := _), add_mul]
  next n c =>
    have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries R) = a := by
      rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [Polynomial.coe_smul, Polynomial.coe_pow, Polynomial.coe_X, map_smul, map_pow, hX,
      Derivation.map_smul, Derivation.leibniz_pow, PowerSeries.derivative_X, map_nsmul, smul_eq_mul,
      mul_one, map_mul, map_one, nsmul_eq_mul, map_natCast, smul_mul_assoc, mul_assoc]

theorem degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add (f := _)]
  exact Nat.le_add_right _ _

theorem pderiv_subst (g : PowerSeries R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (g.subst a) =
      (derivative g).subst a * MvPowerSeries.pderiv (R := R) i a := by
  classical
  ext e
  have hP : ∀ k ≤ e.degree + 1,
      coeff k ((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R) = coeff k g := by
    intro k hk
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega)]
  have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i (g.subst a)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i
        (((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R).subst a)) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
      coeff_subst_congr ha _ (fun k hk => (hP k (by omega)).symm)]
  rw [h1, pderiv_subst_coe _ ha i, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxd := degree_le_of_mem_antidiagonal hx
  rw [coeff_subst_congr ha x.1 (fun k hk => ?_)]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hP (k + 1) (by omega)]

end Chain

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

theorem mem_unitBall {x : K} : x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem integral_one : Formalism.G.IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_mul {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by
  classical
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ =>
    Subring.mul_mem _ (mem_unitBall.2 (hF _)) (mem_unitBall.2 (hG _))

theorem integral_pow {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (n : ℕ) :
    Formalism.G.IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hF

theorem integral_pderiv {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (i : σ) :
    Formalism.G.IntegralMv (MvPowerSeries.pderiv (R := K) i F) := by
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_pderiv]
  refine Subring.mul_mem _ (mem_unitBall.2 (hF _)) ?_
  exact Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _)

theorem integral_subst {c : PowerSeries K} (hc : ∀ n, ‖coeff n c‖ ≤ 1)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : Formalism.G.IntegralMv f) : Formalism.G.IntegralMv (c.subst f) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf0
  intro e
  rw [← mem_unitBall, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1)) ?_]
  · exact Subring.sum_mem _ fun d _ => by
      rw [smul_eq_mul]
      exact Subring.mul_mem _ (mem_unitBall.2 (hc d)) (mem_unitBall.2 (integral_pow hf d e))
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_subst_congr_lemma hf0 d e (by omega), smul_zero])

end Integral

end Formalism.ELL.SubstitutionCoefficientCongruence

namespace Formalism.ELL

theorem N_partial_derivative : NPderiv := by
  intro K _ _ _ σ G hG i
  obtain ⟨f, hf0, hf, rfl⟩ := hG
  unfold logOnePlus
  rw [SubstitutionCoefficientCongruence.pderiv_subst _ hf0]
  refine SubstitutionCoefficientCongruence.integral_mul ?_ (SubstitutionCoefficientCongruence.integral_pderiv hf i)
  refine SubstitutionCoefficientCongruence.integral_subst ?_ hf0 hf
  intro n
  unfold PowerSeries.log
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n)]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast, Nat.cast_succ, div_mul_cancel₀ _ hn,
    norm_pow, norm_neg, norm_one, one_pow]

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.Change
section -- merged from Formalism.EllipticTorsion.ChangeIntegral
universe u

namespace Formalism.ELL

def ChangeIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K),
    IntegralModel W → IntegralModel (C • W) → W.Δ ≠ 0 → ‖(C • W).Δ‖ = ‖W.Δ‖ →
      ‖(C.u : K)‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1

end Formalism.ELL
end

open Formalism.ELL Formalism.G

namespace Formalism.ELL.RootExponentBounds

universe u

section
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma addle {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

lemma tb {a r : K} (k n : ℕ) (ha : ‖a‖ ≤ 1) (hr : 1 ≤ ‖r‖) (hk : k ≤ n) :
    ‖a * r ^ k‖ ≤ ‖r‖ ^ n := by
  rw [norm_mul, norm_pow]
  calc ‖a‖ * ‖r‖ ^ k ≤ 1 * ‖r‖ ^ n :=
        mul_le_mul ha (pow_le_pow_right₀ hr hk) (by positivity) zero_le_one
    _ = _ := one_mul _

lemma root2 {a b r : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : r ^ 2 + a * r + b = 0) :
    ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : r ^ 2 = -(a * r ^ 1 + b * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 1 + b * r ^ 0‖ ≤ ‖r‖ ^ 1 :=
    addle (tb 1 1 ha hr.le le_rfl) (tb 0 1 hb hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_pow] at hb'
  have : ‖r‖ ^ 1 < ‖r‖ ^ 2 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root3 {c a b d r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (h : c * r ^ 3 + a * r ^ 2 + b * r + d = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e : c * r ^ 3 = -(a * r ^ 2 + b * r ^ 1 + d * r ^ 0) := by linear_combination h
  have hb' : ‖a * r ^ 2 + b * r ^ 1 + d * r ^ 0‖ ≤ ‖r‖ ^ 2 :=
    addle (addle (tb 2 2 ha hr.le le_rfl) (tb 1 2 hb hr.le (by norm_num)))
      (tb 0 2 hd hr.le (by norm_num))
  rw [← norm_neg, ← e, norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 2 < ‖r‖ ^ 3 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma root4 {c a b d e r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (h : c * r ^ 4 + a * r ^ 3 + b * r ^ 2 + d * r + e = 0) : ‖r‖ ≤ 1 := by
  by_contra hr; push Not at hr
  have e' : c * r ^ 4 = -(a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0) := by
    linear_combination h
  have hb' : ‖a * r ^ 3 + b * r ^ 2 + d * r ^ 1 + e * r ^ 0‖ ≤ ‖r‖ ^ 3 :=
    addle (addle (addle (tb 3 3 ha hr.le le_rfl) (tb 2 3 hb hr.le (by norm_num)))
      (tb 1 3 hd hr.le (by norm_num))) (tb 0 3 he hr.le (by norm_num))
  rw [← norm_neg, ← e', norm_mul, norm_pow, hc, one_mul] at hb'
  have : ‖r‖ ^ 3 < ‖r‖ ^ 4 := pow_lt_pow_right₀ hr (by norm_num)
  linarith

lemma memB {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

lemma natB (n : ℕ) : (n : K) ∈ unitBall K := memB.2 (IsUltrametricDist.norm_natCast_le_one K n)

lemma ofNatB (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : K) ∈ unitBall K := by
  have := natB (K := K) n
  exact this

end

lemma bmem {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (h1 : W.a₁ ∈ unitBall K) (h2 : W.a₂ ∈ unitBall K) (h3 : W.a₃ ∈ unitBall K)
    (h4 : W.a₄ ∈ unitBall K) (h6 : W.a₆ ∈ unitBall K) :
    W.b₂ ∈ unitBall K ∧ W.b₄ ∈ unitBall K ∧ W.b₆ ∈ unitBall K ∧ W.b₈ ∈ unitBall K := by
  let S := unitBall K
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.b₂]
    exact S.add_mem (S.pow_mem h1 2) (S.mul_mem (ofNatB 4) h2)
  · rw [WeierstrassCurve.b₄]
    exact S.add_mem (S.mul_mem (ofNatB 2) h4) (S.mul_mem h1 h3)
  · rw [WeierstrassCurve.b₆]
    exact S.add_mem (S.pow_mem h3 2) (S.mul_mem (ofNatB 4) h6)
  · rw [WeierstrassCurve.b₈]
    exact S.sub_mem
      (S.add_mem
        (S.sub_mem
          (S.add_mem (S.mul_mem (S.pow_mem h1 2) h6) (S.mul_mem (S.mul_mem (ofNatB 4) h2) h6))
          (S.mul_mem (S.mul_mem h1 h3) h4))
        (S.mul_mem h2 (S.pow_mem h3 2)))
      (S.pow_mem h4 2)

theorem change_of_variables_integral_of : ChangeIntegral.{u} := by
  intro K _ _ W C hW hW' hΔ0 hΔ
  set W' := C • W with hW'def
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨h1', h2', h3', h4', h6'⟩ := hW'

  have hv : ‖((C.u⁻¹ : Kˣ) : K)‖ = 1 := by
    have e := WeierstrassCurve.variableChange_Δ W C
    rw [← hW'def] at e
    rw [e, norm_mul, norm_pow] at hΔ
    have hn : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.2 hΔ0
    have : ‖((C.u⁻¹ : Kˣ) : K)‖ ^ 12 = 1 := by
      have := mul_right_cancel₀ hn (hΔ.trans (one_mul _).symm); exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have hu : ‖(C.u : K)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at hv; exact hv
  set u : K := (C.u : K)
  set v : K := ((C.u⁻¹ : Kˣ) : K)
  have hvu : v * u = 1 := by simp [u, v]
  have hvu2 : v ^ 2 * u ^ 2 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu6 : v ^ 6 * u ^ 6 = 1 := by rw [← mul_pow, hvu, one_pow]
  have hvu8 : v ^ 8 * u ^ 8 = 1 := by rw [← mul_pow, hvu, one_pow]
  rw [← memB] at h1 h2 h3 h4 h6 h1' h2' h3' h4' h6'
  have hu' : u ∈ unitBall K := by rw [memB, hu]
  obtain ⟨hb2, hb4, hb6, hb8⟩ := bmem W h1 h2 h3 h4 h6
  obtain ⟨-, -, hb6', hb8'⟩ := bmem W' h1' h2' h3' h4' h6'

  let S := unitBall K
  have hr : C.r ∈ unitBall K := by
    rw [memB]
    rcases (IsUltrametricDist.norm_natCast_le_one K 2).lt_or_eq with h2lt | h2eq
    ·
      have h3n : ‖(3 : K)‖ = 1 := by
        have h3le : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
        have : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
          have := IsUltrametricDist.norm_add_le_max (3 : K) (-2)
          rw [norm_neg] at this
          have e : (3 : K) + -2 = 1 := by norm_num
          rwa [e] at this
        rw [norm_one] at this
        push_cast at h2lt
        rcases le_max_iff.1 this with h | h
        · exact le_antisymm h3le h
        · linarith
      have e8 := WeierstrassCurve.variableChange_b₈ W C
      rw [← hW'def] at e8
      have key : (3 : K) * C.r ^ 4 + W.b₂ * C.r ^ 3 + (3 * W.b₄) * C.r ^ 2 + (3 * W.b₆) * C.r
          + (W.b₈ - u ^ 8 * W'.b₈) = 0 := by
        linear_combination (-u ^ 8) * e8 - (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄
          + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) * hvu8
      exact root4 h3n (memB.1 hb2) (memB.1 (S.mul_mem (ofNatB 3) hb4))
        (memB.1 (S.mul_mem (ofNatB 3) hb6))
        (memB.1 (S.sub_mem hb8 (S.mul_mem (S.pow_mem hu' 8) hb8'))) key
    ·
      have h4n : ‖(4 : K)‖ = 1 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this, norm_mul]; push_cast at h2eq; rw [h2eq]; norm_num
      have e6 := WeierstrassCurve.variableChange_b₆ W C
      rw [← hW'def] at e6
      have key : (4 : K) * C.r ^ 3 + W.b₂ * C.r ^ 2 + (2 * W.b₄) * C.r
          + (W.b₆ - u ^ 6 * W'.b₆) = 0 := by
        linear_combination (-u ^ 6) * e6 - (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂
          + 4 * C.r ^ 3) * hvu6
      exact root3 h4n (memB.1 hb2) (memB.1 (S.mul_mem (ofNatB 2) hb4))
        (memB.1 (S.sub_mem hb6 (S.mul_mem (S.pow_mem hu' 6) hb6'))) key

  have hs : C.s ∈ unitBall K := by
    have e2 : W'.a₂ = v ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
    have key : C.s ^ 2 + W.a₁ * C.s + (-W.a₂ - 3 * C.r + u ^ 2 * W'.a₂) = 0 := by
      linear_combination u ^ 2 * e2 + (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * hvu2
    have hconst : -W.a₂ - 3 * C.r + u ^ 2 * W'.a₂ ∈ S :=
      S.add_mem (S.sub_mem (S.neg_mem h2) (S.mul_mem (ofNatB 3) hr))
        (S.mul_mem (S.pow_mem hu' 2) h2')
    exact memB.2 (root2 (memB.1 h1) (memB.1 hconst) key)

  have ht : C.t ∈ unitBall K := by
    have e6 : W'.a₆ = v ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) := rfl
    have key : C.t ^ 2 + (W.a₃ + C.r * W.a₁) * C.t
        + (-(W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3) + u ^ 6 * W'.a₆) = 0 := by
      linear_combination u ^ 6 * e6 + (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁) * hvu6
    have hsum : W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 ∈ S :=
      S.add_mem (S.add_mem (S.add_mem h6 (S.mul_mem hr h4)) (S.mul_mem (S.pow_mem hr 2) h2))
        (S.pow_mem hr 3)
    exact memB.2 (root2 (memB.1 (S.add_mem h3 (S.mul_mem hr h1)))
      (memB.1 (S.add_mem (S.neg_mem hsum) (S.mul_mem (S.pow_mem hu' 6) h6'))) key)
  exact ⟨hu, memB.1 hr, memB.1 hs, memB.1 ht⟩

end Formalism.ELL.RootExponentBounds

namespace Formalism.ELL

universe v

theorem change_of_variables_integral : ChangeIntegral.{v} := Formalism.ELL.RootExponentBounds.change_of_variables_integral_of

end Formalism.ELL
end
