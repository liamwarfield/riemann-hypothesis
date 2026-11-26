module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable (l : ℕ) [Fact l.Prime]

theorem hensel_mem (P : Polynomial ℂ_[l]) (hK : ∀ i, P.coeff i ∈ MaximalUnramifiedExtension l) (hP : ∀ i, ‖P.coeff i‖ ≤ 1)
    (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (h0 : P.eval x = 0) (h1 : ‖P.derivative.eval x‖ = 1) : x ∈ MaximalUnramifiedExtension l := by
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial (MaximalUnramifiedExtension l), Q.map (MaximalUnramifiedExtension l).subtype = P := by
    have : P ∈ Polynomial.lifts (MaximalUnramifiedExtension l).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨P.coeff i, hK i⟩, rfl⟩
    exact (Polynomial.mem_lifts P).mp this
  obtain ⟨ξ, hξ, hd⟩ := res_full l x hx
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le l hξ
  let a : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  have hev : ∀ b : MaximalUnramifiedExtension l, ((Q.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.eval (b : ℂ_[l]) := fun b => by
    rw [← hQ]
    exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hdev : ∀ b : MaximalUnramifiedExtension l, ((Q.derivative.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.derivative.eval (b : ℂ_[l]) :=
    fun b => by
      rw [← hQ, Polynomial.derivative_map]
      exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    have := hP i
    rw [← hQ, Polynomial.coeff_map] at this
    exact this
  have e0 : ‖P.eval ξ‖ < 1 := by
    have := newton_lipschitz P hP ξ x hξ1 hx
    rw [h0, sub_zero, norm_sub_rev] at this
    exact lt_of_le_of_lt this hd
  have e1 : ‖P.derivative.eval ξ‖ = 1 := by
    have h2 := newton_lipschitz P.derivative (newton_derivative_coeff P hP) ξ x hξ1 hx
    rw [norm_sub_rev ξ x] at h2
    have h3 : ‖P.derivative.eval ξ - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt h2 hd
    have h4 : P.derivative.eval ξ = (P.derivative.eval ξ - P.derivative.eval x) + P.derivative.eval x := by
      ring
    rw [h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne, max_eq_right h3.le, h1]
  obtain ⟨x', hx'0, hx'd⟩ := newton_root Q hQc a hξ1
    (show ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1 by rw [hev]; exact e0)
    (show ‖((Q.derivative.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 by rw [hdev]; exact e1)
  have hx'd' : ‖(x' : ℂ_[l]) - ξ‖ < 1 := by
    have h5 : ‖((x' - a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ := hx'd
    rw [hev] at h5
    exact lt_of_le_of_lt h5 e0
  have hP0 : P.eval (x' : ℂ_[l]) = 0 := by
    rw [← hev, hx'0]; rfl
  set y : ℂ_[l] := (x' : ℂ_[l]) - x with hy
  have hy1 : ‖y‖ < 1 := by
    have : y = ((x' : ℂ_[l]) - ξ) + (ξ - x) := by rw [hy]; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx'd' ?_)
    rwa [norm_sub_rev]
  obtain ⟨k, hk, hexp⟩ := newton_expansion P hP x y hx hy1.le
  have hxy : x + y = (x' : ℂ_[l]) := by rw [hy]; ring
  rw [hxy, hP0, h0, zero_add] at hexp
  have hfac : y * (P.derivative.eval x + k * y) = 0 := by
    rw [hexp]; ring
  have hne : P.derivative.eval x + k * y ≠ 0 := by
    intro h
    have h6 : P.derivative.eval x = -(k * y) := eq_neg_of_add_eq_zero_left h
    rw [h6, norm_neg, norm_mul] at h1
    have : ‖k‖ * ‖y‖ < 1 := by
      calc ‖k‖ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr
        _ < 1 := by rwa [one_mul]
    exact absurd h1 this.ne
  have hy0 : y = 0 := (mul_eq_zero.mp hfac).resolve_right hne
  have : x = (x' : ℂ_[l]) := by rw [← hxy, hy0, add_zero]
  rw [this]
  exact x'.2

theorem sqrt_mem (hl : l ≠ 2) (c y : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (hy : ‖y‖ = 1) (h : y ^ 2 = c) : y ∈ MaximalUnramifiedExtension l := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hle : ‖(2 : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
      exact_mod_cast this
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hl)
    have hg : Int.gcd 2 (l : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast 2 l
      simpa [Nat.Coprime.gcd_eq_one hcop] using this
    have hz' : (1 : ℤ) = 2 * Int.gcdA 2 l + l * Int.gcdB 2 l := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℂ_[l]) hz'
    push_cast at h1
    have hm := IsUltrametricDist.norm_add_le_max (2 * ((Int.gcdA 2 l : ℤ) : ℂ_[l]))
      ((l : ℂ_[l]) * ((Int.gcdB 2 l : ℤ) : ℂ_[l]))
    rw [← h1, norm_one, norm_mul, norm_mul] at hm
    have ha := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdA 2 l)
    have hb := IsUltrametricDist.norm_intCast_le_one ℂ_[l] (Int.gcdB 2 l)
    have hl1 := norm_prime_lt_one_complexPadic (l := l)
    rcases le_max_iff.1 hm with h | h
    · nlinarith [norm_nonneg ((Int.gcdA 2 l : ℤ) : ℂ_[l]), norm_nonneg (2 : ℂ_[l])]
    · nlinarith [norm_nonneg ((Int.gcdB 2 l : ℤ) : ℂ_[l]), norm_nonneg (l : ℂ_[l])]
  have hc1 : ‖c‖ = 1 := by rw [← h, norm_pow, hy, one_pow]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.C c) (fun i => ?_) (fun i => ?_) y hy.le ?_ ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).one_mem (MaximalUnramifiedExtension l).zero_mem
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem hc
    · exact (MaximalUnramifiedExtension l).sub_mem (MaximalUnramifiedExtension l).zero_mem (MaximalUnramifiedExtension l).zero_mem
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs <;> first | (exfalso; omega) | simp [hc1]
  · simp [h]
  · simp [Polynomial.derivative_X_pow, norm_mul, hy]
    rw [one_add_one_eq_two]
    exact h2

theorem exists_sqrt (hl : l ≠ 2) (c : ℂ_[l]) (hc : c ∈ MaximalUnramifiedExtension l) (h1 : ‖c‖ = 1) :
    ∃ b ∈ MaximalUnramifiedExtension l, b ^ 2 = c ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hb1 : ‖b‖ = 1 := by
    have : ‖b‖ ^ 2 = 1 := by rw [← norm_pow, hb, h1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) two_ne_zero).1 this
  exact ⟨b, sqrt_mem l hl c b hc hb1 hb, hb, hb1⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem good_norm_two (h : GoodPair l g2 g3) : ‖(2 : ℂ_[l])‖ = 1 := by
  have hl : ¬ (l ∣ 2) := by
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := h.five
    omega
  have hQ : ‖(2 : ℚ_[l])‖ = 1 := by
    have e2 := Padic.eq_padicNorm (p := l) (2 : ℚ)
    push_cast at e2
    rw [e2]
    exact_mod_cast (padicNorm.nat_eq_one_iff 2).mpr hl
  have e : (2 : ℂ_[l]) = (((2 : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    rw [map_ofNat]
    first
    | exact (map_ofNat (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) 2).symm
    | exact (UniformSpace.Completion.coe_ofNat 2).symm
    | exact (map_ofNat (algebraMap (PadicAlgCl l) ℂ_[l]) 2).symm
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, hQ]

theorem good_norm_four (h : GoodPair l g2 g3) : ‖(4 : ℂ_[l])‖ = 1 := by
  rw [show (4 : ℂ_[l]) = 2 * 2 by norm_num, norm_mul, good_norm_two h, mul_one]

theorem good_model (h : GoodPair l g2 g3) : IntegralModel (shortW g2 g3) ∧ ‖(shortW g2 g3).Δ‖ = 1 := by
  have h4 := good_norm_four h
  refine ⟨?_, ?_⟩
  · unfold IntegralModel shortW
    simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2, h.norm3,
      and_self]
  · have hΔ : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hΔ, h.disc]

theorem good_int (h : GoodPair l g2 g3) : IntCurve (shortW g2 g3) := by
  have h4 := good_norm_four h
  have hΔ := (good_model h).2
  unfold IntCurve
  simp only [shortW] at hΔ ⊢
  simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2,
    h.norm3, and_self, hΔ]

theorem good_coeff (h : GoodPair l g2 g3) : CoeffSub (MaximalUnramifiedExtension l) (shortW g2 g3) := by
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact ofNat_mem (MaximalUnramifiedExtension l) 4
    | (have h4' := natCast_mem (MaximalUnramifiedExtension l) 4
       exact_mod_cast h4')
  unfold CoeffSub shortW
  exact ⟨zero_mem _, zero_mem _, zero_mem _, div_mem (neg_mem h.mem2) h4,
    div_mem (neg_mem h.mem3) h4⟩

theorem integral_of_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P) :
    P ≠ 0 ∧ ‖px _ P‖ ≤ 1 ∧ ‖py _ P‖ ≤ 1 := by
  unfold InFormalGroupPoints at hP
  cases P with
  | zero => exact absurd trivial hP
  | some x y hxy =>
    have hx : ‖x‖ ≤ 1 := not_lt.mp hP
    have h4 := good_norm_four h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hxy.1
    simp only [shortW, zero_mul, mul_zero, add_zero] at heq
    have hb1 : ‖x ^ 3‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    have hb2 : ‖-g2 / 4 * x‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_neg, h4, div_one]
      exact mul_le_one₀ h.norm2 (norm_nonneg _) hx
    have hb3 : ‖-g3 / 4‖ ≤ 1 := by
      rw [norm_div, norm_neg, h4, div_one]
      exact h.norm3
    have hsum : ‖x ^ 3 + -g2 / 4 * x + -g3 / 4‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb1 hb2)) hb3)
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, heq]
      exact hsum
    refine ⟨by rintro (_ | _), ?_, ?_⟩
    · exact hx
    · show ‖y‖ ≤ 1
      nlinarith [norm_nonneg y]

theorem torsion_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (hP0 : P ≠ 0) : ¬ InFormalGroupPoints P := fun hE => by
  have hn := norm_natCast_Cl_of_not_dvd (l := l) hN
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
  have hmul := (FormalGroupPointsTorsion.mulz (good_model h).1 P hE hP0 m).2
  rw [hNP, Affine.Point.zero_def] at hmul
  simp only [FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at hmul
  exact lt_irrefl _ hmul

theorem not_mem_formalGroup_sub (h : GoodPair l g2 g3) (P D : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P)
    (hD : InFormalGroupPoints D) : ¬ InFormalGroupPoints (P - D) := fun hE => by
  have hadd : InFormalGroupPoints (P - D + D) := by
    generalize P - D = E at hE ⊢
    cases E with
    | zero =>
      change InFormalGroupPoints (0 + D)
      rwa [zero_add]
    | some x₁ y₁ h₁ =>
      cases D with
      | zero =>
        change InFormalGroupPoints (Affine.Point.some x₁ y₁ h₁ + 0)
        rwa [add_zero]
      | some x₂ y₂ h₂ =>
        by_cases hxy : x₁ = x₂ ∧ y₁ = (shortW g2 g3).toAffine.negY x₂ y₂
        · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
          trivial
        · rw [Affine.Point.add_some hxy]
          exact FormalGroupPointsSubgroup.addX_norm _ (good_model h).1 h₁.1 h₂.1 hxy hE hD
  exact hP (by simpa only [sub_add_cancel] using hadd)

theorem tor_y_unit (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (h2 : P + P ≠ 0) : ‖py _ P‖ = 1 := by
  have hP0 : P ≠ 0 := fun h0 => h2 (by rw [h0, add_zero])
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P (torsion_not_mem_formalGroup h P N hN hNP hP0)
  have hN2 : N • (P + P) = 0 := by rw [smul_add, hNP, add_zero]
  obtain ⟨-, hx2, -⟩ := integral_of_not_mem_formalGroup h (P + P) (torsion_not_mem_formalGroup h (P + P) N hN hN2 h2)
  have hu := Formalism.L2.Th1.E.UnitPsi2_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] _ (good_int h) P hP0 h2 hx hy hx2
  have he : Formalism.L2.Th1.E.psi2 (shortW g2 g3) P = 2 * py _ P := by
    simp [Formalism.L2.Th1.E.psi2, shortW]
  rw [he, norm_mul, good_norm_two h, one_mul] at hu
  exact hu

end ReciprocityTheory.ChartRestriction.L1
end
end
