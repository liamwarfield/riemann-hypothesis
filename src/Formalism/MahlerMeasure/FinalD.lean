module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler
public import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
public import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm

@[expose] public section

section -- merged from Formalism.MahlerMeasure.MahlerMeasureProofs.LieRoots
namespace Formalism.GM

open Finset Polynomial

namespace GaussNormRoots

section
variable {K : Type} [NormedField K]

theorem gaussR_eq_sup_of_subset (ρ : NNReal) (P : K[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    gaussR ρ P = s.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k) := by
  unfold gaussR
  apply le_antisymm (Finset.sup_mono hs)
  refine Finset.sup_le fun k _ => ?_
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · rw [Polynomial.notMem_support_iff.mp hk]
    simp

theorem gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (Polynomial.C a) = ‖a‖₊ := by
  rw [gaussR_eq_sup_of_subset ρ _ {0} (Polynomial.support_C_subset a)]
  simp

theorem gaussR_lin (ρ : NNReal) (q a : K) :
    gaussR ρ (Polynomial.C q * X + Polynomial.C a) = max ‖a‖₊ (‖q‖₊ * ρ) := by
  have hs : (Polynomial.C q * X + Polynomial.C a).support ⊆ {0, 1} := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk
    rcases k with _ | _ | k <;> simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
  rw [gaussR_eq_sup_of_subset ρ _ _ hs]
  simp [Polynomial.coeff_C, Polynomial.coeff_X, max_comm]

theorem gaussR_multiset_prod (hG : GaussMulRad) [IsUltrametricDist K] (ρ : NNReal) (hρ : 0 < ρ)
    (m : Multiset K) (f : K → K[X]) :
    gaussR ρ (m.map f).prod = (m.map (fun ζ => gaussR ρ (f ζ))).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← Polynomial.C_1, gaussR_C]
    simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [hG K ρ _ _ hρ, ih]

end

theorem multiset_sum_le_sum {α : Type} (m : Multiset α) (f g : α → ℝ) (hfg : ∀ x, f x ≤ g x) :
    (m.map f).sum ≤ (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (hfg a) ih

theorem multiset_sum_neg {α : Type} (m : Multiset α) (f : α → ℝ) :
    (m.map fun x => -f x).sum = -(m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, neg_add]

theorem multiset_sum_add {α : Type} (m : Multiset α) (f g : α → ℝ) :
    (m.map fun x => f x + g x).sum = (m.map f).sum + (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

theorem multiset_sum_mul_left {α : Type} (m : Multiset α) (c : ℝ) (f : α → ℝ) :
    (m.map fun x => c * f x).sum = c * (m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add]

theorem multiset_card_filter_eq_sum {α : Type} (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    ((m.filter P).card : ℝ) = (m.map fun x => if P x then (1 : ℝ) else 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : P a
    · rw [Multiset.filter_cons_of_pos _ h]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, h, if_true]
      push_cast
      rw [ih]
      ring
    · rw [Multiset.filter_cons_of_neg _ h]
      simp only [Multiset.map_cons, Multiset.sum_cons, h, if_false]
      rw [ih]
      ring

theorem multiset_prod_pos {α : Type} (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < (m.map f).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (hf a) ih

theorem logb_multiset_prod {α : Type} (b : ℝ) (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    Real.logb b (m.map f).prod = (m.map fun x => Real.logb b (f x)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Real.logb_mul (hf a).ne' (multiset_prod_pos m f hf).ne', ih]

theorem vmin_step (p : ℕ) (hp1 : (1 : ℝ) < p) (h : ℕ) (E : ℝ) (hE : 0 ≤ E) (u : ℝ) (_hu : 0 ≤ u)
    [Decidable (u ≤ (p : ℝ) ^ (-(h : ℤ)))] :
    -Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) ≤
      -Real.logb p (max u ((p : ℝ) ^ (-(h : ℤ)))) + E * (if u ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hB : (0 : ℝ) < (p : ℝ) ^ (-((h : ℝ) + E)) := Real.rpow_pos_of_pos hp0 _
  have hAeq : (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ) ^ (-(h : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hBA : (p : ℝ) ^ (-((h : ℝ) + E)) ≤ (p : ℝ) ^ (-(h : ℤ)) := by
    rw [hAeq]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  split_ifs with hu
  · rw [max_eq_right hu, mul_one]
    have h1 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) ≤
        Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) :=
      Real.logb_le_logb_of_le hp1 hB (le_max_right _ _)
    have h2 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) = -((h : ℝ) + E) :=
      Real.logb_rpow hp0 hp1.ne'
    have h3 : Real.logb p ((p : ℝ) ^ (-(h : ℤ))) = -(h : ℝ) := by
      rw [hAeq]
      exact Real.logb_rpow hp0 hp1.ne'
    linarith
  · push_neg at hu
    rw [max_eq_left (le_trans hBA hu.le), max_eq_left hu.le]
    simp

end GaussNormRoots

open GaussNormRoots in
theorem lieRoots_of (hG : GaussMulRad) : LieRoots := by
  unfold LieRoots
  intro p _ K _ _ _ h β E D lead roots t₀ hE hlead hD hbound
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hρ : 0 < ((p : ℝ) ^ (-E)).toNNReal := Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos hp0 _)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] K) p, norm_algebraMap', Padic.norm_p]
  have hnph : ‖(p : K) ^ h‖ = (p : ℝ) ^ (-(h : ℤ)) := by
    rw [norm_pow, hnp, inv_pow, zpow_neg, zpow_natCast]
  have hcomp : D.comp (C ((p : K) ^ h) * X + C (t₀ : K)) =
      C lead * (roots.map fun ζ => C ((p : K) ^ h) * X + C ((t₀ : K) - ζ)).prod := by
    rw [hD, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  have hpt : ∀ ζ : K, ((max ‖(t₀ : K) - ζ‖₊ (‖(p : K) ^ h‖₊ * ((p : ℝ) ^ (-E)).toNNReal) : NNReal) : ℝ) =
      max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) := by
    intro ζ
    rw [NNReal.coe_max, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, hnph,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos hp0 _).le]
    congr 1
    rw [← Real.rpow_intCast, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  have hreal : ((gaussR ((p : ℝ) ^ (-E)).toNNReal (D.comp (C ((p : K) ^ h) * X + C (t₀ : K))) : NNReal) : ℝ) =
      ‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod := by
    rw [hcomp, hG K _ _ _ hρ, gaussR_C, gaussR_multiset_prod hG _ hρ]
    simp only [gaussR_lin]
    rw [NNReal.coe_mul, coe_nnnorm, NNReal.coe_multiset_prod, Multiset.map_map]
    congr 1
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun ζ _ => hpt ζ)
  rw [hreal] at hbound
  have hFpos : ∀ ζ : K, 0 < max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) :=
    fun ζ => lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) (le_max_right _ _)
  have hlpos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead
  have hPpos := multiset_prod_pos roots _ hFpos
  have hlog : Real.logb p (‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod)
      ≤ -(E * β) := by
    calc _ ≤ Real.logb p ((p : ℝ) ^ (-(E * β))) :=
          Real.logb_le_logb_of_le hp1 (mul_pos hlpos hPpos) hbound
      _ = -(E * β) := Real.logb_rpow hp0 hp1.ne'
  rw [Real.logb_mul hlpos.ne' hPpos.ne', logb_multiset_prod _ _ _ hFpos] at hlog
  have hstep := multiset_sum_le_sum roots
    (fun ζ => -Real.logb p (max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))))
    (fun ζ => vmin p h ((t₀ : K) - ζ) +
      E * (if ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0)) (fun ζ => by
        have := vmin_step p hp1 h E hE ‖(t₀ : K) - ζ‖ (norm_nonneg _)
        unfold vmin
        simpa only using this)
  rw [multiset_sum_add, multiset_sum_mul_left, multiset_sum_neg] at hstep
  rw [multiset_card_filter_eq_sum]
  linarith

end Formalism.GM
end

section -- merged from Formalism.MahlerMeasure.MahlerMeasureProofs.MahlerK
namespace Formalism.GM

open Polynomial

theorem mahler_binomial_unit_ball : MahlerK := by
  intro p hp K _ _ h k t₀ hk m
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set P : ℚ[X] := Polynomial.C ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).comp (Polynomial.C ((p : ℚ) ^ h) * X + Polynomial.C (t₀ : ℚ)) with hP
  have hmap : P.map (Rat.castHom K) =
      (binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K)) := by
    rw [hP, binK, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, descPochhammer_map,
      mul_comp, C_comp]
    simp
  rw [← hmap, Polynomial.coeff_map]
  have h1 := mahler_disc_bound p h k t₀ hp.out hk m
  rw [← hP] at h1
  have h2 : ((Rat.castHom K) (P.coeff m)) = algebraMap ℚ_[p] K ((P.coeff m : ℚ) : ℚ_[p]) := by
    rw [map_ratCast]; rfl
  rw [h2, norm_algebraMap', Padic.eq_padicNorm]
  exact_mod_cast h1

end Formalism.GM
end

section -- merged from Formalism.MahlerMeasure.MahlerMeasureProofs.GaussRad
namespace Formalism.GM

open Finset Polynomial

section

variable {K : Type} [NormedField K]

lemma gaussR_term_le (ρ : NNReal) (P : K[X]) (k : ℕ) :
    ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P := by
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · have h0 : P.coeff k = 0 := by simpa using hk
    simp [h0]

lemma gaussR_le_iff (ρ : NNReal) (P : K[X]) (c : NNReal) :
    gaussR ρ P ≤ c ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ c := ⟨fun h k => (gaussR_term_le ρ P k).trans h, fun h => Finset.sup_le fun k _ => h k⟩

lemma gaussR_attained (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ k, ‖P.coeff k‖₊ * ρ ^ k = gaussR ρ P := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  exact ⟨k, hk.symm⟩

lemma gaussR_attained_least (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ i₀, ‖P.coeff i₀‖₊ * ρ ^ i₀ = gaussR ρ P ∧
      ∀ i < i₀, ‖P.coeff i‖₊ * ρ ^ i < gaussR ρ P := by
  classical
  have h := gaussR_attained ρ P hP
  exact ⟨Nat.find h, Nat.find_spec h, fun i hi => lt_of_le_of_ne (gaussR_term_le ρ P i) (Nat.find_min h hi)⟩

lemma gaussR_pos (ρ : NNReal) (hρ : 0 < ρ) (P : K[X]) (hP : P ≠ 0) : 0 < gaussR ρ P := by
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  unfold gaussR
  rw [hk']
  exact mul_pos (nnnorm_pos.2 (Polynomial.mem_support_iff.1 hk)) (pow_pos hρ k)

lemma gaussR_zero (ρ : NNReal) : gaussR ρ (0 : K[X]) = 0 := by
  simp [gaussR]

variable [IsUltrametricDist K]

lemma gaussR_mul_le (ρ : NNReal) (P Q : K[X]) :
    gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]
  intro k
  rw [Polynomial.coeff_mul]
  have h1 : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ ≤
      (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) :=
    IsUltrametricDist.nnnorm_sum_le_of_forall_le
      (fun x hx => Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) hx)
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup (Finset.HasAntidiagonal.antidiagonal k) ⟨(0, k), by simp⟩
    (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)
  have hk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k
      ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) * ρ ^ k :=
        mul_le_mul_of_nonneg_right h1 zero_le
    _ = ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k := by rw [hxe]
    _ = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
        rw [nnnorm_mul, ← hk, pow_add]
        ring
    _ ≤ gaussR ρ P * gaussR ρ Q := mul_le_mul' (gaussR_term_le ρ P _) (gaussR_term_le ρ Q _)

lemma le_gaussR_mul (ρ : NNReal) (hρ : 0 < ρ) (P Q : K[X]) :
    gaussR ρ P * gaussR ρ Q ≤ gaussR ρ (P * Q) := by
  by_cases hP : P = 0
  · simp [hP, gaussR_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gaussR_zero]
  obtain ⟨i₀, hi₀, hlt_i⟩ := gaussR_attained_least ρ P hP
  obtain ⟨j₀, hj₀, hlt_j⟩ := gaussR_attained_least ρ Q hQ
  have hgP := gaussR_pos ρ hρ P hP
  have hgQ := gaussR_pos ρ hρ Q hQ
  have hρk : 0 < ρ ^ (i₀ + j₀) := pow_pos hρ _
  have hsplit : (P * Q).coeff (i₀ + j₀) = P.coeff i₀ * Q.coeff j₀ +
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2 := by
    have hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [Polynomial.coeff_mul, Finset.add_sum_erase _ (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem]
  have hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    intro x hx
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.1 hx
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx'
    have e : ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) =
        (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
      rw [nnnorm_mul, ← hsum, pow_add]
      ring
    rw [e]
    by_cases h1 : x.1 < i₀
    · calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ (‖P.coeff x.1‖₊ * ρ ^ x.1) * gaussR ρ Q := mul_le_mul_of_nonneg_left (gaussR_term_le ρ Q _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_right (hlt_i _ h1) hgQ
    · have h2 : x.2 < j₀ := by
        by_contra h
        exact hne (Prod.ext (by omega) (by omega))
      calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ gaussR ρ P * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := mul_le_mul_of_nonneg_right (gaussR_term_le ρ P _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_left (hlt_j _ h2) hgP
  have hsup : ((Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀)).sup
      (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) < gaussR ρ P * gaussR ρ Q :=
    (Finset.sup_lt_iff (mul_pos hgP hgQ)).2 hterm
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    refine lt_of_le_of_lt ?_ hsup
    rw [← le_div_iff₀ hρk]
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro x hx
    rw [le_div_iff₀ hρk]
    exact Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) hx
  have hmain : ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) = gaussR ρ P * gaussR ρ Q := by
    rw [nnnorm_mul, pow_add, ← hi₀, ← hj₀]
    ring
  have h' : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) := by
    rw [hmain]
    exact hrest
  have hlt := lt_of_mul_lt_mul_right h' zero_le
  have heq : ‖(P * Q).coeff (i₀ + j₀)‖₊ = ‖P.coeff i₀ * Q.coeff j₀‖₊ := by
    rw [hsplit, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hlt.ne', max_eq_left hlt.le]
  calc gaussR ρ P * gaussR ρ Q = ‖(P * Q).coeff (i₀ + j₀)‖₊ * ρ ^ (i₀ + j₀) := by rw [heq, hmain]
    _ ≤ gaussR ρ (P * Q) := gaussR_term_le ρ (P * Q) _

end

theorem gauss_norm_multiplicative : GaussMulRad := fun K _ _ ρ P Q hρ => le_antisymm (gaussR_mul_le ρ P Q) (le_gaussR_mul ρ hρ P Q)

end Formalism.GM
end

namespace Formalism.GM.Top
open Formalism.GM
theorem smithZp : SmithZp := smith_form_p_adic_integers
theorem lieMat : LieMat := lieMat_of mahler_binomial_unit_ball
theorem lieRoots : LieRoots := lieRoots_of gauss_norm_multiplicative
theorem valuation_window_lower_bound : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
