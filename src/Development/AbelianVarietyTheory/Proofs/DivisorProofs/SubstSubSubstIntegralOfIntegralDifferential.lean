module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_sub_eq_p_mul_of_constantCoeff_eq {x y : WittVector p k}
    (h : WittVector.constantCoeff x = WittVector.constantCoeff y) : ∃ z, x - y = p * z := by
  by_cases hxy : x - y = 0
  · exact ⟨0, by rw [hxy, mul_zero]⟩
  obtain ⟨m, z, hz, hxyz⟩ := WittVector.exists_eq_pow_p_mul (x - y) hxy
  rcases m with _ | m
  · exfalso; apply hz
    have h1 := congrArg WittVector.constantCoeff hxyz
    rw [map_sub, h, sub_self, pow_zero, one_mul] at h1
    exact h1.symm
  · exact ⟨p ^ m * z, by rw [hxyz, pow_succ]; ring⟩

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem prod_sub_prod_divisible_lemma_2 {σ τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k)
    (U V : σ → MvPowerSeries τ (WittVector p k)) (e : σ → ℕ) (S : Finset σ)
    (h : ∀ i ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (U i ^ e i - V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (∏ i ∈ S, U i ^ e i - ∏ i ∈ S, V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i S hi ih =>
    obtain ⟨Y1, hY1⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Y2, hY2⟩ := h i (Finset.mem_insert_self i S)
    refine ⟨U i ^ e i * Y1 + Y2 * ∏ j ∈ S, V j ^ e j, ?_⟩
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    simp only [Algebra.smul_def, map_sub, map_mul, map_add (f := _), map_pow, map_prod] at hY1 hY2 ⊢
    linear_combination
      (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i)) ^ e i * hY1 +
      (∏ j ∈ S, (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V j)) ^ e j) * hY2

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_choose_mul_p_pow_mul_eq_p_mul (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t : WittVector p k, c * ((n.choose j : _root_.GlobalTheory.Katz.Fr p k) * (p : _root_.GlobalTheory.Katz.Fr p k) ^ j) =
      algebraMap (WittVector p k) _ (p * t) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨e, j', hj', hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p hp.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'
  have hej : e < j := by
    have h1 : p ^ e ≤ j := by rw [hjeq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)
    exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h1
  obtain ⟨q, rfl⟩ : ∃ q, j = q + e + 1 := ⟨j - e - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hunit : IsUnit (j' : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h2 : (j' : WittVector p k).coeff 0 = (j' : k) :=
      map_natCast (WittVector.constantCoeff (p := p) (R := k)) j'
    rw [h2]
    exact (CharP.cast_eq_zero_iff k p j').not.2 hj'
  obtain ⟨s, hs⟩ := hunit.exists_right_inv
  refine ⟨m * (n'.choose (q + e) : WittVector p k) * (p : WittVector p k) ^ q * s, ?_⟩
  set ι := algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)
  have hs' : (j' : _root_.GlobalTheory.Katz.Fr p k) * ι s = 1 := by
    rw [← map_natCast ι, ← map_mul, hs, map_one]
  have hjK : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) = (p : _root_.GlobalTheory.Katz.Fr p k) ^ e * j' := by
    rw [hjeq]; push_cast; ring
  have hchoose : ((n' + 1).choose (q + e + 1) : _root_.GlobalTheory.Katz.Fr p k) * ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) =
      ((n' + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) := by
    have := Nat.add_one_mul_choose_eq n' (q + e)
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  have hj0 : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) ≠ 0 := by
    rw [hjK]
    have hinj : Function.Injective ι := IsFractionRing.injective _ _
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 (WittVector.p_nonzero p k)
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 hunit.ne_zero
  apply mul_right_cancel₀ hj0
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (c * (p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1)) * hchoose +
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k)) * hc -
    ((p : _root_.GlobalTheory.Katz.Fr p k) * ι m * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) *
      (p : _root_.GlobalTheory.Katz.Fr p k) ^ q * ι s) * hjK -
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) * ι m) * hs'

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_algebraMap_smul' {τ : Type} (a : WittVector p k) (Y : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (a • Y) =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a •
        MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  ext β
  simp only [MvPowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_add_p_mul_pow_sub_pow_eq_p_smul {τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (V H : MvPowerSeries τ (WittVector p k)) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      ((V + (p : MvPowerSeries τ (WittVector p k)) * H) ^ n - V ^ n) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    mul_one, add_sub_cancel_right, map_sum, Finset.smul_sum]
  have key : ∀ j ∈ Finset.range n, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, ht⟩ := exists_choose_mul_p_pow_mul_eq_p_mul c m hc (n - j) (by omega) (by omega)
    rw [Nat.choose_symm (by omega)] at ht
    refine ⟨t • (V ^ j * H ^ (n - j)), ?_⟩
    have e1 : V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k)) =
        ((n.choose j * p ^ (n - j) : ℕ) : WittVector p k) • (V ^ j * H ^ (n - j)) := by
      rw [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e1, map_algebraMap_smul', map_algebraMap_smul', smul_smul, smul_smul, map_natCast]
    congr 1
    rw [← map_mul, ← ht]; push_cast; ring
  have hsum : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) →
      ∃ Y, ∑ j ∈ S, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro S hS
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨Y1, hY1⟩ := ih fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨Y2, hY2⟩ := hS j (Finset.mem_insert_self j S)
      exact ⟨Y2 + Y1, by rw [Finset.sum_insert hj, hY1, hY2, map_add (f := _), smul_add]⟩
  exact hsum _ key


open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
theorem _root_.GlobalTheory.Katz.subst_sub_subst_mem_intBy : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (_root_.GlobalTheory.Katz.Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (_root_.GlobalTheory.Katz.Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (u i) (w i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (v i) (w i)) → f ∈ _root_.GlobalTheory.Katz.quasiInt p k σ → subst u f - subst v f ∈ _root_.GlobalTheory.Katz.intBy p k τ p := by
  intro p _ k _ _ _ σ τ _ u v w f hu0 hv0 hu hv hf
  classical
  choose a ha using fun i β => hu i β
  choose b hb using fun i β => hv i β
  choose hh hhh using fun i β =>
    exists_sub_eq_p_mul_of_constantCoeff_eq ((ha i β).2.trans (hb i β).2.symm)
  let U : σ → MvPowerSeries τ (WittVector p k) := fun i β => a i β
  let V : σ → MvPowerSeries τ (WittVector p k) := fun i β => b i β
  let Hs : σ → MvPowerSeries τ (WittVector p k) := fun i β => hh i β
  have hUV : ∀ i, U i = V i + (p : MvPowerSeries τ (WittVector p k)) * Hs i := by
    intro i; refine MvPowerSeries.ext fun β => ?_
    have e : (p : MvPowerSeries τ (WittVector p k)) * Hs i = (p : WittVector p k) • Hs i := by
      rw [Algebra.smul_def, map_natCast]
    rw [e, map_add (f := _), map_smul, smul_eq_mul]
    show a i β = b i β + p * hh i β
    rw [← hhh]; ring
  have huM : u = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (ha i β).1
  have hvM : v = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (hb i β).1
  have hf' : ∀ (α : σ →₀ ℕ) (i : σ), ∃ m, ((α i : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * MvPowerSeries.coeff α f =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) m := hf
  have hsu := MvPowerSeries.hasSubst_of_constantCoeff_zero hu0
  have hsv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  unfold _root_.GlobalTheory.Katz.intBy
  refine fun β => ?_
  rw [map_sub, MvPowerSeries.coeff_subst hsu, MvPowerSeries.coeff_subst hsv,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hsu f β)
      (MvPowerSeries.coeff_subst_finite hsv f β)]
  refine finsum_induction (fun x => ∃ w, x = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) (p * w))
    ⟨0, by simp⟩ (fun x y ⟨w1, h1⟩ ⟨w2, h2⟩ => ⟨w1 + w2, by rw [h1, h2, mul_add, map_add (f := _)]⟩) fun α => ?_
  obtain ⟨Y, hY⟩ := prod_sub_prod_divisible_lemma_2 (MvPowerSeries.coeff α f) U V α α.support fun i _ => by
    obtain ⟨mi, hmi⟩ := hf' α i
    rw [hUV i]
    exact map_add_p_mul_pow_sub_pow_eq_p_smul _ mi hmi (V i) (Hs i)
  refine ⟨MvPowerSeries.coeff β Y, ?_⟩
  rw [huM, hvM]
  simp only [Finsupp.prod, ← map_pow, ← map_prod]
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← map_sub, ← smul_eq_mul, ← map_smul, hY,
    map_smul, MvPowerSeries.coeff_map, smul_eq_mul, map_mul]

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferentialStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_integral_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, Red p (u i) (w i)) → (∀ i, Red p (v i) (w i)) → f ∈ quasiInt p k σ → subst u f - subst v f ∈ intBy p k τ p := by
  first | exact @GlobalTheory.Katz.subst_sub_subst_mem_intBy | exact GlobalTheory.Katz.subst_sub_subst_mem_intBy | (intros; apply GlobalTheory.Katz.subst_sub_subst_mem_intBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Polynomial IntermediateField

namespace GlobalTheory.LadicDenom

theorem norm_natCast_padicComplex (l : ℕ) [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_ratCast_padicComplex (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = ‖(q : ℚ_[l])‖ := by
  have h : (q : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_padicComplex, Padic.norm_p]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem not_dvd_den_of_norm_le_one (l : ℕ) [hl : Fact l.Prime] (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hnum : ‖(q.num : ℚ_[l])‖ = 1 := by
    have hc : l.Coprime q.num.natAbs := (Nat.Prime.coprime_iff_not_dvd hl.out).2 fun hn =>
      hl.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced hn hd)
    rcases Int.natAbs_eq q.num with e | e
    · rw [e, Int.cast_natCast]; exact Padic.norm_natCast_eq_one_iff.2 hc
    · rw [e, Int.cast_neg, Int.cast_natCast, norm_neg]; exact Padic.norm_natCast_eq_one_iff.2 hc
  have hden : ‖(q.den : ℚ_[l])‖ < 1 := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · exact_mod_cast Padic.norm_int_le_one (q.den : ℤ)
    · have := Padic.norm_natCast_eq_one_iff.1 e
      exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hd)
  have e : (q : ℚ_[l]) * (q.den : ℚ_[l]) = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have e2 := congrArg norm e
  rw [norm_mul, hnum] at e2
  have : ‖(q : ℚ_[l])‖ * ‖(q.den : ℚ_[l])‖ < 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) h).trans_lt hden
  exact this.ne e2


set_option synthInstance.maxHeartbeats 400000 in
theorem norm_root_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (β : ℂ_[l]) (hβ : β ∈ (minpoly ℚ α).aroots ℂ_[l]) :
    ‖β‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let φ := (algHomAdjoinIntegralEquiv ℚ hα).symm ⟨β, hβ⟩
  letI : Algebra ℚ⟮α⟯ ℂ_[l] := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ⟮α⟯ (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let ψ : algebraicClosure ℚ ℂ →ₐ[ℚ⟮α⟯] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have e : ψ α = β := by
    have h1 := ψ.commutes (AdjoinSimple.gen ℚ α)
    rw [AdjoinSimple.algebraMap_gen] at h1
    rw [h1]
    exact algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα ⟨β, hβ⟩
  rw [← e]
  exact h ψ.toRingHom

theorem coeff_norm_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (i : ℕ) :
    ‖(((minpoly ℚ α).coeff i : ℚ) : ℂ_[l])‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set P := (minpoly ℚ α).map (algebraMap ℚ ℂ_[l]) with hP
  let S := (NormedField.valuation (K := ℂ_[l])).integer
  have memS : ∀ z : ℂ_[l], z ∈ S ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  have hmon : P.Monic := (minpoly.monic hα).map _
  have hroots : ∀ β ∈ P.roots, β ∈ S := fun β hβ => (memS β).2 (norm_root_le_one l α h β hβ)
  have hc : (((minpoly ℚ α).coeff i : ℚ) : ℂ_[l]) = P.coeff i := by
    rw [hP, coeff_map, eq_ratCast]
  rw [hc, ← memS]
  by_cases hi : i ≤ P.natDegree
  · rw [coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hi, hmon.leadingCoeff, one_mul]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
    unfold Multiset.esymm
    refine S.multiset_sum_mem _ fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hz
    exact S.multiset_prod_mem _ fun w hw => hroots w (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hw)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact S.zero_mem

theorem intAt_of_forall_norm_le_one (l : ℕ) [hl : Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) : IntAt l (α : ℂ) := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly ℚ α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hden : ∀ i, ¬ l ∣ (p.coeff i).den := fun i =>
    not_dvd_den_of_norm_le_one l _ (by rw [← norm_ratCast_padicComplex]; exact coeff_norm_le_one l α h i)
  set D : ℕ := ∏ i ∈ Finset.range p.natDegree, (p.coeff i).den with hD
  have hDc : D.Coprime l := Nat.Coprime.prod_left fun i _ =>
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 (hden i)).symm
  refine ⟨D, hDc, ?_⟩
  set q := p.scaleRoots (D : ℚ) with hq
  have hql : q ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hq, coeff_scaleRoots]
    rcases lt_trichotomy n p.natDegree with hn | hn | hn
    · obtain ⟨e, he⟩ : (p.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - n = k + 1 := ⟨p.natDegree - n - 1, by omega⟩
      have h1 : p.coeff n * ((p.coeff n).den : ℚ) = (p.coeff n).num := Rat.mul_den_eq_num _
      refine ⟨(p.coeff n).num * e * D ^ k, ?_⟩
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [hk, pow_succ, ← h1]
      have h2 : (D : ℚ) = (p.coeff n).den * e := by exact_mod_cast he
      rw [h2]
      ring
    · refine ⟨1, ?_⟩
      rw [hn, hmon.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt hn, zero_mul, map_zero]
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_scaleRoots]; exact hmon
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hql hqm
  have hroot : aeval ((D : algebraicClosure ℚ ℂ) * α) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (D : ℚ)) (minpoly.aeval ℚ α)
    simpa using this
  have hint : IsIntegral ℤ ((D : algebraicClosure ℚ ℂ) * α) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, hQ]
    exact hroot
  have := map_isIntegral_int (algebraicClosure ℚ ℂ).val.toRingHom hint
  simpa using this

theorem valGe_iff_forall_sz (l : ℕ) [hl : Fact l.Prime] (r : ℝ) (x : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  constructor
  · intro hv lam
    obtain ⟨N, hN, hi⟩ := hv ⌈r⌉ 1 one_pos (by simpa using Int.le_ceil r)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hN
      exact hl.out.one_lt.ne' hN
    have hmem : x ∈ algebraicClosure ℚ ℂ := by
      have h1 : (N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1) ∈ algebraicClosure ℚ ℂ :=
        mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic
      have h2 : ((N : ℂ) * (l : ℂ) ^ ⌈r⌉) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      have h3 : x = ((N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1)) * ((N : ℂ) * (l : ℂ) ^ ⌈r⌉)⁻¹ := by
        rw [pow_one, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ h2, one_mul]
      rw [h3]
      exact mul_mem h1 (inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (zpow_mem (IntermediateField.natCast_mem _ _) _)))
    refine ⟨hmem, ?_⟩
    set t := ‖lam ⟨x, hmem⟩‖ with ht
    have key : ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → t ^ n ≤ (l : ℝ) ^ m := by
      intro m n hn hmn
      obtain ⟨N, hN, hi⟩ := hv m n hn hmn
      set β : algebraicClosure ℚ ℂ := (N : algebraicClosure ℚ ℂ) * ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)
      have hiβ : IsIntegral ℤ β := by
        refine (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) Subtype.val_injective).1 ?_
        have e : ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) β = (N : ℂ) * ((l : ℂ) ^ m * x ^ n) :=
          Complex.ext rfl rfl
        rw [e]; exact hi
      have h1 := norm_le_one_of_isIntegral (map_isIntegral_int lam hiβ)
      simp only [β, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow] at h1
      rw [norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff.2 hN.symm, norm_prime_padicComplex, one_mul,
        inv_zpow', zpow_neg, inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one] at h1
      exact h1
    by_contra hgt
    rw [not_le] at hgt
    have htp : 0 < t := (Real.rpow_pos_of_pos hl0 r).trans hgt
    have hr : r < Real.logb l t := (Real.lt_logb_iff_rpow_lt hl1 htp).2 hgt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hq3 : (l : ℝ) ^ (q : ℝ) < t := (Real.lt_logb_iff_rpow_lt hl1 htp).1 hq2
    have hqe : (q : ℝ) = (q.num : ℝ) / (q.den : ℕ) := by exact_mod_cast (Rat.num_div_den q).symm
    have hk := key q.num q.den q.den_pos (by rw [← hqe]; exact hq1.le)
    have h4 : ((l : ℝ) ^ (q : ℝ)) ^ q.den < t ^ q.den :=
      pow_lt_pow_left₀ hq3 (Real.rpow_nonneg hl0.le _) q.den_pos.ne'
    have h5 : ((l : ℝ) ^ (q : ℝ)) ^ q.den = (l : ℝ) ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, hqe,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 q.den_pos.ne')]
    rw [h5] at h4
    exact absurd hk (not_le.2 h4)
  · intro h
    let lam₀ : algebraicClosure ℚ ℂ →+* ℂ_[l] := (IsAlgClosed.lift : algebraicClosure ℚ ℂ →ₐ[ℚ] ℂ_[l]).toRingHom
    obtain ⟨hmem, -⟩ := h lam₀
    intro m n hn hmn
    have hmn' : r * n ≤ m := by rwa [le_div_iff₀ (Nat.cast_pos.2 hn)] at hmn
    have hb : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l],
        ‖lam ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)‖ ≤ 1 := by
      intro lam
      obtain ⟨h', hle⟩ := h lam
      rw [map_mul, map_zpow₀, map_pow, map_natCast, norm_mul, norm_zpow, norm_pow, norm_prime_padicComplex,
        inv_zpow', zpow_neg]
      have h2 : ‖lam ⟨x, hmem⟩‖ ^ n ≤ (l : ℝ) ^ m := by
        calc ‖lam ⟨x, hmem⟩‖ ^ n ≤ ((l : ℝ) ^ r) ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
          _ = (l : ℝ) ^ (r * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
          _ ≤ (l : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1.le hmn'
          _ = (l : ℝ) ^ m := Real.rpow_intCast _ _
      rw [inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one]
      exact h2
    have := intAt_of_forall_norm_le_one l _ hb
    have e : (((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n : algebraicClosure ℚ ℂ) : ℂ) = (l : ℂ) ^ m * x ^ n :=
      Complex.ext rfl rfl
    rwa [e] at this

end GlobalTheory.LadicDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddiStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  first | exact @GlobalTheory.LadicDenom.valGe_iff_forall_sz | exact GlobalTheory.LadicDenom.valGe_iff_forall_sz | (intros; apply GlobalTheory.LadicDenom.valGe_iff_forall_sz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
noncomputable section

open GlobalTheory.LatVal (Sz)

namespace GlobalTheory.QFam

theorem exists_algebraic_norm_eq_rpow (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    ∃ x : algebraicClosure ℚ ℂ, x ≠ 0 ∧ ‖lam x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hlc : (l : algebraicClosure ℚ ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((l : algebraicClosure ℚ ℂ) ^ q.num) q.den_pos
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow q.den_ne_zero] at hx
    exact zpow_ne_zero _ hlc hx.symm
  · have h1 : ‖lam x‖ ^ q.den = ((l : ℝ) ^ (-(q : ℝ))) ^ q.den := by
      rw [← norm_pow, ← map_pow, hx, map_zpow₀, map_natCast, norm_zpow, hl, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
        inv_zpow', ← Real.rpow_intCast]
      congr 1
      have h2 : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast q.mul_den_eq_num
      push_cast
      rw [neg_mul, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hl0.le _) q.den_ne_zero).1 h1

theorem sz_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam (-r) (x : ℂ) :=
  ⟨x.2, hx.le⟩

theorem sz_inv_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam r (x : ℂ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨inv_mem x.2, ?_⟩
  have e : (⟨(x : ℂ)⁻¹, inv_mem x.2⟩ : algebraicClosure ℚ ℂ) = x⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, hx, Real.rpow_neg hl0.le, inv_inv]

theorem exists_sz_scale : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ,
    ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  intro l _ lam q
  obtain ⟨x, hx0, hx⟩ := exists_algebraic_norm_eq_rpow l lam q
  exact ⟨x, fun h => hx0 (Subtype.ext h), sz_of_norm_eq hx, sz_inv_of_norm_eq hx⟩

end GlobalTheory.QFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuationStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_of_rational_valuation : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ, ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  first | exact @GlobalTheory.QFam.exists_sz_scale | exact GlobalTheory.QFam.exists_sz_scale | (intros; apply GlobalTheory.QFam.exists_sz_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
namespace GlobalTheory.LFun

theorem norm_le_card_of_heckeVec_eq_smul :
    ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) →
      (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) →
      {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x →
      ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  intro G _ K V _ _ ρ Bf hsym hpos hinv h x c hh hfin hx hc
  classical
  have hnn : ∀ y, 0 ≤ (Bf y y).re := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by rw [hsym x y]; simp
      re_inner_nonneg := hnn
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have cs : ∀ y, ‖Bf x y‖ * ‖Bf y x‖ ≤ (Bf x x).re * (Bf y y).re :=
    fun y => @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ core x y
  have hr : 0 < (Bf x x).re := hpos x hx
  have hb : ∀ g, ‖Bf x (ρ g x)‖ ≤ (Bf x x).re := by
    intro g
    have h1 := cs (ρ g x)
    rw [hinv, hsym x (ρ g x), RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (Bf x (ρ g x))]
  have hxx : ‖Bf x x‖ = (Bf x x).re := by
    have e : (starRingEnd ℂ) (Bf x x) = Bf x x := (hsym x x).symm
    rw [RCLike.conj_eq_iff_re] at e
    rw [← e]
    simp [abs_of_pos hr]
  set S := hfin.toFinset
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ S := by
    intro q hq
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ S, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  have key : c * Bf x x = ∑ q ∈ S, h q.out * Bf x (ρ q.out x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← smul_eq_mul, ← map_smul, ← hc, hsum, map_sum]
    simp
  have hcard : Nat.card {q : G ⧸ K // h q.out ≠ 0} = S.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hle : ‖c‖ * (Bf x x).re ≤ (S.card : ℝ) * (Bf x x).re := by
    calc ‖c‖ * (Bf x x).re = ‖c * Bf x x‖ := by rw [norm_mul, hxx]
      _ = ‖∑ q ∈ S, h q.out * Bf x (ρ q.out x)‖ := by rw [key]
      _ ≤ ∑ q ∈ S, ‖h q.out * Bf x (ρ q.out x)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, (Bf x x).re := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        calc ‖h q.out‖ * ‖Bf x (ρ q.out x)‖ ≤ 1 * (Bf x x).re :=
              mul_le_mul (hh _) (hb _) (norm_nonneg _) zero_le_one
          _ = (Bf x x).re := one_mul _
      _ = (S.card : ℝ) * (Bf x x).re := by simp
  rw [hcard]
  exact le_of_mul_le_mul_right hle hr

end GlobalTheory.LFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosetsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets : ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) → (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) → {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x → ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  first | exact @GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | exact GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul | (intros; apply GlobalTheory.LFun.norm_le_card_of_heckeVec_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPow
open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  let A := G.A n
  let S := ULift.{0} R
  let σ : R →+* S := ULift.ringEquiv.symm.toRingHom.comp (frobRing h)
  let : Algebra R S := σ.toAlgebra
  let : Module R S := Algebra.toModule
  let : SMul R S := Algebra.toSMul
  have hA : (p : A) = 0 := natCast_eq_zero_of_algebra h A
  -- With Frobenius acting on the target scalars, precomposition by the pth power is linear.
  let pullPow (φ : CartierDual R A) : WithConv (A →ₗ[R] S) := toConv
    { toFun := fun x => ULift.up (φ (x ^ p))
      map_add' := fun x y => by
        change ULift.up (φ.ofConv ((x + y) ^ p)) =
          ULift.up (φ.ofConv (x ^ p) + φ.ofConv (y ^ p))
        rw [← frobRing_apply hA (x + y), map_add, map_add, frobRing_apply, frobRing_apply]
      map_smul' := fun r x => by
        change ULift.up (φ.ofConv ((r • x) ^ p)) = r • ULift.up (φ.ofConv (x ^ p))
        rw [smul_pow, φ.ofConv.map_smul, Algebra.smul_def (R := R) (A := S)]
        change ULift.up (r ^ p * φ.ofConv (x ^ p)) =
          ULift.up (frobRing h r * φ.ofConv (x ^ p))
        rw [frobRing_apply] }
  let pull : CartierDual R A →* WithConv (A →ₗ[R] S) :=
    { toFun := pullPow
      map_one' := WithConv.ext (LinearMap.ext fun x => by
        change ULift.up ((1 : CartierDual R A) (x ^ p)) = (1 : WithConv (A →ₗ[R] S)) x
        rw [LinearMap.convOne_apply, LinearMap.convOne_apply, counit_pow]
        change ULift.up (counit (R := R) x ^ p) = ULift.up (frobRing h (counit x))
        rw [frobRing_apply])
      map_mul' := fun φ ψ => WithConv.ext (LinearMap.ext fun x => by
        let d := Coalgebra.Repr.arbitrary R x
        let dPow : Coalgebra.Repr R (x ^ p) (A × A) :=
          ⟨d.index, fun i => d.left i ^ p, fun i => d.right i ^ p, by
            rw [comul_pow, ← d.eq,
              ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A)), map_sum]
            simp only [frobRing_apply, Algebra.TensorProduct.tmul_pow]⟩
        change ULift.up ((φ * ψ) (x ^ p)) = (pullPow φ * pullPow ψ) x
        rw [dPow.convMul_apply, d.convMul_apply]
        exact map_sum ULift.ringEquiv.symm (fun i => φ (d.left i ^ p) * ψ (d.right i ^ p)) d.index) }
  obtain ⟨s, hs⟩ := exists_dualSystem R A
  have hmul : mulBy R A p a = ∑ i ∈ s, (i.1 ^ p) a • i.2 ^ p := by
    have he := BialgHom.toLinearMap_convPow (toConv (BialgHom.id R A)) p
    exact (congrArg (fun f : WithConv (A →ₗ[R] A) => f a) he).trans
      (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun x => (hs x).symm) a)
  let f := (pull χ).ofConv
  have hf (x : A) : f x = ∑ i ∈ s, i.1 x • f i.2 := by
    simpa only [map_sum, map_smul] using congrArg f (hs x).symm
  let g : A →ₗ[R] S := (Algebra.linearMap R S).comp χ.ofConv
  have hg (x : A) : f x ^ p = g (x ^ p) := by
    change ULift.up (χ (x ^ p) ^ p) = ULift.up (frobRing h (χ (x ^ p)))
    rw [frobRing_apply]
  have e : pull (χ ^ p) a = g (mulBy R A p a) := by
    rw [map_pow]
    change (toConv f ^ p) a = _
    rw [convPow_prime_apply h s Prod.fst (fun i => f i.2) f hf a, hmul, map_sum]
    simp only [map_smul, hg]
  exact (congrArg ULift.down e).trans (frobRing_apply h _)

theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualConvPowPrimePowApplyPowStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_convPow_primePow_apply_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n), (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  first | exact @GlobalTheory.PDivGroup.convPow_primePow_apply_pow | exact GlobalTheory.PDivGroup.convPow_primePow_apply_pow | (intros; apply GlobalTheory.PDivGroup.convPow_primePow_apply_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.OnePair.coeff_subst_kill {σ R : Type} [CommRing R] [Finite σ] (p : σ → Prop)
    [DecidablePred p] (c : MvPowerSeries σ R) (γ : σ →₀ ℕ) [Decidable (∀ s, ¬ p s → γ s = 0)] :
    coeff γ (subst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) c) =
      if ∀ s, ¬ p s → γ s = 0 then coeff γ c else 0 := by
  classical
  have hsub : HasSubst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) :=
    hasSubst_of_constantCoeff_zero fun s => by split_ifs <;> simp
  have key : ∀ d : σ →₀ ℕ,
      coeff γ (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
        if d = γ ∧ ∀ s, ¬ p s → γ s = 0 then 1 else 0 := by
    intro d
    by_cases hd : ∀ s, ¬ p s → d s = 0
    · have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
          monomial d 1 := by
        rw [monomial_one_eq]
        refine Finsupp.prod_congr fun s hs => ?_
        have hps : p s := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hs) (hd s h)
        rw [if_pos hps]
      rw [hprod, coeff_monomial]
      by_cases hγ : γ = d
      · subst hγ
        rw [if_pos rfl, if_pos ⟨rfl, hd⟩]
      · rw [if_neg hγ, if_neg fun h => hγ h.1.symm]
    · push_neg at hd
      obtain ⟨s, hps, hds⟩ := hd
      have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds) (by rw [if_neg hps, zero_pow hds])
      rw [hprod, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hds (h s hps)
  rw [coeff_subst hsub, finsum_eq_single _ γ]
  · rw [key]
    by_cases h : ∀ s, ¬ p s → γ s = 0 <;> simp [h]
  · intro d hd
    rw [key, if_neg fun h => hd h.1, smul_zero]

end OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.coeff_at2_single_X_inl_inr (R : Type) [CommRing R] (d : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (_root_.GlobalTheory.Katz.at2 c
      (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m)))) =
      if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  classical
  have hfun : Sum.elim (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m))) = fun s =>
        if (s = Sum.inl m ∨ s = Sum.inr m) then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0 := by
    funext s
    rcases s with i | i <;> by_cases h : i = m <;> simp [h, Pi.single_apply]
  have hiff : (∀ s, ¬ (s = Sum.inl m ∨ s = Sum.inr m) → γ s = 0) ↔
      γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) := by
    constructor
    · intro h
      ext s
      by_cases hs : s = Sum.inl m ∨ s = Sum.inr m
      · rcases hs with rfl | rfl <;> simp [Finsupp.single_apply]
      · push_neg at hs
        rw [h s (not_or.mpr hs)]
        simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
    · intro h s hs
      push_neg at hs
      rw [h]
      simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
  unfold _root_.GlobalTheory.Katz.at2
  rw [hfun, _root_.GlobalTheory.OnePair.coeff_subst_kill]
  by_cases hγ : γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (γ (Sum.inr m))
  · rw [if_pos hγ, if_pos (hiff.mpr hγ)]
  · rw [if_neg hγ, if_neg fun h => hγ (hiff.mp h)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePairStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m)))) = if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) + Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  first | exact @GlobalTheory.coeff_at2_single_X_inl_inr | exact GlobalTheory.coeff_at2_single_X_inl_inr | (intros; apply GlobalTheory.coeff_at2_single_X_inl_inr <;> assumption)
end
end
