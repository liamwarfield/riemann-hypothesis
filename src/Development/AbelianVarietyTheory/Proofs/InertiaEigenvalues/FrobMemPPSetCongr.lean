module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamilies
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem dpDen_mul_dvd_add (e i₁ i₂ n₁ n₂ : ℕ) :
    dpDen e i₁ n₁ * dpDen e i₂ n₂ ∣ dpDen e (i₁ + i₂) (n₁ + n₂) := by
  unfold dpDen
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂
  have h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))
  have h3 := mul_dvd_mul h1 h2
  rwa [mul_mul_mul_comm] at h3

theorem mul_mem_QSet_of_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2,
    ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) *
      (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩
  funext τ
  ext i n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_ofW, coeff_ofW]
  simp only [map_mul, map_natCast]
  have hd := dpDen_mul_dvd_add e q.1 q.2 r.1 r.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr] at hd
  have h1 : (dpDen e q.1 r.1 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h2 : (dpDen e q.2 r.2 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h3 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  rw [Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]
  push_cast
  field_simp

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMemCrystallinePrismDividedPowerFamiliesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  first | exact @GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | exact GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | (intros; apply GlobalTheory.CrysPrism.mul_mem_QSet_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBox
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBox
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem exists_eq_of_coeff_box_eq_zero {R : Type} [CommRing R] (i n : ℕ) (D : R⟦X⟧⟦X⟧)
    (h : ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' D) = 0) :
    ∃ A B : R⟦X⟧⟦X⟧, D = X ^ (i + 1) * A + C (X ^ (n + 1)) * B := by
  classical
  obtain ⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by
    refine ⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩
    ext m
    rw [coeff_X_pow_mul', coeff_mk]
    split_ifs with hm
    · rw [coeff_mk, Nat.sub_add_cancel hm]
    · exact (h k hk m (by omega)).symm
  have hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_C_mul, hlow k (by omega), sub_self]
  obtain ⟨A, hA⟩ := hdvd
  exact ⟨A, B, by rw [← hA]; ring⟩

theorem coeff_frob2_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  intro l _ K _ φ₂ hC hX i n G H h
  obtain ⟨A, B, hAB⟩ := exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by
    rw [map_sub, map_sub, h i' hi' n' hn', sub_self])
  obtain ⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by
    rw [hX, map_pow]
    have hd := sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l
    rwa [add_sub_cancel_left] at hd
  have hl : 1 ≤ l := (Fact.out : Nat.Prime l).one_lt.le
  have e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A) := by
    rw [map_mul, map_pow, hc]
    ring
  have e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B := by
    rw [map_mul, hC, map_pow, frob_X, ← pow_mul]
  have hz : coeff n (coeff i (φ₂ (G - H))) = 0 := by
    rw [hAB, map_add (f := _), e1, e2, map_add (f := _), map_add (f := _), coeff_X_pow_mul',
      if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul',
      if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]
  rwa [map_sub, map_sub, map_sub, sub_eq_zero] at hz

end GlobalTheory.CrysPrism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBoxStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_frobeniusDoublePowerSeries_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  first | exact @GlobalTheory.CrysPrism.coeff_frob2_congr_box | exact GlobalTheory.CrysPrism.coeff_frob2_congr_box | (intros; apply GlobalTheory.CrysPrism.coeff_frob2_congr_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectiv
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem injective_of_charZero {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {K : Type} [Field K] [CharZero K]
    (f : Wq l a →+* K) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l a) w h0
  rw [map_mul, map_pow, map_natCast] at hw
  have hb : f b ≠ 0 := (b.isUnit.map f).ne_zero
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact mul_ne_zero (pow_ne_zero m hl) hb hw

theorem emb_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact injective_of_charZero ((algebraMap O K).comp (emb t τ).toRingHom)

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectivStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWittEmbeddingTwisted_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  first | exact @GlobalTheory.CrysPrism.emb_algebraMap_injective | exact GlobalTheory.CrysPrism.emb_algebraMap_injective | (intros; apply GlobalTheory.CrysPrism.emb_algebraMap_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPow
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem zero_mem_QSet_goodU : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp

theorem uPow_mem_QSet_goodU [CharZero K] (m : ℕ) :
    (fun _ => C (X ^ m) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, m) then ((dpDen e 0 m : ℕ) : Wq l a) else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases h : (i, n) = (0, m)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have : (dpDen e 0 n : K) ≠ 0 := Nat.cast_ne_zero.mpr (dpDen_pos e 0 n).ne'
    simp only [if_true, map_natCast, coeff_X_pow_self]
    exact div_self this
  · rw [if_neg h]
    simp only [map_zero, zero_div]
    by_cases hi : i = 0
    · subst hi
      have hn : n ≠ m := fun hn => h (by rw [hn])
      rw [if_pos rfl, coeff_X_pow, if_neg hn]
    · rw [if_neg hi, map_zero]

end

theorem uFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hf : frob2 φ₂ (uFam a K) = (fun _ => C (X ^ l) : ZMod a → K⟦X⟧⟦X⟧) := by
    funext τ
    show φ₂ (C X) = _
    rw [hC, frob_X]
  refine ⟨?_, ?_, 0, zero_mem_QSet_goodU t K e, ?_⟩
  · have := uPow_mem_QSet_goodU t K e 1
    rw [pow_one] at this
    exact this
  · rw [hf]; exact uPow_mem_QSet_goodU t K e l
  · rw [hf, mul_zero, add_zero]
    funext τ
    simp [uFam]

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizerFamily_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.uFam_mem_GoodSet | exact GlobalTheory.CrysPrism.uFam_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.uFam_mem_GoodSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeries
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.FinSupp

section
variable {K : Type} [CommRing K]

def Bd (M : ℕ) (F : K⟦X⟧⟦X⟧) : Prop := ∀ i n, M < i ∨ M < n → coeff n (coeff i F) = 0

theorem Bd.mono {M M' : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) (hM : M ≤ M') : Bd M' F :=
  fun i n hin => h i n (by omega)

theorem Bd.mul {M M' : ℕ} {F G : K⟦X⟧⟦X⟧} (h : Bd M F) (h' : Bd M' G) : Bd (M + M') (F * G) := by
  intro i n hin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : M < p.1 ∨ M < q.1
  · rw [h _ _ h1, zero_mul]
  · rw [h' _ _ (by omega), mul_zero]

theorem bd_CC (c : K) : Bd 0 (C (C c) : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_C, if_neg (by omega)]
  · simp

theorem bd_CX : Bd 1 (C X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_X, if_neg (by omega)]
  · simp

theorem bd_X : Bd 1 (X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_X]
  split_ifs with h
  · rw [coeff_one, if_neg (by omega)]
  · simp


variable (K) in
def fin : Subring K⟦X⟧⟦X⟧ where
  carrier := {F | ∃ M, Bd M F}
  mul_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨_, h.mul h'⟩
  one_mem' := ⟨0, by simpa using bd_CC (1 : K)⟩
  add_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨M + M', fun i n hin => by
      rw [map_add (f := _), map_add (f := _), h i n (by omega), h' i n (by omega), add_zero]⟩
  zero_mem' := ⟨0, fun i n _ => by simp⟩
  neg_mem' := by
    rintro F ⟨M, h⟩
    exact ⟨M, fun i n hin => by rw [map_neg, map_neg, h i n hin, neg_zero]⟩

theorem Bd.eq_sum {M : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) :
    F = ∑ i ∈ Finset.range (M + 1), C (∑ n ∈ Finset.range (M + 1),
      C (coeff n (coeff i F)) * X ^ n) * X ^ i := by
  ext i n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum (coeff i), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hi : i < M + 1
  · simp only [if_pos hi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum (coeff n), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hn
    · rfl
    · exact h i n (by omega)
  · simp only [if_neg hi, map_zero]
    exact h i n (by omega)

theorem map_mem (φ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (h1 : ∀ c : K, φ (C (C c)) ∈ fin K)
    (h2 : φ (C X) ∈ fin K) (h3 : φ X ∈ fin K) {F : K⟦X⟧⟦X⟧} (hF : F ∈ fin K) : φ F ∈ fin K := by
  obtain ⟨M, h⟩ := hF
  rw [h.eq_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow]
  refine sum_mem fun i _ => mul_mem (sum_mem fun n _ => mul_mem (h1 _) (pow_mem h2 _)) (pow_mem h3 _)

theorem unif {ι : Type} [Finite ι] (F : ι → K⟦X⟧⟦X⟧) (h : ∀ τ, F τ ∈ fin K) : ∃ M, ∀ τ, Bd M (F τ) := by
  choose M hM using h
  obtain ⟨B, hB⟩ := (Set.finite_range M).bddAbove
  exact ⟨B, fun τ => (hM τ).mono (hB ⟨τ, rfl⟩)⟩

end

theorem exists_coeff_frob2_ofW_and_pow_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX N w hw
  have hF : ∀ τ, ofW t K e w τ ∈ fin K := fun τ => ⟨N, fun i n hin => by
    rw [coeff_ofW, hw i n hin]; simp⟩
  have hCX : (C X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_CX⟩
  have hX' : (X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_X⟩
  obtain ⟨M, hM⟩ := unif (frob2 φ₂ (ofW t K e w)) fun τ => by
    change φ₂ (ofW t K e w (τ - 1)) ∈ _
    refine map_mem φ₂ (fun c => ?_) ?_ ?_ (hF _)
    · have : frob K l (C c) = C c := (frob K l).commutes c
      rw [hC, this]; exact ⟨_, bd_CC c⟩
    · rw [hC, frob_X, map_pow]; exact pow_mem hCX _
    · rw [hX, map_pow]; exact sub_mem (pow_mem (add_mem hCX hX') _) (pow_mem hCX _)
  obtain ⟨M', hM'⟩ := unif (ofW t K e w ^ l) fun τ => pow_mem (hF τ) l
  exact ⟨M + M', fun τ i n hin => ⟨hM τ i n (by omega), hM' τ i n (by omega)⟩⟩

end GlobalTheory.CrysPrism.FinSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeriesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  first | exact @GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | exact GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | (intros; apply GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBox
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBox
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory

theorem coeff_coeff_pow_eq_of_box :
    ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧),
      (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  intro R _ m i n G H h
  induction m generalizing i n with
  | zero => simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨s, t⟩ hst
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hst
    dsimp only at hpq hst ⊢
    rw [ih p s (fun i' hi' n' hn' => h i' (by omega) n' (by omega)), h q (by omega) t (by omega)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffCoeffPowEqOfBoxStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le : ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  first | exact @GlobalTheory.coeff_coeff_pow_eq_of_box | exact GlobalTheory.coeff_coeff_pow_eq_of_box | (intros; apply GlobalTheory.coeff_coeff_pow_eq_of_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffFamilyFrobeniusCongrPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffFamilyFrobeniusCongrPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem cstW_mem_QSet_of_const (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, 0) then c else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp only [cstW, coeff_C]
  by_cases hi : i = 0
  · by_cases hn : n = 0
    · simp [hi, hn, dpDen]
    · simp [hi, hn, coeff_C]
  · simp [hi]

theorem exists_sigma_eq_pow_add (c : Wq l a) : ∃ d : Wq l a, sigma l a c = c ^ l + (l : Wq l a) * d := by
  have h : sigma l a c - c ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, coeff_sigma, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
  exact ⟨d, by rw [← hd]; ring⟩

end

theorem cstW_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ c
  have h1 : frob2 φ₂ (cstW t K c) = cstW t K (sigma l a c) := by
    funext τ
    change φ₂ (cstW t K c (τ - 1)) = _
    simp only [cstW]
    rw [hC, frob_C, emb_sigma]
  refine ⟨cstW_mem_QSet_of_const t K e c, h1 ▸ cstW_mem_QSet_of_const t K e _, ?_⟩
  obtain ⟨d, hd⟩ := exists_sigma_eq_pow_add c
  refine ⟨cstW t K d, cstW_mem_QSet_of_const t K e d, ?_⟩
  rw [h1, hd]
  funext τ
  simp [cstW]

end GlobalTheory.CrysPrism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffFamilyFrobeniusCongrPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeffFamily_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.cstW_mem_GoodSet | exact GlobalTheory.CrysPrism.cstW_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.cstW_mem_GoodSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem ofW_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t i n c
  funext τ
  have hR : (cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i) τ
      = C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i := by
    simp only [Pi.mul_apply, Pi.pow_apply, cstW, uFam, dFam, xFam]
    have h1 : (X : K⟦X⟧) ^ n = X ^ (n % e) * X ^ (e * (n / e)) := by
      rw [← pow_add, Nat.mod_add_div]
    rw [h1, dpDen, Nat.cast_mul, div_eq_mul_inv, mul_inv]
    simp only [map_mul, map_pow]
    ring
  rw [hR]
  ext i' n'
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow, Pi.single_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hn : n' = n
    · subst hn
      simp [coeff_C_mul, coeff_X_pow]
    · simp [coeff_C_mul, coeff_X_pow, hn]
  · simp [hi]

end GlobalTheory.CrysPrism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerFamily_single_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  first | exact @GlobalTheory.CrysPrism.ofW_single | exact GlobalTheory.CrysPrism.ofW_single | (intros; apply GlobalTheory.CrysPrism.ofW_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedUniformizerPowerFrobeniusCongrPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedUniformizerPowerFrobeniusCongrPow
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_pow_dvd_factorial_mul (q k : ℕ) : q.factorial ^ k ∣ (k * q).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_factorial_quot (l q : ℕ) (hl : 0 < l) :
    ∃ (A B : ℕ) (D : ℤ), A * q.factorial = (l * q).factorial ∧ B * q.factorial ^ l = (l * q).factorial ∧
      (A : ℤ) = B + l * D := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨1, 1, 0, by simp, by simp, by simp⟩
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc⟩ := factorial_pow_dvd_factorial_mul (p + 1) k
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (k * (p + 1)) (p + 1)
  have h2 := Nat.add_one_mul_choose_eq (k * (p + 1) + p) p
  have h3 : (k * (p + 1) + (p + 1)).choose (p + 1) = (k + 1) * (k * (p + 1) + p).choose p := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos p)
    rw [← add_assoc, ← h2]; simp only [Nat.succ_eq_add_one]; ring
  have h4 : (k + 1) * (p + 1) = k * (p + 1) + (p + 1) := by ring
  set m := (k * (p + 1) + p).choose p
  refine ⟨(k + 1) * m * (k * (p + 1)).factorial, (k + 1) * m * c,
    (m * (k * (p + 1)).factorial : ℕ) - (m * c : ℕ), ?_, ?_, ?_⟩
  · rw [h4, ← h1, h3]
  · rw [h4, ← h1, h3, hc]; ring
  · push_cast; ring

section

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ) [NeZero e]

theorem intCast_div_factorial_mem_QSet (z : ℤ) (m : ℕ) :
    (fun _ => C (C ((z : K) / (m.factorial : K)) * X ^ (e * m)) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  classical
  refine ⟨Pi.single (0, e * m) (z : Wq l a), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl, coeff_C_mul, coeff_X_pow]
    by_cases hn : n = e * m
    · subst hn
      simp [dpDen, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne e))]
    · rw [if_neg hn, Pi.single_eq_of_ne (by simpa using hn)]; simp
  · rw [if_neg hi, Pi.single_eq_of_ne (by simp [hi])]; simp

end

theorem dFam_mem_goodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ q
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨A, B, D, hA, hB, hD⟩ := exists_factorial_quot l q hl.out.pos
  have hq : (q.factorial : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hlq : ((l * q).factorial : K) ≠ 0 := by exact_mod_cast (l * q).factorial_ne_zero
  have hA' : (A : K) * q.factorial = (l * q).factorial := by exact_mod_cast hA
  have hB' : (B : K) * (q.factorial : K) ^ l = (l * q).factorial := by exact_mod_cast hB
  have hD' : (A : K) = B + l * D := by exact_mod_cast hD
  have eA : (q.factorial : K)⁻¹ = ((A : ℤ) : K) / (l * q).factorial := by
    rw [Int.cast_natCast]; field_simp; rw [← hA']; ring
  have eB : ((q.factorial : K)⁻¹) ^ l = (B : K) / (l * q).factorial := by
    rw [eq_div_iff hlq, ← hB', mul_left_comm, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  have hf : frob2 φ₂ (dFam a K e q) =
      fun _ => C (C (((A : ℤ) : K) / ((l * q).factorial : K)) * X ^ (e * (l * q))) := by
    funext τ
    change φ₂ (dFam a K e q (τ - 1)) = _
    simp only [dFam]
    rw [hC, map_mul, map_pow, frob_C, frob_X, ← pow_mul, eA]
    congr 3; ring
  refine ⟨?_, ?_, _, intCast_div_factorial_mem_QSet t K e D (l * q), ?_⟩
  · have := intCast_div_factorial_mem_QSet t K e 1 q
    rw [Int.cast_one, one_div] at this
    exact this
  · rw [hf]; exact intCast_div_factorial_mem_QSet t K e _ _
  · rw [hf]
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, dFam]
    rw [← map_pow, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_mul, ← map_add (f := _), mul_pow, ← map_pow, eB,
      ← pow_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc (C (l : K)), ← map_mul,
      show e * q * l = e * (l * q) by ring, ← add_mul, ← map_add, Int.cast_natCast, hD']
    congr 3; ring

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedUniformizerPowerFrobeniusCongrPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedUniformizerPower_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.dFam_mem_goodSet | exact GlobalTheory.CrysPrism.dFam_mem_goodSet | (intros; apply GlobalTheory.CrysPrism.dFam_mem_goodSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m i n : ℕ) (G : K⟦X⟧⟦X⟧) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * G)) = (m : K) * coeff n (coeff i G) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

theorem goodSet_of_finite_of_local (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hfin : ∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)),
      ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂)
    (hφ : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)))
    (hpow : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) :
    ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  classical
  rintro z ⟨w, rfl⟩
  have key : ∀ p : ℕ × ℕ, ∃ v b : Wq l a, ∀ τ : ZMod a,
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        algebraMap O K (emb t τ v) / (dpDen e p.1 p.2 : K) ∧
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        coeff p.2 (coeff p.1 ((ofW t K e w τ) ^ l)) +
          (l : K) * (algebraMap O K (emb t τ b) / (dpDen e p.1 p.2 : K)) := by
    rintro ⟨i, n⟩
    set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (n + 1) with hs
    obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hfin w s
    have hagree : ∀ τ : ZMod a, ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' (ofW t K e w τ)) =
        coeff n' (coeff i' (ofW t K e (fun p => if p ∈ s then w p else 0) τ)) := by
      intro τ i' hi n' hn
      have hm : (i', n') ∈ s := by
        simp only [hs, Finset.mem_product, Finset.mem_range]
        omega
      rw [coeff_ofW, coeff_ofW, if_pos hm]
    refine ⟨v (i, n), b (i, n), fun τ => ?_⟩
    have h1 : coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) =
        coeff n (coeff i (frob2 φ₂ (ofW t K e (fun p => if p ∈ s then w p else 0)) τ)) :=
      hφ i n _ _ (hagree (τ - 1))
    refine ⟨?_, ?_⟩
    · rw [h1, ← hv, coeff_ofW]
    · rw [h1, hB, hpow i n _ _ (hagree τ), Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
  choose v b hvb using key
  refine ⟨⟨w, rfl⟩, ⟨v, ?_⟩, ofW t K e b, ⟨b, rfl⟩, ?_⟩
  · funext τ
    ext i n
    rw [coeff_ofW]
    exact ((hvb (i, n) τ).1).symm
  · funext τ
    ext i n
    rw [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
    exact (hvb (i, n) τ).2

end GlobalTheory.CrysPrism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)), ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H))) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) → ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.goodSet_of_finite_of_local | exact GlobalTheory.CrysPrism.goodSet_of_finite_of_local | (intros; apply GlobalTheory.CrysPrism.goodSet_of_finite_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongr
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

namespace FrobPP

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O)

theorem coeff_natCast_mul_double {R : Type} [CommRing R] (m : ℕ) (G : R⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : R⟦X⟧⟦X⟧) * G)) = (m : R) * coeff n (coeff i G) := by
  rw [← map_natCast (C : R⟦X⟧ →+* R⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : R →+* R⟦X⟧), coeff_C_mul]

theorem ofW_add (w w' : ℕ × ℕ → Wq l a) : ofW t K e (w + w') = ofW t K e w + ofW t K e w' := by
  funext τ; ext i n; simp [coeff_ofW, add_div]

theorem ofW_zero : ofW t K e (0 : ℕ × ℕ → Wq l a) = 0 := by
  funext τ; ext i n; simp [coeff_ofW]

theorem ofW_neg (w : ℕ × ℕ → Wq l a) : ofW t K e (-w) = -ofW t K e w := by
  funext τ; ext i n; simp [coeff_ofW, neg_div]


variable (K e) in
def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) where
  toFun := ofW t K e
  map_zero' := ofW_zero t
  map_add' := ofW_add t

theorem Q_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; obtain ⟨w', rfl⟩ := hy; exact ⟨w + w', ofW_add t w w'⟩

theorem Q_neg {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; exact ⟨-w, ofW_neg t w⟩

theorem Q_sub {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x - y ∈ QSet t K e := by
  rw [sub_eq_add_neg]; exact Q_add t hx (Q_neg t hy)

theorem Q_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := ⟨0, ofW_zero t⟩

theorem Q_natCast (m : ℕ) : (m : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨Pi.single (0, 0) (m : Wq l a), funext fun τ => ?_⟩
  ext i n
  rw [coeff_ofW, Pi.natCast_apply, ← mul_one ((m : K⟦X⟧⟦X⟧)), coeff_natCast_mul_double]
  rcases i with _ | i <;> rcases n with _ | n <;> simp [dpDen, Pi.single_apply, coeff_one]

theorem Q_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x * y ∈ QSet t K e :=
  GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies l a e O K t x hx y hy

theorem Q_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (k : ℕ) : x ^ k ∈ QSet t K e := by
  induction k with
  | zero => simpa using Q_natCast t (K := K) (e := e) 1
  | succ k ih => rw [pow_succ]; exact Q_mul t ih hx

theorem Q_sum {ι : Type} (s : Finset ι) (f : ι → ZMod a → K⟦X⟧⟦X⟧) (h : ∀ i ∈ s, f i ∈ QSet t K e) :
    ∑ i ∈ s, f i ∈ QSet t K e :=
  Finset.sum_induction f (· ∈ QSet t K e) (fun _ _ => Q_add t) (Q_zero t) h

variable {φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧}

theorem good_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x + y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_add t hxQ hyQ, by rw [map_add (f := _)]; exact Q_add t hfxQ hfyQ,
    A + B - x * y * ∑ k ∈ Finset.Ioo 0 l, x ^ (k - 1) * y ^ (l - k - 1) * ((l.choose k / l : ℕ) : ZMod a → K⟦X⟧⟦X⟧),
    ?_, ?_⟩
  · exact Q_sub t (Q_add t hA hB) (Q_mul t (Q_mul t hxQ hyQ) (Q_sum t _ _ fun k _ =>
      Q_mul t (Q_mul t (Q_pow t hxQ _) (Q_pow t hyQ _)) (Q_natCast t _)))
  · rw [map_add (f := _), hxA, hyB, add_pow_prime_eq hl.out]; ring

theorem good_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x * y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_mul t hxQ hyQ, by rw [map_mul]; exact Q_mul t hfxQ hfyQ,
    A * y ^ l + B * x ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * A * B, ?_, ?_⟩
  · exact Q_add t (Q_add t (Q_mul t hA (Q_pow t hyQ _)) (Q_mul t hB (Q_pow t hxQ _)))
      (Q_mul t (Q_mul t (Q_natCast t _) hA) hB)
  · rw [map_mul, hxA, hyB]; ring

theorem good_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨Q_zero t, by rw [map_zero]; exact Q_zero t, 0, Q_zero t, by simp [zero_pow hl.out.ne_zero]⟩

theorem good_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨by simpa using Q_natCast t (K := K) (e := e) 1, by rw [map_one]; simpa using Q_natCast t (K := K) (e := e) 1,
    0, Q_zero t, by simp⟩

theorem good_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (k : ℕ) : x ^ k ∈ GoodSet t e φ₂ := by
  induction k with
  | zero => rw [pow_zero]; exact good_one t
  | succ k ih => rw [pow_succ]; exact good_mul t ih hx

theorem good_fin (hφC : ∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) (hφX : φ₂ X = (C X + X) ^ l - C (X ^ l))
    (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)) :
    ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂ := by
  have h : (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, Pi.single p (w p) := by
    funext q; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq']
  have h2 : ofW t K e (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, ofW t K e (Pi.single p (w p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h]; exact map_sum (ofWHom (K := K) (e := e) t) _ s
  rw [h2]
  refine Finset.sum_induction _ (· ∈ GoodSet t e φ₂) (fun _ _ => good_add t) (good_zero t) fun p _ => ?_
  rw [GlobalTheory.T.dividedPowerFamily_single_eq_mul l a e O K t p.1 p.2 (w p)]
  exact good_mul t (good_mul t (good_mul t (GlobalTheory.T.constantCoeffFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX _)
    (good_pow t (GlobalTheory.T.uniformizerFamily_frobenius_congr_pow l a e O K t φ₂ hφC hφX) _)) (GlobalTheory.T.dividedUniformizerPower_frobenius_congr_pow l a e O K t φ₂ hφC hφX _))
    (GlobalTheory.T.dividedVariablePower_frobenius_congr_pow l a e O K t φ₂ hφC hφX (fun x hx y hy => Q_mul t hx hy) _)

theorem ofW_mem_PPSet {w : ℕ × ℕ → Wq l a} (hw : LTo0 l w) : ofW t K e w ∈ PPSet t K e := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨w, hw, fun τ i n => ?_⟩
  rw [coeff_ofW]
  have : ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  exact mul_div_cancel₀ _ this

end Main

theorem frob_mem_PPSet_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh φ₂ hφC hφsh F hF
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hφX : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    have h2 : φ₂ X = sh (X ^ l) - C (X ^ l) := by rw [h, map_sub, hφsh, hφC, frob_X]
    rw [h2, map_pow, sh_X sh hsh]
  obtain ⟨w, hw, hFw⟩ := hF
  have hF' : F = ofW t K e w := funext fun τ => by
    ext i n
    have h0 : ((dpDen e i n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
    rw [coeff_ofW, eq_div_iff h0, mul_comm]
    exact hFw τ i n
  have hQ := GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower l a e O K t φ₂ (good_fin t hφC hφX) (GlobalTheory.T.coeff_frobeniusDoublePowerSeries_congr_box l K φ₂ hφC hφX) (fun i n G H => GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le K l i n G H)
  obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hQ F ⟨w, hF'.symm⟩
  rw [hF'] at hv hB ⊢
  obtain ⟨hv0, hb0⟩ := GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower l a e O K t φ₂ (GlobalTheory.T.unramifiedWittEmbeddingTwisted_algebraMap_injective l a e O K t) (fun x hx y hy => Q_mul t hx hy) hQ
    (GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries l a e O K t φ₂ hφC hφX) w hw v b hv.symm hB
  exact ⟨hv ▸ ofW_mem_PPSet t hv0, ofW t K e b, ofW_mem_PPSet t hb0, hB⟩

end FrobPP

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongrStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | exact GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr | (intros; apply GlobalTheory.CrysPrism.FrobPP.frob_mem_PPSet_congr <;> assumption)
end
