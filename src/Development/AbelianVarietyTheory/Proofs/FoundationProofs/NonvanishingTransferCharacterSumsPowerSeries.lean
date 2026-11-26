module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.MapEvalOfFixCoeff
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tval_coe (Q : Polynomial (Qbar l)) {N : ℕ} (hN : Q.natDegree < N) (z : Qbar l) :
    tval (Q : PowerSeries (Qbar l)) N z = Q.eval (z - 1) := by
  rw [Polynomial.eval_eq_sum_range' hN]
  simp only [tval, Polynomial.coeff_coe]

theorem tval_dirac {y N : ℕ} (hN : y < N) (z : Qbar l) : tval ((1 + PowerSeries.X) ^ y) N z = z ^ y := by
  have h : (((1 + Polynomial.X) ^ y : Polynomial (Qbar l)) : PowerSeries (Qbar l)) = (1 + PowerSeries.X) ^ y := by simp
  rw [← h, tval_coe _ (lt_of_le_of_lt _ hN)]
  · simp
  · refine Polynomial.natDegree_pow_le.trans ?_
    rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]

theorem mass_dirac {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x y : ℕ} (hx : x < l ^ r) (hy : y < l ^ r) :
    mass ((1 + PowerSeries.X) ^ y) r ξ x = if x = y then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero (by omega)
  have hy' : y < l ^ (3 * r) := hy.trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have e : ∀ k, ξ ^ (l ^ r - (k * x) % l ^ r) * tval ((1 + PowerSeries.X) ^ y) (l ^ (3 * r)) (ξ ^ k) = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    rw [tval_dirac hy', pow_sub₀ _ h0 (Nat.mod_lt _ (by omega)).le, hξ.pow_eq_one,
      ← pow_eq_pow_mod _ hξ.pow_eq_one, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm x k, mul_comm y k]
    field_simp
  simp only [mass, e]
  split_ifs with h1
  · subst h1; simp [h0]
  · have hne : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0)] at h
      exact h1 (hξ.pow_inj hx hy h.symm)
    have := mul_geom_sum (ξ ^ y / ξ ^ x) (l ^ r)
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm x, mul_comm y, pow_mul, pow_mul, hξ.pow_eq_one, one_pow, one_pow, div_one,
      sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombination
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem tval_eq_sum_pow_of_integral : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  intro l _ c F N hF
  let Q : Polynomial c.O := ∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n
  refine ⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩
  have hdeg : Q.natDegree < N ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · left
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)
      calc n * (Polynomial.X - Polynomial.C (1 : c.O)).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)
        _ ≤ k := by omega
  rcases hdeg with hd | rfl
  · have h1 := Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd
    have h2 : Polynomial.aeval z Q = tval F N z := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Q, tval, map_sum]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  · simp [tval]

end GlobalTheory.KZ.Cmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombinationStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_shifted_series_eq_integral_poly_combination : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  first | exact @GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | exact GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | (intros; apply GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvPrim
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  classical
  have h1 : ∀ a b : ZMod n, e (b * a) * e⁻¹ b = e (b * (a - 1)) := by
    intro a b
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc gaussSum χ e * gaussSum χ⁻¹ e⁻¹
      = ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
        rw [show gaussSum χ⁻¹ e⁻¹ = ∑ b, χ⁻¹ b * e⁻¹ b from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum_mulShift_of_isPrimitive e hχ]
        ring
    _ = ∑ b, ∑ a, χ a * e (b * (a - 1)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.mulShift_apply, mul_assoc, h1]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod n) : K) else 0) := by
        simp_rw [AddChar.sum_mulShift _ he, Nat.cast_ite, Nat.cast_zero]
    _ = n := by
        simp [sub_eq_zero, ZMod.card]

end GlobalTheory.KummerEisensteinGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp

theorem sum_mulChar_eq_sum_units {K : Type} [CommRing K] {n : ℕ} (ψ : MulChar (ZMod n) K)
    (f : ZMod n → K) [Fintype (ZMod n)] :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun a _ h => by
    by_contra hu; exact h (by rw [MulChar.map_nonunit ψ hu, zero_mul]))]
  refine (Finset.sum_nbij' (fun b : (ZMod n)ˣ => (b : ZMod n)) (fun a => if h : IsUnit a then h.unit else 1)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro b _; simp
  · intro a _; simp
  · intro b _; simp
  · intro a ha
    have hu : IsUnit a := (Finset.mem_filter.1 ha).2
    simp [hu]
  · intro b _; rfl

theorem gSum_mul_gSum_inv_prim : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l)
    (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive →
    gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  intro l _ m z ψ hz hψ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e : AddChar (ZMod (l ^ m)) (Qbar l) := AddChar.zmodChar (l ^ m) hz.pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root (l ^ m) hz
  have h1 : gSum m z ψ = gaussSum ψ e := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.zmodChar_apply]
  have h2 : gSum m z⁻¹ ψ⁻¹ = gaussSum ψ⁻¹ e⁻¹ := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.inv_apply', AddChar.zmodChar_apply, inv_pow]
  rw [h1, h2, GlobalTheory.KummerEisensteinGalois.gaussSum_mul_gaussSum_inv_prim hψ he]
  push_cast
  rfl

end GlobalTheory.KZ.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  first | exact @GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | exact GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | (intros; apply GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AmiceRiemannSumCongrDiracCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AmiceRiemannSumCongrDiracCoefficients
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.RiemannDirac

variable {l : ℕ} [Fact l.Prime]

theorem norm_tval_sub_tval_le (F : PowerSeries (Qbar l)) (hF : ∀ n, ‖F.coeff n‖ ≤ 1) {z : Qbar l} (hz : ‖z - 1‖ ≤ 1)
    {M N : ℕ} (h : M ≤ N) : ‖tval F N z - tval F M z‖ ≤ ‖z - 1‖ ^ M := by
  unfold tval
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hz (Finset.mem_Ico.1 hn).1)

theorem sum_root_pow {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) (j : ℕ) :
    ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * (ξ ^ k) ^ j =
      if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  rw [← mass_dirac hξ hx (Nat.mod_lt j hpos)]
  unfold mass
  refine Finset.sum_congr rfl fun k _ => ?_
  have hy : j % l ^ r < l ^ (3 * r) :=
    (Nat.mod_lt j hpos).trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [tval_dirac hy, ← pow_eq_pow_mod j h1]

theorem norm_mass_sub_le {F : PowerSeries (Qbar l)} {a : ℕ → Qbar l} {N r : ℕ} {ξ : Qbar l} (hN : l ^ (3 * r) ≤ N)
    (hF : ∀ n, ‖F.coeff n‖ ≤ 1) (ht : ∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j)
    (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) :
    ‖mass F r ξ x - ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤
      ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hn : ‖ξ‖ = 1 := by
    have h1 := congrArg norm hξ.pow_eq_one
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  have e : ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) =
      ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval F N (ξ ^ k) := by
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_root_pow hξ hx j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, mass, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [← mul_sub, norm_mul, norm_pow ξ, hn, one_pow, one_mul, norm_sub_rev]
  exact (norm_tval_sub_tval_le F hF (GlobalTheory.AmiceDist.norm_sub_one_le h1) hN).trans
    (GlobalTheory.AmiceDist.norm_sub_one_pow_three_le h1)

theorem norm_term_sub_le (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ‖∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
        φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
      (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hd : l ∣ l ^ r := dvd_pow_self l (by omega)
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hc : ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l) := by
      rw [← ZMod.natCast_mod (j % l ^ r) l, Nat.mod_mod_of_dvd _ hd, ZMod.natCast_mod]
    obtain ⟨c, hc'⟩ := ((Nat.mod_modEq j (l ^ r)).pow e).symm.dvd
    have h2 : ((j % l ^ r : ℕ) : Qbar l) ^ e - (j : Qbar l) ^ e = (l : Qbar l) ^ r * (c : Qbar l) := by
      have := congrArg (Int.cast : ℤ → Qbar l) hc'
      simpa only [Int.cast_sub, Int.cast_natCast, Nat.cast_pow, Int.cast_mul, Int.cast_pow] using this
    have h3 : φ ((j % l ^ r : ℕ) : ZMod l) * ((j % l ^ r : ℕ) : Qbar l) ^ e * (l : Qbar l) ^ r -
        (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e) =
        (l : Qbar l) ^ (2 * r) * (φ (j : ZMod l) * (c : Qbar l)) := by
      rw [hc]
      linear_combination (φ (j : ZMod l) * (l : Qbar l) ^ r) * h2
    rw [h3, norm_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _))
  · have h1 : l ∣ j := by
      rw [Finset.mem_filter, Finset.mem_range] at h
      by_contra h0
      exact h ⟨Nat.mod_lt j hpos, fun h' => h0 ((Nat.dvd_mod_iff hd).1 h')⟩
    rw [(ZMod.natCast_eq_zero_iff j l).2 h1, MulChar.map_zero]
    simp only [zero_mul, mul_zero, sub_zero, norm_zero, norm_nonneg]

theorem rSum_cg : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l))
    (a : ℕ → Qbar l) (N r : ℕ) (ξ : Qbar l), 1 ≤ r → l ^ (3 * r) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ j, ‖a j‖ ≤ 1) →
    (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot ξ (l ^ r) →
    Cg (2 * r) (rSum φ e F r ξ)
      ((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
  intro l _ φ e F a N r ξ hr hN hF ha ht hξ
  have h1 : ‖rSum φ e F r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    rw [rSum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x hx => ?_
    rw [← mul_sub, norm_mul, norm_mul, norm_pow (x : Qbar l)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)))).trans
      (norm_mass_sub_le hN hF ht hξ (Finset.mem_range.1 (Finset.mem_filter.1 hx).1))
  have h2 : ‖(∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)) -
      (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    have e1 : (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
        (a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0))) -
        (l : Qbar l) ^ r * (a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) =
        a j * (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
          (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun x _ => by ring
      · ring
    rw [e1, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha j)).trans (norm_term_sub_le φ e hr j)
  unfold Cg
  rw [← sub_add_sub_cancel]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

end GlobalTheory.KZ.Cmp.RiemannDirac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AmiceRiemannSumCongrDiracCoefficientsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amiceRiemannSum_congr_dirac_coefficients : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N r : ℕ) (ξ : Qbar l), 1 ≤ r → l ^ (3 * r) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ j, ‖a j‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot ξ (l ^ r) → Cg (2 * r) (rSum φ e F r ξ) ((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
  first | exact @GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg | exact GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg | (intros; apply GlobalTheory.KZ.Cmp.RiemannDirac.rSum_cg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDirac
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimCharMulRootPowModPow
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zpow_eq_zpow_of_intCast_eq {K : Type} [Field K] {ξ : K} {N : ℕ} (h0 : ξ ≠ 0)
    (h : ξ ^ N = 1) {k j : ℤ} (hkj : (k : ZMod N) = (j : ZMod N)) : ξ ^ k = ξ ^ j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkj
  obtain ⟨q, hq⟩ := hkj
  have hj : j = k + (N : ℤ) * q := by linarith
  rw [hj, zpow_add₀ h0, zpow_mul, zpow_natCast, h, one_zpow, mul_one]

theorem sum_zmod_val_eq_sum_range {K : Type} [Field K] (N : ℕ) [NeZero N] (G : ℕ → K) :
    ∑ r : ZMod N, G r.val = ∑ k ∈ Finset.range N, G k := by
  refine Finset.sum_nbij' (fun f => f.val) (fun v => (v : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro f _; simpa using ZMod.val_lt f
  · intro v _; simp
  · intro f _; simp
  · intro v hv; exact ZMod.val_cast_of_lt (by simpa using hv)
  · intro f _; rfl

theorem sum_range_mul_split {K : Type} [Field K] (G : ℕ → K) (b c : ℕ) :
    ∑ k ∈ Finset.range (b * c), G k = ∑ t ∈ Finset.range c, ∑ a ∈ Finset.range b, G (a + b * t) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [add_comm]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem sum_primChar_mul_rootPow_mod_pow : ∀ (K : Type) [Field K] [CharZero K] (l m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)] (ζ : K) (ψ : DirichletCharacter K (l ^ m)), l.Prime → 1 ≤ m → m ≤ n → IsPrimitiveRoot ζ (l ^ n) → ψ.IsPrimitive → ∀ X : ℤ, ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X) = if (l : ℤ) ^ (n - m) ∣ X then (l : K) ^ (n - m) * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) * ψ⁻¹ ((X / (l : ℤ) ^ (n - m) : ℤ) : ZMod (l ^ m)) else 0 := by
  intro K _ _ l m n _ _ ζ ψ hl hm hmn hζ hψ X
  have hl0 : 0 < l := hl.pos
  have hN : l ^ n = l ^ (n - m) * l ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  have hN' : l ^ n = l ^ m * l ^ (n - m) := by rw [hN, mul_comm]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  set F : ℕ → K := fun k => ψ (k : ZMod (l ^ m)) * ζ ^ ((k : ℤ) * X) with hF
  have h1 : ∑ r : ZMod (l ^ n), ψ ((r.val : ℕ) : ZMod (l ^ m)) * ζ ^ ((r.val : ℤ) * X)
      = ∑ k ∈ Finset.range (l ^ n), F k := sum_zmod_val_eq_sum_range (l ^ n) F
  set y : K := ζ ^ (((l ^ m : ℕ) : ℤ) * X) with hy
  have h3 : ∀ a t : ℕ, F (a + l ^ m * t) = F a * y ^ t := by
    intro a t
    simp only [hF, hy]
    have hc : ((a + l ^ m * t : ℕ) : ZMod (l ^ m)) = (a : ZMod (l ^ m)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [hc, mul_assoc]
    congr 1
    have he : ((a + l ^ m * t : ℕ) : ℤ) * X = (a : ℤ) * X + (((l ^ m : ℕ) : ℤ) * X) * (t : ℤ) := by
      push_cast; ring
    rw [he, zpow_add₀ hζ0, zpow_mul ζ (((l ^ m : ℕ) : ℤ) * X) (t : ℤ), zpow_natCast]
  have h2 : ∑ k ∈ Finset.range (l ^ n), F k
      = (∑ a ∈ Finset.range (l ^ m), F a) * ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t := by
    rw [hN', sum_range_mul_split, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3]
  have hω : IsPrimitiveRoot (ζ ^ (l ^ m)) (l ^ (n - m)) := hζ.pow (by positivity) hN'
  have hyω : y = (ζ ^ (l ^ m)) ^ X := by
    rw [hy, zpow_mul, zpow_natCast]
  have h4 : ∑ t ∈ Finset.range (l ^ (n - m)), y ^ t
      = if (l : ℤ) ^ (n - m) ∣ X then ((l : K) ^ (n - m)) else 0 := by
    split_ifs with hd
    · have : y = 1 := by
        rw [hyω]; exact (hω.zpow_eq_one_iff_dvd X).2 (by exact_mod_cast hd)
      simp [this]
    · have hy1 : y ≠ 1 := by
        rw [hyω]; intro h
        exact hd (by exact_mod_cast (hω.zpow_eq_one_iff_dvd X).1 h)
      rw [geom_sum_eq hy1]
      have : y ^ (l ^ (n - m)) = 1 := by
        rw [hyω, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one,
          one_zpow]
      rw [this, sub_self, zero_div]
  have h5 : ∑ a ∈ Finset.range (l ^ m), F a = ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * X) := by
    rw [← sum_zmod_val_eq_sum_range (l ^ m) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hF, ZMod.natCast_zmod_val]
  rw [h1, h2, h4, h5]
  split_ifs with hd
  · obtain ⟨Y, rfl⟩ := hd
    have hL0 : (l : ℤ) ^ (n - m) ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left _ hL0]
    have hξ : IsPrimitiveRoot (ζ ^ (l ^ (n - m))) (l ^ m) := hζ.pow (by positivity) hN
    have hξ0 : ζ ^ (l ^ (n - m)) ≠ 0 := pow_ne_zero _ hζ0
    let e : AddChar (ZMod (l ^ m)) K := AddChar.zmodChar (l ^ m) hξ.pow_eq_one
    have key := gaussSum_mulShift_of_isPrimitive e hψ (Y : ZMod (l ^ m))
    have hG : gaussSum ψ e = ∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.zmodChar_apply, pow_mul]
    have hS : ∑ a : ZMod (l ^ m), ψ a * ζ ^ ((a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y))
        = gaussSum ψ (e.mulShift Y) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [AddChar.mulShift_apply, AddChar.zmodChar_apply]
      congr 1
      have he : (a.val : ℤ) * ((l : ℤ) ^ (n - m) * Y) = ((l ^ (n - m) : ℕ) : ℤ) * ((a.val : ℤ) * Y) := by
        push_cast; ring
      rw [he, zpow_mul, zpow_natCast, ← zpow_natCast (ζ ^ l ^ (n - m)) ((Y : ZMod (l ^ m)) * a).val]
      refine zpow_eq_zpow_of_intCast_eq hξ0 hξ.pow_eq_one ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id', mul_comm]
    rw [hS, key, ← hG]
    ring
  · simp
end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDirac
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp.ChD

variable {l : ℕ} [Fact l.Prime]

theorem sum_units_eq_sum {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (f : ZMod N → Qbar l) :
    ∑ b : (ZMod N)ˣ, ψ b * f b = ∑ a : ZMod N, ψ a * f a := by
  refine Fintype.sum_of_injective (fun b : (ZMod N)ˣ => (b : ZMod N)) Units.val_injective _ _ ?_ (fun b => rfl)
  intro a ha
  have : ¬ IsUnit a := fun hu => ha ⟨hu.unit, rfl⟩
  rw [MulChar.map_nonunit ψ this, zero_mul]

theorem norm_apply_unit_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (b : (ZMod N)ˣ) :
    ‖ψ b‖ ≤ 1 := by
  have h : (ψ b) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h1 := congrArg norm h
  rw [norm_pow, norm_one] at h1
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le

theorem sum_units_char_pow (m : ℕ) (hm : 1 ≤ m) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (hz : IsPrimitiveRoot z (l ^ m)) (hψ : ψ.IsPrimitive) (j : ℕ) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j = ψ⁻¹ (j : ZMod (l ^ m)) * gSum m z ψ := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := GlobalTheory.EisM.sum_primChar_mul_rootPow_mod_pow (Qbar l) l m m z ψ (Fact.out) hm le_rfl hz hψ (j : ℤ)
  simp only [Nat.sub_self, pow_zero, one_dvd, if_true, one_mul, Int.ediv_one, Int.cast_natCast] at key
  rw [sum_units_eq_sum ψ (fun a => (z ^ a.val) ^ j)]
  unfold gSum
  rw [sum_units_eq_sum ψ (fun a => z ^ a.val)]
  have e1 : ∑ a : ZMod (l ^ m), ψ a * (z ^ a.val) ^ j =
      ∑ r : ZMod (l ^ m), ψ ((r.val : ℕ) : ZMod (l ^ m)) * z ^ ((r.val : ℤ) * (j : ℤ)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ZMod.natCast_zmod_val, ← Nat.cast_mul, zpow_natCast, pow_mul]
  rw [e1, key, mul_comm]

theorem chSum_gauss : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  intro l _ F a N m z ψ hm hN hF htv hz hψ
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hex : gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m)) =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F N (z ^ (b : ZMod (l ^ m)).val) := by
    simp_rw [htv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (a j * (z ^ (b : ZMod (l ^ m)).val) ^ j) =
        a j * ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, sum_units_char_pow m hm z ψ hz hψ j]
    ring
  unfold Cg
  rw [hex]
  unfold chSum
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_apply_unit_le_one ψ b)).trans ?_
  have hy : (z ^ (b : ZMod (l ^ m)).val) ^ (l ^ m) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hy1 := GlobalTheory.AmiceDist.norm_sub_one_le hy
  have hy3 := GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hy
  unfold tval
  rw [← Finset.sum_range_add_sum_Ico _ hN, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    ((pow_le_pow_of_le_one (norm_nonneg _) hy1 (Finset.mem_Ico.1 hn).1).trans hy3)

end GlobalTheory.KZ.Cmp.ChD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDiracStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  first | exact @GlobalTheory.KZ.Cmp.ChD.chSum_gauss | exact GlobalTheory.KZ.Cmp.ChD.chSum_gauss | (intros; apply GlobalTheory.KZ.Cmp.ChD.chSum_gauss; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeries
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem exists_series_limit : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (b : ℕ → ℕ → Qbar l) (t : ℕ → ℕ → ℕ), (∀ N j, b N j ∈ c.O) → ∃ A : PowerSeries (Qbar l), (∀ n, A.coeff n ∈ c.O) ∧ ∀ (g z X : Qbar l) (M N₀ : ℕ) (δ : ℝ), ‖z - 1‖ ≤ 1 → ‖g‖ * ‖z - 1‖ ^ M ≤ δ → (∀ N, N₀ ≤ N → ‖g * ∑ j ∈ Finset.range N, b N j * z ^ (t N j) - X‖ ≤ δ) → ‖g * tval A M z - X‖ ≤ δ := by
  intro l _ c b t hb
  let a : ℕ → ℕ → Qbar l := fun n N => ∑ j ∈ Finset.range N, b N j * ((t N j).choose n : Qbar l)
  have ha : ∀ n N, a n N ∈ c.O := fun n N => sum_mem fun j _ => mul_mem (hb N j) (natCast_mem _ _)
  have hlim : ∀ n, ∃ y ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds y) := by
    intro n
    obtain ⟨y, hy, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨y, hy, h⟩
  choose y hy hay using hlim
  refine ⟨PowerSeries.mk y, fun n => by simpa using hy n, fun g z X M N₀ δ hz hδ hN => ?_⟩
  unfold tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun N => ‖g * ∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - X‖) (Filter.hyperfilter ℕ)
      (nhds ‖g * ∑ n ∈ Finset.range M, y n * (z - 1) ^ n - X‖) :=
    (((tendsto_finsetSum _ fun n _ => (hay n).mul_const _).const_mul _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ N in (Filter.hyperfilter ℕ : Filter ℕ), N₀ ≤ N :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop N₀)
  filter_upwards [hev] with N hN'
  rw [show g * ∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - X =
    g * (∑ n ∈ Finset.range M, a n N * (z - 1) ^ n - ∑ j ∈ Finset.range N, b N j * z ^ (t N j)) +
      (g * ∑ j ∈ Finset.range N, b N j * z ^ (t N j) - X) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_trans ?_ hδ) (hN N hN'))
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hb N j))).trans ?_
  have h := GlobalTheory.AmiceDist.norm_trunc_binomial hz M (t N j)
  rwa [sub_add_cancel] at h

theorem exists_coef_roots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l), ‖x‖ ≤ 1 → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O ∧ ∀ y : Qbar l, y ^ (l - 1) = 1 → y ∈ c'.O := by
  intro l _ c x hx
  have h1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  haveI : NeZero (l - 1) := ⟨h1.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Qbar l, IsPrimitiveRoot ζ (l - 1) := HasEnoughRootsOfUnity.prim
  obtain ⟨c₁, h₁, hx₁⟩ := (UpperTheory.V.HV.coefSup l).2.2.1 c x (GlobalTheory.BlochKatoIntegralScalars.isIntegral_of_norm_le_one x hx)
  obtain ⟨c₂, h₂, hx₂⟩ := (UpperTheory.V.HV.coefSup l).2.2.1 c₁ ζ (hζ.isIntegral h1).tower_top
  refine ⟨c₂, h₁.trans h₂, h₂ hx₁, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  exact pow_mem hx₂ i

theorem lower_bound_of_not_cg : ∀ (l : ℕ) [Fact l.Prime] (f : Qbar l) (S T : ℕ → Qbar l) (n₀ r₁ : ℕ), f ≠ 0 → (∀ r, r₁ ≤ r → Cg (2 * r) (f * S r) ((l : Qbar l) ^ r * T r)) → (∀ r, r₁ ≤ r → ¬ Cg (n₀ + r) (S r) 0) → ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℕ, ∀ r, R ≤ r → δ < ‖T r‖ := by
  intro l _ f S T n₀ r₁ hf h1 h2
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  have hδ : 0 < ‖f‖ * ‖(l : Qbar l)‖ ^ n₀ := mul_pos (norm_pos_iff.2 hf) (pow_pos hq0 _)
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨_, hδ, max R r₁, fun r hr => ?_⟩
  by_contra hT
  rw [not_lt] at hT
  have a1 := h1 r (le_of_max_le_right hr)
  have a2 := h2 r (le_of_max_le_right hr)
  unfold Cg at a1 a2
  rw [sub_zero] at a2
  apply a2
  have hr' : ‖(l : Qbar l)‖ ^ r ≤ ‖f‖ * ‖(l : Qbar l)‖ ^ n₀ :=
    (pow_le_pow_of_le_one hq0.le hq1.le (le_of_max_le_left hr)).trans hR.le
  have a3 : ‖f * S r‖ ≤ ‖(l : Qbar l)‖ ^ r * (‖f‖ * ‖(l : Qbar l)‖ ^ n₀) := by
    rw [show f * S r = (f * S r - (l : Qbar l) ^ r * T r) + (l : Qbar l) ^ r * T r by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (a1.trans ?_) ?_)
    · rw [norm_pow, two_mul, pow_add]; gcongr
    · rw [norm_mul, norm_pow]; gcongr
  rw [norm_mul] at a3
  refine le_of_mul_le_mul_left (a3.trans_eq ?_) (norm_pos_iff.2 hf)
  rw [norm_pow, pow_add]; ring

theorem not_cg_of_lower_bound : ∀ (l : ℕ) [Fact l.Prime] (δ : ℝ), 0 < δ → ∃ n₁ : ℕ, ∀ r, n₁ ≤ r → ∀ S T : Qbar l, δ < ‖T‖ → Cg (2 * r) S ((l : Qbar l) ^ r * T) → ¬ Cg (n₁ + r) S 0 := by
  intro l _ δ hδ
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hq1
  refine ⟨n, fun r hr S T hT h1 h2 => ?_⟩
  unfold Cg at h1 h2
  rw [sub_zero] at h2
  have a3 : ‖(l : Qbar l) ^ r * T‖ ≤ ‖(l : Qbar l)‖ ^ r * ‖(l : Qbar l)‖ ^ n := by
    rw [show (l : Qbar l) ^ r * T = -(S - (l : Qbar l) ^ r * T) + S by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h2.trans_eq ?_))
    · rw [norm_neg]
      refine h1.trans ?_
      rw [norm_pow, ← pow_add]
      exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    · rw [norm_pow, pow_add, mul_comm]
  rw [norm_mul, norm_pow] at a3
  have := le_of_mul_le_mul_left a3 (pow_pos hq0 r)
  linarith

theorem norm_tval_le_of_coeff_cg : ∀ (l : ℕ) [Fact l.Prime] (A B : PowerSeries (Qbar l)) (w : ℕ → Qbar l) (z : Qbar l) (M : ℕ), (∀ m, ‖w m‖ = 1) → ‖z - 1‖ ≤ 1 → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n)) → ‖tval B M z‖ ≤ ‖tval A M z‖ := by
  intro l _ A B w z M hw hz h
  have hq1 := GlobalTheory.KZ.norm_prime_lt_one_qbar l
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq1
  obtain ⟨m, hm⟩ := h k
  have a1 : ‖tval A M z - w m * tval B M z‖ ≤ ‖(l : Qbar l) ^ k‖ := by
    unfold tval
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n _ => ?_
    rw [← mul_assoc, ← sub_mul, norm_mul, norm_pow (z - 1)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans (hm m le_rfl n)
  have a2 := norm_sub_norm_le (w m * tval B M z) (tval A M z)
  rw [norm_mul, hw, one_mul, norm_sub_rev] at a2
  rw [norm_pow] at a1
  linarith

theorem cg_div_gauss : ∀ (l : ℕ) [Fact l.Prime] (k c₁ : ℕ) (SG SL τ τ' TG TL f v v' a a' κ p : Qbar l), 2 * c₁ ≤ k → ‖v‖ = 1 → ‖v'‖ = 1 → ‖a‖ = 1 → ‖a'‖ = 1 → ‖p‖ ≤ 1 → ‖p * κ‖ ≤ 1 → τ * τ' = (l : Qbar l) ^ (k + 1) → ‖τ'‖ ≤ ‖(l : Qbar l) ^ ((k + 1) / 2)‖ → Cg (k + 1) SG (τ * TG) → Cg (k + 1) (f * SL) (τ * TL) → Cg (k + 1 - c₁) (f * (v' * κ * a' ^ (k + 1) * SL)) (v * a ^ (k + 1) * SG) → Cg (k / 2 - c₁) (p * TG) (v' / v * (a' / a) * (a' / a) ^ k * (p * κ * TL)) := by
  intro l _ k c₁ SG SL τ τ' TG TL f v v' a a' κ p hk hv hv' ha ha' hp hpκ hτ hτ' h1 h2 h3
  have hq0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hq1 := (GlobalTheory.KZ.norm_prime_lt_one_qbar l).le
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  unfold Cg at h1 h2 h3 ⊢
  rw [norm_pow] at h1 h2 h3 hτ' ⊢
  set D := p * TG - v' / v * (a' / a) * (a' / a) ^ k * (p * κ * TL) with hD
  have hm : ‖(l : Qbar l)‖ ^ (k + 1) ≤ ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := pow_le_pow_of_le_one hq0.le hq1 (by omega)
  have e : v * a ^ (k + 1) * (τ * D) = (-(p * (v * a ^ (k + 1) * (SG - τ * TG))) +
      -(p * (f * (v' * κ * a' ^ (k + 1) * SL) - v * a ^ (k + 1) * SG))) + p * κ * (v' * a' ^ (k + 1) * (f * SL - τ * TL)) := by
    rw [hD, div_pow]; field_simp; ring
  have b1 : ‖τ‖ * ‖D‖ ≤ ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := by
    have : ‖τ‖ * ‖D‖ = ‖v * a ^ (k + 1) * (τ * D)‖ := by simp [hv, ha]
    rw [this, e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
    · rw [norm_neg, norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hp).trans ?_
      rw [norm_mul, norm_mul, norm_pow, hv, ha, one_pow, one_mul, one_mul]
      exact h1.trans hm
    · rw [norm_neg, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans h3
    · rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hpκ).trans ?_
      rw [norm_mul, norm_mul, norm_pow, hv', ha', one_pow, one_mul, one_mul]
      exact h2.trans hm
  have b2 : ‖(l : Qbar l)‖ ^ (k + 1) * ‖D‖ ≤ ‖(l : Qbar l)‖ ^ ((k + 1) / 2) * ‖(l : Qbar l)‖ ^ (k + 1 - c₁) := by
    rw [← norm_pow, ← hτ, norm_mul, mul_comm ‖τ‖, mul_assoc]
    gcongr
  refine le_of_mul_le_mul_left (b2.trans ?_) (pow_pos hq0 (k + 1))
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_of_le_one hq0.le hq1 (by omega)

theorem ratio_units_cg : ∀ (l : ℕ) [Fact l.Prime] (v v' : ℕ → Qbar l) (u : Qbar l), ‖u‖ = 1 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → ∀ k, ‖v' (k + 1) / v (k + 1) * u‖ = 1 ∧ Cg k (v' (k + 1 + 1) / v (k + 1 + 1) * u) (v' (k + 1) / v (k + 1) * u) := by
  intro l _ v v' u hu hv hv' k
  have hq1 := (GlobalTheory.KZ.norm_prime_lt_one_qbar l).le
  have hv0 : ∀ m, v m ≠ 0 := fun m h => by have := (hv m).1; rw [h] at this; simp at this
  refine ⟨by rw [norm_mul, norm_div, (hv _).1, (hv' _).1, hu]; simp, ?_⟩
  have a1 := (hv (k + 1)).2
  have a2 := (hv' (k + 1)).2
  unfold Cg at a1 a2 ⊢
  have e : v' (k + 1 + 1) / v (k + 1 + 1) * u - v' (k + 1) / v (k + 1) * u =
      u / (v (k + 1 + 1) * v (k + 1)) * (v (k + 1) * (v' (k + 1 + 1) - v' (k + 1)) + -(v' (k + 1) * (v (k + 1 + 1) - v (k + 1)))) := by
    have := hv0 (k + 1); have := hv0 (k + 1 + 1)
    field_simp; ring
  rw [e, norm_mul, norm_div, norm_mul, (hv _).1, (hv _).1, hu, mul_one, div_one, one_mul]
  refine le_trans ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) (b := ‖(l : Qbar l) ^ (k + 1)‖) ?_
  · rwa [norm_mul, (hv _).1, one_mul]
  · rwa [norm_neg, norm_mul, (hv' _).1, one_mul]
  · rw [norm_pow, norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hq1 (by omega)

theorem smoothing_factor_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (c₀ e : ℕ), 2 ≤ c₀ → ¬ l ∣ c₀ → 1 - (c₀ : Qbar l) * ((c₀ : Qbar l) ^ e * φ (c₀ : ZMod l)) ≠ 0 := by
  intro l _ φ c₀ e h2 hl h
  have hlp := (Fact.out : l.Prime)
  have h0 : (c₀ : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h1 : φ (c₀ : ZMod l) ^ (l - 1) = 1 := by rw [← map_pow, ZMod.pow_card_sub_one_eq_one h0, map_one]
  have h3 : ((c₀ : Qbar l) * ((c₀ : Qbar l) ^ e * φ (c₀ : ZMod l))) ^ (l - 1) = 1 := by rw [← sub_eq_zero.1 h, one_pow]
  rw [← mul_assoc, mul_pow, h1, mul_one, ← pow_succ', ← pow_mul] at h3
  have h4 : c₀ ^ ((e + 1) * (l - 1)) = 1 := by exact_mod_cast h3
  have h5 : (e + 1) * (l - 1) ≠ 0 := mul_ne_zero (by omega) (by have := hlp.two_le; omega)
  have := (Nat.pow_eq_one.1 h4).resolve_right h5
  omega

theorem norm_char_le_one : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (ψ : DirichletCharacter (Qbar l) n) (x : ZMod n), 0 < n → ‖ψ x‖ ≤ 1 := by
  intro l _ n ψ x _
  exact ψ.norm_le_one x

theorem mellin_comp (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l)
    (e d : ℕ) (hl2 : l ≠ 2) (hc : ∀ y : Qbar l, y ^ (l - 1) = 1 → y ∈ c.O) (hF : ∀ n, F.coeff n ∈ c.O) :
    ∃ A : PowerSeries (Qbar l), (∀ n, A.coeff n ∈ c.O) ∧
      (∀ r, 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
        Cg (2 * r) ((d : Qbar l) ^ e * φ (d : ZMod l) * rSum φ e F r ξ) ((l : Qbar l) ^ r * tval A r ((1 + (l : Qbar l)) ^ e))) ∧
      ∀ k, 1 ≤ k → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ (k + 1)) → ∀ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)),
        ψ.IsPrimitive → InComp φ e ψ → ∀ ζ : Qbar l, ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ → ζ ^ (l ^ k) = 1 →
        Cg (k + 1) (ψ⁻¹ (d : ZMod (l ^ (k + 1))) * chSum F (k + 1) z ψ) (gSum (k + 1) z ψ * tval A (l ^ (3 * k)) ζ) := by
  have hlp := (Fact.out : l.Prime)
  have hl1 : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hmono : ∀ {i j : ℕ}, i ≤ j → ‖(l : Qbar l) ^ j‖ ≤ ‖(l : Qbar l) ^ i‖ := fun h => by
    rw [norm_pow, norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1 h
  choose a haO ha using fun N => GlobalTheory.T.truncated_shifted_series_eq_integral_poly_combination l c F N hF
  choose ε t hε hεr hεc using fun R j => GlobalTheory.T.teichmuller_decomposition_dirichlet_twisted_power l φ e R j hl2
  have hεO : ∀ R j, ε R j ∈ c.O := fun R j => (hε R j).elim (fun h => h ▸ zero_mem _) (hc _)
  have hF1 : ∀ n, ‖F.coeff n‖ ≤ 1 := fun n => FirstDer.norm_le_one_of_mem c (hF n)
  have ha1 : ∀ N j, ‖a N j‖ ≤ 1 := fun N j => FirstDer.norm_le_one_of_mem c (haO N j)
  obtain ⟨A, hAO, hA⟩ := exists_series_limit l c (fun N j => a N j * ε N (d * j)) (fun N j => t N (d * j))
    (fun N j => mul_mem (haO N j) (hεO _ _))
  refine ⟨A, hAO, fun r hr ξ hξ => ?_, fun k hk z hz ψ hψ hin ζ hζ hζ1 => ?_⟩
  · have hy : ‖(1 + (l : Qbar l)) ^ e - 1‖ ≤ ‖(l : Qbar l)‖ := by
      rw [← mul_geom_sum, add_sub_cancel_left, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      have : ∑ i ∈ Finset.range e, (1 + (l : Qbar l)) ^ i = ((∑ i ∈ Finset.range e, (1 + l) ^ i : ℕ) : Qbar l) := by
        push_cast; rfl
      rw [this]; exact IsUltrametricDist.norm_natCast_le_one _ _
    unfold Cg
    rw [norm_sub_rev]
    refine hA _ _ _ r (l ^ (3 * r) + r) _ (hy.trans hl1) ?_ fun N hN => ?_
    · rw [two_mul, pow_add, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_pow (l : Qbar l)]
      exact pow_le_pow_left₀ (norm_nonneg _) hy r
    · have h1 := GlobalTheory.T.amiceRiemannSum_congr_dirac_coefficients l φ e F (a N) N r ξ hr (by omega) hF1 (ha1 N) (ha N) hξ
      unfold Cg at h1
      have e1 : (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)) -
          (d : Qbar l) ^ e * φ (d : ZMod l) * rSum φ e F r ξ =
          -((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * (φ ((d * j : ℕ) : ZMod l) * ((d * j : ℕ) : Qbar l) ^ e -
            ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)))) +
          -((d : Qbar l) ^ e * φ (d : ZMod l) * (rSum φ e F r ξ -
            (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a N j * (φ (j : ZMod l) * (j : Qbar l) ^ e))) := by
        have e2 : ∑ j ∈ Finset.range N, a N j * (φ ((d * j : ℕ) : ZMod l) * ((d * j : ℕ) : Qbar l) ^ e -
            ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j))) =
            (d : Qbar l) ^ e * φ (d : ZMod l) * ∑ j ∈ Finset.range N, a N j * (φ (j : ZMod l) * (j : Qbar l) ^ e) -
            ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ((1 + (l : Qbar l)) ^ e) ^ (t N (d * j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.cast_mul, Nat.cast_mul, map_mul]; ring
        rw [e2]; ring
      rw [e1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_neg, norm_mul, two_mul, pow_add, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha1 N j)).trans ((hεr N (d * j)).trans (hmono (by omega)))
      · rw [norm_neg, norm_mul]
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans h1
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ d)) (norm_nonneg _)
          (norm_char_le_one l l φ _ hlp.pos)
  · have hg : ‖gSum (k + 1) z ψ‖ ≤ 1 := (GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power l (k + 1) z ψ hz.pow_eq_one).trans (by simpa using hmono (Nat.zero_le _))
    unfold Cg
    rw [norm_sub_rev]
    refine hA _ _ _ (l ^ (3 * k)) (l ^ (3 * (k + 1)) + (k + 1)) _ (GlobalTheory.AmiceDist.norm_sub_one_le hζ1) ?_ fun N hN => ?_
    · exact (mul_le_of_le_one_left (by positivity) hg).trans
        ((GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hζ1).trans (hmono (by omega)))
    · have h1 := GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac l F (a N) N (k + 1) z ψ (by omega) (by omega) hF1 (ha N) hz hψ
      unfold Cg at h1
      have e2 : ∑ j ∈ Finset.range N, a N j * ε N (d * j) * ζ ^ (t N (d * j)) =
          ψ⁻¹ (d : ZMod (l ^ (k + 1))) * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h2 := hεc N (d * j) (k + 1) (by omega) (by omega) ψ hin
        rw [Nat.cast_mul, map_mul, hζ] at h2
        rw [mul_assoc, ← h2]; ring
      have e1 : gSum (k + 1) z ψ * (ψ⁻¹ (d : ZMod (l ^ (k + 1))) * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1)))) -
          ψ⁻¹ (d : ZMod (l ^ (k + 1))) * chSum F (k + 1) z ψ = -(ψ⁻¹ (d : ZMod (l ^ (k + 1))) * (chSum F (k + 1) z ψ -
            gSum (k + 1) z ψ * ∑ j ∈ Finset.range N, a N j * ψ⁻¹ (j : ZMod (l ^ (k + 1))))) := by ring
      rw [e2, e1, norm_neg, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one l _ ψ⁻¹ _ (pow_pos hlp.pos _))).trans (h1.trans (hmono (by omega)))

theorem nonvanishing_transfer : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0 := by
  intro l _ c Gs L a a' κ v v' c₀ m₀ c₁ n₀ φ e hl2 he hm₀ hGs hL ha ha' hκ hv hv' hc₀ hlc₀ hyp hLnz
  obtain ⟨r₁, hr₁⟩ := hLnz
  have hlp := (Fact.out : l.Prime)
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hc1 : ‖(c₀ : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ c₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(l : Qbar l) ^ N * κ‖ ≤ 1 := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hκ)) (GlobalTheory.KZ.norm_prime_lt_one_qbar l)
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_pow, ← le_div_iff₀ (norm_pos_iff.2 hκ), one_div]
    exact hN.le
  set p : Qbar l := (l : Qbar l) ^ N with hp
  have hp0 : p ≠ 0 := pow_ne_zero _ hl0
  have hp1 : ‖p‖ ≤ 1 := by
    rw [hp, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ l)
  obtain ⟨c', hcc, hκO, hroot⟩ := exists_coef_roots l c _ hN
  obtain ⟨AG, hGO, hGr, hGc⟩ := mellin_comp l c' Gs φ e 1 hl2 hroot fun n => hcc (hGs n)
  obtain ⟨A₁, h1O, h1r, h1c⟩ := mellin_comp l c' L φ e 1 hl2 hroot fun n => hcc (hL n)
  obtain ⟨A₂, h2O, h2r, h2c⟩ := mellin_comp l c' L φ e c₀ hl2 hroot fun n => hcc (hL n)
  simp only [Nat.cast_one, one_pow, map_one, one_mul] at hGr hGc h1r h1c
  have hcomb : ∀ (n : ℕ) (x₁ y₁ x₂ y₂ : Qbar l), Cg n x₁ y₁ → Cg n x₂ y₂ → Cg n (x₁ - (c₀ : Qbar l) * x₂) (y₁ - (c₀ : Qbar l) * y₂) := by
    intro n x₁ y₁ x₂ y₂ h1 h2
    unfold Cg at h1 h2 ⊢
    rw [show x₁ - (c₀ : Qbar l) * x₂ - (y₁ - (c₀ : Qbar l) * y₂) = (x₁ - y₁) + -((c₀ : Qbar l) * (x₂ - y₂)) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans h2
  set AL := A₁ - PowerSeries.C (c₀ : Qbar l) * A₂ with hAL
  have hprim : ∀ r : ℕ, ∃ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) := fun r =>
    haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    HasEnoughRootsOfUnity.prim
  choose ξ hξ using hprim
  obtain ⟨δ, hδ, R, hR⟩ := lower_bound_of_not_cg l _ (fun r => rSum φ e L r (ξ r)) (fun r => tval AL r ((1 + (l : Qbar l)) ^ e)) n₀ (max r₁ 1)
    (smoothing_factor_ne_zero l φ c₀ e hc₀ hlc₀)
    (fun r hr => by
      have h := hcomb _ _ _ _ _ (h1r r (le_of_max_le_right hr) _ (hξ r)) (h2r r (le_of_max_le_right hr) _ (hξ r))
      rw [hAL, tval_sub_C_mul]
      convert h using 1 <;> ring)
    (fun r hr => hr₁ r (le_of_max_le_left hr) (le_of_max_le_right hr) _ (hξ r))
  have hu : ‖a' / a‖ = 1 := by rw [norm_div, ha, ha', div_one]
  have hw := ratio_units_cg l v v' (a' / a) hu hv hv'
  have hBO : ∀ n, (PowerSeries.C (p * κ) * AL).coeff n ∈ c'.O := fun n => by
    rw [PowerSeries.coeff_C_mul, hAL, map_sub, PowerSeries.coeff_C_mul]
    exact mul_mem hκO (sub_mem (h1O n) (mul_mem (natCast_mem _ _) (h2O n)))
  have hAO : ∀ n, (PowerSeries.C p * AG).coeff n ∈ c'.O := fun n => by
    rw [PowerSeries.coeff_C_mul]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (hGO n)
  have hpκ : 0 < ‖p * κ‖ := norm_pos_iff.2 (mul_ne_zero hp0 hκ)
  have hB0 : PowerSeries.C (p * κ) * AL ≠ 0 := by
    intro h0
    have h1 := tval_C_mul AL (p * κ) R ((1 + (l : Qbar l)) ^ e)
    rw [h0] at h1
    have h2 : tval (0 : PowerSeries (Qbar l)) R ((1 + (l : Qbar l)) ^ e) = 0 := by simp [tval]
    rw [h2] at h1
    have h3 := (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp0 hκ)
    have h4 := hR R le_rfl
    simp only [h3, norm_zero] at h4
    linarith
  obtain ⟨-, hpin⟩ := GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots l c' _ _ (a' / a) (fun k => v' (k + 1) / v (k + 1) * (a' / a)) c₁ (m₀ + 2 * c₁) hAO hBO hB0 hu hw
    (fun k hk ζ hζ => by
      obtain ⟨z, hz, hzψ⟩ := hyp (k + 1) (by omega)
      obtain ⟨ψ, hψ, hin, hψζ⟩ := GlobalTheory.T.exists_primitive_character_twist l φ e k ζ hl2 (by omega) hζ
      have g1 := hGc k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one
      have g2 := hcomb _ _ _ _ _ (h1c k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one)
        (h2c k (by omega) z hz ψ hψ hin ζ hψζ hζ.pow_eq_one)
      rw [tval_C_mul, tval_C_mul]
      refine cg_div_gauss l k c₁ (chSum Gs (k + 1) z ψ) (chSum L (k + 1) z ψ) _ _ _ _
        (1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ (k + 1)))) _ _ a a' κ p (by omega) (hv _).1 (hv' _).1 ha ha' hp1 hN
        (GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow l (k + 1) z ψ hz hψ) (GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power l (k + 1) z⁻¹ ψ⁻¹ hz.inv.pow_eq_one) g1 ?_ (hzψ ψ hψ)
      rw [hAL, tval_sub_C_mul]
      convert g2 using 1 <;> ring)
  have hy : ‖(1 + (l : Qbar l)) ^ e - 1‖ ≤ 1 := by
    have : (1 + (l : Qbar l)) ^ e - 1 = (((1 + l) ^ e - 1 : ℤ) : Qbar l) := by push_cast; rfl
    rw [this]; exact IsUltrametricDist.norm_intCast_le_one _ _
  obtain ⟨n₁, hn₁⟩ := not_cg_of_lower_bound l (‖p * κ‖ * δ) (mul_pos hpκ hδ)
  refine ⟨n₁, max (max n₁ R) 1, fun r hr η hη => hn₁ r (by omega) _ _ ?_ (hGr r (by omega) η hη)⟩
  have h := norm_tval_le_of_coeff_cg l _ _ _ _ r (fun m => (hw m).1) hy hpin
  rw [tval_C_mul, tval_C_mul, norm_mul, norm_mul p (tval _ _ _)] at h
  exact ((mul_lt_mul_of_pos_left (hR r (by omega)) hpκ).trans_le h).trans_le (mul_le_of_le_one_left (norm_nonneg _) hp1)

end GlobalTheory.KZ.Cmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeriesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0 := by
  first | (exact @GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (exact GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (intros; apply GlobalTheory.KZ.Cmp.nonvanishing_transfer  <;> assumption)
end
