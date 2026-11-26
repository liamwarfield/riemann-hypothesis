module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NewtonRecursionPolyUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NewtonRecursionPolyUnique
open Finset Polynomial

namespace GlobalTheory

lemma shiftDiffPoly_coeff_comp (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by
  rw [comp, eval₂_eq_sum_range]
  simp [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]

lemma shiftDiffPoly_coeff_top (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (f.comp (X + 1) - f).coeff n = 0 := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by simp at hb; omega
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hn'
    have : f.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hn'; omega)
    simp [this]

lemma shiftDiffPoly_coeff_sub (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, he, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero]
  · simp [Nat.choose_succ_self_right]; ring
  · intro i hi
    simp at hi
    simp [Nat.choose_eq_zero_of_lt hi]

theorem newton_recursion_poly_unique : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  intro m N p f r hmN hp0 hf hr hid
  have hlead : ∀ k : ℕ, ((X - C (m:ℂ)) ^ k).coeff k = 1 := fun k => by
    have h := ((monic_X_sub_C (m:ℂ)).pow k).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  set Pi : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * p k) * (X - C (m:ℂ)) ^ (N - k) with hPi
  set g : ℂ[X] := f.comp (X + 1) - f with hg
  have hpoly : (X - C (m:ℂ)) ^ (N + 1) * g - f * Pi = r := by
    apply Polynomial.funext
    intro u
    simp only [hg, hPi, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add,
      eval_one, Polynomial.eval_finsetSum]
    rw [← hid u]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPiN : Pi.coeff N = (m : ℂ) + 1 := by
    rw [hPi, Polynomial.finsetSum_coeff, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [pow_zero, one_mul, Nat.sub_zero, coeff_C_mul, hlead, hp0, mul_one, zero_add]
    · intro k hk
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_pow, natDegree_X_sub_C]
      simp at hk
      omega
  have hPideg : Pi.natDegree ≤ N := by
    rw [hPi]
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  set d := f.natDegree with hd
  have hcoef : ((X - C (m:ℂ)) ^ (N + 1) * g - f * Pi).coeff (d + N) = r.coeff (d + N) := by rw [hpoly]
  rw [coeff_sub] at hcoef
  have hr0 : r.coeff (d + N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (f * Pi).coeff (d + N) = f.coeff d * Pi.coeff N :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hPideg
  have h1 : ((X - C (m:ℂ)) ^ (N + 1) * g).coeff (d + N) = d * f.coeff d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hg0 : g = 0 := by
        ext n
        rw [coeff_zero]
        exact shiftDiffPoly_coeff_top f n (by omega)
      rw [hg0, mul_zero, coeff_zero, h0]
      simp
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hgdeg : g.natDegree ≤ e := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        exact shiftDiffPoly_coeff_top f n (by omega)
      have hidx : d + N = (N + 1) + e := by omega
      rw [hidx, coeff_mul_add_eq_of_natDegree_le (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]) hgdeg,
        hlead, one_mul, shiftDiffPoly_coeff_sub f e he, he]
      push_cast
      ring
  rw [h1, h2, hPiN, hr0] at hcoef
  have hne : (d : ℂ) - ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have h' : (d : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination h
    have := Nat.cast_injective h'
    omega
  have hc : f.coeff d = 0 := by
    have : f.coeff d * ((d : ℂ) - ((m : ℂ) + 1)) = 0 := by linear_combination hcoef
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  exact leadingCoeff_eq_zero.mp hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NewtonRecursionPolyUniqueStatement
open Finset Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poly_eq_zero_of_newton_recursion : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  first | exact @GlobalTheory.newton_recursion_poly_unique | exact GlobalTheory.newton_recursion_poly_unique | (intros; apply GlobalTheory.newton_recursion_poly_unique <;> assumption)
end
end

open Formalism.REAL Finset Polynomial

open GlobalTheory.Dec (gelfVal)

namespace GlobalTheory.CapelliNewton

theorem gelfVal_zero (m : ℕ) (χ : Fin (m+1) → ℂ) : gelfVal χ 0 = (m:ℂ) + 1 := by
  simp [gelfVal, Matrix.one_apply]

theorem etr_apply_all {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (k : ℕ) (w : V) :
    etr E k w = gelfVal χ k • w := by
  cases k with
  | zero => rw [gelfVal_zero]; simp [etr, epow, add_smul]; rw [Nat.cast_smul_eq_nsmul]
  | succ k => exact hetr k w

noncomputable def polyOf {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : ℂ[X] :=
  ∑ i ∈ range (d + 1), C (φ (c i v)) * X ^ i

theorem polyOf_eval {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) (u : ℂ) :
    (polyOf d c φ v).eval u = φ ((∑ i ∈ range (d + 1), u ^ i • c i) v) := by
  unfold polyOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval_finsetSum, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm]

theorem polyOf_natDegree {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).natDegree ≤ d := by
  unfold polyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hi)

theorem polyOf_coeff {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).coeff d = φ (c d v) := by
  unfold polyOf
  rw [finsetSum_coeff, sum_eq_single d]
  · simp
  · intro b _ hb; simp [coeff_C_mul_X_pow, hb.symm]
  · intro h; exact absurd (self_mem_range_succ d) h

noncomputable def capQ (m : ℕ) (χ : Fin (m+1) → ℂ) : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2))

theorem capQ_eval (m : ℕ) (χ : Fin (m+1) → ℂ) (u : ℂ) :
    (capQ m χ).eval u = ∏ s, (u - (m : ℂ) / 2 + χ s) := by
  simp [capQ, eval_prod]; refine prod_congr rfl fun s _ => by ring

theorem capQ_monic (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_add_C _

theorem capQ_natDegree (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).natDegree = m + 1 := by
  unfold capQ
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem main_succ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ) (hE : GlRel E)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (u : ℂ) (v : V) :
    qdet E u v = (∏ s, (u - (m : ℂ) / 2 + χ s)) • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  set P := polyOf (m + 1) c φ v with hPdef
  have hP : ∀ w : ℂ, φ (qdet E w v) = P.eval w := fun w => by rw [polyOf_eval, hc]

  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let N := m + 1
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w * epow E (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (P.eval (w + 1) - P.eval w) - P.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k = (C (-(-1) ^ N) * Rp).eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k) • qdet E w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, etr_apply_all m E χ hetr, smul_smul]
      rw [← sum_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul, LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval] at h1
    simp only [hP] at h1
    simp only [eval_mul, eval_neg, eval_pow, eval_C]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m N (gelfVal χ) (P - C (φ v) * capQ m χ) (C (-(-1) ^ N) * Rp - C (φ v) * rs)
    (Nat.lt_succ_self m) (gelfVal_zero m χ) ?_ ?_ ?_
  · have := congrArg (eval u) hf
    simp only [eval_sub, eval_mul, eval_C, eval_zero, capQ_eval] at this
    rw [map_sub, map_smul, hP, smul_eq_mul]; linear_combination this
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt h),
        coeff_eq_zero_of_natDegree_lt (by rw [capQ_natDegree]; exact h)]; simp
    · have hk' : k = m + 1 := le_antisymm h hk
      subst hk'
      have := (capQ_monic m χ).coeff_natDegree
      rw [capQ_natDegree] at this
      rw [this, polyOf_coeff, hc1]; simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (polyOf_natDegree _ _ _ _)
    · exact natDegree_C_mul_le _ _ |>.trans hrs
  · intro w
    have h1 := hrec w
    have h2 := hrsE w
    rw [← capQ_eval m χ (w + 1), ← capQ_eval m χ w] at h2
    simp only [eval_sub, eval_mul, eval_C] at h1 h2 ⊢
    linear_combination h1 - φ v * h2

end GlobalTheory.CapelliNewton

namespace GlobalTheory.CapelliNewton

theorem capelli_of_gelfand : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  intro V _ _ n E χ hE hetr Y v
  cases n with
  | zero => simp [qdet, qminor]
  | succ m =>
    rw [main_succ V m E χ hE hetr]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    push_cast; ring

end GlobalTheory.CapelliNewton
