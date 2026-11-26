module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SltEqZeroOfCompact
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PositionDegree

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

def slRest {k : ℕ} (i : Fin k) :
    (Fin k → Fin n × Fin n) ≃ (Fin n × Fin n) × ({j // j ≠ i} → Fin n × Fin n) :=
  Equiv.funSplitAt i _

def slt {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => A ((slRest i).symm (ι 0, r)))

theorem slRest_symm_self {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n) :
    (slRest i).symm (p, r) i = p := by
  simp [slRest, Equiv.funSplitAt_symm_apply]

theorem update_slRest_symm {k : ℕ} (i : Fin k) (p q : Fin n × Fin n)
    (r : {j // j ≠ i} → Fin n × Fin n) :
    Function.update ((slRest i).symm (p, r)) i q = (slRest i).symm (q, r) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem update_eq_slRest {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (q : Fin n × Fin n) :
    Function.update κ i q = (slRest i).symm (q, (slRest i κ).2) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, Equiv.funSplitAt_apply, h]

theorem slice_eq_slt {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (A : Big n k M) :
    slice i κ A = slt i (slRest i κ).2 A := by
  simp only [slice, slt, update_eq_slRest]

theorem slt_sum_fin_one_fun {β : Type*} [AddCommMonoid β] (f : (Fin n × Fin n) → β) :
    ∑ ι : Fin 1 → Fin n × Fin n, f (ι 0) = ∑ p, f p := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun ι => by simp)

theorem slt_inner_eq_sum {k : ℕ} (i : Fin k) (A B : Big n k M) :
    inner ℂ A B = ∑ r, inner ℂ (slt i r A) (slt i r B) := by
  rw [PiLp.inner_apply, ← (slRest i).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [PiLp.inner_apply]
  exact (slt_sum_fin_one_fun
    (fun p => inner ℂ (A ((slRest i).symm (p, r))) (B ((slRest i).symm (p, r))))).symm

theorem slt_ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := rfl

theorem slt_coord_apply (k : ℕ) (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ F = F κ := rfl

theorem slt_mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem slt_positionAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  rw [factorAd, slt_ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> simp [slt_coord_apply]

theorem slt_crossOp_apply (k : ℕ) (i : Fin k) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    crossOp ε E k i F κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
  rw [← slt_coord_apply k κ (crossOp ε E k i F)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [crossOp, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [slt_coord_apply]
  change factorAd k i a b (mAct E k b a F) κ = _
  rw [slt_positionAd_apply, slt_mAct_apply, slt_mAct_apply]

private theorem slt_apply {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n)
    (A : Big n k M) (ι : Fin 1 → Fin n × Fin n) : slt i r A ι = A ((slRest i).symm (ι 0, r)) :=
  rfl

theorem slt_crossOp {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) :
    slt i r (crossOp ε E k i A) = crossOp ε E 1 0 (slt i r A) := by
  refine PiLp.ext fun ι => ?_
  rw [slt_apply, slt_crossOp_apply, slt_crossOp_apply, slRest_symm_self]
  simp only [update_slRest_symm, slt_apply, Function.update_self]

end PositionDegree

section PositionB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem slt_mem_ncV_iff {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap, slt_coord_apply]

theorem slRest_symm_ne {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n)
    {j : Fin k} (h : j ≠ i) : (slRest i).symm (p, r) j = r ⟨j, h⟩ := by
  simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem slt_eq_slice {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (p : Fin n × Fin n)
    (A : Big n k M) : slt i r A = slice i ((slRest i).symm (p, r)) A := by
  simp only [slice_eq_slt, Equiv.apply_symm_apply]

theorem slt_big_one_eq_zero (he : IsEmpty (Fin n × Fin n)) (x : Big n 1 M) : x = 0 := by
  exact PiLp.ext fun ι => (he.false (ι 0)).elim

theorem slt_slice_mem_ncV {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slice i κ F ∈ ncV ε V 1 := by
  rw [slt_mem_ncV_iff] at hF ⊢
  intro ι
  have h := hF (Function.update κ i (ι 0))
  change F (Function.update κ i (ι 0)) ∈ _
  by_cases c : ∀ j : Fin 1, ε (ι j).1 ≠ ε (ι j).2
  · rw [if_pos c]
    split_ifs at h with c'
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]
      exact V.zero_mem
  · rw [if_neg c]
    have c' : ¬ ∀ j, ε ((Function.update κ i (ι 0)) j).1 ≠ ε ((Function.update κ i (ι 0)) j).2 := by
      intro hall
      apply c
      intro j
      have hj := hall i
      rw [Function.update_self] at hj
      rwa [Subsingleton.elim j 0]
    rwa [if_neg c'] at h

theorem slt_mem_ncV {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slt i r F ∈ ncV ε V 1 := by
  by_cases he : IsEmpty (Fin n × Fin n)
  · rw [slt_big_one_eq_zero he (slt i r F)]
    exact Submodule.zero_mem _
  · rw [not_isEmpty_iff] at he
    obtain ⟨p⟩ := he
    rw [slt_eq_slice i r p]
    exact slt_slice_mem_ncV i _ hF

end PositionB

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Slot

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem position_perp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hperp : ∀ F ∈ ncV ε V k, (∀ κ, slice i κ F ∈ Wm ε E V) → inner ℂ F P = 0) :
    ∀ κ, slice i κ P ∈ Wp ε E V := by
  intro κ
  rw [slice_eq_slt]
  set r := (slRest i κ).2 with hr
  have hx : slt i r P ∈ ncV ε V 1 := slt_mem_ncV i r hP
  obtain ⟨xm, hxm, xp, hxp, hdec⟩ := ncV_one_decomp hE hU hV hmono hh hbig hx
  have hkey : inner ℂ xm (slt i r P) = (‖xm‖ : ℂ) ^ 2 := by
    rw [hdec, inner_add_right, Wm_perp_Wp hU hxm hxp, add_zero]
    exact inner_self_eq_norm_sq_to_K xm
  suffices hz : xm = 0 by
    rw [hdec, hz, zero_add]
    exact hxp
  have hxm1 := slt_mem_ncV_iff.1 (Wm_le_ncV hxm)

  have hbad : (∃ j : {j // j ≠ i}, ε (r j).1 = ε (r j).2) → xm = 0 := by
    rintro ⟨j, hj⟩
    have hx0 : slt i r P = 0 := by
      ext ι
      have hPm := (slt_mem_ncV_iff.1 hP) ((slRest i).symm (ι 0, r))
      have hcoord : ((slRest i).symm (ι 0, r)) j.1 = r j := by
        simp [slRest, Equiv.funSplitAt_symm_apply, j.2]
      rw [if_neg] at hPm
      · simpa [slt] using hPm
      · intro hall
        exact hall j.1 (by rw [hcoord]; exact hj)
    have h2 := hkey
    rw [hx0, inner_zero_right] at h2
    simpa using h2.symm
  let F : Big n k M := WithLp.toLp 2 (fun κ' =>
    if (slRest i κ').2 = r then xm (fun _ => (slRest i κ').1) else 0)
  have hFapp : ∀ κ', F κ' = if (slRest i κ').2 = r then xm (fun _ => (slRest i κ').1) else 0 :=
    fun κ' => rfl
  have hsltF : ∀ r', slt i r' F = if r' = r then xm else 0 := by
    intro r'
    split_ifs with h1
    · subst h1
      ext ι
      simp only [slt, hFapp]
      simp only [Equiv.apply_symm_apply, if_true]
      rw [show (fun _ : Fin 1 => ι 0) = ι from funext fun j => by rw [Fin.fin_one_eq_zero j]]
    · ext ι
      simp [slt, hFapp, h1]
  have hFmem : F ∈ ncV ε V k := by
    rw [slt_mem_ncV_iff]
    intro κ'
    rw [hFapp]
    by_cases hrest : (slRest i κ').2 = r
    · rw [if_pos hrest]
      have hι := hxm1 (fun _ => (slRest i κ').1)
      by_cases hc : ∀ j, ε (κ' j).1 ≠ ε (κ' j).2
      · rw [if_pos hc]
        split_ifs at hι
        · exact hι
        · rw [(Submodule.mem_bot ℂ).1 hι]
          exact zero_mem _
      · rw [if_neg hc]
        push_neg at hc
        obtain ⟨j, hj⟩ := hc
        by_cases hji : j = i
        · subst hji
          rw [if_neg] at hι
          · exact hι
          · intro hall
            exact hall 0 (by simpa [slRest] using hj)
        · rw [hbad ⟨⟨j, hji⟩, by rw [← hrest]; simpa [slRest] using hj⟩]
          simp
    · rw [if_neg hrest]
      exact zero_mem _
  have hinner : inner ℂ F P = inner ℂ xm (slt i r P) := by
    rw [slt_inner_eq_sum i F P]
    simp only [hsltF]
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hF0 := hperp F hFmem (fun κ' => by
    rw [slice_eq_slt, hsltF]
    split_ifs
    · exact hxm
    · exact zero_mem _)
  rw [hinner, hkey] at hF0
  simpa using hF0

theorem crossOp_position_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : ∀ κ, slice i κ P ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖P‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
  have hr : ∀ r, slt i r P ∈ Wp ε E V := by
    intro r
    by_cases hne : IsEmpty (Fin n × Fin n)
    · rw [slt_big_one_eq_zero hne (slt i r P)]
      exact zero_mem _
    · rw [not_isEmpty_iff] at hne
      obtain ⟨p⟩ := hne
      rw [slt_eq_slice i r p]
      exact hP _
  have hn : ‖P‖ ^ 2 = ∑ r, ‖slt i r P‖ ^ 2 := by
    have h1 : (inner ℂ P P : ℂ) = ∑ r, inner ℂ (slt i r P) (slt i r P) := slt_inner_eq_sum i P P
    simp only [inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  have hc : RCLike.re (inner ℂ (crossOp ε E k i P) P) =
      ∑ r, RCLike.re (inner ℂ (crossOp ε E 1 0 (slt i r P)) (slt i r P)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [slt_inner_eq_sum i, map_sum]
    simp only [slt_crossOp]
  rw [hn, hc, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => Wp_bound hE hU hV hmono hh hbig (hr r)

end Slot

end ReciprocityTheory.ChartRestriction.DS
