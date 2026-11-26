module

public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restNil : RestNil := by
  intro K V _ _ _ _ _ n E hE a b hab k hk
  have hs := gl_rep_shifts_weights hE
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h1 : (E a b) ^ (2 * m + 1) = 0 := by
    have hle : (⊤ : Submodule K V) ≤ LinearMap.ker ((E a b) ^ (2 * m + 1)) := by
      rw [← hE.2.2]
      refine iSup_le fun ν x hx => ?_
      rw [LinearMap.mem_ker]
      by_contra h0
      have hx0 : weightSp E ν ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hx
        exact h0 (by rw [hx, map_zero])
      have hw := operator_pow_shifts_weight hs a b ν (2 * m + 1) x hx
      have hw0 : weightSp E (ν + ((2 * m + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hw
        exact h0 hw
      have b1 := hm _ hx0 a
      have b2 := hm _ hw0 a
      rw [Pi.add_apply, root_multiple_apply_first a b hab] at b2
      rw [abs_le] at b1 b2
      push_cast at b2
      omega
    exact LinearMap.ker_eq_top.1 (top_le_iff.1 hle)
  have h2 : LinearMap.ker ((E a b) ^ k) = ⊤ := by
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hk,
      ← Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_left (Module.finrank K V) (2 * m + 1)),
      pow_eq_zero_of_le (le_max_right _ _) h1]
    exact LinearMap.ker_zero
  exact LinearMap.ker_eq_top.1 h2

theorem pf_trunc {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (hab : a ≠ b) (c T T' : ℕ)
    (hT : Module.finrank K V ≤ T) (hT' : Module.finrank K V ≤ T') : pf E a b c T = pf E a b c T' := by
  have hz : ∀ k, Module.finrank K V ≤ k → divPowE E a b k = 0 := by
    intro k hk
    unfold divPowE
    rw [restNil K V n E hE a b hab k hk, smul_zero]
  have hsum : ∀ S : ℕ, Module.finrank K V ≤ S → pf E a b c S = pf E a b c (Module.finrank K V) := by
    intro S hS
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hS
    unfold pf
    rw [show Module.finrank K V + m + 1 = (Module.finrank K V + 1) + m by ring, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range m, ((-1 : K) ^ (Module.finrank K V + 1 + x) /
        ((Nat.choose (c + (Module.finrank K V + 1 + x)) (Module.finrank K V + 1 + x) : ℕ) : K)) •
        (divPowE E b a (Module.finrank K V + 1 + x) * divPowE E a b (Module.finrank K V + 1 + x)) = 0 :=
      Finset.sum_eq_zero (fun x _ => by rw [hz _ (by omega), mul_zero, smul_zero])
    rw [h0, add_zero]
  rw [hsum T hT, hsum T' hT']

end Formalism.MainNotions.G.ExtremalProjector
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPairOf
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem comm_of_disj {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : b ≠ c) (h2 : d ≠ a) :
    Commute (E a b) (E c d) := by
  have := hE.1 a b c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at this
  exact this

theorem divPow_comm {E : GLOps n K V} {a b c d : Fin n} (h : Commute (E a b) (E c d)) (j k : ℕ) :
    Commute (divPowE E a b j) (divPowE E c d k) := by
  unfold divPowE
  exact ((h.pow_pow j k).smul_left _).smul_right _

theorem pf_comm {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c)
    (h4 : b ≠ d) (s s' T : ℕ) : Commute (pf E a b s T) (pf E c d s' T) := by
  unfold pf
  refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_
  refine (Commute.smul_left ?_ _).smul_right _
  have c1 : Commute (E b a) (E d c) := comm_of_disj hE h2 h3.symm
  have c2 : Commute (E b a) (E c d) := comm_of_disj hE h1 h4.symm
  have c3 : Commute (E a b) (E d c) := comm_of_disj hE h4 h1.symm
  have c4 : Commute (E a b) (E c d) := comm_of_disj hE h3 h2.symm
  exact Commute.mul_left (Commute.mul_right (divPow_comm c1 j k) (divPow_comm c2 j k))
    (Commute.mul_right (divPow_comm c3 j k) (divPow_comm c4 j k))

theorem dual_mem (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) :
    x ∈ weightSp (dualOps E) (-ν) ↔ x ∈ weightSp E ν := by
  rw [mem_weightSpace_iff_diagonal_eigen, mem_weightSpace_iff_diagonal_eigen]
  refine forall_congr' fun a => ?_
  simp only [dualOps, LinearMap.neg_apply, Pi.neg_apply, Int.cast_neg, neg_smul, neg_inj]

theorem dual_rep {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (dualOps E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    have := hE.1 b a d c
    simp only [dualOps, neg_mul_neg]
    rw [this, if_congr (eq_comm (a := a) (b := d)) rfl rfl, if_congr (eq_comm (a := c) (b := b)) rfl rfl]
    split_ifs <;> abel
  · intro x
    obtain ⟨W, h1, h2, h3⟩ := hE.2.1 x
    exact ⟨W, h1, h2, fun a b y hy => by
      simp only [dualOps, LinearMap.neg_apply]
      exact W.neg_mem (h3 b a y hy)⟩
  · rw [eq_top_iff, ← hE.2.2]
    refine iSup_le fun ν => le_iSup_of_le (-ν) fun x hx => (dual_mem E ν x).2 hx

theorem divPow_dual (E : GLOps n K V) (x y : Fin n) (k : ℕ) :
    divPowE (dualOps E) x y k = (-1 : K) ^ k • divPowE E y x k := by
  simp only [divPowE, dualOps]
  rw [show -E y x = (-1 : K) • E y x by simp, smul_pow, smul_comm]

theorem pf_dual (E : GLOps n K V) (x y : Fin n) (c T : ℕ) : pf (dualOps E) x y c T = pf E y x c T := by
  unfold pf
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [divPow_dual, divPow_dual, smul_mul_smul_comm, ← mul_pow]
  simp

end

theorem restComm : RestComm := fun _ _ _ _ _ _ _ hE _ _ _ _ h1 h2 h3 h4 s s' T => pf_comm hE h1 h2 h3 h4 s s' T

theorem restPair'_of (h : RestPair) : RestPair' := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν t u hu T hT w hw
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t u
    (by simp only [Pi.neg_apply]; omega) T hT w ((dual_mem E ν w).2 hw)
  simp only [pf_dual] at this
  simp only [dualOps, LinearMap.neg_apply, map_neg, neg_inj] at this
  exact this

theorem ybat_symm (sg ta : ℕ) (h : YBat sg ta) : YBat ta sg := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t s
    (by simp only [Pi.neg_apply]; omega) (by simp only [Pi.neg_apply]; omega) T hT x ((dual_mem E ν x).2 hx)
  simp only [pf_dual] at this
  rw [add_comm t s] at this
  exact this.symm

end Formalism.MainNotions.G.ExtremalProjector
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestTruncOfNil
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {n : ℕ} {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem pf_apply (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x = ∑ k ∈ Finset.range (T + 1),
      ((-1 : K) ^ k / ((Nat.choose (c + k) k : ℕ) : K)) •
        (((k.factorial : K)⁻¹) • ((E b a) ^ k) (((k.factorial : K)⁻¹) • ((E a b) ^ k) x)) := by
  unfold pf
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [divPowE, Module.End.mul_apply]

theorem pow_mem_stable (f : Module.End K W) (S : Submodule K W) (h : ∀ w ∈ S, f w ∈ S) (k : ℕ) (w : W)
    (hw : w ∈ S) : (f ^ k) w ∈ S := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact h _ ih

theorem pf_mem (A : GLOps n K W) (S : Submodule K W) (x y : Fin n) (h1 : ∀ w ∈ S, A x y w ∈ S)
    (h2 : ∀ w ∈ S, A y x w ∈ S) (c T : ℕ) (w : W) (hw : w ∈ S) : pf A x y c T w ∈ S := by
  rw [pf_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (pow_mem_stable _ S h2 k _ (Submodule.smul_mem _ _ (pow_mem_stable _ S h1 k w hw))))

theorem pow_intertw (f : Module.End K W) (g : Module.End K V) (π : W →ₗ[K] V) (S : Submodule K W)
    (hS : ∀ w ∈ S, f w ∈ S) (h : ∀ w ∈ S, π (f w) = g (π w)) (k : ℕ) (w : W) (hw : w ∈ S) :
    π ((f ^ k) w) = (g ^ k) (π w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      h _ (pow_mem_stable f S hS k w hw), ih]

theorem pf_intertw (A : GLOps n K W) (E : GLOps n K V) (π : W →ₗ[K] V) (S : Submodule K W) (x y : Fin n)
    (hS : ∀ w ∈ S, A x y w ∈ S) (h1 : ∀ w ∈ S, π (A x y w) = E x y (π w)) (h2 : ∀ w, π (A y x w) = E y x (π w))
    (c T : ℕ) (w : W) (hw : w ∈ S) : π (pf A x y c T w) = pf E x y c T (π w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pf_apply, pf_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, pow_intertw (A y x) (E y x) π ⊤ (fun _ _ => Submodule.mem_top)
    (fun w _ => h2 w) k _ Submodule.mem_top, map_smul, pow_intertw (A x y) (E x y) π S hS h1 k w hw]

theorem pf_wt {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      (E a' b' ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero => intro μ y hy; simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply]
      have := hs a' b' _ _ (ih μ y hy)
      convert this using 2
      rw [succ_nsmul, add_assoc]
  have hr : rootW a b + rootW b a = 0 := by
    unfold rootW
    abel
  rw [pf_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  have h1 := hpow b a k _ _ (Submodule.smul_mem _ ((k.factorial : K)⁻¹) (hpow a b k ν x hx))
  have he : ν + k • rootW a b + k • rootW b a = ν := by
    rw [add_assoc, ← smul_add, hr, smul_zero, add_zero]
  rw [he] at h1
  exact h1

theorem pf_sub (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x - x ∈ LinearMap.range (E b a) := by
  rw [pf_apply, Finset.sum_range_succ', add_sub_assoc]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => ?_) ?_
  · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    rw [pow_succ', Module.End.mul_apply]
    exact LinearMap.mem_range_self _ _
  · simp

end Gen

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tensOps (E : GLOps n K V) : GLOps n K (Fin n → V) := fun x y =>
  LinearMap.pi fun i => E x y ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V) +
    if i = x then (LinearMap.proj y : (Fin n → V) →ₗ[K] V) else 0

theorem tensOps_apply (E : GLOps n K V) (x y : Fin n) (w : Fin n → V) (i : Fin n) :
    tensOps E x y w i = E x y (w i) + if i = x then w y else 0 := by
  by_cases h : i = x <;> simp [tensOps, h]

theorem tens_rel {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) :
    tensOps E a b * tensOps E c d - tensOps E c d * tensOps E a b =
      (if b = c then tensOps E a d else 0) - (if d = a then tensOps E c b else 0) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  have hc := LinearMap.congr_fun (hE.1 a b c d) (w i)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, tensOps_apply, map_add (f := _)]
  split_ifs at hc ⊢ <;> subst_vars <;>
    (try simp only [tensOps_apply, LinearMap.zero_apply, Pi.zero_apply, map_zero, add_zero, zero_add,
      sub_zero, LinearMap.sub_apply] at hc ⊢) <;>
    (try split_ifs at hc ⊢) <;> (try subst_vars) <;>
    first
    | abel1
    | (rw [sub_eq_iff_eq_add] at hc; rw [hc]; abel1)
    | skip
  all_goals done

theorem tens_single_wt (E : GLOps n K V) (ν : Fin n → ℤ) (i : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    (Pi.single i x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single i 1) := by
  unfold weightSp at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro a
  have ha := hx a
  rw [LinearMap.mem_ker] at ha ⊢
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at ha ⊢
  funext j
  rw [tensOps_apply]
  by_cases hj : j = i
  · subst hj
    by_cases hja : j = a
    · subst hja
      simp [ha, add_smul]
    · simp [ha, hja, Ne.symm hja]
  · by_cases hja : j = a
    · subst hja
      simp [hj]
    · simp [hj, hja]

theorem tens_isGLRep [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (tensOps E) := by
  refine ⟨fun a b c d => tens_rel hE a b c d,
    fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hw : w i ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ mu : Fin n → ℤ, weightSp E mu) ≤
      (⨆ mu : Fin n → ℤ, weightSp (tensOps E) mu).comap (LinearMap.single K (fun _ : Fin n => V) i) :=
    iSup_le fun mu y hy => Submodule.mem_iSup_of_mem (mu + Pi.single i 1) (tens_single_wt E mu i y hy)
  exact hle hw

end Tens

end Formalism.MainNotions.G.ExtremalProjector
end
end
