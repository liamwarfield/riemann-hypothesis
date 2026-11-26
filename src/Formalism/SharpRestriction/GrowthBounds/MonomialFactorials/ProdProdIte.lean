module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ValFactSumLe
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfNumericBound
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SLetCastSucc
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfValuationBound
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DegSubSingle
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Comm

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem pderiv_glAct (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c' d' : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    pderiv (a, c) (M.glAct p LL J c' d' x) = M.glAct p LL J c' d' (pderiv (a, c) x) +
      (if (a : ℕ) < J then
        (if LL.vec a then (if c = c' then pderiv (a, d') x else 0) else (if c = d' then -pderiv (a, c') x else 0))
       else 0) := by
  classical
  have hcomm : ∀ (u v : Fin N × Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      pderiv u (pderiv v y) = pderiv v (pderiv u y) := by
    intro u v y
    refine MvPolynomial.induction_on' y (fun s b => ?_) (fun q q' hq hq' => ?_)
    · simp only [pderiv_monomial]
      by_cases huv : u = v
      · subst huv
        rfl
      · have h1 : (s - Finsupp.single v 1 : Fin N × Fin r →₀ ℕ) u = s u := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm huv), Nat.sub_zero]
        have h2 : (s - Finsupp.single u 1 : Fin N × Fin r →₀ ℕ) v = s v := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg huv, Nat.sub_zero]
        rw [h1, h2, tsub_right_comm, mul_assoc, mul_assoc, mul_comm ((s u : ℚ_[p]))]
    · simp only [map_add (f := _), hq, hq']
  have hg : ∀ y, M.glAct p LL J c' d' y = ∑ i : Fin N, (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') y else -(X (i, d') * pderiv (i, c') y)) else 0) := by
    intro y
    simp only [M.glAct, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have key : ∀ i : Fin N, pderiv (a, c) (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') x else -(X (i, d') * pderiv (i, c') x)) else 0) =
      (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') (pderiv (a, c) x)
        else -(X (i, d') * pderiv (i, c') (pderiv (a, c) x))) else 0) +
      (if a = i then (if (i : ℕ) < J then (if LL.vec i then (if c = c' then pderiv (i, d') x else 0)
        else (if c = d' then -pderiv (i, c') x else 0)) else 0) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < J
    · by_cases hv : LL.vec i
      · simp only [hi, hv, if_true, pderiv_mul, pderiv_X, Pi.single_apply]
        rw [hcomm (a, c) (i, d') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcc : c = c'
          · subst hcc
            simp
            try abel
          · simp [hcc, Ne.symm hcc]
        · have hne : (i, c') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
      · simp only [hi, hv, if_true, Bool.false_eq_true, if_false, map_neg, pderiv_mul, pderiv_X,
          Pi.single_apply]
        rw [hcomm (a, c) (i, c') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcd : c = d'
          · subst hcd
            simp
            try abel
          · simp [hcd, Ne.symm hcd]
        · have hne : (i, d') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
    · simp [hi]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hg, hg, map_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq]
  simp

theorem pderiv_keep {σ : Type} (v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → m - Finsupp.single v 1 ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, pderiv v x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  have hx' := (mem_restrictSupport_iff ℚ_[p]).mp hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmv : m v = 0
  · simp [hmv]
  · rw [mem_restrictSupport_iff]
    intro m' hm'
    have h1 := support_monomial_subset hm'
    rw [Finset.mem_singleton] at h1
    rw [h1]
    exact h m (hx' hm) (Nat.one_le_iff_ne_zero.mpr hmv)

theorem wt_sub_single (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c0 : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (h : 1 ≤ m (a, c)) :
    M.wt LL J c0 (m - Finsupp.single (a, c) 1) =
      M.wt LL J c0 m - (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then 1 else -1) else 0) := by
  have key : ∀ i, (((m - Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ)) (i, c0) : ℤ) =
      (m (i, c0) : ℤ) - (if i = a ∧ c = c0 then 1 else 0) := by
    intro i
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hh : i = a ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hh
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Nat.cast_sub h]
      simp
    · rw [if_neg, if_neg hh]
      · simp
      · intro h'
        apply hh
        simp only [Prod.mk.injEq] at h'
        exact ⟨h'.1.symm, h'.2⟩
  unfold M.wt
  simp only [key]
  rw [show (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then (1 : ℤ) else -1) else 0) =
      ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then (if i = a ∧ c = c0 then (1 : ℤ) else 0)
        else -(if i = a ∧ c = c0 then 1 else 0)) else 0) from ?_]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  · rw [Finset.sum_eq_single a]
    · by_cases h1 : (a : ℕ) < J <;> by_cases h2 : c = c0 <;> by_cases h3 : LL.vec a <;> simp [h1, h2, h3]
    · intro b _ hb
      simp [hb]
    · simp

variable [NeZero r]

theorem ycond_vec (LL LL' : M.Letters N) (h : LL.vec = LL'.vec) (J : ℕ) (Mt : WithTop ℤ) :
    M.YCond p (r := r) LL J Mt = M.YCond p (r := r) LL' J Mt := by
  obtain ⟨v, d⟩ := LL
  obtain ⟨v', d'⟩ := LL'
  simp only at h
  subst h
  rfl

theorem pderiv_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (a : Fin N) (hva : (a : ℕ) < J → LL.vec a = true)
    (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    pderiv (a, c) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
      S' = Submodule.span ℚ_[p] {z | ∃ (c'' : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
        y ∈ M.YCond p (r := r) LL J Mt ∧ z = pderiv (a, c'') y} := ⟨_, rfl⟩
  have hgen : ∀ (c'' : Fin r) y, y ∈ M.YCond p (r := r) LL J Mt → pderiv (a, c'') y ∈ S' := by
    intro c'' y hy
    rw [hS']
    exact Submodule.subset_span ⟨c'', y, hy, rfl⟩
  have hsupp : S' ≤ MvPolynomial.restrictSupport ℚ_[p]
      {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨c'', y, hy, rfl⟩
    refine pderiv_keep (a, c'') _ _ ?_ y (Formalism.CountingSumsFrames.ycond_le_supp LL J Mt hy)
    intro m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [wt_sub_single LL J a c'' 0 m h1]
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    by_cases ha : (a : ℕ) < J
    · have hv := hva ha
      by_cases hc : c'' = 0 <;> simp [ha, hv, hc]
    · simp [ha]
  have hstab : M.GlStable p LL J S' := by
    intro c d z hz
    rw [hS'] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c'', y, hy, rfl⟩ := hz
      have e := pderiv_glAct LL J a c'' c d y
      have hy' : M.glAct p LL J c d y ∈ M.YCond p (r := r) LL J Mt :=
        Formalism.CountingSumsFrames.ycond_glStable LL J Mt c d y hy
      have hext : (if (a : ℕ) < J then
          (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) ∈ S' := by
        split_ifs
        · exact hgen d y hy
        · exact S'.zero_mem
        · exact S'.neg_mem (hgen c y hy)
        · exact S'.zero_mem
        · exact S'.zero_mem
      rw [show M.glAct p LL J c d (pderiv (a, c'') y) = pderiv (a, c'') (M.glAct p LL J c d y) -
        (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) by rw [e]; abel]
      exact S'.sub_mem (hgen c'' _ hy') hext
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add (f := _)]
      exact S'.add_mem hz hz'
    | smul t z _ hz =>
      rw [map_smul]
      exact S'.smul_mem t hz
  have hle : S' ≤ M.YCond p (r := r) LL J Mt := by
    unfold M.YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (hgen c x hx)

theorem tieF_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (W E : Fin N) (hW : (W : ℕ) < J) (hE : (E : ℕ) < J)
    (hvW : LL.vec W = true) (hvE : LL.vec E = false)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    tieF (fun c => (W, c)) (fun c => (E, c)) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  have ht : ∀ y : MvPolynomial (Fin N × Fin r) ℚ_[p], tieF (fun c => (W, c)) (fun c => (E, c)) y =
      ∑ c0 : Fin r, pderiv (W, c0) (pderiv (E, c0) y) := by
    intro y
    simp [tieF, LinearMap.sum_apply]
  refine Formalism.CountingSumsFrames.ycond_keep LL J Mt (tieF (fun c => (W, c)) (fun c => (E, c))) ?_ ?_ x hx
  · intro c d y
    have step : ∀ c0, pderiv (W, c0) (pderiv (E, c0) (M.glAct p LL J c d y)) =
        M.glAct p LL J c d (pderiv (W, c0) (pderiv (E, c0) y)) +
        (if c0 = c then pderiv (W, d) (pderiv (E, c0) y) else 0) +
        (if c0 = d then -pderiv (W, c0) (pderiv (E, c) y) else 0) := by
      intro c0
      rw [pderiv_glAct LL J E c0 c d y, map_add (f := _), pderiv_glAct LL J W c0 c d (pderiv (E, c0) y)]
      simp only [hE, hW, hvW, hvE, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> simp [map_neg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, ht, map_sum, Finset.sum_congr rfl (fun c0 _ => step c0), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, add_assoc, add_neg_cancel, add_zero]
  · intro z hz
    rw [ht]
    refine Submodule.sum_mem _ fun c0 _ => ?_
    have hQ1 : pderiv (E, c0) z ∈ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ |
        (((M.wt LL J 0 m - (if c0 = 0 then 1 else 0) : ℤ)) : WithTop ℤ) ≤ Mt} := by
      refine pderiv_keep (E, c0) {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} _ ?_ z hz
      intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J E c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hE, hvE, hc] using hm
    refine pderiv_keep (W, c0) _ {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} ?_ _ hQ1
    · intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J W c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hW, hvW, hc] using hm

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hyp

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem hypU_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypU p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp c y hy
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨hpol _ _ G.uPos c ?_ ?_ y hy.1, fun k => ?_⟩
  · simp only [M.BlockData.lettersAt, eq_self_iff_true, if_true]
    omega
  · intro i hi
    simp only [M.BlockData.lettersAt, if_neg hi]
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt j (jp + 1)) (G.lettersAt j jp) rfl]
    exact pderiv_ycond (p := p) _ _ _ G.uPos (fun _ => hB.2.2.1) c y (hy.2 k)

theorem sum_update_ite {t : ℕ} (P : Fin t → Prop) [DecidablePred P] (j : Fin t → ℕ) (i : Fin t) :
    ∑ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      ∑ i', (if P i' then j i' else 0) + (if P i then 1 else 0) := by
  have h : ∀ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      (if P i' then j i' else 0) + (if i' = i then (if P i then 1 else 0) else 0) := by
    intro i'
    by_cases hi : i' = i
    · subst hi
      rw [Function.update_self]
      split_ifs <;> simp_all
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  rw [Finset.sum_congr rfl fun i' _ => h i', Finset.sum_add_distrib]
  simp

theorem hypTie_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypJoin p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp i y hy
  obtain ⟨hlt, hvW, hvE⟩ := hB.1.2.1 i
  set W := G.letterAt (G.T.pos i) with hWdef
  set E := G.letterAt (G.T.pos i + 1) with hEdef
  have hWv : (W : ℕ) = G.T.pos i := by
    simp only [hWdef, M.BlockData.letterAt]
    omega
  have hEv : (E : ℕ) = G.T.pos i + 1 := by
    simp only [hEdef, M.BlockData.letterAt]
    omega
  have hWE : W ≠ E := fun h => by
    have := congrArg Fin.val h
    omega
  have hvW' : G.LL.vec W = true := by
    rwa [show W = ⟨G.T.pos i, by omega⟩ from Fin.ext hWv]
  have hvE' : G.LL.vec E = false := by
    rwa [show E = ⟨G.T.pos i + 1, hlt⟩ from Fin.ext hEv]

  have hdeg : ∀ x : Fin N, (G.lettersAt (Function.update j i (j i + 1)) jp).deg x =
      (G.lettersAt j jp).deg x -
        (if ((x : ℕ) = G.T.pos i ∨ (x : ℕ) = G.T.pos i + 1) then 1 else 0) := by
    intro x
    simp only [M.BlockData.lettersAt]
    change G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
      (x : ℕ) = G.T.pos k + 1 then Function.update j i (j i + 1) k else 0) -
      (if x = G.uPos then jp else 0) =
      (G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
        (x : ℕ) = G.T.pos k + 1 then j k else 0) -
        (if x = G.uPos then jp else 0)) - _
    rw [sum_update_ite]
    omega
  have htie : ∀ x : MvPolynomial (Fin N × Fin r) ℚ_[p],
      Formalism.GM.tieF (fun c => (W, c)) (fun c => (E, c)) x =
      ∑ c, pderiv (W, c) (pderiv (E, c) x) := by
    intro x
    simp [Formalism.GM.tieF]
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨?_, fun k => ?_⟩
  · rw [htie]
    refine Submodule.sum_mem _ fun c _ => ?_
    let L1 : M.Letters N := ⟨G.LL.vec, fun x =>
      if x = E then (G.lettersAt j jp).deg x - 1 else (G.lettersAt j jp).deg x⟩
    have h1 := hpol (G.lettersAt j jp) L1 E c (by show (if E = E then _ else _) = _; rw [if_pos rfl])
      (fun x hx => by show (if x = E then _ else _) = _; rw [if_neg hx]) y hy.1
    refine hpol L1 _ W c ?_ ?_ _ h1
    · rw [hdeg W, if_pos (Or.inl hWv)]
      show _ = (if W = E then _ else _) - 1
      rw [if_neg hWE]
    · intro x hx
      rw [hdeg x]
      show _ = (if x = E then _ else _)
      by_cases hxE : x = E
      · have hxv : (x : ℕ) = G.T.pos i + 1 := by rw [hxE]; exact hEv
        rw [if_pos hxE, if_pos (Or.inr hxv)]
      · rw [if_neg hxE, if_neg, Nat.sub_zero]
        rintro (h | h)
        · exact hx (Fin.ext (h.trans hWv.symm))
        · exact hxE (Fin.ext (h.trans hEv.symm))
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt (Function.update j i (j i + 1)) jp)
      (G.lettersAt j jp) rfl]
    have hx := hy.2 k
    by_cases hE : (E : ℕ) < G.T.J k
    · exact tieF_ycond (p := p) (G.lettersAt j jp) (G.T.J k) (G.T.thr k) W E (by omega) hE hvW' hvE' y hx
    · rw [htie]
      exact Submodule.sum_mem _ fun c _ => pderiv_ycond (p := p) _ _ _ W (fun _ => hvW') c _
        (pderiv_ycond (p := p) _ _ _ E (fun h => absurd h hE) c y hx)

end Hyp

section Inst

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restLL_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestLL C0 CE1 CE2 X :=
  restLL_of C0 CE1 CE2 X hCYb hCE1 hCE2 hH fun aTop aPlus b =>
    ⟨hypTie_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b),
      hypU_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b)⟩

theorem block_valuation_Zp_of_valuation_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestVal C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_lattice_inclusion C0 CE1 CE2 X (Nat.one_le_iff_ne_zero.mpr X.hm)
    (restLL_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH) hV

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hom

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def zLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.castSucc G.uPos) (fun i => M.finPos N (G.T.pos i))

def sLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.last N) (fun i => M.finPos N (G.T.pos i + 1))

def wL (a : Fin (N + 1)) : M.BVar N r G.T.t → ℕ
  | Sum.inl (a', _) => if a' = a then 1 else 0
  | Sum.inr (i, false) => if zLet G i = a then 1 else 0
  | Sum.inr (i, true) => if sLet G i = a then 1 else 0

def chDeg (LL : M.Letters N) (a : Fin (N + 1)) : ℕ := ∑ a0 : Fin N, if Fin.castSucc a0 = a then LL.deg a0 else 0

def dLvl (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∑ i, j i • ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0))) +
    jp • ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) +
    (∑ i, G.T.z i • (if M.finPos N (G.T.pos i) = a then 1 else 0)) +
    G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) + chDeg (G.lettersAt j jp) a +
    (if Fin.last N = a then G.B - jp else 0)

theorem zLet_castSucc (i : Fin G.T.t) : zLet G (Fin.castSucc i) = M.finPos N (G.T.pos i) := by
  simp [zLet]

theorem zLet_last : zLet G (Fin.last G.T.t) = Fin.castSucc G.uPos := by
  simp [zLet]

theorem sLet_castSucc (i : Fin G.T.t) : sLet G (Fin.castSucc i) = M.finPos N (G.T.pos i + 1) := by
  simp [sLet]

theorem sLet_last : sLet G (Fin.last G.T.t) = Fin.last N := by
  simp [sLet]

theorem hom_Ehat (a : Fin (N + 1)) (i : Fin G.T.t) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Ehat p (r := r) i)
      ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0)) := by
  unfold M.BlockData.Ehat
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.castSucc i))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_castSucc, sLet_castSucc]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i), c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i + 1), c) : M.BVar N r G.T.t)) using 1
    simp [wL]

theorem hom_Eplus (a : Fin (N + 1)) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Eplus p (r := r))
      ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) := by
  unfold M.BlockData.Eplus
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.last G.T.t))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_last, sLet_last]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.xiVar N r G.T.t c)) using 1
    simp [wL, M.xiVar]

theorem hom_chain (a : Fin (N + 1)) (LL : M.Letters N) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (wL (r := r) G a) (rename (M.chainEmb N r G.T.t) y) (chDeg LL a) := by
  classical
  have hsupp : ∀ m ∈ y.support, M.MultiDeg LL m := fun m hm => hy hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [y.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  unfold chDeg
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hsupp m hm i]
  simp only [M.chainEmb, wL]
  by_cases h : Fin.castSucc i = a <;> simp [h]

theorem hom_xi (a : Fin (N + 1)) (b : ℕ) (g : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ M.XiPolZ p N r G.T.t b) :
    IsWeightedHomogeneous (wL (r := r) G a) g (if Fin.last N = a then b else 0) := by
  classical
  intro μ hμ
  obtain ⟨hv, hb⟩ := hg.1 (mem_support_iff.mpr hμ)
  have hw : ∀ v, μ v * wL (r := r) G a v = μ v * (if Fin.last N = a then 1 else 0) := by
    intro v
    by_cases h0 : μ v = 0
    · simp [h0]
    · obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
      rfl
  have hsum : ∑ v, μ v = ∑ c, μ (M.xiVar N r G.T.t c) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := M.xiVar N r G.T.t) (by intro c _ c' _ h; simpa [M.xiVar] using h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv'
    by_contra h0
    obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
    exact hv' (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [smul_eq_mul, hw, ← Finset.sum_mul, hsum, hb]
  split_ifs <;> simp

theorem hom_gens (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hx : x ∈ G.gens p (r := r) j jp) : IsWeightedHomogeneous (wL (r := r) G a) x (dLvl G j jp a) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  have hX : ∀ i, IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.castSucc i)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if M.finPos N (G.T.pos i) = a then 1 else 0) := by
    intro i
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i)) using 1
    simp [wL, M.scalZ, zLet_castSucc]
  have hXP : IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.last G.T.t)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if Fin.castSucc G.uPos = a then 1 else 0) := by
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t)) using 1
    simp [wL, M.scalZ, zLet_last]
  unfold dLvl
  exact (((((IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hom_Ehat p G a i).pow (j i))).mul
    ((hom_Eplus p G a).pow jp)).mul (IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hX i).pow (G.T.z i)))).mul
    (hXP.pow G.zPlus)).mul (hom_chain p G a _ y hy.2.1)).mul (hom_xi p G a _ g hg)

theorem SSZ_support (z : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hz : z ∈ G.SSZ p (r := r)) :
    ∀ μ ∈ z.support, ∃ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp ∧
      ∀ a, Finsupp.weight (wL (r := r) G a) μ = dLvl G j jp a := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hlev, hx⟩ := hx
    intro μ hμ
    exact ⟨j, jp, hlev, fun a => hom_gens p G a j jp x hx (mem_support_iff.mp hμ)⟩
  | zero => simp
  | add x y _ _ hx hy =>
    intro μ hμ
    rcases Finset.mem_union.mp (support_add hμ) with h | h
    · exact hx μ h
    · exact hy μ h
  | smul c x _ hx =>
    intro μ hμ
    exact hx μ (support_smul hμ)

end Hom

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestValNum : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ (j' : Fin (gB C0 CE1 CE2 X aTop aPlus b).T.t → ℕ) (jp' : ℕ), (gB C0 CE1 CE2 X aTop aPlus b).LevelOK j' jp' →
        ∀ μ : Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t →₀ ℕ,
          (∀ a, Finsupp.weight (wL (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) a) μ =
            dLvl (gB C0 CE1 CE2 X aTop aPlus b) j' jp' a) →
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem restVal_of_num (h : RestValNum C0 CE1 CE2 X) : RestVal C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK l hl z hz μ hμ
  obtain ⟨j', jp', hl', hw⟩ := SSZ_support X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) z hz μ hμ
  exact h aTop hT aPlus hP b hK l hl j' jp' hl' μ hw

theorem block_valuation_Zp_of_numeric_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestValNum C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_valuation_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restVal_of_num C0 CE1 CE2 X hV)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

section Arith

variable (p : ℕ) [hp : Fact p.Prime]

theorem val_fact_sum_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (L : ℕ) (hL : Nat.log p (∑ i ∈ s, f i) ≤ L) :
    padicValNat p (∑ i ∈ s, f i)! ≤ padicValNat p (∏ i ∈ s, (f i)!) + s.card * L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL
    have hL' : Nat.log p (∑ i ∈ s, f i) ≤ L := le_trans (Nat.log_mono_right (Nat.le_add_left _ _)) hL
    have ih' := ih hL'
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_eq_ite, if_neg ha]
    generalize hT : ∑ i ∈ s, f i = T at *
    have hC : (f a + T).choose (f a) * (f a)! * T ! = (f a + T)! := by
      have h5 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (f a) T)
      rwa [Nat.add_sub_cancel_left] at h5
    have hv : padicValNat p ((f a + T).choose (f a)) ≤ L := by
      have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + T) (k := f a)
      rw [Nat.factorization_def _ hp.out] at h1
      rw [← Nat.padicValNat_def] at h1
      exact h1.trans hL
    have hc0 : (f a + T).choose (f a) ≠ 0 := (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    have hpr : (∏ i ∈ s, (f i)!) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
    rw [← hC, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (mul_ne_zero hc0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hc0 (Nat.factorial_ne_zero _), (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.factorial_ne_zero _) hpr]
    nlinarith

end Arith

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def letOf : M.BVar N r G.T.t → Fin (N + 1)
  | Sum.inl (a', _) => a'
  | Sum.inr (i, false) => zLet G i
  | Sum.inr (i, true) => sLet G i

theorem wL_eq (a : Fin (N + 1)) (v : M.BVar N r G.T.t) : wL (r := r) G a v = if letOf G v = a then 1 else 0 := by
  rcases v with ⟨a', c⟩ | ⟨i, _ | _⟩ <;> rfl

theorem weight_eq (a : Fin (N + 1)) (μ : M.BVar N r G.T.t →₀ ℕ) :
    Finsupp.weight (wL (r := r) G a) μ = ∑ v ∈ Finset.univ.filter (fun v => letOf G v = a), μ v := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [wL_eq]
  split_ifs <;> simp

theorem val_letters_le (μ : M.BVar N r G.T.t →₀ ℕ) (d : Fin (N + 1) → ℕ)
    (hw : ∀ a, Finsupp.weight (wL (r := r) G a) μ = d a) (L : ℕ) (hL : ∀ a, Nat.log p (d a) ≤ L) :
    padicValNat p (∏ a, (d a)!) ≤ padicValNat p (μ.prod fun _ k => k !) + ((N + 1) * r + (G.T.t + 1) * 2) * L := by
  classical
  have hprod : ∀ {α : Type} (s : Finset α) (g : α → ℕ), (∀ i ∈ s, g i ≠ 0) →
      padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i) := by
    intro α s g hg
    induction s using Finset.induction_on with
    | empty => simp [Nat.padicValNat_def, multiplicity_one_right]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]
  have hμ : (μ.prod fun _ k => k !) = ∏ v, (μ v)! := Finsupp.prod_fintype _ _ (fun _ => rfl)
  rw [hμ, hprod _ _ (fun _ _ => Nat.factorial_ne_zero _), hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)]
  have hfib : ∀ a, padicValNat p (d a)! ≤ ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
      (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L := by
    intro a
    have hd : d a = ∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), μ v := by rw [← hw a, weight_eq]
    have h6 := val_fact_sum_le p (Finset.univ.filter (fun v => letOf (r := r) G v = a)) μ L (by rw [← hd]; exact hL a)
    rw [hprod _ _ (fun _ _ => Nat.factorial_ne_zero _)] at h6
    rw [hd]
    exact h6
  calc ∑ a, padicValNat p (d a)!
      ≤ ∑ a, (∑ v ∈ Finset.univ.filter (fun v => letOf (r := r) G v = a), padicValNat p (μ v)! +
          (Finset.univ.filter (fun v => letOf (r := r) G v = a)).card * L) := Finset.sum_le_sum (fun a _ => hfib a)
    _ = ∑ v, padicValNat p (μ v)! + (Finset.univ : Finset (M.BVar N r G.T.t)).card * L := by
        rw [Finset.sum_add_distrib, Finset.sum_fiberwise, ← Finset.sum_mul,
          Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (letOf (r := r) G v))]
    _ = _ := by
        simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

theorem prod_prod_ite {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] (x : ι → α) (n : ι → ℕ) :
    ∏ a : α, ∏ i : ι, (if x i = a then n i else 0)! = ∏ i, (n i)! := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_single (x i)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem smul_ite_one (n : ℕ) (c : Prop) [Decidable c] : n • (if c then 1 else 0 : ℕ) = if c then n else 0 := by
  split_ifs <;> simp

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def fL (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∏ i, ((if M.finPos N (G.T.pos i) = a then j i else 0)! * (if M.finPos N (G.T.pos i + 1) = a then j i else 0)!)) *
    ((if Fin.castSucc G.uPos = a then jp else 0)! * (if Fin.last N = a then jp else 0)!) *
    (∏ i, (if M.finPos N (G.T.pos i) = a then G.T.z i else 0)!) *
    (if Fin.castSucc G.uPos = a then G.zPlus else 0)! *
    (∏ a0 : Fin N, (if Fin.castSucc a0 = a then (G.lettersAt j jp).deg a0 else 0)!) *
    (if Fin.last N = a then G.B - jp else 0)!

theorem fL_dvd (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : fL G j jp a ∣ (dLvl G j jp a)! := by
  have hfac : ∀ {x y X Y : ℕ}, x ∣ X ! → y ∣ Y ! → x * y ∣ (X + Y)! := fun hx hy =>
    (mul_dvd_mul hx hy).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  unfold fL dLvl chDeg
  simp only [smul_add, smul_ite_one]
  refine hfac (hfac (hfac (hfac (hfac ?_ ?_) ?_) dvd_rfl) ?_) dvd_rfl
  · exact (Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
      Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.prod_factorial_dvd_factorial_sum _ _)
  · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _

theorem prod_fL (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∏ a, fL G j jp a = (∏ i, (j i)!) * (∏ i, (j i)!) * (jp ! * jp !) * (∏ i, (G.T.z i)!) * G.zPlus ! *
      (∏ a0, ((G.lettersAt j jp).deg a0)!) * (G.B - jp)! := by
  have hsingle : ∀ (b : Fin (N + 1)) (n : ℕ), ∏ a, (if b = a then n else 0)! = n ! := by
    intro b n
    rw [Finset.prod_eq_single b]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  unfold fL
  simp only [Finset.prod_mul_distrib, prod_prod_ite, hsingle]

def binT (j : Fin G.T.t → ℕ) (jp : ℕ) (i : Fin G.T.t) : ℕ :=
  ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
    (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i)

def binP (jp : ℕ) : ℕ := ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp

theorem lvC_eq (j : Fin G.T.t → ℕ) (jp : ℕ) :
    lvC (r := r) G j jp * degFact G j jp = (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) := by
  rw [prod_fL]
  unfold lvC degFact binT binP
  rw [Finset.prod_mul_distrib]
  ring

theorem val_lvC_le (j : Fin G.T.t → ℕ) (jp : ℕ) (L : ℕ)
    (h1 : ∀ i, Nat.log p ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
      (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1) ≤ L)
    (h2 : Nat.log p ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1) ≤ L) :
    padicValNat p (lvC (r := r) G j jp * degFact G j jp) ≤
      padicValNat p (∏ a, (dLvl G j jp a)!) + (G.T.t + 1) * L := by
  have hp' := hp.out
  rw [lvC_eq]
  by_cases h0 : (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) = 0
  · simp [h0, Nat.padicValNat_def]
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp h0
  obtain ⟨hBt, hBp⟩ := mul_ne_zero_iff.mp hB
  have hD : (∏ a, (dLvl G j jp a)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero _
  rw [Nat.padicValNat_def, Nat.padicValNat_def,
    ← Nat.factorization_def _ hp', ← Nat.factorization_def _ hp', Nat.factorization_mul hA hB,
    Nat.factorization_mul hBt hBp]
  simp only [Finsupp.add_apply]
  have h1' : (∏ a, fL G j jp a).factorization p ≤ (∏ a, (dLvl G j jp a)!).factorization p :=
    (Nat.factorization_le_iff_dvd hA hD).mpr
      (Finset.prod_dvd_prod_of_dvd _ _ fun a _ => fL_dvd G j jp a) p
  have h2' : (∏ i, binT (r := r) G j jp i).factorization p ≤ G.T.t * L := by
    rw [Nat.factorization_prod (fun i _ => Finset.prod_ne_zero_iff.mp hBt i (Finset.mem_univ _))]
    rw [Finset.sum_apply']
    calc ∑ i, (binT (r := r) G j jp i).factorization p ≤ ∑ _i : Fin G.T.t, L :=
          Finset.sum_le_sum fun i _ => le_trans Nat.factorization_choose_le_log (h1 i)
      _ = G.T.t * L := by simp
  have h3' : (binP (r := r) G jp).factorization p ≤ L := le_trans Nat.factorization_choose_le_log h2
  rw [add_mul, one_mul]
  linarith

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
