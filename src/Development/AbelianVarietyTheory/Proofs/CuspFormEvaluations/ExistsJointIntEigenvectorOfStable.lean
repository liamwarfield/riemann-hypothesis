module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable
namespace GlobalTheory

theorem exists_int_eigenvector_of_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ⨆ n : ℤ, f.eigenspace (n : K) = ⊤)
    (U : Submodule K V) (hU : ∀ x ∈ U, f x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
  classical
  have key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) →
      ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx0 hx; simp at hx; exact absurd hx hx0
    | insert a s _ ih =>
      intro x hxU hx0 hx
      by_cases hw : f x - (a : K) • x = 0
      · exact ⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩
      · refine ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_
        rw [Finset.iSup_insert, Submodule.mem_sup] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        rw [Module.End.mem_eigenspace_iff] at hy
        have h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z := by
          rw [map_add (f := _), hy, smul_add]; abel
        rw [h1]
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)
        have : (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f := by
          refine iSup₂_le fun n hn => ?_
          intro w hw
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]
          exact Submodule.smul_mem _ _
            (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)
        exact this hz
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K) := by rw [hf]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  exact key s x hxU hx0 hs

theorem exists_joint_int_eigenvector_of_stable {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : ι → Module.End K V) (hc : ∀ a b, f a * f b = f b * f a)
    (hf : ∀ a, ⨆ n : ℤ, (f a).eigenspace (n : K) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, f a x ∈ W) (hW0 : W ≠ ⊥) :
    ∃ κ : ι → ℤ, ∃ u ∈ W, u ≠ 0 ∧ ∀ a, f a u = (κ a : K) • u := by
  classical
  have key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧
      ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨U, hUW, hU0, hU, κ, hκ⟩ := ih
      obtain ⟨n, u, huU, hu0, hu⟩ := exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0
      refine ⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_,
        Function.update κ a n, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩
      · intro b x hx
        refine ⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 := Module.End.mem_eigenspace_iff.mp hx.2
        have h2 := LinearMap.congr_fun (hc a b) x
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb x hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hx.2
        · have : b ≠ a := fun h => ha (h ▸ hb)
          rw [Function.update_of_ne this]; exact hκ b hb x hx.1
  obtain ⟨U, hUW, hU0, -, κ, hκ⟩ := key Finset.univ
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩

theorem exists_highest_vector {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by
  classical

  obtain ⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩ := exists_joint_int_eigenvector_of_stable
    (fun a : T × Fin m => e a.1 a.2 a.2)
    (by
      intro a b
      have := he a.1 b.1 a.2 b.2 b.2
      rw [sub_self, ite_self, zero_smul] at this
      exact sub_eq_zero.mp this)
    (by
      intro a
      rw [eq_top_iff, ← hdiag]
      refine iSup_le fun κ => ?_
      exact le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2))
        (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))
    W (fun a => hW a.1 a.2 a.2) hW0

  let ht : (T → Fin m → ℤ) → ℤ := fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i
  let h : Module.End K V := ∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i
  have hhW : ∀ w ∈ W, h w ∈ W := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)
  have hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) →
      h v = (ht κ : K) • v := by
    intro κ v hv
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℤ := {n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhW)
    refine (hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_
    rintro n ⟨κ, rfl, v, hvW, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh κ v hv)
    · exact fun h0 => hv0 (congrArg Subtype.val h0)
  have hSne : S.Nonempty :=
    ⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩
  obtain ⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨v, hvW, hv0, ?_, κ, hv⟩
  intro t' k l hkl
  by_contra hne
  let δ : T → Fin m → ℤ := fun t i =>
    if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0
  have hmem : ht (κ + δ) ∈ S := by
    refine ⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩
    have h1 := LinearMap.congr_fun (he t t' i k l) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv,
      map_smul] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ← add_smul, add_comm]
    congr 1
    simp only [δ, Pi.add_apply]
    push_cast
    rfl
  have hδ : ht δ = (k : ℤ) - (l : ℤ) := by
    simp only [ht, δ]
    rw [Finset.sum_eq_single t']
    · simp [mul_sub, Finset.sum_sub_distrib]
    · intro b _ hb; simp [hb]
    · simp
  have hadd : ht (κ + δ) = ht κ + ht δ := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h2 := hmin _ hmem
  have h3 : (k : ℕ) < l := hkl
  simp only [id] at h2
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogExpMulLeOfGeneratorSupBound
namespace GlobalTheory

private theorem log_one_add_le_log_two_add_of_log_le (x M : ℝ) (hx : 0 < x) (hM : 0 ≤ M)
    (h : Real.log x ≤ M) : Real.log (1 + x) ≤ Real.log 2 + M := by
  rcases le_or_gt x 1 with h1 | h1
  · have : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith
  · have : Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx.ne'] at this
    linarith


set_option maxHeartbeats 800000 in
theorem log_exp_mul_le_of_generator_sup_bound : ∀ (f r n d : ℕ) (L ℓ a rd lam t c S v p1 : ℝ), 2 ≤ L → 1 ≤ f → 1 ≤ r → r ≤ n → (d : ℝ) ≤ a → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log f ≤ 2 * L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < lam → Real.log (1 / lam ^ 2) ≤ 80 * L → 0 < t → 0 ≤ ℓ → 0 ≤ p1 → p1 ≤ Real.exp ℓ → 0 ≤ c → c ≤ Real.exp (f * r * n * L) → 0 ≤ S → S ≤ 2 * v → v ≤ c * (p1 * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (f * r : ℕ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) / (Real.sqrt Real.pi * lam)) ^ (f * r * n)) → Real.log (Real.exp (-((d : ℝ) / 2) * Real.log (Real.pi * t)) * S) ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
  intro f r n d L ℓ a rd lam t c S v p1 hL hf hr hrn hda ha hn hfL hrd hrdL hlam hlamL ht hℓ hp1
    hp1ℓ hc hcL hS hSv hv
  have hf' : 0 < f := by omega
  have hr' : 0 < r := by omega
  have hn' : 0 < n := by omega
  have hf0 : (0:ℝ) < f := by exact_mod_cast hf'
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr'
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn'
  have hrd0 : (0:ℝ) < rd := by linarith
  have hfr0 : (0:ℝ) < ((f * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hf' hr'
  have hrnR : (r:ℝ) ≤ n := by exact_mod_cast hrn
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have ha0 : 0 ≤ a := hd0.trans hda
  have hK1 : (1:ℝ) ≤ (f:ℝ) * r * n := by
    have h1 : 1 ≤ f * r * n := Nat.mul_pos (Nat.mul_pos hf' hr') hn'
    exact_mod_cast h1
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsq1 : 0 < Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
  have hfp : 0 < (f : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hf0 _
  set X := 4 * Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
    / (Real.sqrt Real.pi * lam) with hX
  have hX0 : 0 < X := by positivity
  have hlogX : Real.log X ≤ 3.5 * Real.log 2 + 49 * L := by
    have e1 : Real.log (Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n))
        = (Real.log 2 + Real.log f + Real.log r + Real.log n) / 2 := by
      rw [Real.log_sqrt (by positivity)]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    have e2 : Real.log (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
        = Real.log 2 + 3 / 2 * Real.log f + 2 * Real.log n + Real.log rd := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hf0, Real.log_pow]
      push_cast
      ring
    have e3 : Real.log (Real.sqrt Real.pi * lam) = Real.log Real.pi / 2 + Real.log lam := by
      rw [Real.log_mul hsqpi.ne' hlam.ne', Real.log_sqrt hpi.le]
    have e4 : Real.log (1 / lam ^ 2) = -2 * Real.log lam := by
      rw [one_div, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have e5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have hlr : Real.log r ≤ Real.log n := Real.log_le_log hr0 hrnR
    have hlogf0 : 0 ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
    rw [hX, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), e1, e2, e3, e5]
    rw [e4] at hlamL
    nlinarith
  have hC : Real.log (1 + X) ≤ 55 * L := by
    have := log_one_add_le_log_two_add_of_log_le X (3.5 * Real.log 2 + 49 * L) hX0
      (by nlinarith) hlogX
    nlinarith
  have hRHS0 : 0 ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L) ha0,
      mul_nonneg (by linarith : (0:ℝ) ≤ (f:ℝ) * r * n) (by linarith : (0:ℝ) ≤ L)]
  rcases hS.eq_or_lt with hS0 | hSpos
  · rw [← hS0, mul_zero, Real.log_zero]
    exact hRHS0
  set E := (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) with hEdef
  have hE : 0 < E ∧ Real.log E - (d / 2) * Real.log (Real.pi * t) ≤ 10 * L * a := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [hEdef, Nat.cast_zero, zero_div, Real.rpow_zero, Real.log_one, zero_mul, sub_zero]
      exact ⟨one_pos, by nlinarith⟩
    · have hdR : (0:ℝ) < d := by exact_mod_cast hd
      have hB : 0 < Real.pi * Real.exp 1 * t * d := by positivity
      refine ⟨Real.rpow_pos_of_pos hB _, ?_⟩
      rw [hEdef, Real.log_rpow hB, Real.log_mul (by positivity) hdR.ne',
        Real.log_mul (by positivity) ht.ne', Real.log_mul hpi.ne' (Real.exp_pos 1).ne',
        Real.log_mul hpi.ne' ht.ne', Real.log_exp]
      have hld : Real.log d ≤ 2 * L :=
        (Real.log_le_log hdR (by linarith)).trans ha
      nlinarith [mul_le_mul_of_nonneg_left hld (by linarith : (0:ℝ) ≤ d / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ a - d) (by linarith : (0:ℝ) ≤ 1 + 2 * L),
        mul_nonneg ha0 (by linarith : (0:ℝ) ≤ L - 2)]
  obtain ⟨hE0, hEb⟩ := hE
  have hvpos : 0 < v := by linarith
  have hcpos : 0 < c := by
    rcases hc.eq_or_lt with h | h
    · rw [← h, zero_mul] at hv
      linarith
    · exact h
  have hp1pos : 0 < p1 := by
    rcases hp1.eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul, zero_mul, mul_zero] at hv
      linarith
    · exact h
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hC0 : 0 < 1 + X := by linarith
  have hprod : Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n)))
      = Real.log c + Real.log p1 + Real.log E + Real.log 2 / 2
        + ((f:ℝ) * r * n) * Real.log (1 + X) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_sqrt (by norm_num)]
    push_cast
    ring
  have hlv : Real.log v ≤ Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n))) :=
    Real.log_le_log hvpos hv
  have hlS : Real.log S ≤ Real.log 2 + Real.log v := by
    rw [← Real.log_mul (by norm_num) hvpos.ne']
    exact Real.log_le_log hSpos hSv
  have hlc : Real.log c ≤ (f:ℝ) * r * n * L := by
    have := Real.log_le_log hcpos hcL
    rwa [Real.log_exp] at this
  have hlp : Real.log p1 ≤ ℓ := by
    have := Real.log_le_log hp1pos hp1ℓ
    rwa [Real.log_exp] at this
  have hKC : ((f:ℝ) * r * n) * Real.log (1 + X) ≤ ((f:ℝ) * r * n) * (55 * L) :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  have hKL : 2 ≤ ((f:ℝ) * r * n) * L := by nlinarith
  rw [Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp]
  rw [hprod] at hlv
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
namespace GlobalTheory

theorem casimir_on_highest {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (v : V) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) :
    ∑ i, ∑ j, e i j (e j i v) = ((∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) : ℤ) : K) • v := by
  have key : ∀ i j, e i j (e j i v) =
      ((if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) : K) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End K V => f v) (he i j j i)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ↓reduceIte] at h1
      rw [hv i j h, map_zero, sub_zero, hκ, hκ] at h1
      rw [h1, if_pos h]
      push_cast
      rw [sub_smul]
    · subst h
      rw [if_neg (lt_irrefl i), if_pos rfl, hκ, map_smul, hκ, smul_smul]
      push_cast
      rfl
    · rw [hv j i h, map_zero, if_neg (lt_asymm h), if_neg h.ne']
      simp
  have hsum : (∑ i : Fin m, ∑ j : Fin m,
      (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ)) =
      ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
    have h2 : ∀ i j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) =
        ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0)) -
          (if i < j then κ j else 0) := by
      intro i j
      by_cases h : i < j
      · simp [h, h.ne]
      · simp [h]
    simp_rw [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul, nsmul_eq_mul]
    have hi := i.isLt
    have hc : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = m - 1 - (i : ℕ) := by omega
    rw [hc]
    ring
  simp_rw [key]
  rw [← hsum, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.sum_smul]

theorem sl2_nonneg_weight_of_highest_weight_vector {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E F H : Module.End K V) (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ w ∈ W, F w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (l : ℤ) (hE : E v = 0) (hH : H v = (l : K) • v) : 0 ≤ l := by
  have hHFk : ∀ k : ℕ, H ((F ^ k) v) = ((l : K) - 2 * k) • (F ^ k) v := by
    intro k
    induction k with
    | zero => simp [hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ k) v)) hHF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
        LinearMap.add_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul]
      push_cast
      module
  have hEFk : ∀ k : ℕ, E ((F ^ (k + 1)) v) = (((k : K) + 1) * ((l : K) - k)) • (F ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h1 := congrArg (fun f : Module.End K V => f v) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, map_zero, sub_zero] at h1
      simp [h1, hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ (k + 1)) v)) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      have hp : (F ^ (k + 1 + 1)) v = F ((F ^ (k + 1)) v) := by
        rw [pow_succ' F (k + 1), Module.End.mul_apply]
      have hq : F ((F ^ k) v) = (F ^ (k + 1)) v := by
        rw [pow_succ' F k, Module.End.mul_apply]
      rw [hp, h1, ih, map_smul, hq, hHFk, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hl0
  have hl : l < 0 := not_le.mp hl0
  have hne : ∀ k : ℕ, (F ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hv0
    | succ k ih =>
      intro h0
      have h1 := hEFk k
      rw [h0, map_zero] at h1
      have hc : ((k : K) + 1) * ((l : K) - k) ≠ 0 := by
        refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
        intro h
        have h3 : ((l : ℤ) : K) = ((k : ℤ) : K) := by
          rw [sub_eq_zero] at h
          rw [h]
          push_cast
          rfl
        have h4 : l = (k : ℤ) := Int.cast_injective h3
        omega
      exact ih ((smul_eq_zero.mp h1.symm).resolve_left hc)
  have hmem : ∀ k : ℕ, (F ^ k) v ∈ W := by
    intro k
    induction k with
    | zero => simpa using hvW
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  have hli : LinearIndependent K (fun k : Fin (Module.finrank K W + 1) => (F ^ (k : ℕ)) v) := by
    refine Module.End.eigenvectors_linearIndependent' H
      (fun k : Fin (Module.finrank K W + 1) => (l : K) - 2 * ((k : ℕ) : K)) ?_ _
      (fun k => ⟨Module.End.mem_eigenspace_iff.2 (hHFk k), hne k⟩)
    intro a b hab
    have h1 : (2 : K) * ((a : ℕ) : K) = 2 * ((b : ℕ) : K) := sub_right_injective hab
    have h2 : ((a : ℕ) : K) = ((b : ℕ) : K) := mul_left_cancel₀ two_ne_zero h1
    exact Fin.ext (Nat.cast_injective h2)
  have hw : LinearIndependent K
      (fun k : Fin (Module.finrank K W + 1) => (⟨(F ^ (k : ℕ)) v, hmem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have h5 := hw.fintype_card_le_finrank
  simp at h5

theorem highest_weight_antitone {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) : Antitone κ := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · have hne : a ≠ b := h.ne
    have hEF : e a b * e b a - e b a * e a b = e a a - e b b := by
      simpa only [↓reduceIte] using he a b b a
    have hHF : (e a a - e b b) * e b a - e b a * (e a a - e b b) = -(e b a + e b a) := by
      have h1 := he a a b a
      have h2 := he b b b a
      simp only [if_neg hne, ↓reduceIte, zero_sub, sub_zero] at h1 h2
      calc (e a a - e b b) * e b a - e b a * (e a a - e b b)
          = (e a a * e b a - e b a * e a a) - (e b b * e b a - e b a * e b b) := by
            rw [sub_mul, mul_sub]
            abel
        _ = -(e b a + e b a) := by
            rw [h1, h2]
            abel
    have hHv : (e a a - e b b) v = (((κ a - κ b : ℤ)) : K) • v := by
      rw [LinearMap.sub_apply, hκ, hκ]
      push_cast
      rw [sub_smul]
    have h0 := sl2_nonneg_weight_of_highest_weight_vector (e a b) (e b a) (e a a - e b b) hEF hHF W
      (hW b a) v hvW hv0 (κ a - κ b) (hv a b h) hHv
    linarith
  · subst h
    exact le_rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowAddGenericRowAddTerm
open MvPolynomial

namespace GlobalTheory

section RowAdd

variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]

noncomputable def rowAddTerm (K : Type*) [Field K] (u w : ι → σ) (s : σ) : MvPolynomial σ K :=
  ∑ k, if s = w k then X (u k) else 0

noncomputable def rowAddGeneric (u w : ι → σ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun s => Polynomial.C (X s) + Polynomial.X * Polynomial.C (rowAddTerm K u w s)

theorem eval_rowAddGeneric (u w : ι → σ) (t : K) (P : MvPolynomial σ K) :
    Polynomial.eval (C t) (rowAddGeneric u w P) =
      bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    simp [rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]
    simp only [mul_comm]

theorem eval_zero_rowAddGeneric (u w : ι → σ) (P : MvPolynomial σ K) :
    Polynomial.eval 0 (rowAddGeneric u w P) = P := by
  have h := eval_rowAddGeneric u w (0 : K) P
  simpa using h

theorem rowAddGeneric_rowAddTerm (u w : ι → σ) (huw : ∀ k l, u k ≠ w l) (s : σ) :
    rowAddGeneric u w (rowAddTerm K u w s) = Polynomial.C (rowAddTerm K u w s) := by
  have h0 : ∀ k, rowAddTerm K u w (u k) = 0 := fun k => by
    simp [rowAddTerm, huw k]
  conv_lhs => rw [rowAddTerm]
  conv_rhs => rw [rowAddTerm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp [rowAddGeneric, h0]
  · simp

theorem sum_X_mul_pderiv_X (u w : ι → σ) (s : σ) :
    ∑ k, X (u k) * pderiv (w k) (X s : MvPolynomial σ K) = rowAddTerm K u w s := by
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [h]
  · simp [pderiv_X_of_ne h]

theorem derivative_rowAddGeneric (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p s hp =>
    have h : ∑ k, X (u k) * pderiv (w k) (p * X s) =
        (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s := by
      rw [← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [h, map_add (f := _), map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w),
      map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp,
      rowAddGeneric_rowAddTerm u w huw]
    have hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) =
        Polynomial.C (rowAddTerm K u w s) := by
      simp [rowAddGeneric]
    rw [hX]

end RowAdd


set_option linter.unusedVariables false in
theorem rowAdd_invariant_iff {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ) (hw : Function.Injective w)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by
  tfae_have 2 → 1 := fun h t => h t
  tfae_have 1 → 3 := by
    intro h
    have hc : rowAddGeneric u w P = Polynomial.C P := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K) :=
        fun a b hab => Int.cast_injective (C_injective σ K hab)
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      rw [eval_rowAddGeneric, h t]
    have hd := derivative_rowAddGeneric u w huw P
    rw [hc, Polynomial.derivative_C] at hd
    rw [← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]
  tfae_have 3 → 2 := by
    intro h t
    have hd := derivative_rowAddGeneric u w huw P
    rw [h, map_zero] at hd
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    rw [← eval_rowAddGeneric]
    conv_rhs => rw [← eval_zero_rowAddGeneric u w P]
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  tfae_finish

end GlobalTheory
end
