module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitary
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_diag_unitOn (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (hU : UnitOn s F U) :
    (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧
      (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  obtain ⟨hfin, hst, ip, hherm, hpos, hadj⟩ := hU
  have hw : ∀ w ∈ U, (ip w w).im = 0 ∧ 0 ≤ (ip w w).re := by
    intro w hw
    constructor
    · have h := congrArg Complex.im (hherm w hw w hw)
      simp at h
      linarith
    · by_cases h0 : w = 0
      · simp [h0]
      · exact le_of_lt (hpos w hw h0)
  have key : ∀ v ∈ U, ip v (cas s F v) = ∑ a, ∑ b, if s a = s b then ip (F b a v) (F b a v) else 0 := by
    intro v hv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cas, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact (hadj b a h.symm v hv (F b a v) (hst b a h.symm v hv)).symm
    · simp
  have hS : ∀ v ∈ U, (ip v (cas s F v)).im = 0 ∧ 0 ≤ (ip v (cas s F v)).re := by
    intro v hv
    rw [key v hv, Complex.im_sum, Complex.re_sum]
    constructor
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).1
      · simp
    · refine Finset.sum_nonneg fun a _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).2
      · simp
  have first : ∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re := by
    intro c v hv h0 hc
    have e := hS v hv
    rw [hc, map_smul, smul_eq_mul, Complex.mul_im, Complex.mul_re] at e
    have r0 := (hw v hv).1
    have rp := hpos v hv h0
    rw [r0] at e
    simp only [mul_zero, zero_add, sub_zero] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h (ne_of_gt rp)
    · by_contra hneg
      push_neg at hneg
      nlinarith
  refine ⟨first, fun hne => ?_⟩
  have hcU : ∀ x ∈ U, cas s F x ∈ U := by
    intro x hx
    simp only [cas, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact hst a b h _ (hst b a h.symm x hx)
    · simp
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : FiniteDimensional ℂ U := hfin
  let g : Module.End ℂ U := (cas s F).restrict hcU
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
  obtain ⟨w, hw'⟩ := hc.exists_hasEigenvector
  have hgw : g w = c • w := Module.End.mem_eigenspace_iff.mp hw'.1
  have hw0 : (w : M) ≠ 0 := fun h => hw'.2 (Subtype.ext h)
  have hcw : cas s F (w : M) = c • (w : M) := by
    have := congrArg Subtype.val hgw
    simpa [g] using this
  have hc' := first c w w.2 hw0 hcw
  refine ⟨c.re, w, w.2, hw0, ?_⟩
  rw [hcw]
  congr 1
  apply Complex.ext <;> simp [hc'.1]

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitaryStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U, UnitOn s F U → (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧ (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  first | exact @GlobalTheory.HoweR.cas_diag_unitOn | exact GlobalTheory.HoweR.cas_diag_unitOn | (intros; apply GlobalTheory.HoweR.cas_diag_unitOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentit
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem qop_quadratic_on_eigenvector : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  intro ι M _ _ _ _ s F α β x y hq hs ht hf a
  have hall : ∀ c, ∑ b, F c b (y b) = x • y c := by
    intro c
    cases hc : s c
    · rw [hf c hc, hs c hc, smul_zero]
    · exact ht c hc
  cases ha : s a
  · rw [hs a ha, smul_zero]
  · have key : ∑ b, qop F α β a b (y b) = 0 := by simp [hq]
    have pt : ∀ b, qop F α β a b (y b)
        = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0) := by
      intro b
      simp only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      split_ifs <;> simp
    have expand : ∑ b, qop F α β a b (y b)
        = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a := by
      rw [Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    rw [expand, ht a ha] at key
    simp only [hall, map_smul] at key
    rw [← Finset.smul_sum, ht a ha] at key
    rw [sub_smul, sub_smul, pow_two, mul_smul, mul_smul]
    exact key

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentitStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  first | exact @GlobalTheory.HoweR.qop_quadratic_on_eigenvector | exact GlobalTheory.HoweR.qop_quadratic_on_eigenvector | (intros; apply GlobalTheory.HoweR.qop_quadratic_on_eigenvector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlock
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR
variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem casDrop_term (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (a b j k : ι) :
    F a b * F b a * F j k = F j k * (F a b * F b a) + (F a b * (if a = j then F b k else 0) - F a b * (if k = b then F j a else 0))
      + ((if b = j then F a k else 0) * F b a - (if k = a then F j b else 0) * F b a) := by
  have h1 := hF b a j k
  have h2 := hF a b j k
  have e1 : F b a * F j k = F j k * F b a + ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
    rw [← h1]; abel
  have e2 : F a b * F j k = F j k * F a b + ((if b = j then F a k else 0) - (if k = a then F j b else 0)) := by
    rw [← h2]; abel
  calc F a b * F b a * F j k = F a b * (F b a * F j k) := mul_assoc _ _ _
    _ = F a b * F j k * F b a + F a b * ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
        rw [e1, mul_add, mul_assoc]
    _ = _ := by rw [e2]; simp only [add_mul, sub_mul, mul_sub, mul_assoc]; abel

theorem cas_mul_off (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (j k : ι) (hj : s j = false)
    (hk : s k = true) :
    cas s F * F j k = F j k * cas s F + (2 : ℂ) • (∑ b, if s b = false then F j b * F b k else 0)
      - (2 : ℂ) • (∑ b, if s b = true then F j b * F b k else 0)
      + (((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • F j k := by
  have hjk : j ≠ k := by intro h; rw [h, hk] at hj; exact Bool.noConfusion hj
  have sw : ∀ a, F a k * F j a = F j a * F a k - F j k := by
    intro a
    have h := hF a k j a
    rw [if_neg (Ne.symm hjk), if_pos rfl] at h
    calc F a k * F j a = (F a k * F j a - F j a * F a k) + F j a * F a k := by abel
      _ = _ := by rw [h]; abel
  have cnt : ∀ c : Bool, (∑ a, if s a = c then F a k * F j a else 0)
      = (∑ a, if s a = c then F j a * F a k else 0) - ((Finset.univ.filter fun a => s a = c).card : ℂ) • F j k := by
    intro c
    have : (∑ a, if s a = c then F a k * F j a else 0)
        = ∑ a, ((if s a = c then F j a * F a k else 0) - (if s a = c then F j k else 0)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : s a = c
      · simp only [if_pos h, sw]
      · simp [h]
    rw [this, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have S1 : ∑ a, ∑ b, (if s a = s b then F a b * (if a = j then F b k else 0) else 0)
      = ∑ b, if s b = false then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hj]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, (if s a = s b then F a b * (if k = b then F j a else 0) else 0)
      = ∑ a, if s a = true then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [hk]; simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have S3 : ∑ a, ∑ b, (if s a = s b then (if b = j then F a k else 0) * F b a else 0)
      = ∑ a, if s a = false then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [hj]; simp
    · intro b _ hb; simp [hb]
    · simp
  have S4 : ∑ a, ∑ b, (if s a = s b then (if k = a then F j b else 0) * F b a else 0)
      = ∑ b, if s b = true then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single k]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hk]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  have expand : ∀ a b, (if s a = s b then F a b * F b a else 0) * F j k
      = (if s a = s b then F j k * (F a b * F b a) else 0)
        + ((if s a = s b then F a b * (if a = j then F b k else 0) else 0)
          - (if s a = s b then F a b * (if k = b then F j a else 0) else 0))
        + ((if s a = s b then (if b = j then F a k else 0) * F b a else 0)
          - (if s a = s b then (if k = a then F j b else 0) * F b a else 0)) := by
    intro a b
    by_cases h : s a = s b
    · simp only [if_pos h]; exact casDrop_term F hF a b j k
    · simp [h]
  unfold cas
  simp only [Finset.sum_mul, expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4, cnt, cnt]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  simp only [two_smul, sub_smul]
  abel

end GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_drop : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) →
    (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) →
    ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  intro ι M _ _ _ _ s F α β x ω y hF hq hy0 hyA hω j hj
  set r : ℂ := ((Finset.univ.filter fun a => s a = true).card : ℂ)
  set r' : ℂ := ((Finset.univ.filter fun a => s a = false).card : ℂ)
  set T : ι → Module.End ℂ M := fun b => ∑ c, if s c = true then F j c * F c b else 0 with hT

  have quad : ∀ b, s b = true → (∑ c, if s c = false then F j c * F c b else 0) = α • F j b - T b := by
    intro b hb
    have hjb : j ≠ b := by intro h; rw [h, hb] at hj; exact Bool.noConfusion hj
    have h := hq j b
    simp only [qop, if_neg hjb, sub_zero] at h
    have split : (∑ c, F j c * F c b) = (∑ c, if s c = false then F j c * F c b else 0) + T b := by
      rw [hT, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      cases s c <;> simp
    rw [split] at h
    calc (∑ c, if s c = false then F j c * F c b else 0) = ((∑ c, if s c = false then F j c * F c b else 0) + T b - α • F j b)
          + α • F j b - T b := by abel
      _ = α • F j b - T b := by rw [h]; abel

  have term : ∀ b, cas s F (F j b (y b)) = (ω + 2 * α + r - r') • F j b (y b) - (4 : ℂ) • T b (y b) := by
    intro b
    cases hb : s b
    · simp [hT, hy0 b hb]
    · have h := cas_mul_off s F hF j b hj hb
      rw [quad b hb] at h
      have h' := congrArg (fun L : Module.End ℂ M => L (y b)) h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h'
      rw [h', hω b, map_smul]
      module
  have sumT : (∑ b, T b (y b)) = x • ∑ b, F j b (y b) := by
    have : ∀ b, T b (y b) = ∑ c, if s c = true then F j c (F c b (y b)) else 0 := by
      intro b
      simp only [hT, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    simp only [this]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    cases hc : s c
    · simp [hy0 c hc]
    · simp only [if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hyA c hc, map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [term]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sumT, smul_smul, ← sub_smul]
  congr 1
  ring

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlockStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) → ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  first | exact @GlobalTheory.HoweR.cas_drop | exact GlobalTheory.HoweR.cas_drop | (intros; apply GlobalTheory.HoweR.cas_drop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMin
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem real_root_quad_le {x : ℝ} {α β : ℂ} (h : (x : ℂ) ^ 2 - α * x - β = 0) : x ≤ ‖α‖ + ‖β‖ + 1 := by
  have h1 : (x : ℂ) ^ 2 = α * x + β := by linear_combination h
  have h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by
    calc ‖(x : ℂ)‖ ^ 2 = ‖(x : ℂ) ^ 2‖ := (norm_pow _ _).symm
    _ = ‖α * x + β‖ := by rw [h1]
    _ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _
    _ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]
  have hx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx] at h2
  have ha := norm_nonneg α
  have hb := norm_nonneg β
  by_contra hc
  push_neg at hc
  have ht : ‖α‖ + ‖β‖ + 1 < |x| := lt_of_lt_of_le hc (le_abs_self x)
  nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1),
    mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]

theorem diag_eig_le_of_cas_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  intro ι _ _ s α β
  refine ⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩
  intro M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas
  by_cases hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0
  · have hbc := GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity ι M s F α β x y hq hfalse htrue hz
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (funext h)
    have h0 : (x : ℂ) ^ 2 - α * x - β = 0 := by
      by_contra hne
      exact ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)
    exact le_max_of_le_left (real_root_quad_le h0)
  · push_neg at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hd := GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock ι M s F α β x ω y hGl hq hfalse htrue hcas j hj
    obtain ⟨U, hU, hUU⟩ := hLoc {∑ b, F j b (y b)}
    have hzU : ∑ b, F j b (y b) ∈ U := hU _ (Finset.mem_singleton_self _)
    have him := ((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1
    set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc
    have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt := hω c.re _ hzj (by rw [← hcre]; exact hd)
    have hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ)
      - ((Finset.univ.filter fun a => s a = false).card : ℝ) := by simp [hc]
    have hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι := by
      have := Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hαre : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ) := Nat.cast_nonneg _
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    linarith

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMinStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  first | exact @GlobalTheory.HoweR.diag_eig_le_of_cas_min | exact GlobalTheory.HoweR.diag_eig_le_of_cas_min | (intros; apply GlobalTheory.HoweR.diag_eig_le_of_cas_min <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem re_inner_apply_le_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (R : ℝ)
    (hR : ∀ (x : ℝ) (v : E), v ≠ 0 → T v = (x : ℂ) • v → x ≤ R) (y : E) :
    (inner ℂ y (T y)).re ≤ R * (inner ℂ y y).re := by
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  set b := hT.eigenvectorBasis hn
  set ev := hT.eigenvalues hn
  have hb : ∀ i, T (b i) = ((ev i : ℝ) : ℂ) • b i := fun i => hT.apply_eigenvectorBasis hn i
  have hle : ∀ i, ev i ≤ R := fun i => hR _ _ (b.orthonormal.ne_zero i) (hb i)
  have h3 : ∀ i, inner ℂ y (b i) * inner ℂ (b i) y = ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm (b i) y, Complex.norm_conj]
    first
      | (rw [Complex.mul_conj']; push_cast; rfl)
      | (rw [mul_comm, Complex.conj_mul']; push_cast; rfl)
  have h1 : inner ℂ y (T y) = ∑ i, ((ev i * ‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y (T y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT (b i) y, hb i, inner_smul_left, Complex.conj_ofReal, mul_left_comm, h3 i]
    push_cast; ring
  have h2 : inner ℂ y y = ∑ i, ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y y]
    exact Finset.sum_congr rfl fun i _ => h3 i
  rw [h1, h2, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hle i) (by positivity)

section Block

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def blockSub (s : ι → Bool) (U : Submodule ℂ M) : Submodule ℂ (ι → M) where
  carrier := {y | ∀ c, y c ∈ U ∧ (s c = false → y c = 0)}
  add_mem' {x y} hx hy c := ⟨U.add_mem (hx c).1 (hy c).1, fun h => by simp [(hx c).2 h, (hy c).2 h]⟩
  zero_mem' c := ⟨U.zero_mem, fun _ => rfl⟩
  smul_mem' r x hx c := ⟨U.smul_mem r (hx c).1, fun h => by simp [(hx c).2 h]⟩

def blockOp (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) : blockSub s U →ₗ[ℂ] blockSub s U where
  toFun y := ⟨fun a => if s a = true then ∑ b, F a b (y.1 b) else 0, fun c => by
    refine ⟨?_, fun h => by simp [h]⟩
    show (if s c = true then ∑ b, F c b (y.1 b) else 0) ∈ U
    split_ifs with hc
    · refine U.sum_mem fun b _ => ?_
      by_cases hb : s b = true
      · exact hst c b (hc.trans hb.symm) _ (y.2 b).1
      · rw [(y.2 b).2 (by simpa using hb), map_zero]; exact U.zero_mem
    · exact U.zero_mem⟩
  map_add' y z := by
    ext a
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
    split_ifs <;> simp
  map_smul' r y := by
    ext a
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
    split_ifs <;> simp [Finset.smul_sum]

theorem blockOp_apply (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) (y : blockSub s U) (a : ι) :
    (blockOp s F U hst y : ι → M) a = if s a = true then ∑ b, F a b (y.1 b) else 0 := rfl

def blockCore (s : ι → Bool) (U : Submodule ℂ M) (ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hsym : ∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) (hpos : ∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) :
    InnerProductSpace.Core ℂ (blockSub s U) where
  inner y z := ∑ c, ip (y.1 c) (z.1 c)
  conj_inner_symm y z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun c _ => hsym _ (z.2 c).1 _ (y.2 c).1
  re_inner_nonneg y := by
    simp only [RCLike.re_to_complex, Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    by_cases h : y.1 c = 0
    · simp [h]
    · exact (hpos _ (y.2 c).1 h).le
  add_left y z w := by simp [Finset.sum_add_distrib]
  smul_left y z r := by simp [Finset.mul_sum]
  definite y h := by
    have h' : ∑ c, (ip (y.1 c) (y.1 c)).re = 0 := by rw [← Complex.re_sum, h]; rfl
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (ip (y.1 c) (y.1 c)).re := fun c _ => by
      by_cases h : y.1 c = 0
      · simp [h]
      · exact (hpos _ (y.2 c).1 h).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h'
    ext c
    by_contra hc
    exact (hpos _ (y.2 c).1 hc).ne' (hz c (Finset.mem_univ c))

end Block

theorem re_diag_le_of_eigen_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  intro ι M _ _ _ _ s F U R hU hR a ha u hu hu0 m hm
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := hU
  let cd := blockCore s U ip hsym hpos
  letI : NormedAddCommGroup (blockSub s U) := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (blockSub s U) := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ U := hfd
  haveI : FiniteDimensional ℂ (blockSub s U) := by
    let e : blockSub s U →ₗ[ℂ] (ι → U) :=
      { toFun := fun y c => ⟨y.1 c, (y.2 c).1⟩
        map_add' := fun y z => rfl
        map_smul' := fun r y => rfl }
    exact Module.Finite.of_injective e
      (fun y z h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hinner : ∀ y z : blockSub s U, inner ℂ y z = ∑ c, ip (y.1 c) (z.1 c) := fun _ _ => rfl
  have key : ∀ (y z : blockSub s U) (c b : ι),
      ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) =
        ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
    intro y z c b
    by_cases hc : s c = true
    · by_cases hb : s b = true
      · rw [if_pos hc, if_pos hb]
        exact hadj c b (hc.trans hb.symm) _ (y.2 b).1 _ (z.2 c).1
      · rw [if_pos hc, if_neg hb, (y.2 b).2 (by simpa using hb)]
        simp
    · rw [if_neg hc, (z.2 c).2 (by simpa using hc)]
      simp
  have hT : (blockOp s F U hst).IsSymmetric := by
    intro y z
    rw [hinner, hinner]
    simp only [blockOp_apply]
    have e1 : ∀ c, ip (if s c = true then ∑ b, F c b (y.1 b) else 0) (z.1 c) =
        ∑ b, ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) := by
      intro c; split_ifs <;> simp [map_sum]
    have e2 : ∀ b, ip (y.1 b) (if s b = true then ∑ c, F b c (z.1 c) else 0) =
        ∑ c, ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
      intro b; split_ifs <;> simp [map_sum]
    simp only [e1, e2, key]
    exact Finset.sum_comm
  have hR' : ∀ (x : ℝ) (v : blockSub s U), v ≠ 0 → blockOp s F U hst v = (x : ℂ) • v → x ≤ R := by
    intro x v hv hTv
    refine hR x v.1 (fun h => hv (Subtype.ext h)) (fun c => (v.2 c).1) (fun c => (v.2 c).2) fun c hc => ?_
    have := congrFun (congrArg Subtype.val hTv) c
    rw [blockOp_apply, if_pos hc] at this
    exact this
  have hmem : Pi.single a u ∈ blockSub s U := by
    intro c
    by_cases hc : c = a
    · subst hc; simp only [Pi.single_eq_same]; exact ⟨hu, fun h => by simp [ha] at h⟩
    · rw [Pi.single_eq_of_ne hc]; exact ⟨U.zero_mem, fun _ => rfl⟩
  set y0 : blockSub s U := ⟨Pi.single a u, hmem⟩
  have hy0 : (y0 : ι → M) = Pi.single a u := rfl
  have hTa : (blockOp s F U hst y0 : ι → M) a = m • u := by
    rw [blockOp_apply, if_pos ha, hy0, Finset.sum_eq_single a, Pi.single_eq_same, hm]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have i1 : inner ℂ y0 (blockOp s F U hst y0) = m * ip u u := by
    rw [hinner, Finset.sum_eq_single a, hTa, hy0, Pi.single_eq_same, map_smul, smul_eq_mul]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have i2 : inner ℂ y0 y0 = ip u u := by
    rw [hinner, Finset.sum_eq_single a, hy0, Pi.single_eq_same]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have hle := re_inner_apply_le_of_eigen hT R hR' y0
  rw [i1, i2] at hle
  have him : (ip u u).im = 0 := by
    have h := hsym u hu u hu
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have hp := hpos u hu hu0
  rw [Complex.mul_re, him, mul_zero, sub_zero] at hle
  exact le_of_mul_le_mul_right hle hp

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBoundStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  first | exact @GlobalTheory.HoweR.re_diag_le_of_eigen_bound | exact GlobalTheory.HoweR.re_diag_le_of_eigen_bound | (intros; apply GlobalTheory.HoweR.re_diag_le_of_eigen_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_of_le : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U →
    (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  intro ι M _ _ _ _ s F U U' hU hle hst
  obtain ⟨hfin, -, ip, hsym, hpos, hadj⟩ := hU
  refine ⟨Submodule.finiteDimensional_of_le hle, hst, ip, ?_, ?_, ?_⟩
  · intro x hx y hy; exact hsym x (hle hx) y (hle hy)
  · intro x hx h0; exact hpos x (hle hx) h0
  · intro a b hab x hx y hy; exact hadj a b hab x (hle hx) y (hle hy)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStableStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U → (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  first | exact @GlobalTheory.HoweR.unitOn_of_le | exact GlobalTheory.HoweR.unitOn_of_le | (intros; apply GlobalTheory.HoweR.unitOn_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnit
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_mul_comm_of_block : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  intro ι M _ _ _ _ s F hF a b hab
  rw [← sub_eq_zero]
  have key : ∀ c d, F c d * F d c * F a b - F a b * (F c d * F d c) =
      ((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0)) := by
    intro c d
    have e : F c d * F d c * F a b - F a b * (F c d * F d c) =
        F c d * (F d c * F a b - F a b * F d c) + (F c d * F a b - F a b * F c d) * F d c := by noncomm_ring
    rw [e, hF d c a b, hF c d a b]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  have h0 : cas s F * F a b - F a b * cas s F = ∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0 := by
    simp only [cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : s c = s d
    · simp only [h, if_true]; exact key c d
    · simp only [h, if_false, zero_mul, mul_zero, sub_self]
  have h1 : (∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have h4 : (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have h2 : (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  have h3 : (∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [h0]
  have split : (∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0) =
      ((∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0)) +
      ((∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [split, h1, h2, h3, h4]
  abel

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnitStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  first | exact @GlobalTheory.HoweR.cas_mul_comm_of_block | exact GlobalTheory.HoweR.cas_mul_comm_of_block | (intros; apply GlobalTheory.HoweR.cas_mul_comm_of_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymNegTSwap
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isGl_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (F : ι → ι → Module.End ℂ M) (h : IsGl F) : IsGl (negT F) := by
  intro a b c d
  have h1 := h d c b a
  simp only [negT, neg_mul_neg]
  have e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c) := by abel
  rw [e1, h1]
  simp only [@eq_comm _ c b, @eq_comm _ a d]
  split_ifs <;> abel

theorem unitOn_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn s (negT F) U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩
  · simp only [negT, LinearMap.neg_apply]
    exact U.neg_mem (hst b a hab.symm u hu)
  · simp only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
    rw [hadj b a hab.symm x hx y hy]

theorem unitOn_not {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn (fun a => !s a) F U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos,
    fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩

theorem sym_negT_swap : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), (IsGl F → IsGl (negT F)) ∧ cas s (negT F) = cas s F ∧ cas (fun a => !s a) F = cas s F ∧ (∀ U, UnitOn s F U → UnitOn s (negT F) U ∧ UnitOn (fun a => !s a) F U) ∧ (LocU s F → LocU s (negT F) ∧ LocU (fun a => !s a) F) := by
  intro ι M _ _ _ _ s F
  refine ⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold cas negT
    simp only [neg_mul_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [eq_comm]
  · unfold cas
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.not_inj_iff]
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_negT s F U hUn⟩
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_not s F U hUn⟩

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadratic
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem diag_re_le_of_near_min {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (G : ι → ι → Module.End ℂ M) (α β : ℂ) (R : ℝ)
    (hR : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F →
      (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ,
      (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) →
      ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) →
      (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R)
    (hG : IsGl G) (hq : ∀ a b, qop G α β a b = 0) (hL : LocU s G) (U : Submodule ℂ M) (hU : UnitOn s G U) (ω : ℝ)
    (hω : ∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s G v = (ω' : ℂ) • v → ω < ω' + 1)
    (hUe : ∀ u ∈ U, cas s G u = (ω : ℂ) • u) :
    ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, G a a u = m • u → m.re ≤ R :=
  GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound ι M s G U R hU (fun x y hy hyU hf hs => hR M G hG hq hL ω hω x y hy hf hs (fun a => hUe _ (hyU a)))

theorem exists_unitOn_diag_bounded : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ,
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F →
    (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F →
    ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  intro ι _ _ s α β α' β'
  obtain ⟨R1, h1⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α β
  obtain ⟨R2, h2⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α β
  obtain ⟨R3, h3⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α' β'
  obtain ⟨R4, h4⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α' β'
  refine ⟨max (max R1 R2) (max R3 R4), ?_⟩
  intro M _ _ F hnt hG hq hq' hL
  obtain ⟨hGn, hcn, hcs, hUs, hLs⟩ := sym_negT_swap ι M s F
  obtain ⟨-, hcn', hcs', hUs', hLs'⟩ := sym_negT_swap ι M s (negT F)
  let S : Set ℝ := {ω' | ∃ v : M, v ≠ 0 ∧ cas s F v = (ω' : ℂ) • v}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨U, hxU, hU⟩ := hL {x}
    have hne : U ≠ ⊥ := by
      intro h
      have := hxU x (Finset.mem_singleton_self x)
      rw [h, Submodule.mem_bot] at this
      exact hx this
    obtain ⟨ω, v, -, hv, hcv⟩ := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).2 hne
    exact ⟨ω, v, hv, hcv⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, fun ω' hω' => ?_⟩
    obtain ⟨v, hv, hcv⟩ := hω'
    obtain ⟨U, hvU, hU⟩ := hL {v}
    have := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).1 (ω' : ℂ) v (hvU v (Finset.mem_singleton_self v)) hv hcv
    simpa using this.2
  obtain ⟨ω, ⟨v, hv, hcv⟩, hωlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_one (sInf S))
  have hω : ∀ (ω' : ℝ) (w : M), w ≠ 0 → cas s F w = (ω' : ℂ) • w → ω < ω' + 1 := fun ω' w hw hcw => by
    have := csInf_le hSbdd ⟨w, hw, hcw⟩
    linarith
  obtain ⟨U0, hvU0, hU0⟩ := hL {v}
  let U : Submodule ℂ M := U0 ⊓ LinearMap.ker (cas s F - (ω : ℂ) • (1 : Module.End ℂ M))
  have hUe : ∀ u ∈ U, cas s F u = (ω : ℂ) • u := fun u hu => by
    have h2 := hu.2
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    simpa using h2
  have hvU : v ∈ U := ⟨hvU0 v (Finset.mem_singleton_self v), by
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; simpa using hcv⟩
  have hUst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U := by
    intro a b hab u hu
    refine ⟨hU0.2.1 a b hab u hu.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ M => T u) (GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit ι M s F hG a b hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hUe u hu]
    simp
  have hU : UnitOn s F U := GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable ι M s F U0 U hU0 inf_le_left hUst
  refine ⟨U, fun h => hv (by rw [h, Submodule.mem_bot] at hvU; exact hvU), hU, ?_⟩
  intro a u hu hu0 m hm
  have b1 := diag_re_le_of_near_min s F α β R1 h1 hG hq hL U hU ω hω hUe
  have b2 := diag_re_le_of_near_min (fun a => !s a) F α β R2 h2 hG hq (hLs hL).2 U (hUs U hU).2 ω
    (by rw [hcs]; exact hω) (by rw [hcs]; exact hUe)
  have b3 := diag_re_le_of_near_min s (negT F) α' β' R3 h3 (hGn hG) hq' (hLs hL).1 U (hUs U hU).1 ω
    (by rw [hcn]; exact hω) (by rw [hcn]; exact hUe)
  have b4 := diag_re_le_of_near_min (fun a => !s a) (negT F) α' β' R4 h4 (hGn hG) hq' (hLs' (hLs hL).1).2 U
    (hUs' U (hUs U hU).1).2 ω (by rw [hcs', hcn]; exact hω) (by rw [hcs', hcn]; exact hUe)
  have hmn : negT F a a u = (-m) • u := by simp [negT, hm]
  have l1 : R1 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_left _ _)
  have l2 : R2 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_left _ _)
  have l3 : R3 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_right _ _)
  have l4 : R4 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_right _ _)
  rw [abs_le]
  cases hsa : s a
  · have e1 := b2 a (by simp [hsa]) u hu hu0 m hm
    have e2 := b4 a (by simp [hsa]) u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith
  · have e1 := b1 a hsa u hu hu0 m hm
    have e2 := b3 a hsa u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadraticStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F → ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  first | exact @GlobalTheory.HoweR.exists_unitOn_diag_bounded | exact GlobalTheory.HoweR.exists_unitOn_diag_bounded | (intros; apply GlobalTheory.HoweR.exists_unitOn_diag_bounded <;> assumption)
end
