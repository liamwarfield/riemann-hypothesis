module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NotInKernelOfMultiplierTorsion
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ThetaZeroTwoComplexMult
section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LatticePointInKernelSubgroup
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.KFin

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit GaussOne)

theorem norm_coe (q : ℚ_[2]) : ‖((q : ℚ_[2]) : ℂ_[2])‖ = ‖q‖ := PadicComplex.norm_extends' 2 q

theorem norm_two : ‖(2 : ℂ_[2])‖ = 2⁻¹ := by
  have h := norm_coe (2 : ℚ_[2])
  have e : (((2 : ℚ_[2]) : ℚ_[2]) : ℂ_[2]) = 2 := map_ofNat (algebraMap ℚ_[2] ℂ_[2]) 2
  rw [e] at h
  rw [h]
  have := Padic.norm_p (p := 2)
  simpa using this

theorem norm_three : ‖(3 : ℂ_[2])‖ = 1 := by
  have e : (3 : ℂ_[2]) = 1 + 2 := by norm_num
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one, norm_two]; norm_num),
    norm_one, norm_two]
  norm_num

theorem norm_twelve : ‖(12 : ℂ_[2])‖ = 4⁻¹ := by
  have e : (12 : ℂ_[2]) = 2 * 2 * 3 := by norm_num
  rw [e, norm_mul, norm_mul, norm_two, norm_three]
  norm_num

theorem nle_add {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem nle_sub {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact nle_add ha (by rw [norm_neg]; exact hb)

theorem nle_mul {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

theorem unit_sq (b : ℤ_[2]) (hb : ‖b‖ = 1) : ‖1 - b ^ 2‖ ≤ 4⁻¹ := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range b
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  have h2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  interval_cases n
  · exfalso
    have : ‖b‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]
      simpa using hmem
    rw [hb] at this
    exact lt_irrefl _ this
  · obtain ⟨c, hc⟩ := hmem
    have e : 1 - b ^ 2 = -(2 * 2 * (c * (c + 1))) := by
      have : b = 1 + 2 * c := by
        have hc' : b - 1 = 2 * c := by simpa using hc
        rw [← hc']; ring
      rw [this]; ring
    rw [e, norm_neg, norm_mul, norm_mul, h2]
    have := PadicInt.norm_le_one (c * (c + 1))
    nlinarith [norm_nonneg (c * (c + 1))]

theorem unit_sq' (b : ℤ_[2]) (hb : ‖b‖ = 1) : ‖1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2‖ ≤ 4⁻¹ := by
  have e : 1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2 = ((((1 - b ^ 2 : ℤ_[2]) : ℚ_[2])) : ℂ_[2]) := by
    have : (((1 - b ^ 2 : ℤ_[2]) : ℚ_[2])) = 1 - (b : ℚ_[2]) ^ 2 := by push_cast; ring
    rw [this]
    exact (by simp : algebraMap ℚ_[2] ℂ_[2] (1 - (b : ℚ_[2]) ^ 2)
      = 1 - (algebraMap ℚ_[2] ℂ_[2] (b : ℚ_[2])) ^ 2).symm
  rw [e, norm_coe]
  exact unit_sq b hb

section Pts

variable {L : PeriodPair} {ι : ℂ ≃+* ℂ_[2]} {W : WeierstrassCurve ℂ_[2]}

theorem mem_kernel_subgroup_iff_norm (hU : Unif 2 L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    InFormalGroupPoints (ptW 2 L ι W t) ↔ 1 < ‖ι (L.weierstrassP t) - W.b₂ / 12‖ := by
  rw [Formalism.L2.Th1.E.AnaSysW.ptW_notMem hU t ht]
  exact Iff.rfl

theorem lattice_point_in_kernel_subgroup (hU : Unif 2 L ι W) (t : ℂ) (ht : t ∈ L.lattice) : InFormalGroupPoints (ptW 2 L ι W t) := by
  rw [(Formalism.L2.Th1.E.ptWZero 2 L ι W hU t).2 ht]
  trivial

open Classical in
theorem ptW_neg (hU : Unif 2 L ι W) (t : ℂ) : ptW 2 L ι W (-t) = - ptW 2 L ι W t := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Formalism.L2.Th1.E.ptWAdd 2 L ι W hU, neg_add_cancel]
  exact (Formalism.L2.Th1.E.ptWZero 2 L ι W hU 0).2 L.lattice.zero_mem

open Classical in
theorem kernel_subgroup_add_mem (hU : Unif 2 L ι W) (hW : IntCurve W) (s t : ℂ) (hs : InFormalGroupPoints (ptW 2 L ι W s))
    (ht : InFormalGroupPoints (ptW 2 L ι W t)) : InFormalGroupPoints (ptW 2 L ι W (s + t)) := by
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW
  rw [Formalism.L2.Th1.E.ptWAdd 2 L ι W hU]
  exact (Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[2] W ⟨a1, a2, a3, a4, a6⟩ hΔ _ _ hs ht).1

open Classical in
theorem kernel_subgroup_neg_mem (hU : Unif 2 L ι W) (hW : IntCurve W) (t : ℂ) (ht : InFormalGroupPoints (ptW 2 L ι W t)) :
    InFormalGroupPoints (ptW 2 L ι W (-t)) := by
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW
  rw [ptW_neg hU]
  exact (Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[2] W ⟨a1, a2, a3, a4, a6⟩ hΔ _ _ ht ht).2

theorem norm_b2_div_twelve_le_four (hW : IntCurve W) : ‖W.b₂ / 12‖ ≤ 4 := by
  obtain ⟨a1, a2, -⟩ := hW
  have h4 : ‖(4 : ℂ_[2])‖ ≤ 1 := by
    have e : (4 : ℂ_[2]) = 2 * 2 := by norm_num
    rw [e, norm_mul, norm_two]; norm_num
  have hb : ‖W.b₂‖ ≤ 1 := by
    unfold WeierstrassCurve.b₂
    rw [pow_two]
    exact nle_add (nle_mul a1 a1) (nle_mul h4 a2)
  rw [norm_div, norm_twelve]
  rw [div_inv_eq_mul]
  linarith

end Pts

theorem kernel_stable_of_integral_kernel (hK : KernelIntegral) : KernelStableUnderMultiplier := by
  intro L ι W hU hW ha1 α b hα hmul hb hnb t ht
  have hK' := hK L ι W hU hW ha1 α b hα hmul hb hnb
  by_cases htL : t ∈ L.lattice
  · exact lattice_point_in_kernel_subgroup hU _ (hmul t htL)
  have hαt : α * t ∉ L.lattice := fun h => hK' t h htL ht
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hmul
  have hiso := Formalism.L2.Th1.F.isogenyP L α S hα hmul hS t hαt
  have hP : ∀ P ∈ S, ‖ι (L.weierstrassP P) - W.b₂ / 12‖ ≤ 1 := by
    intro P hPS
    exact not_lt.1 (mt (mem_kernel_subgroup_iff_norm hU P (hS.1 P hPS).2).2 (hK' P (hS.1 P hPS).1 (hS.1 P hPS).2))
  have htP : ∀ P ∈ S, ‖ι (L.weierstrassP (t + P)) - W.b₂ / 12‖ ≤ 1 := by
    intro P hPS
    have hn : ¬ InFormalGroupPoints (ptW 2 L ι W (t + P)) := by
      intro H
      apply hK' P (hS.1 P hPS).1 (hS.1 P hPS).2
      have e : P = (t + P) + -t := by ring
      rw [e]
      exact kernel_subgroup_add_mem hU hW _ _ H (kernel_subgroup_neg_mem hU hW _ ht)
    have hl : t + P ∉ L.lattice := fun h => hn (lattice_point_in_kernel_subgroup hU _ h)
    exact not_lt.1 (mt (mem_kernel_subgroup_iff_norm hU _ hl).2 hn)
  have h := congrArg ι hiso
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_pow, map_add (f := _), map_sum, map_sub] at h
  rw [hb] at h
  rw [mem_kernel_subgroup_iff_norm hU _ hαt]
  rw [mem_kernel_subgroup_iff_norm hU _ htL] at ht
  by_contra hle
  rw [not_lt] at hle
  have hB : ‖(((b : ℚ_[2]) : ℂ_[2]))‖ ≤ 1 := by
    rw [norm_coe]; exact le_of_eq hnb
  have hsum : ‖∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
      (ι (L.weierstrassP P) - W.b₂ / 12))‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun P hPS => nle_sub (htP P hPS) (hP P hPS))
  have hc : ‖(1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)‖ ≤ 1 := by
    rw [norm_mul]
    have h1 := unit_sq' b hnb
    have h2 := norm_b2_div_twelve_le_four hW
    nlinarith [norm_nonneg (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2), norm_nonneg (W.b₂ / 12)]
  have e : ι (L.weierstrassP t) - W.b₂ / 12 =
      (((b : ℚ_[2]) : ℂ_[2])) ^ 2 * (ι (L.weierstrassP (α * t)) - W.b₂ / 12)
        - (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)
        - ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
            (ι (L.weierstrassP P) - W.b₂ / 12)) := by
    have e2 : ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
        (ι (L.weierstrassP P) - W.b₂ / 12)) =
        ∑ P ∈ S, (ι (L.weierstrassP (t + P)) - ι (L.weierstrassP P)) :=
      Finset.sum_congr rfl (fun P _ => by ring)
    rw [e2]
    linear_combination -h
  rw [e] at ht
  have : ‖(((b : ℚ_[2]) : ℂ_[2])) ^ 2 * (ι (L.weierstrassP (α * t)) - W.b₂ / 12)
        - (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)
        - ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
            (ι (L.weierstrassP P) - W.b₂ / 12))‖ ≤ 1 := by
    refine nle_sub (nle_sub (nle_mul ?_ hle) hc) hsum
    rw [pow_two]
    exact nle_mul hB hB
  exact absurd ht (not_lt.2 this)

open Classical in
theorem PointsTwoFinal_of (hK : KernelIntegral) (hS : KernelStableUnderMultiplier) (hU2 : TwoTorsionKernelUnique) :
    PointsTwoFinal := by
  intro L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  have hK' := hK L ι W hU hW ha1 α b hα hmul hb hnb
  have hS' := hS L ι W hU hW ha1 α b hα hmul hb hnb
  have hadd := Formalism.L2.Th1.E.ptWAdd 2 L ι W hU
  have hzero := Formalism.L2.Th1.E.ptWZero 2 L ι W hU
  obtain ⟨tr, n, htr, hn, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L α hmul
  have hcm : MulStable L (conj α) := by
    intro ω hω'
    have e : conj α * ω = tr • ω - α * ω := by
      rw [zsmul_eq_mul, ← htr]; ring
    rw [e]
    exact sub_mem (zsmul_mem hω' _) (hmul ω hω')
  have h2n : (2 : ℤ) ∣ n := by
    have h1 : ι α * ι (conj α) = (n : ℂ_[2]) := by rw [← map_mul, hn, map_intCast]
    rw [hb, hb'] at h1
    have h2 : ‖(n : ℂ_[2])‖ < 1 := by
      rw [← h1, norm_mul, norm_coe, norm_coe]
      have e1 : ‖(b : ℚ_[2])‖ = 1 := hnb
      have e2 : ‖(b' : ℚ_[2])‖ < 1 := hnb'
      rw [e1, one_mul]
      exact e2
    have h3 : ‖((n : ℤ_[2]))‖ < 1 := by
      have e : (n : ℂ_[2]) = ((((n : ℤ_[2]) : ℚ_[2])) : ℂ_[2]) := by
        have : (((n : ℤ_[2]) : ℚ_[2])) = (n : ℚ_[2]) := by push_cast; rfl
        rw [this]
        exact (map_intCast (algebraMap ℚ_[2] ℂ_[2]) n).symm
      rw [e, norm_coe] at h2
      exact h2
    exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd n).1 h3
  obtain ⟨m, rfl⟩ := h2n
  have key : ∀ z, 2 * z ∈ L.lattice → conj α * (α * z) ∈ L.lattice := by
    intro z hz
    have e : conj α * (α * z) = m • (2 * z) := by
      rw [zsmul_eq_mul]
      have : conj α * (α * z) = (α * conj α) * z := by ring
      rw [this, hn]
      push_cast
      ring
    rw [e]
    exact zsmul_mem hz _
  have ht0 : ω₀ / 2 ∉ L.lattice := fun h => hc (hcm _ h)
  have h2t0 : 2 * (ω₀ / 2) ∈ L.lattice := by
    have : 2 * (ω₀ / 2) = ω₀ := by ring
    rw [this]; exact hω
  have first : ¬ InFormalGroupPoints (ptW 2 L ι W (ω₀ / 2)) := by
    intro H
    have h1 := hS' _ H
    have h2 : α * (ω₀ / 2) ∉ L.lattice := fun h => hK' _ h ht0 H
    have d1 : ptW 2 L ι W (α * (ω₀ / 2)) + ptW 2 L ι W (α * (ω₀ / 2)) = 0 := by
      rw [← hadd, hzero]
      have : α * (ω₀ / 2) + α * (ω₀ / 2) = α * ω₀ := by ring
      rw [this]; exact hmul _ hω
    have d2 : ptW 2 L ι W (ω₀ / 2) + ptW 2 L ι W (ω₀ / 2) = 0 := by
      rw [← hadd, hzero]
      have : ω₀ / 2 + ω₀ / 2 = ω₀ := by ring
      rw [this]; exact hω
    have heq := (hU2 ℂ_[2] W hW norm_two ha1 (ptW 2 L ι W (α * (ω₀ / 2))) (ptW 2 L ι W (ω₀ / 2))
      (fun h => h2 ((hzero _).1 h)) d1 h1).2 (fun h => ht0 ((hzero _).1 h)) d2 H
    have hd : α * (ω₀ / 2) - ω₀ / 2 ∈ L.lattice := by
      rw [← hzero, sub_eq_add_neg, hadd, ptW_neg hU, heq, add_neg_cancel]
    apply hc
    have e : conj α * (ω₀ / 2) = conj α * (α * (ω₀ / 2)) - conj α * (α * (ω₀ / 2) - ω₀ / 2) := by
      ring
    rw [e]
    exact sub_mem (key _ h2t0) (hcm _ hd)
  refine ⟨first, ?_, ?_⟩
  · intro Q hQ H
    apply first
    have e : ω₀ / 2 = α * Q + -(α * Q - ω₀ / 2) := by ring
    rw [e]
    exact kernel_subgroup_add_mem hU hW _ _ (hS' _ H) (kernel_subgroup_neg_mem hU hW _ (lattice_point_in_kernel_subgroup hU _ hQ))
  · intro z hz h2z
    apply hc
    have e : conj α * (ω₀ / 2) = conj α * (α * z) - conj α * (α * z - ω₀ / 2) := by ring
    rw [e]
    exact sub_mem (key _ h2z) (hcm _ hz)

theorem Th0TwoFinal_of (hP : PointsTwoFinal) : ThetaZeroAtTwo := by
  intro L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  obtain ⟨p1, p2, p3⟩ := hP L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  have ht0 : ω₀ / 2 ∉ L.lattice := fun h => p1 (lattice_point_in_kernel_subgroup hU _ h)
  have hx : ‖px W (ptW 2 L ι W (ω₀ / 2))‖ ≤ 1 := Half.norm_x_le_one_of_not_in_kernel _ p1
  have hI : Formalism.L2.Th1.A.IntModel W := ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨q1, q2⟩ := th0TwoAnalytic L ι W hU hI α ω₀ b b' hα hmul hω ht0 hb hb' hnb hnb' p3 hx
    (fun z hz => Half.norm_x_le_one_of_not_in_kernel _ (p2 z hz))
  exact ⟨q1, q2, Formalism.L2.Th1.E.shiftAnalyticW 2 L ι W hU hW ω₀ hω ht0 hx q2⟩

end Formalism.L2.Th1.B.KFin
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionKernelUniqueHolds
noncomputable section

namespace Formalism.L2.Th1.B.KNorm

open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma nadd_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma nadd_lt {a b : K} {r : ℝ} (ha : ‖a‖ < r) (hb : ‖b‖ < r) : ‖a + b‖ < r :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

lemma nsub_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact nadd_le ha (by rwa [norm_neg])

lemma ndom {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma nmul1 {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

lemma npow1 {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ha

lemma n2le : ‖(2 : K)‖ ≤ 1 := by
  rw [show (2 : K) = 1 + 1 by norm_num]
  exact nadd_le norm_one.le norm_one.le

lemma n4le : ‖(4 : K)‖ ≤ 1 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact nmul1 n2le n2le

lemma n4 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(4 : K)‖ = 4⁻¹ := by
  rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]
  norm_num

lemma n3 (h2 : ‖(2 : K)‖ = 2⁻¹) : ‖(3 : K)‖ = 1 := by
  rw [show (3 : K) = 1 + 2 by norm_num, ndom (by rw [h2, norm_one]; norm_num), norm_one]

lemma two_ne (h2 : ‖(2 : K)‖ = 2⁻¹) : (2 : K) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h2
  norm_num at h2

lemma b_int (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨nadd_le (npow1 h1 2) (nmul1 n4le h2), nadd_le (nmul1 n2le h4) (nmul1 h1 h3),
    nadd_le (npow1 h3 2) (nmul1 n4le h6), ?_⟩
  exact nsub_le (nadd_le (nsub_le (nadd_le (nmul1 (npow1 h1 2) h6) (nmul1 (nmul1 n4le h2) h6))
    (nmul1 (nmul1 h1 h3) h4)) (nmul1 h2 (npow1 h3 2))) (npow1 h4 2)

lemma t4 (h2 : ‖(2 : K)‖ = 2⁻¹) (x : K) : ‖4 * x ^ 3‖ = ‖x‖ ^ 3 / 4 := by
  rw [norm_mul, norm_pow, n4 h2]
  ring

lemma tb2 {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖b * x ^ 2‖ ≤ ‖x‖ ^ 2 := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) hb

lemma tb4 (h2 : ‖(2 : K)‖ = 2⁻¹) {b : K} (hb : ‖b‖ ≤ 1) (x : K) : ‖2 * b * x‖ ≤ ‖x‖ / 2 := by
  rw [norm_mul, norm_mul, h2]
  nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg x)]

variable {b2 b4 b6 b8 x : K}

lemma psi_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ ‖x‖ ^ 3 / 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.2 hx)]
  have e2 : ‖x‖ / 2 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [mul_nonneg r0 (sub_nonneg.2 hx)]
  have e3 : 1 ≤ ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  exact nadd_le (nadd_le (nadd_le (t4 h2 x).le ((tb2 hb2 x).trans e1)) ((tb4 h2 hb4 x).trans e2))
    (hb6.trans e3)

lemma psi_zero_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ ≤ 4 := by
  by_contra hlt
  push_neg at hlt
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 3 / 4 := by nlinarith [mul_pos (by linarith : (0:ℝ) < ‖x‖) (sub_pos.2 hlt)]
  have e3 : 1 < ‖x‖ ^ 3 / 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hlt.le 3]
  have hr : ‖b2 * x ^ 2 + 2 * b4 * x + b6‖ < ‖4 * x ^ 3‖ := by
    rw [t4 h2]
    exact nadd_lt (nadd_lt ((tb2 hb2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show 4 * x ^ 3 + (b2 * x ^ 2 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, t4 h2] at key
  nlinarith [pow_pos (by linarith : (0:ℝ) < ‖x‖) 3]

lemma num_norm (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1) (hb8 : ‖b8‖ ≤ 1)
    (hx : 4 ≤ ‖x‖) : ‖x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8‖ = ‖x‖ ^ 4 := by
  have r0 : 0 ≤ ‖x‖ := norm_nonneg _
  have r2 : 16 ≤ ‖x‖ ^ 2 := by nlinarith
  have r4 : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  have e1 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  have e3 : 1 < ‖x‖ ^ 4 := by rw [r4]; nlinarith
  rw [show x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8 = x ^ 4 + -(b4 * x ^ 2 + 2 * b6 * x + b8) by ring]
  rw [ndom, norm_pow]
  rw [norm_neg, norm_pow]
  exact nadd_lt (nadd_lt ((tb2 hb4 x).trans_lt e1) ((tb4 h2 hb6 x).trans_lt e2)) (hb8.trans_lt e3)

lemma dup_core (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hb8 : ‖b8‖ ≤ 1) (hx : 4 ≤ ‖x‖) {X : K}
    (hX : X * (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
      = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) : 4 < ‖X‖ := by
  have hn := num_norm h2 hb4 hb6 hb8 hx
  have hp := psi_le h2 hb2 hb4 hb6 hx
  have hm := congrArg norm hX
  rw [norm_mul, hn] at hm
  by_contra hle
  push_neg at hle
  have hb : ‖X‖ * ‖4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6‖ ≤ 4 * (‖x‖ ^ 3 / 4) :=
    mul_le_mul hle hp (norm_nonneg _) (by norm_num)
  have r3 : 0 < ‖x‖ ^ 3 := pow_pos (by linarith) 3
  nlinarith

lemma psi_zero_eq (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ = 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : 1 < ‖x‖) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) : ‖x‖ = 4 := by
  refine le_antisymm (psi_zero_le h2 hb2.le hb4 hb6 h0) ?_
  by_contra hlt
  push_neg at hlt
  have e1 : ‖x‖ ^ 3 / 4 < ‖x‖ ^ 2 := by nlinarith [mul_pos (pow_pos (by linarith : (0:ℝ) < ‖x‖) 2) (sub_pos.2 hlt)]
  have e2 : ‖x‖ / 2 < ‖x‖ ^ 2 := by nlinarith
  have e3 : 1 < ‖x‖ ^ 2 := by nlinarith
  have hd : ‖b2 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, hb2, one_mul, norm_pow]
  have hr : ‖4 * x ^ 3 + 2 * b4 * x + b6‖ < ‖b2 * x ^ 2‖ := by
    rw [hd]
    exact nadd_lt (nadd_lt ((t4 h2 x).trans_lt e1) ((tb4 h2 hb4 x).trans_lt e2)) (hb6.trans_lt e3)
  have key := ndom hr
  rw [show b2 * x ^ 2 + (4 * x ^ 3 + 2 * b4 * x + b6) = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 by ring,
    h0, norm_zero, hd] at key
  nlinarith

lemma four_add_le (h2 : ‖(2 : K)‖ = 2⁻¹) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    (hx : ‖x‖ = 4) (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0) :
    ‖4 * x + b2‖ ≤ 1 / 8 := by
  have e : x ^ 2 * (4 * x + b2) = -(2 * b4 * x + b6) := by linear_combination h0
  have hr : ‖2 * b4 * x + b6‖ ≤ 2 :=
    nadd_le ((tb4 h2 hb4 x).trans (by rw [hx]; norm_num)) (hb6.trans (by norm_num))
  have hm := congrArg norm e
  rw [norm_mul, norm_pow, hx, norm_neg] at hm
  nlinarith [norm_nonneg (4 * x + b2)]

lemma psi_zero_unique (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    {x' : K} (hx : ‖x‖ = 4) (hx' : ‖x'‖ = 4)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0)
    (h0' : 4 * x' ^ 3 + b2 * x' ^ 2 + 2 * b4 * x' + b6 = 0) : x = x' := by
  have f := four_add_le h2 hb4 hb6 hx h0
  have f' := four_add_le h2 hb4 hb6 hx' h0'
  have hfac : (x - x') * (4 * x * x' + (x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4)) = 0 := by
    linear_combination h0 - h0'
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  exfalso
  have hdom : ‖4 * x * x'‖ = 4 := by
    rw [norm_mul, norm_mul, n4 h2, hx, hx']
    norm_num
  have a1 : ‖x * (4 * x + b2)‖ < 4 := by
    rw [norm_mul, hx]
    linarith
  have a2 : ‖x' * (4 * x' + b2)‖ < 4 := by
    rw [norm_mul, hx']
    linarith
  have a3 : ‖2 * b4‖ < 4 := by
    rw [norm_mul, h2]
    nlinarith [norm_nonneg b4]
  have hr : ‖x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4‖ < ‖4 * x * x'‖ := by
    rw [hdom]
    exact nadd_lt (nadd_lt a1 a2) a3
  have key := ndom hr
  rw [h, norm_zero, hdom] at key
  norm_num at key

end Norm

section Curve

variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}

lemma psi_eq (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * h

lemma negY_iff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  constructor <;> intro h <;> linear_combination h

variable [DecidableEq K]

lemma dup (h : W.toAffine.Equation x y) (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y)
        * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hden : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.2 hy
  have hdd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, ← hdd, div_mul_cancel₀ _ hden]
  rw [← psi_eq h, WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
      + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hl
    + (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * h

lemma add_self_iff (h : W.toAffine.Nonsingular x y) :
    (Point.some x y h + Point.some x y h = 0) ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [true_and]
  exact negY_iff

lemma px_add_self (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) :
    px W (Point.some x y h + Point.some x y h)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  rw [WeierstrassCurve.Affine.Point.add_some (fun hxy => hy hxy.2)]
  rfl

end Curve

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}

lemma two_tors_le (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hP : P + P = 0) : ‖px W P‖ ≤ 4 := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change ‖(0 : K)‖ ≤ 4
    rw [norm_zero]
    norm_num
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 := psi_eq h.1
    rw [hd] at h0
    exact psi_zero_le (x := x) h2 hb2 hb4 hb6 (by rw [← h0]; ring)

lemma dup_big (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point)
    (hx : 4 ≤ ‖px W P‖) (hP : P + P ≠ 0) : 4 < ‖px W (P + P)‖ := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_int W h1 h2a h3 h4 h6
  cases P with
  | zero =>
    change 4 ≤ ‖(0 : K)‖ at hx
    rw [norm_zero] at hx
    norm_num at hx
  | some x y h =>
    have hy : y ≠ W.toAffine.negY x y := fun e => hP ((add_self_iff h).2 (negY_iff.1 e))
    rw [px_add_self h hy]
    exact dup_core h2 hb2 hb4 hb6 hb8 hx (dup h.1 hy)

lemma tors_bound (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point) (k : ℕ)
    (hk : (2 ^ k) • P = 0) (hP : P + P ≠ 0) : ‖px W P‖ < 4 := by
  by_contra hge
  push_neg at hge
  have claim : ∀ j : ℕ, 4 < ‖px W ((2 ^ (j + 1)) • P)‖ := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, two_nsmul]
      exact dup_big hW h2 P hge hP
    | succ j ih =>
      have hQ : (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P ≠ 0 := by
        intro e
        have := two_tors_le hW h2 _ e
        linarith
      have e : (2 ^ (j + 1 + 1)) • P = (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P := by
        rw [← add_nsmul]
        congr 1
        ring
      rw [e]
      exact dup_big hW h2 _ ih.le hQ
  cases k with
  | zero =>
    rw [pow_zero, one_nsmul] at hk
    rw [hk, add_zero] at hP
    exact hP rfl
  | succ k =>
    have hc := claim k
    rw [hk] at hc
    change 4 < ‖(0 : K)‖ at hc
    rw [norm_zero] at hc
    norm_num at hc

lemma two_torsion_kernel_norm_unique (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (ha : ‖W.a₁‖ = 1)
    (P Q : W.toAffine.Point) (hP0 : P ≠ 0) (hP : P + P = 0) (hPE : InFormalGroupPoints P) :
    ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q) := by
  obtain ⟨h1, h2a, h3, h4, h6, -⟩ := hW
  obtain ⟨-, hb4, hb6, -⟩ := b_int W h1 h2a h3 h4 h6
  have hb2 : ‖W.b₂‖ = 1 := by
    simp only [WeierstrassCurve.b₂]
    rw [ndom (by rw [norm_pow, ha, one_pow, norm_mul, n4 h2]; nlinarith [norm_nonneg W.a₂]),
      norm_pow, ha, one_pow]
  cases P with
  | zero => exact (hP0 rfl).elim
  | some x y h =>
    have hd := (add_self_iff h).1 hP
    have h0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      have e := psi_eq h.1
      rw [hd] at e
      rw [← e]
      ring
    have hx4 : ‖x‖ = 4 := psi_zero_eq (x := x) h2 hb2 hb4 hb6 hPE h0
    refine ⟨hx4, fun hQ0 hQ hQE => ?_⟩
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x' y' h' =>
      have hd' := (add_self_iff h').1 hQ
      have h0' : 4 * x' ^ 3 + W.b₂ * x' ^ 2 + 2 * W.b₄ * x' + W.b₆ = 0 := by
        have e := psi_eq h'.1
        rw [hd'] at e
        rw [← e]
        ring
      have hx4' : ‖x'‖ = 4 := psi_zero_eq (x := x') h2 hb2 hb4 hb6 hQE h0'
      have hxx := psi_zero_unique h2 hb2.le hb4 hb6 hx4 hx4' h0 h0'
      subst hxx
      have hyy : y = y' := by
        have e2 : (2 : K) * y = 2 * y' := by linear_combination hd - hd'
        exact mul_left_cancel₀ (two_ne h2) e2
      subst hyy
      rfl

end Main

open Classical in
theorem two_torsion_kernel_unique_holds : TwoTorsionKernelUnique := by
  intro K _ _ W hW h2 ha P Q hP0 hP hPE
  exact two_torsion_kernel_norm_unique hW h2 ha P Q hP0 hP hPE

open Classical in
theorem torsion_norm_bound_holds : TorsBound := by
  intro K _ _ W hW h2 P k hk hP
  exact tors_bound hW h2 P k hk hP

theorem kappa_norm_holds : KapNorm := by
  intro K _ _ _ W hM h2 x
  obtain ⟨h1, h2a, h3, h4, h6⟩ := hM
  obtain ⟨hb2, hb4, -, -⟩ := b_int W h1 h2a h3 h4 h6
  have e : 3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4
      = 3 * x ^ 2 + 2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄ := by
    simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.c₄]
    ring
  have ni : ‖(2 : K)⁻¹‖ = 2 := by rw [norm_inv, h2, inv_inv]
  have t1 : ‖3 * x ^ 2‖ = ‖x‖ ^ 2 := by rw [norm_mul, n3 h2, one_mul, norm_pow]
  have t2 : ‖2⁻¹ * W.b₂ * x‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul, norm_mul, ni]
    nlinarith [mul_le_mul_of_nonneg_right hb2 (norm_nonneg x), norm_nonneg W.b₂]
  have t3 : ‖2⁻¹ * W.b₄‖ ≤ 2 := by
    rw [norm_mul, ni]
    linarith
  rw [e]
  constructor
  · intro hx
    have hr : ‖2⁻¹ * W.b₂ * x + 2⁻¹ * W.b₄‖ < ‖3 * x ^ 2‖ := by
      rw [t1, hx]
      exact nadd_lt (t2.trans_lt (by rw [hx]; norm_num)) (t3.trans_lt (by norm_num))
    rw [add_assoc, ndom hr, t1, hx]
    norm_num
  · intro hx
    have r0 := norm_nonneg x
    exact nadd_lt (nadd_lt (by rw [t1]; nlinarith) (t2.trans_lt (by linarith))) (t3.trans_lt (by norm_num))

end Formalism.L2.Th1.B.KNorm
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CoeffTwoPSeries
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.KSum

open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

theorem coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)

theorem coeff_two_shift (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact (L.lattice.toAddSubgroup).isClosed_of_discreteTopology)
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring

theorem kappa_sum_holds : KappaSum := by
  intro L α S hα hst hS
  obtain ⟨neg, -, -, -, h3⟩ := Formalism.L2.Th1.F.endoZInstance L α S hα hst hS
  have h4 := congrArg (PowerSeries.coeff 2) h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add (f := _), map_sum,
    coeff_two_pSeries] at h4
  have h5 : ∀ P : S, PowerSeries.coeff 2
      (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ)))
        = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4 := by
    intro P
    rw [map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]
    simp
  rw [Finset.sum_congr rfl (fun P _ => h5 P),
    Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)] at h4
  linear_combination -h4

end Formalism.L2.Th1.B.KSum
end
end

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.LCm

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)
open Polynomial

theorem norm_odd (T : ℤ) (hT : Odd T) : ‖(T : ℤ_[2])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h
  obtain ⟨k, hk⟩ := hT
  obtain ⟨m, hm⟩ := h
  push_cast at hm
  omega

theorem norm_even (N : ℤ) (hN : Even N) : ‖(N : ℤ_[2])‖ < 1 := by
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact_mod_cast even_iff_two_dvd.mp hN

theorem quadratic_two_adic_holds : QuadTwoAdic := by
  intro T N hT hN
  let F : Polynomial ℤ_[2] := X ^ 2 - C (T : ℤ_[2]) * X + C (N : ℤ_[2])
  have hF0 : F.aeval (0 : ℤ_[2]) = (N : ℤ_[2]) := by simp [F]
  have hD0 : F.derivative.aeval (0 : ℤ_[2]) = -(T : ℤ_[2]) := by simp [F]
  have hnorm : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hD0, norm_neg, norm_odd T hT]
    simpa using norm_even N hN
  obtain ⟨z, hz, hz1, -, -⟩ := hensels_lemma hnorm
  rw [hD0, norm_neg, norm_odd T hT, sub_zero] at hz1
  have hz' : z ^ 2 - (T : ℤ_[2]) * z + (N : ℤ_[2]) = 0 := by simpa [F] using hz
  refine ⟨(T : ℤ_[2]) - z, z, by ring, by linear_combination -hz', ?_, hz1⟩
  have h := PadicInt.norm_add_eq_max_of_ne (q := (T : ℤ_[2])) (r := -z)
    (by rw [norm_neg, norm_odd T hT]; exact hz1.ne')
  rw [sub_eq_add_neg, h, norm_neg, norm_odd T hT]
  exact max_eq_left hz1.le

theorem roots_two_adic_holds : RootsTwoAdic := by
  intro ι α T N hT hN hTo hNe
  obtain ⟨b, b', hs, hp, hb, hb'⟩ := quadratic_two_adic_holds T N hTo hNe
  let φ : ℤ_[2] →+* ℂ_[2] := UniformSpace.Completion.coeRingHom.comp
    ((algebraMap ℚ_[2] (PadicAlgCl 2)).comp PadicInt.Coe.ringHom)
  have hφ : ∀ x : ℤ_[2],
      φ x = ((algebraMap ℚ_[2] (PadicAlgCl 2) (x : ℚ_[2]) : PadicAlgCl 2) : ℂ_[2]) :=
    fun x => rfl
  refine ⟨b, b', hb, hb', ?_⟩
  simp only [← hφ]
  have hs' : φ b + φ b' = ι α + ι (conj α) := by
    rw [← map_add (f := _), ← map_add (f := _), hs, hT]
    simp
  have hp' : φ b * φ b' = ι α * ι (conj α) := by
    rw [← map_mul, ← map_mul, hp, hN]
    simp
  have key : (ι α - φ b) * (ι α - φ b') = 0 := by
    linear_combination (-(ι α)) * hs' + hp'
  rcases mul_eq_zero.mp key with h | h
  · have e : ι α = φ b := sub_eq_zero.mp h
    exact Or.inl ⟨e, by linear_combination -hs' - e⟩
  · have e : ι α = φ b' := sub_eq_zero.mp h
    exact Or.inr ⟨e, by linear_combination -hs' - e⟩

theorem mulStable_conj (L : PeriodPair) (α : ℂ) (T : ℤ) (h : MulStable L α)
    (hT : α + conj α = (T : ℂ)) : MulStable L (conj α) := by
  intro ω hω
  have h1 : conj α = (T : ℂ) - α := by rw [← hT]; ring
  rw [h1, sub_mul, ← zsmul_eq_mul]
  exact L.lattice.sub_mem (L.lattice.smul_mem T hω) (h ω hω)

theorem theta_zero_two_adic_trace : ThetaZeroTwoTrace := by
  have KI : KernelIntegral := KKer.KernelIntegral_of KNorm.two_torsion_kernel_unique_holds
    KNorm.torsion_norm_bound_holds KNorm.kappa_norm_holds KSum.kappa_sum_holds
  have hF : ThetaZeroAtTwo :=
    KFin.Th0TwoFinal_of (KFin.PointsTwoFinal_of KI (KFin.kernel_stable_of_integral_kernel KI) KNorm.two_torsion_kernel_unique_holds)
  intro L ι W hU hI ha α ω₀ T N hα hT hN hTo hNe hω h1 h2
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : (T : ℂ) = 0 := by rw [← hT]; simp
    have hT0 : T = 0 := by exact_mod_cast h0
    obtain ⟨k, hk⟩ := hTo
    omega
  obtain ⟨b, b', hb, hb', (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := roots_two_adic_holds ι α T N hT hN hTo hNe
  · exact hF L ι W hU hI ha α ω₀ b b' hα0 hα e1 e2 hb hb' hω h2
  · have hc : conj (conj α) = α := Complex.conj_conj α
    have hs := mulStable_conj L α T hα hT
    exact hF L ι W hU hI ha (conj α) ω₀ b b' (by simpa using hα0) hs e2
      (by rw [hc]; exact e1) hb hb' hω (by rw [hc]; exact h1)

theorem conj_omegaK (d : ℕ) :
    conj (Formalism.L2.Th1.CM.omegaK d) = (1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [Formalism.L2.Th1.CM.omegaK, map_div₀, map_add (f := _), map_one, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

theorem theta_zero_two_complex_mult : ThetaZeroTwoCM := by
  intro d L hd hCM ι W hU hI ha ω₀ hω h1 h2
  obtain ⟨k, hk⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
  have hs2 : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = 8 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), hk]
    push_cast
    ring
  refine theta_zero_two_adic_trace L ι W hU hI ha (CM.omegaK d) ω₀ 1 (2 * (k : ℤ) + 2) hCM ?_ ?_ ?_ ?_
    hω h1 h2
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    ring
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4) * hs2
  · exact odd_one
  · exact ⟨k + 1, by push_cast; ring⟩

end Formalism.L2.Th1.B.LCm
end
end

namespace Formalism.L2.Th1.B

theorem th0TwoCM : ThetaZeroTwoCM := LCm.theta_zero_two_complex_mult

end Formalism.L2.Th1.B
