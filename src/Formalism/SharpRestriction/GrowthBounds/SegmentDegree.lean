module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypOfTypical
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.M0LeBwOfIsW
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BfamAtWLetterEq

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BetaRatioBound
section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AdmissibleSmallRatio
section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementN
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K

def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)

def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

theorem geom_range_le (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : (0:ℝ) < (p:ℝ)^(m0+n) := pow_pos hP0 _
    have e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n) := by
      rw [← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n)) := by ring
    linarith

theorem geometricSumDistinct : GeomDistinct := by
  intro p m0 s hp hs
  have hP0 : (0:ℝ) < p := by
    have : (2:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  obtain ⟨n, hn⟩ : ∃ n, ∀ D ∈ s, D < m0 + n :=
    ⟨s.sup (fun x => x) + 1, fun D hD => by
      have := Finset.le_sup (f := fun x => x) hD
      omega⟩
  have hsub : s ⊆ (Finset.range n).image (fun i => m0 + i) := by
    intro D hD
    simp only [Finset.mem_image, Finset.mem_range]
    have h1 := hn D hD
    have h2 := hs D hD
    exact ⟨D - m0, by omega, by omega⟩
  calc ∑ D ∈ s, (1 / (p:ℝ)^D)
      ≤ ∑ D ∈ (Finset.range n).image (fun i => m0 + i), (1 / (p:ℝ)^D) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range n, (1 / (p:ℝ)^(m0+i)) := by
        rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    _ ≤ 2 / (p:ℝ)^m0 - 2 / (p:ℝ)^(m0+n) := geom_range_le p m0 n hp
    _ ≤ 2 / (p:ℝ)^m0 := by
        have : (0:ℝ) ≤ 2 / (p:ℝ)^(m0+n) := by positivity
        linarith

theorem admissibleSmallRatio : AdmissibleSmallRatio := by
  intro p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hNs' : (1:ℝ) ≤ Ns := by exact_mod_cast hNs
  have hY0 : (0:ℝ) < Y := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hNs0 : (0:ℝ) < Ns := by linarith
  have hR : (0:ℝ) < (p:ℝ)^R := pow_pos hP0 _
  have hR' : (0:ℝ) < (p:ℝ)^R' := pow_pos hP0 _
  have hD1 : (0:ℝ) < (p:ℝ)^D1 := pow_pos hP0 _
  have hL : (0:ℝ) < (p:ℝ)^L1 := pow_pos hP0 _
  have hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R := by positivity
  have sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤
      (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) :=
    div_le_div_of_nonneg_right hbe hT.le
  have sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) =
      4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) := by
    rw [show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]
    field_simp
  have ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn)) := by
    rwa [div_lt_iff₀ (by positivity)] at h7
  have sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) <
      32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [div_lt_div_iff₀ (by positivity) hL]
    have := mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)
    nlinarith
  have hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y) := by
    rw [div_le_div_iff₀ hL (by positivity), hPL]
    have := mul_le_mul_of_nonneg_right h8 hP0.le
    nlinarith
  have s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [sB] at sA
    exact lt_of_le_of_lt sA sC
  have s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ⟨s1, s2, by linarith⟩

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem beta_ratio_bound : BetaRatioBound 1088 := by
  intro p n' r K _ _ _ X hX hLa hk j b hA
  classical
  have hV := hX.valid
  have B := basics hX
  have hr : 0 < r := NeZero.pos r
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hp2 : 2 ≤ p := hX.prime.two_le
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have ha0 : 0 < X.a := by have := TE.four_hundred_sixteen_le_a hX; linarith

  have hL1 : 1 ≤ X.L₁ := by
    by_contra h
    have h0 : X.L₁ = 0 := by omega
    have hP2 := hX.P2
    rw [h0] at hP2
    have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
    rw [e1] at hP2
    have e2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ B.p1
    have e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 := by
      have k5 := B.k5
      unfold Dat.k at k5
      have a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith [B.Y1]
      have a3 := B.Ns1
      have a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) := by nlinarith
      nlinarith
    linarith
  have hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1) := by
    have h := hX.P2
    have e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast] at h
    exact h
  set D1 := X.F.dist j (X.F.fr j 0) with hD1
  set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs
  have hfr0 : X.F.fr j 0 ∈ X.F.letters j := k_fr_mem_letters X.F hV j hr
  have hD1c := TE.dist_cast hfr0

  have hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x := by
    intro x hx
    have hne : s.Nonempty := ⟨x, hx⟩
    have hmax := Finset.max'_mem s hne
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hmax
    have hgap := hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt =>
      Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))
    have hle := Finset.le_max' s x hx
    have hxc := TE.dist_cast (Finset.mem_filter.mp hx).1
    omega

  have hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1) := by
    unfold Dat.beS
    push_cast
    have h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have b1 := (TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2
      have b2 := (TE.c_bounds hX h41 j x hx1).2.2
      refine le_trans b1 ?_
      rw [pow_add]
      have hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x := by positivity
      have hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
      rw [div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]
      exact div_le_div_of_nonneg_right b2 (by positivity)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn (X.F.dist j) (s : Set ℤ) := by
      intro x hx y hy hxy
      have c1 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      have c2 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
      have : (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ) := by exact_mod_cast hxy
      omega
    have h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D) :=
      (Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm
    have h3 := Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by
      intro D hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
      exact hU1 x hx)
    rw [h2]
    have hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_
    rw [div_mul_div_comm, ← pow_add]
    have e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1 := by ring
    rw [e]
    apply le_of_eq
    ring

  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by
    have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hV (by omega : j < j + 1)
    exact ⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d := by
    have : ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0 := by
      unfold Frames.dist
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) <
      (p : ℝ) ^ X.Rj p K (j + 1) := by
    have h := lt_pow_Rj hX (j + 1)
    unfold Tj at h
    rw [add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))] at h
    unfold Dat.k at h
    have hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have k5 := B.k5
      unfold Dat.k at k5
      have := B.Ns1
      have := B.Y1
      positivity
    rw [div_lt_iff₀ hden] at h
    have hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) =
          (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := by ring
      rw [e]; exact mul_pos hp0 hden
    rw [div_lt_iff₀ hden2]
    calc X.a < (p : ℝ) ^ X.Rj p K (j + 1) * (p : ℝ) *
          (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := h
      _ = _ := by ring
  have hcore := (Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y
    ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega)
    (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2.2

  have hexp := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0 := (mem_letters_bounds hfr0).1
  have hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j := by
    unfold Dat.Qc
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    have : (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) =
        X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    omega
  rw [← hQ] at hcore
  have hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ) := by
    rw [hQ]; positivity
  rw [div_le_div_iff₀ hQpos (by have := B.Y1; positivity)] at hcore
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightAlt
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightOfTopCount
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdFromSelfEqOne
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DomOfStripDown
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TailTGlueT
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def tailT (t : ℕ) (la : Fin (r + K) → ℤ) : Fin (K + t) → ℤ := fun l =>
  if h : (r - t) + l.val < r + K then la ⟨(r - t) + l.val, h⟩ else 0

def glueT (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) : Fin (r + K) → ℤ := fun m =>
  if h : m.val < r - t then be else if h' : m.val - (r - t) < K + t then τ ⟨m.val - (r - t), h'⟩ else 0

theorem tailT_glueT (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) : tailT (r := r) t (glueT t be τ) = τ := by
  funext l
  have hl := l.2
  have h1 : (r - t) + l.val < r + K := by omega
  simp only [tailT, glueT, dif_pos h1]
  simp

theorem tailT_apply (t : ℕ) (ht : t ≤ r) (la : Fin (r + K) → ℤ) (l : Fin (K + t)) :
    tailT t la l = la ⟨(r - t) + l.val, by have := l.2; omega⟩ := by
  unfold tailT; rw [dif_pos]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem finite_SAll [NeZero r] [NeZero K] (H : HypT N n0 r K LL B od bb a La p) :
    (SAll (r := r) (K := K) LL n0 B).Finite := by
  have hS : (SP (r := r) (K := K) LL n0 B).Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.pi Set.univ fun _ : Fin (r + K) => Set.Icc (-(beA n0 B : ℤ)) (beA n0 B)) fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _).subset ?_
    rintro μ ⟨dd, hpa⟩
    obtain ⟨P, rfl⟩ := hpa.path
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, true_implies]
    intro s m
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast dminus_le_beA H hpa.degs s.val)) (neg_dminus_le_mu P s.val s.2 m), path_le_beA H P hpa s.val s.2 m⟩
  refine (hS.biUnion fun μ _ => (Set.finite_singleton μ).prod (finite_St (tanPart μ))).subset ?_
  rintro ⟨μ, I⟩ ⟨h1, h2⟩
  exact Set.mem_biUnion h1 ⟨rfl, h2⟩


open Classical in
def Af (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) :
    Finset (QT N r K) :=
  hfin.toFinset.filter fun q => ∀ t : Fin (N + 1), t.val ≤ s → q.1 t = μ0 t

open Classical in
theorem Af_fiber (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (la' : Fin (r + K) → ℤ) :
    (Af hfin s μ0).filter (fun q => q.1 (⟨s, hs⟩ : Fin N).succ = la') =
      Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la') := by
  ext q
  simp only [Af, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, h⟩, h'⟩
    refine ⟨hq, fun t ht => ?_⟩
    by_cases e : t = (⟨s, hs⟩ : Fin N).succ
    · subst e
      rw [Function.update_apply, if_pos rfl]
      exact h'
    · rw [Function.update_of_ne e]
      apply h
      have : t.val ≠ s + 1 := fun h2 => e (Fin.ext (by simp [h2]))
      omega
  · rintro ⟨hq, h⟩
    refine ⟨⟨hq, fun t ht => ?_⟩, ?_⟩
    · have e : t ≠ (⟨s, hs⟩ : Fin N).succ := by
        rintro rfl
        simp at ht
      rw [h t (by omega), Function.update_of_ne e]
    · rw [h _ (by simp)]
      simp

theorem Af_step (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ)
    (hs : s < N) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (q : QT N r K) (hq : q ∈ Af hfin s μ0) :
    Dominant (q.1 (⟨s, hs⟩ : Fin N).succ) ∧
      StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (q.1 (⟨s, hs⟩ : Fin N).succ) := by
  classical
  simp only [Af, Finset.mem_filter, Set.Finite.mem_toFinset] at hq
  obtain ⟨⟨hsp, -⟩, hμ⟩ := hq
  obtain ⟨dd, hpa⟩ := hsp
  obtain ⟨P, hP⟩ := hpa.path
  have hc : q.1 (⟨s, hs⟩ : Fin N).castSucc = μ0 (⟨s, hs⟩ : Fin N).castSucc := hμ _ (by simp)
  rw [← hc]
  have hstep := P.step ⟨s, hs⟩
  rw [hP] at hstep
  refine ⟨by rw [← hP]; exact P.dom _, fun hlt => ?_, fun hge => ⟨⟨dd ⟨s, hs⟩, ?_⟩, fun m hm => hpa.head _ m hge hm⟩⟩
  · rwa [← hpa.degs _ hlt]
  · have hv : LL.vec ⟨s, hs⟩ = true := H.vec_true_of_late _ (Nat.le_add_right_of_le hge)
    rwa [if_pos hv] at hstep


open Classical in
theorem Af_card_sum (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (E : Finset (Fin (r + K) → ℤ))
    (hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ E) :
    (Af hfin s μ0).card = ∑ la' ∈ E, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la')).card := by
  rw [Finset.card_eq_sum_card_fiberwise hE]
  refine Finset.sum_congr rfl fun la' _ => ?_
  rw [Af_fiber hfin s hs]

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

theorem glueT_lt (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : m.val < r - t) :
    glueT t be τ m = be := by
  unfold glueT; rw [dite_eq_left h]

theorem glueT_ge (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : r - t ≤ m.val) :
    glueT t be τ m = τ ⟨m.val - (r - t), by have := m.2; omega⟩ := by
  unfold glueT; rw [dite_eq_right (by omega), dite_eq_left]

theorem dom_of_strip_up {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hm1 : (m'.val - 1) + 1 < n := by have := m'.2; have : m.val < m'.val := hlt; omega
    have h2 := h.2.1 ⟨m'.val - 1, by have := m'.2; omega⟩ hm1
    have hme : (⟨(m'.val - 1) + 1, hm1⟩ : Fin n) = m' := Fin.ext (by simp only; have : m.val < m'.val := hlt; omega)
    rw [hme] at h2
    have h3 : ν ⟨m'.val - 1, by have := m'.2; omega⟩ ≤ ν m :=
      hν (by rw [Fin.le_def]; simp only; have : m.val < m'.val := hlt; omega)
    exact le_trans h2 (le_trans h3 (h.1 m))

theorem dom_of_strip_down {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hlt' : m.val < m'.val := hlt
    have hm1 : m.val + 1 < n := by have := m'.2; omega
    have h2 := h.2.1 m hm1
    have h3 : ν m' ≤ ν ⟨m.val + 1, hm1⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    exact le_trans (h.1 m') (le_trans h3 h2)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem tau_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (H : HypT N n0 r K LL B od bb a La p)
    (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (t s : ℕ) (hst : s + t = N) (_ht : t ≤ r) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (K + t) (tailT t (μ0 ⟨s, by omega⟩)) := by
  intro t
  induction t with
  | zero =>
    intro s hst _ μ0 hv
    have hsN : s = N := by omega
    subst hsN
    have hμ : μ0 ∈ SP (r := r) (K := K) LL n0 B := (sp_iff H μ0).2 hv
    have hA : Af hfin s μ0 = (finite_St (tanPart μ0)).toFinset.image (fun I => (μ0, I)) := by
      ext q
      unfold Af
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨⟨_, h2⟩, h3'⟩
        have hq : q.1 = μ0 := funext fun t => h3' t (by have := t.2; omega)
        exact ⟨q.2, by rw [← hq]; exact h2, Prod.ext hq.symm rfl⟩
      · rintro ⟨I, hI, rfl⟩
        exact ⟨⟨hμ, hI⟩, fun t _ => rfl⟩
    have hdom : Dominant (pEnd (tanPart μ0)) := by
      intro x y hxy
      exact hv.2.1 (Fin.last s) (by simp) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
    rw [hA, Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).2), ← Set.ncard_eq_toFinset_card _ (finite_St (tanPart μ0)),
      wt_eq D h3 _ hdom]
    show stCount K _ = stCount K _
    congr 1
    funext l
    have := tailT_apply (r := r) (K := K) 0 (Nat.zero_le r) (μ0 ⟨s, by omega⟩) l
    rw [show (tailT 0 (μ0 ⟨s, by omega⟩) : Fin (K + 0) → ℤ) l = _ from this]
    unfold pEnd tanPart
    congr 1
  | succ t ih =>
    intro s hst ht μ0 hv
    have hs : s < N := by omega
    have hN := H.hN
    have hn0 : n0 ≤ s := by omega
    have hla : ∀ m, μ0 (⟨s, hs⟩ : Fin N).castSucc m ≤ (beA n0 B : ℤ) := fun m => vp_le hv s (by omega) le_rfl m
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    generalize hlaeq : μ0 (⟨s, hs⟩ : Fin N).castSucc = la at hla hlad
    have hheads : ∀ m : Fin (r + K), m.val + 1 < r - t → la m = (beA n0 B : ℤ) := by
      intro m hm
      have hs1 : s - 1 < N := by omega
      have h1 := ((hv.2.2 ⟨s - 1, hs1⟩ (by simp only; omega)).2 (by simp only; omega)).2 m (by simp only; omega)
      have he : (⟨s - 1, hs1⟩ : Fin N).succ = (⟨s, hs⟩ : Fin N).castSucc := Fin.ext (by simp; omega)
      rw [he, hlaeq] at h1
      exact h1
    have hν : ∀ l : Fin (K + t + 1), (tailT (t + 1) la : Fin (K + t + 1) → ℤ) l =
        la ⟨(r - (t + 1)) + l.val, by have := l.2; omega⟩ := fun l => tailT_apply (t + 1) ht la l
    have hνdom : Dominant (tailT (t + 1) la : Fin (K + t + 1) → ℤ) := by
      intro x y hxy
      rw [hν, hν]
      exact hlad (by rw [Fin.le_def] at hxy ⊢; simp only; omega)
    set ν : Fin (K + t + 1) → ℤ := tailT (t + 1) la with hνdef
    set T := Fintype.piFinset (fun l : Fin (K + t) => Finset.Icc (ν l.succ) (ν l.castSucc)) with hT
    have hτ : ∀ τ ∈ T, ∀ l : Fin (K + t), ν l.succ ≤ τ l ∧ τ l ≤ ν l.castSucc := by
      intro τ hτ l
      rw [hT, Fintype.mem_piFinset] at hτ
      exact Finset.mem_Icc.mp (hτ l)
    have hinj : Set.InjOn (glueT (r := r) t (beA n0 B : ℤ)) (T : Set (Fin (K + t) → ℤ)) := by
      intro τ _ τ' _ h
      rw [← tailT_glueT (r := r) t (by omega) (beA n0 B : ℤ) τ, h, tailT_glueT (r := r) t (by omega)]
    have hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ T.image (glueT (r := r) t (beA n0 B : ℤ)) := by
      intro q hq
      obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
      rw [hlaeq] at hstq
      obtain ⟨⟨d, hS⟩, hh⟩ := hstq.2 hn0
      generalize q.1 (⟨s, hs⟩ : Fin N).succ = la' at hS hh
      rw [Finset.mem_image]
      refine ⟨tailT t la', ?_, ?_⟩
      · rw [hT, Fintype.mem_piFinset]
        intro l
        have hl := l.2
        rw [Finset.mem_Icc, hν, hν, tailT_apply t (by omega)]
        constructor
        · have := hS.1 ⟨(r - t) + l.val, by omega⟩
          have he : (⟨(r - (t + 1)) + (l.succ : Fin (K + t + 1)).val, by simp; omega⟩ : Fin (r + K)) =
              ⟨(r - t) + l.val, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact this
        · have := hS.2.1 ⟨(r - (t + 1)) + l.val, by omega⟩ (by simp only; omega)
          have he : (⟨(r - (t + 1)) + l.val + 1, by omega⟩ : Fin (r + K)) = ⟨(r - t) + l.val, by omega⟩ :=
            Fin.ext (by simp only; omega)
          rw [he] at this
          exact this
      · funext m
        by_cases hm : m.val < r - t
        · rw [glueT_lt t _ _ m hm, hh m (by simp only; omega)]
        · rw [glueT_ge t (by omega) _ _ m (by omega), tailT_apply t (by omega)]
          congr 1
          exact Fin.ext (by simp only; omega)
    have hterm : ∀ τ ∈ T, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ
        (glueT (r := r) t (beA n0 B : ℤ) τ))).card = stCount (K + t) τ := by
      intro τ hτT
      have hb := hτ τ hτT
      have hτanti : ∀ l l' : Fin (K + t), l ≤ l' → τ l' ≤ τ l := by
        intro l l' hll
        rcases eq_or_lt_of_le hll with he | hlt
        · rw [he]
        · have h1 := (hb l').2
          have h2 := (hb l).1
          have h3 : ν l'.castSucc ≤ ν l.succ := hνdom (by rw [Fin.le_def]; simp; exact hlt)
          linarith
      have hτbe : ∀ l : Fin (K + t), τ l ≤ (beA n0 B : ℤ) := by
        intro l
        refine le_trans (hb l).2 ?_
        rw [hν]; exact hla _
      have hd' : Dominant (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        intro m m' hmm
        have hmm' : m.val ≤ m'.val := hmm
        by_cases h1 : m'.val < r - t
        · rw [glueT_lt t _ _ m' h1, glueT_lt t _ _ m (by omega)]
        · rw [glueT_ge t (by omega) _ _ m' (by omega)]
          by_cases h2 : m.val < r - t
          · rw [glueT_lt t _ _ m h2]; exact hτbe _
          · rw [glueT_ge t (by omega) _ _ m (by omega)]
            exact hτanti _ _ (by rw [Fin.le_def]; simp only; omega)
      have hS1 : ∀ x, la x ≤ glueT (r := r) t (beA n0 B : ℤ) τ x := by
        intro x
        by_cases h1 : x.val < r - t
        · rw [glueT_lt t _ _ x h1]; exact hla x
        · rw [glueT_ge t (by omega) _ _ x (by omega)]
          have h2 := (hb ⟨x.val - (r - t), by have := x.2; omega⟩).1
          rw [hν] at h2
          have he : (⟨(r - (t + 1)) + ((⟨x.val - (r - t), by have := x.2; omega⟩ : Fin (K + t)).succ :
              Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
          rw [he] at h2
          exact h2
      have hst' : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        rw [hlaeq]
        refine ⟨fun h => absurd h (by simp only; omega), fun _ => ⟨⟨(∑ x, (glueT (r := r) t (beA n0 B : ℤ) τ x - la x)).toNat,
          hS1, ?_, ?_⟩, fun m hm => glueT_lt t _ _ m (by simp only at hm; omega)⟩⟩
        · intro x hx
          by_cases h1 : x.val + 1 < r - t
          · rw [glueT_lt t _ _ _ (by simp only; exact h1), hheads x h1]
          · rw [glueT_ge t (by omega) _ _ _ (by simp only; omega)]
            have h2 := (hb ⟨x.val + 1 - (r - t), by have := x.2; omega⟩).2
            rw [hν] at h2
            have he : (⟨(r - (t + 1)) + ((⟨x.val + 1 - (r - t), by have := x.2; omega⟩ : Fin (K + t)).castSucc :
                Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
            rw [he] at h2
            exact h2
        · exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => sub_nonneg.mpr (hS1 x))).symm
      have hv' := vp_update hs hv _ hd' hst'
      rw [ih (s + 1) (by omega) (by omega) _ hv']
      congr 1
      show tailT t (Function.update μ0 (⟨s, hs⟩ : Fin N).succ (glueT (r := r) t (beA n0 B : ℤ) τ)
        (⟨s, hs⟩ : Fin N).succ) = τ
      rw [Function.update_self, tailT_glueT t (by omega)]
    rw [Af_card_sum hfin s hs μ0 _ hE, Finset.sum_image hinj, Finset.sum_congr rfl hterm]
    have h4' := h4 (K + t) ν hνdom
    show _ = stCount (K + t + 1) (tailT (t + 1) (μ0 (⟨s, hs⟩ : Fin N).castSucc))
    rw [hlaeq]
    exact h4'.symm

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [if_neg he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_neg (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_pos hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_neg (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

theorem lemT_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : LemT :=
  lemT_of (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) path_count_finite (atypical_path_small_weight D hAdm.2.2.1) typical_path_orders_small

theorem good_path_weight_of_top_count (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (h41 : TopCountLowerBounds 1088) : GoodPathWeight 1088 :=
  good_path_weight_of_parts 1088 (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) (lemT_of_adm D hAdm) (TE.letter_dictionary_bounds h41)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem good_path_weight (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : GoodPathWeight 1088 :=
  good_path_weight_of_top_count D hAdm (top_count_lower_bounds 1088 (by norm_num))

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (h41 : DiscriminantNonzeroModUniformiser) (h45 : AdmB D → GeneratorModuloUniformiser 1088)
    (hLam : AdmB D → RestLam 1088) (hPad : RestPad 1088) (hSum : RestSum 1088 1)
    (hMem : AdmB D → RestMem 1088) (hInd : AdmB D → RestInd 1088)
    (hT1 : AdmB D → GoodPathWeight 1088) (hMon : RestMon 1088) : SecondPartClosed D :=
  second_estimate_of_rank_bound D 1088 1 (by norm_num) (by norm_num) restDeg restSel fun hA =>
    restRank_of 1088 1 h41 (h45 hA)
      (restCount_of 1088 1 (hLam hA) (restSeg_of 1088 (hMem hA) (hInd hA) restFin (hT1 hA) hMon) hPad hSum)

theorem restMon : RestMon 1088 := restMon_of 1088 beta_ratio_bound tau_degree_on_path_bound residue_class_count

theorem restInd (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestInd 1088 := restInd_of 1088 (restKey_of D hAdm 1088)

theorem secondPartClosed (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  second_estimate_of_restrictions D discriminant_nonzero_mod_uniformiser (fun hA => generator_modulo_uniformiser_of_adm D hA 1088 (by norm_num))
    (fun hA => restLam_of D hA 1088 restLamDeg)
    restPad restSum (fun hA => restMem_of D hA) (fun hA => restInd D hA) (fun hA => good_path_weight D hA) restMon

end Formalism.MainNotions.SelectionLemmas.Pf
