module

public import Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearOneSlot
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in
theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp only at ha hh
  subst ha hh
  rfl


open Classical in
noncomputable def indLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then 1 else 0
  pos z hz := by rw [if_pos hz]; exact one_pos
  smul c z hc := by
    have : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
      simp [hc]
    simp only [this]
    simp

theorem indLine_smooth : IsSmoothHerm (indLine ι) :=
  (contDiffOn_const (c := (1 : ℝ))).congr fun _ hz => if_pos hz

theorem tensor_indLine {A B : HermLine ι} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) :
    A.tensor (indLine ι) = B.tensor (indLine ι) := by
  refine hermLine_ext (by simp [HermLine.tensor, ha]) (funext fun z => ?_)
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · show A.h z * _ = B.h z * _
    rw [hh z hz]
  · have : (indLine ι).h z = 0 := if_neg hz
    show A.h z * _ = B.h z * _
    rw [this, mul_zero, mul_zero]

theorem additive_congr (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) : φ A = φ B := by
  have h1 := hφ A _ hA indLine_smooth
  have h2 := hφ B _ hB indLine_smooth
  rw [tensor_indLine ha hh] at h1
  linarith

theorem combLine_single {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (j : J) :
    combLine ℓ (Pi.single j 1) = ℓ j := by
  refine hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ i, (Pi.single j 1 : J → ℤ) i • (ℓ i).a = _
    rw [Finset.sum_eq_single j] <;> simp +contextual
  · show ∏ i, (ℓ i).h z ^ (Pi.single j 1 : J → ℤ) i = _
    rw [Finset.prod_eq_single j] <;> simp +contextual

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem additive_comb (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {J : Type} [Fintype J] (ℓ : J → HermLine ι) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) (n : J → ℤ) :
    φ (combLine ℓ n) = ∑ j, (n j : ℝ) * φ (ℓ j) := by
  classical
  have hs : ∀ m, IsSmoothHerm (combLine ℓ m) := fun m => (combLine_smooth_conj_invariant K ι J ℓ m).1 hℓ
  let ψ : (J → ℤ) →+ ℝ := AddMonoidHom.mk' (fun m => φ (combLine ℓ m)) (fun m m' => by
    show φ _ = φ _ + φ _
    rw [← hφ _ _ (hs m) (hs m')]
    refine additive_congr φ hφ (hs _) (tensor_smooth (hs m) (hs m')) ?_ fun z hz => ?_
    · show ∑ i, (m + m') i • (ℓ i).a = ∑ i, m i • (ℓ i).a + ∑ i, m' i • (ℓ i).a
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · show ∏ i, (ℓ i).h z ^ (m + m') i = (∏ i, (ℓ i).h z ^ m i) * ∏ i, (ℓ i).h z ^ m' i
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => zpow_add₀ ((ℓ i).pos z hz).ne' _ _)
  have hn : n = ∑ j, n j • (Pi.single j 1 : J → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  show ψ n = _
  conv_lhs => rw [hn]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  show _ * φ (combLine ℓ (Pi.single j 1)) = _
  rw [combLine_single]

end

end Ii

open Ii in
theorem intersection_multilinear_one_position : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  intro II hII K _ ι _ P d L k J _ ℓ n hP hL hℓ
  exact additive_comb (fun A => II K ι P d (Function.update L k A))
    (fun A B hA hB => hII.2.1 K ι P d L k A B hP hL hA hB) ℓ hℓ n

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.AntisymmetryTowerTheorem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem comp_swap_eq_swapWt {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (x : Ψ × Fin N → ℝ) (τ : Ψ) (a b : Fin N) :
    x ∘ ⇑(Equiv.swap (τ, a) (τ, b)) = fun z : Ψ × Fin N => swapWt τ a b (fun s i => x (s, i)) z.1 z.2 := by
  funext z
  obtain ⟨s, i⟩ := z
  simp only [swapWt, Function.comp_apply, Equiv.swap_apply_def, Prod.mk.injEq]
  by_cases hs : s = τ
  · subst hs
    by_cases hia : i = a
    · subst hia
      simp
    · by_cases hib : i = b
      · subst hib
        simp [hia]
      · simp [hia, hib]
  · simp [hs]

private theorem inWall_and_dominant_of_eq_neighbors {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (hj0 : 1 ≤ j) (hjN : j < N)
    (τ : Ψ) (x : Ψ × Fin N → ℝ)
    (hx : x ∈ Metric.closedBall (fun y : Ψ × Fin N => -(1 / (4 * ((N : ℝ) + 1)) *
        (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ j ≤ (y.2 : ℕ) then 1 else 0))) (1 / (16 * ((N : ℝ) + 1))))
    (hxe : x (τ, ⟨j - 1, by omega⟩) = x (τ, ⟨j, hjN⟩)) :
    InWall j τ (1 / (8 * ((N : ℝ) + 1))) (fun s i => x (s, i)) ∧
      Dominant (Ψ := Ψ) (N := N) (fun s i => x (s, i)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 / 4 := by
    rw [hδ]
    field_simp
  have hr : 1 / (16 * ((N : ℝ) + 1)) = δ / 4 := by
    rw [hδ]
    field_simp
    ring
  have hc : 1 / (8 * ((N : ℝ) + 1)) = δ / 2 := by
    rw [hδ]
    field_simp
    ring
  rw [← hδ, hr] at hx
  rw [hc]
  have hb : ∀ (s : Ψ) (i : Fin N),
      |x (s, i) - -(δ * (((i : ℕ) : ℝ) - if s = τ ∧ j ≤ (i : ℕ) then 1 else 0))| ≤ δ / 4 := by
    intro s i
    have h1 := (dist_pi_le_iff (by linarith)).1 (Metric.mem_closedBall.1 hx) (s, i)
    rwa [Real.dist_eq] at h1
  have G : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → ¬ (s = τ ∧ (b : ℕ) = j) →
      δ / 2 ≤ x (s, a) - x (s, b) := by
    intro s a b hab hn
    have hite : (if s = τ ∧ j ≤ (a : ℕ) then (1 : ℝ) else 0) = if s = τ ∧ j ≤ (b : ℕ) then 1 else 0 := by
      by_cases hs : s = τ
      · have hbj : (b : ℕ) ≠ j := fun h => hn ⟨hs, h⟩
        simp only [hs, true_and]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp [hs]
    have hbR : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
    have ha := abs_le.1 (hb s a)
    have hb2 := abs_le.1 (hb s b)
    rw [hite] at ha
    rw [hbR] at hb2
    linarith [ha.1, ha.2, hb2.1, hb2.2]
  have hcons : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → x (s, b) ≤ x (s, a) := by
    intro s a b hab
    by_cases hs : s = τ ∧ (b : ℕ) = j
    · obtain ⟨rfl, hbj⟩ := hs
      have ha : a = ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩ := Fin.ext (show (a : ℕ) = j - 1 by omega)
      have hb' : b = ⟨j, hjN⟩ := Fin.ext hbj
      have e1 : x (s, b) = x (s, ⟨j, hjN⟩) := congrArg (fun i => x (s, i)) hb'
      have e2 : x (s, a) = x (s, ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩) :=
        congrArg (fun i => x (s, i)) ha
      rw [e1, e2]
      exact hxe.ge
    · have := G s a b hab hs
      linarith
  have hdom : ∀ (s : Ψ) (k : ℕ) (a b : Fin N), (b : ℕ) = (a : ℕ) + k → x (s, b) ≤ x (s, a) := by
    intro s k
    induction k with
    | zero =>
      intro a b h
      have : b = a := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro a b h
      have hbl := b.isLt
      have hc : (a : ℕ) + k < N := by omega
      exact le_trans (hcons s ⟨(a : ℕ) + k, hc⟩ b (show (b : ℕ) = (a : ℕ) + k + 1 by omega))
        (ih a ⟨(a : ℕ) + k, hc⟩ rfl)
  refine ⟨?_, ?_⟩
  · show _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun s =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      show ‖x (s, i)‖ ≤ 1 / 2
      rw [Real.norm_eq_abs]
      have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt.le
      have hI0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) := by
        split_ifs with hh
        · have h1 : 1 ≤ (i : ℕ) := le_trans hj0 hh.2
          have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
          linarith
        · simp
      have hI1 : ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) ≤ N := by
        split_ifs <;> linarith
      have hA := mul_nonneg hδpos.le hI0
      have hB := mul_le_mul_of_nonneg_left hI1 hδpos.le
      have h1 := abs_le.1 (hb s i)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    · simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact sub_eq_zero.2 hxe
    · intro τ' hτ'
      simp only [gap, ent, dite_eq_left (show j - 1 < N by omega), dite_eq_left hjN]
      exact G τ' ⟨j - 1, by omega⟩ ⟨j, hjN⟩ (show j = j - 1 + 1 by omega) (fun h => hτ' h.1)
    · intro s i hi hij
      simp only [ent, dite_eq_left (show i < N by omega), dite_eq_left hi]
      exact G s ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl (fun h => hij h.2)
  · intro s a b hab
    exact hdom s ((b : ℕ) - (a : ℕ)) a b (by have := Fin.le_iff_val_le_val.1 hab; omega)

set_option maxHeartbeats 800000 in
open GroundTheory.Heights₂.Heights in
theorem antisymmetry_tower_theorem : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  intro hS II Ψ _ _ N T hh hprop hW h8 h9
  obtain ⟨hvol, -, -⟩ := hprop
  have hj0 : 1 ≤ T.j := T.j_pos
  have hjN : T.j < N := T.j_lt
  have hv : 0 < T.volT := by
    show 0 < ∑ c : T.Comp, T.vol c
    exact Finset.sum_pos (fun c _ => hvol c) Finset.univ_nonempty
  obtain ⟨h, hhom, hev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) hh
  let x0 : Ψ → Ψ × Fin N → ℝ := fun τ y => -(1 / (4 * ((N : ℝ) + 1)) *
    (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ T.j ≤ (y.2 : ℕ) then 1 else 0))
  let K : Ψ → Set (Ψ × Fin N → ℝ) := fun τ =>
    diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∩ Metric.closedBall (x0 τ) (1 / (16 * ((N : ℝ) + 1)))
  have hK : ∀ τ : Ψ, IsCompact (K τ) ∧ K τ ⊆ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∧
      (∃ O : Set (Ψ × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ⊆ K τ) ∧
      ∀ x ∈ K τ, eval x h = 0 := by
    intro τ
    have hHc : IsClosed (diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩) :=
      isClosed_eq (continuous_apply _) (continuous_apply _)
    refine ⟨(isCompact_closedBall _ _).inter_left hHc, Set.inter_subset_left,
      ⟨Metric.ball (x0 τ) (1 / (16 * ((N : ℝ) + 1))), Metric.isOpen_ball,
        ⟨x0 τ, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩, ?_⟩
    · show x0 τ (τ, ⟨T.j - 1, by omega⟩) = x0 τ (τ, ⟨T.j, hjN⟩)
      simp [x0, show ¬ T.j ≤ T.j - 1 by omega, Nat.cast_sub hj0]
    · rintro x ⟨hxO, hxH⟩
      exact ⟨hxH, Metric.ball_subset_closedBall hxO⟩
    · rintro x ⟨hxH, hxB⟩
      obtain ⟨-, hdom⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
      rw [hev x]
      exact h9.1 (fun s i => x (s, i)) hdom
        ⟨τ, ⟨T.j - 1, by omega⟩, ⟨T.j, hjN⟩, (show T.j = T.j - 1 + 1 by omega), hxH⟩
  obtain ⟨C0, hC⟩ := hS Ψ N T.j (by omega) hjN h K hK
  obtain ⟨CW, B₁, hB⟩ := hW (1 / (8 * ((N : ℝ) + 1))) (by positivity)
  unfold RootTower.ThmB
  refine ⟨C0 * CW, max B₁ 2, fun B hB₂ => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hB₂
  have hB2 : 2 ≤ B := le_trans (le_max_right _ _) hB₂
  let L : RP Ψ N →ₗ[ℝ] ℝ :=
    ∑ c : T.Comp, ((T.M B c).PP II).comp (rename (some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
  have hL : ∀ F, L F = T.PPt II B F := by
    intro F
    simp [L, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  obtain ⟨P, hPhom, hPev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) L
  have hQev : ∀ x : Ψ × Fin N → ℝ, eval x (P - T.volT • h) =
      (L - T.volT • hh) ((-∑ z, MvPolynomial.C (x z) * X z) ^ (dimFl Ψ N + 1)) := by
    intro x
    rw [map_sub, MvPolynomial.smul_eval, hPev, hev]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hQhom : (P - T.volT • h).IsHomogeneous (dimFl Ψ N + 1) :=
    (mem_homogeneousSubmodule _ _).1 (Submodule.sub_mem _ ((mem_homogeneousSubmodule _ _).2 hPhom)
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hhom)))
  have key : ∀ F, T.PPt II B F - T.volT * hh F = ∑ c, (T.PPc II B c F - T.vol c * hh F) := by
    intro F
    simp only [RootTower.PPt, RootTower.volT, Finset.sum_sub_distrib, Finset.sum_mul]
  have hanti : P - T.volT • h ∈ antisymSpace Ψ N T.j := by
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · have hd : antisymDegree Ψ N + 1 = dimFl Ψ N + 1 := by
        simp only [antisymDegree, dimFl, Nat.choose_two_right]
      rw [hd]
      exact (mem_homogeneousSubmodule _ _).2 hQhom
    · rintro σ ⟨τ, a, b, hab, hj, rfl⟩
      have hbj : (b : ℕ) ≠ T.j := by omega
      apply MvPolynomial.funext
      intro x
      rw [eval_rename, map_neg, hQev, hQev, comp_swap_eq_swapWt x τ a b]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL]
      rw [key, key]
      have hsum := Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset T.Comp)) =>
        h8 B hB2 c τ a b hab hbj (fun s i => x (s, i))
      rw [Finset.sum_neg_distrib] at hsum
      exact hsum
  have hsmall : ∀ τ : Ψ, ∀ x ∈ K τ, |eval x P| ≤ CW * Real.log B / B := by
    rintro τ x ⟨hxH, hxB⟩
    obtain ⟨hwall, -⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
    rw [hPev x, hL]
    exact hB B hB1 τ (fun s i => x (s, i)) hwall
  obtain ⟨l, hl, hlc⟩ := hC P T.volT (CW * Real.log B / B) hanti hsmall
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.antisymmetric_perturbation_bound Ψ N T.j (L - T.volT • hh) T.volT (C0 * (CW * Real.log B / B))
    (P - T.volT • h) l hv (fun lam => hQev _) hQhom hl hlc
  refine ⟨α, β, fun m hm => ?_⟩
  have h1 := hαβ m hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h1
  rw [show C0 * CW * Real.log B / B = C0 * (CW * Real.log B / B) by ring]
  refine (le_of_eq ?_).trans h1
  congr 1
  ring

end RootFieldNumerics
end
