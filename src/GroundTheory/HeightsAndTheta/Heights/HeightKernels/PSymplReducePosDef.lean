module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReducePosDef

theorem sum_mul_symplCons {n : ℕ} (c : ℝ) (x : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ p, F p * symplCons c 0 x p =
      F (Sum.inl 0) * c + ∑ q, F (Sum.map Fin.succ Fin.succ q) * x q := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, symplCons]
  ring

end PSymplReducePosDef


open PSymplReducePosDef in
theorem SymplReducePosDef.proof : SymplReducePosDef.Statement := by
  intro n H hH
  have hsymm : ∀ i j, H j i = H i j := fun i j => by
    simpa using hH.isHermitian.apply i j
  have hpos : 0 < H (Sum.inl 0) (Sum.inl 0) := hH.diag_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [symplReduce, star_trivial]
    rw [hsymm (Sum.map Fin.succ Fin.succ a), hsymm (Sum.map Fin.succ Fin.succ a) (Sum.inl 0),
      hsymm (Sum.inl 0) (Sum.map Fin.succ Fin.succ b)]
    ring
  · intro x hx
    simp only [star_trivial]
    set h := H (Sum.inl 0) (Sum.inl 0) with hh
    set S := ∑ b, H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) * x b with hS
    set Q := ∑ a, (∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b) * x a
      with hQ
    have hT : ∑ a, x a * H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = S := by
      rw [hS]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsymm]; ring
    have hy : symplCons (-(S / h)) 0 x ≠ 0 := by
      intro hz
      apply hx
      funext q
      have := congrFun hz (Sum.map Fin.succ Fin.succ q)
      cases q <;> simpa [symplCons] using this
    have h1 := hH.dotProduct_mulVec_pos hy
    simp only [star_trivial] at h1
    have hL : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        (h * (-(S / h)) + S) * (-(S / h)) + (-(S / h)) * S + Q := by
      rw [dotProduct_comm]
      simp only [dotProduct, mulVec, PSymplReducePosDef.sum_mul_symplCons]
      rw [← hh, ← hS]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← hQ]
      have hc : ∑ q, H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) * (-(S / h)) * x q =
          (-(S / h)) * S := by
        rw [← hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [hc]
      ring
    have hRa : ∀ a, ∑ b, (H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
        H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
          h) * x b =
        ∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b -
          H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / h * S := by
      intro a
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hR : x ⬝ᵥ (symplReduce H *ᵥ x) = Q - S / h * S := by
      simp only [dotProduct, mulVec, symplReduce]
      rw [← hh]
      simp only [hRa, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, ← hT, Finset.sum_div, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
    have hne : h ≠ 0 := hpos.ne'
    have key : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        x ⬝ᵥ (symplReduce H *ᵥ x) := by
      rw [hL, hR]
      field_simp
      ring
    rw [← key]
    exact h1

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinExists

variable {ι : Type} [Fintype ι]

theorem qf_smul (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_qf (G : Matrix ι ι ℝ) : Continuous (qf G) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem exists_lower [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x := fun x hx => by
    simpa [qf] using hG.dotProduct_mulVec_pos hx
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (continuous_qf G).continuousOn
  refine ⟨qf G u, hpos u ?_, fun x => ?_⟩
  · rintro rfl
    simp at hu
  · by_cases hx : x = 0
    · subst hx
      simp [qf]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : qf G u ≤ qf G (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ hy
      calc qf G u * ‖x‖ ^ 2 ≤ qf G (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
        _ = qf G x := by
          rw [qf_smul]
          field_simp

end PSymplMinExists

theorem SymplMinExists.proof (h1 : SymplQuadDiag.Statement) : SymplMinExists.Statement := by
  intro ι _ _ _ G hG
  obtain ⟨μ, hμ, hlow⟩ := PSymplMinExists.exists_lower G hG
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def
  set M₀ : ℝ := qf G (intVec v₀) with hM₀
  set R : ℤ := ⌈M₀ / μ⌉ with hR
  set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS
  have hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
    rintro v ⟨-, hq⟩
    have hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ := by
      intro i
      have hi : |(v i : ℝ)| ≤ ‖intVec v‖ := by
        have := norm_le_pi_norm (intVec v) i
        simpa [intVec, Real.norm_eq_abs] using this
      have hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by
        rcases eq_or_ne (v i) 0 with h | h
        · simp [h]
        · have h' : (1 : ℝ) ≤ |(v i : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs h
          nlinarith
      have hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rw [le_div_iff₀ hμ]
      calc |(v i : ℝ)| * μ ≤ μ * ‖intVec v‖ ^ 2 := by nlinarith
        _ ≤ qf G (intVec v) := hlow _
        _ ≤ M₀ := hq
    have hc : ∀ i, |v i| ≤ R := by
      intro i
      have : ((|v i| : ℤ) : ℝ) ≤ (R : ℝ) := by
        rw [Int.cast_abs]
        exact (hb i).trans (Int.le_ceil _)
      exact_mod_cast this
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.mp (hc i)).1
    · exact (abs_le.mp (hc i)).2
  have hfin : S.Finite := (Set.finite_Icc _ _).subset hbox
  have hv₀ : v₀ ∈ S := by
    refine ⟨fun h => ?_, le_rfl⟩
    have := congrFun h i₀
    simp [v₀] at this
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩
  refine ⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  by_cases hvS : qf G (intVec v) ≤ M₀
  · exact hwmin v ⟨hv, hvS⟩
  · exact hwS.2.trans (le_of_lt (not_le.mp hvS))

end GroundTheory.Heights₂.Heights
end
