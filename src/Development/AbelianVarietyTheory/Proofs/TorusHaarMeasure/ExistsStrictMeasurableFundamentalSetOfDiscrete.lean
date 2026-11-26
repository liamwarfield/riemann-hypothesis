module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen ({1} : Set Γ) := by
      rw [isOpen_induced_iff]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (hΓU x x.2 (htU hx))
      · rintro rfl
        exact h1t
    haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split hU
    let C : G → Set G := fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}
    have hCo : ∀ x, IsOpen (C x) := fun x =>
      (hVo.preimage (continuous_id.mul continuous_const)).inter
        (hVo.preimage (continuous_const.mul continuous_inv))
    have hCx : ∀ x, x ∈ C x := fun x => by simp [C, hV1]
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable C hCo
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h1 : (1 : G) ∈ ⋃ x, C x := Set.mem_iUnion.2 ⟨1, hCx 1⟩
      rw [← hT, h] at h1
      simp at h1
    obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
    let W : ℕ → Set G := fun n => C (c n)
    have hWo : ∀ n, IsOpen (W n) := fun n => hCo _
    have hcover : ∀ x, ∃ n, x ∈ W n := by
      intro x
      have hx : x ∈ ⋃ y ∈ T, C y := by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩
      rw [hc] at hx
      simp only [Set.biUnion_range, Set.mem_iUnion] at hx
      exact hx
    have hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1 := by
      intro n x γ hx hγx
      have h := hVU _ hγx.1 _ hx.2
      have he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ := by group
      rw [he] at h
      exact Subtype.ext (hΓU γ γ.2 h)
    let S : ℕ → Set G := fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m
    have hSo : ∀ m, IsOpen (S m) := fun m =>
      isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)
    have hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m := fun m x => by
      simp only [S, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun n =>
        (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)
    · intro g
      have hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔
          ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m := by
        intro y
        simp only [Set.mem_iUnion, Set.mem_diff, not_exists]
        constructor
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m => hm m m.2⟩
      have hex : ∃ n, g ∈ S n := by
        obtain ⟨n, hn⟩ := hcover g
        exact ⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩
      classical
      obtain ⟨γ, hγ⟩ := (hmemS _ g).1 (Nat.find_spec hex)
      refine ⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩
      · obtain ⟨δ, hδ⟩ := (hmemS m _).1 hS
        exact Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)
      · intro γ' hγ'
        obtain ⟨k, hk, hkS⟩ := (hmemF _).1 hγ'
        have hkN : k = Nat.find hex := by
          refine le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))
          by_contra hlt
          push_neg at hlt
          exact hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)
        rw [hkN] at hk
        have h1 := hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)
        exact mul_inv_eq_one.1 h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsScalarSubPosSemidef
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open scoped Matrix.Norms.L2Operator MatrixOrder in
open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_scalar_sub_posSemidef {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
  have h1 : (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := A) hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact Matrix.le_iff.1 h
  refine ⟨1 + ‖A‖, by linarith [norm_nonneg A], ?_⟩
  have e : ((1 + ‖A‖ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A =
      1 + (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A) := by
    rw [Complex.coe_smul, add_smul, one_smul, add_sub_assoc]
  rw [e]
  exact Matrix.PosSemidef.one.add h1

theorem gram_det_eq_zero_of_lt_card {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by
  by_contra hd
  have hu : IsUnit (Nᴴ * N) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := (Matrix.rank_mul_le_right Nᴴ N).trans (Matrix.rank_le_card_height N)
  rw [h1, Fintype.card_fin] at h2
  omega

theorem gram_det_mul_le :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) := by
  intro H r a
  obtain ⟨c, hc1, hc⟩ := exists_scalar_sub_posSemidef (aᴴ * a) (Matrix.isHermitian_conjTranspose_mul_self a)
  refine ⟨c ^ r, one_le_pow₀ hc1, ?_⟩
  intro ι _ _ M
  by_cases hι : r < Fintype.card ι
  · rw [gram_det_eq_zero_of_lt_card (a * M) hι, gram_det_eq_zero_of_lt_card M hι]
    simp
  · push Not at hι
    have hP : (Mᴴ * (aᴴ * a) * M).PosSemidef :=
      (Matrix.posSemidef_conjTranspose_mul_self a).conjTranspose_mul_mul_same M
    have hQ : (Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M).PosSemidef := hc.conjTranspose_mul_mul_same M
    obtain ⟨-, hle, -⟩ := H ι _ _ hP hQ
    have hM0 : 0 ≤ (Mᴴ * M).det.re :=
      (H ι _ _ (Matrix.posSemidef_conjTranspose_mul_self M) (Matrix.posSemidef_conjTranspose_mul_self M)).1
    have e1 : (a * M)ᴴ * (a * M) = Mᴴ * (aᴴ * a) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : Mᴴ * (aᴴ * a) * M + Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M = (c : ℂ) • (Mᴴ * M) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [e1]
    refine hle.trans ?_
    rw [e2, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hι) hM0

end GlobalTheory
end
