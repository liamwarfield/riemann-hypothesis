module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.RedAbs
namespace CrystallineSemistableComparison.Inj

theorem dual_span {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Module.Dual k V) (hf : ∀ v, (∀ i, f i v = 0) → v = 0) (g : Module.Dual k V) :
    ∃ c : ι → k, ∀ v, g v = ∑ i, c i * f i v := by
  have hker : LinearMap.ker (LinearMap.pi f) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hf v fun i => congrFun hv i
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.pi f) hker
  refine ⟨fun i => g (ρ (Pi.single i 1)), fun v => ?_⟩
  have h1 : v = ρ (LinearMap.pi f v) := by rw [← LinearMap.comp_apply, hρ, LinearMap.id_apply]
  have h2 : LinearMap.pi f v = ∑ i, f i v • Pi.single i (1 : k) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1, h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem red_abs {k B V : Type*} [Field k] [CommRing B] [AddCommGroup V] [Module k V] (q : k →+* B) (S : AddSubgroup B)
    (hS : ∀ x s, s ∈ S → q x * s ∈ S) {ι : Type*} [Fintype ι] (f : ι → Module.Dual k V)
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) {n : ℕ} (b : Module.Basis (Fin n) k V) (z : Fin n → B)
    (hy : ∀ i, ∑ m, z m * q (f i (b m)) ∈ S) (m' : Fin n) : z m' ∈ S := by
  classical
  obtain ⟨c, hc⟩ := dual_span f hf (b.coord m')
  have key : z m' = ∑ i, q (c i) * ∑ m, z m * q (f i (b m)) := by
    calc z m' = ∑ m, z m * q (b.coord m' (b m)) := by
          simp [Module.Basis.coord_apply, Finsupp.single_apply]
      _ = ∑ m, z m * q (∑ i, c i * f i (b m)) := by simp_rw [← hc]
      _ = _ := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp_rw [map_sum, map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  exact sum_mem fun i _ => hS _ _ (hy i)

end CrystallineSemistableComparison.Inj
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ConnAbs
noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Inj

theorem cup_fil {K B : Type*} [Field K] [CommRing B] (P : Subring B) (t : B) (ht : t ∈ P) (o : K →+* B)
    (ho : ∀ k, o k ∈ P) {H1 H2 H3 : Type*} [AddCommGroup H1] [Module K H1] [AddCommGroup H2] [Module K H2]
    [AddCommGroup H3] [Module K H3] (F1 : ℕ → Set H1) (F2 : ℕ → Set H2) (F3 : ℕ → Set H3)
    (cup : H1 →ₗ[K] H2 →ₗ[K] H3) (hcup : ∀ r s, ∀ x ∈ F1 r, ∀ y ∈ F2 s, cup x y ∈ F3 (r + s))
    (d : ℕ) (hd : ∀ e, d < e → ∀ x ∈ F3 e, x = 0)
    {m m' : ℕ} (b : Module.Basis (Fin m) K H1) (w : Fin m → ℕ)
    (hb : ∀ s, b s ∈ F1 (w s) ∧ ∀ x ∈ F1 (w s + 1), b.coord s x = 0)
    (b' : Module.Basis (Fin m') K H2) (w' : Fin m' → ℕ)
    (hb' : ∀ s, b' s ∈ F2 (w' s) ∧ ∀ x ∈ F2 (w' s + 1), b'.coord s x = 0)
    (C1 : Module.Dual K H1 → B) (hC1 : ∀ r φ, (∀ x ∈ F1 (r + 1), φ x = 0) → t ^ r * C1 φ ∈ P)
    (C2 : Module.Dual K H2 → B) (hC2 : ∀ r φ, (∀ x ∈ F2 (r + 1), φ x = 0) → t ^ r * C2 φ ∈ P)
    (φ : Module.Dual K H3) :
    t ^ d * ∑ s, ∑ s', C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s'))) ∈ P := by
  rw [Finset.mul_sum]
  refine P.sum_mem fun s _ => ?_
  rw [Finset.mul_sum]
  refine P.sum_mem fun s' _ => ?_
  by_cases h : w s + w' s' ≤ d
  · have h1 := hC1 (w s) (b.coord s) (hb s).2
    have h2 := hC2 (w' s') (b'.coord s') (hb' s').2
    have e : t ^ d * (C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s')))) =
        t ^ (d - (w s + w' s')) * (t ^ w s * C1 (b.coord s)) * (t ^ w' s' * C2 (b'.coord s')) *
          o (φ (cup (b s) (b' s'))) := by
      have : d = (d - (w s + w' s')) + w s + w' s' := by omega
      conv_lhs => rw [this]
      ring
    rw [e]
    exact P.mul_mem (P.mul_mem (P.mul_mem (P.pow_mem ht _) h1) h2) (ho _)
  · have h0 : cup (b s) (b' s') = 0 :=
      hd _ (by omega) _ (hcup _ _ _ (hb s).1 _ (hb' s').1)
    rw [h0, map_zero, map_zero, mul_zero, mul_zero]
    exact P.zero_mem

theorem exists_int_mul {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (v : ℚ_[p] ⊗[ℤ_[p]] T) : ∃ s : ℤ_[p], s ≠ 0 ∧ ∃ x : T, (s : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q y =>
    obtain ⟨⟨ζ, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) q
    refine ⟨s, nonZeroDivisors.ne_zero s.2, ζ • y, ?_⟩
    simp only at hs
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    calc ((s : ℤ_[p]) : ℚ_[p]) • q = q * algebraMap ℤ_[p] ℚ_[p] s := by rw [smul_eq_mul, mul_comm]; rfl
      _ = algebraMap ℤ_[p] ℚ_[p] ζ := hs
      _ = ζ • (1 : ℚ_[p]) := by rw [Algebra.smul_def, mul_one]
  | add v v' hv hv' =>
    obtain ⟨s, hs, x, hx⟩ := hv
    obtain ⟨s', hs', x', hx'⟩ := hv'
    refine ⟨s * s', mul_ne_zero hs hs', s' • x + s • x', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hx, ← hx', smul_add]
    simp only [PadicInt.coe_mul]
    rw [← algebraMap_smul ℚ_[p] s', ← algebraMap_smul ℚ_[p] s, smul_smul, smul_smul]
    congr 2 <;> simp [PadicInt.algebraMap_apply] <;> ring

end CrystallineSemistableComparison.Inj
end
end
