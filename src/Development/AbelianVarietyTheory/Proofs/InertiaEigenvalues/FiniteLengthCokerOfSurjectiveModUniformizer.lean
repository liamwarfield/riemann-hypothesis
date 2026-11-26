module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdeals
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def boundedCoeffSeries (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c}
  mul_mem' hf hg := Hom.bdd_mul hf hg
  add_mem' hf hg := Hom.bdd_add hf hg
  algebraMap_mem' c := ⟨1, (A O K).algebraMap_mem c⟩

theorem Hom.exists_E_pow_mul_frob_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have key : ∀ {μ : Type} [Fintype μ] (Y : ZMod a → Matrix μ μ K⟦X⟧),
      (∀ τ i j, Y τ i j ∈ invE l e (A O K)) → ∃ n : ℕ, ∀ τ i j, E K l e ^ n * Y τ i j ∈ A O K := by
    intro μ _ Y hY
    choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn (τ, i, j))
  obtain ⟨n₁, hn₁⟩ := key P.mx P.mx_mem
  obtain ⟨n₂, hn₂⟩ := key Q.mxInv Q.mxInv_mem
  refine ⟨n₁ + n₂, fun τ h hh => ?_⟩
  obtain ⟨hb, Y, ⟨c, hc⟩, hF⟩ := hh
  have hA : ∀ f ∈ A O K, f ∈ boundedCoeffSeries O K := fun f hf => ⟨1, hf⟩
  have hfr : ∀ f ∈ boundedCoeffSeries O K, frob K l f ∈ boundedCoeffSeries O K := by
    rintro f ⟨d, hd⟩
    refine ⟨d, fun n => ?_⟩
    rw [coeff_frob]
    split_ifs
    · exact hd _
    · simpa using (norm_nonneg _).trans (hd 0)
  have hE : E K l e ∈ A O K := E_mem l e _
  refine ⟨mul_mem (hA _ (pow_mem hE _)) (hfr _ hb),
    (E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ), ?_, ?_⟩
  · have hmem : ∀ i j, ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ)) i j ∈
        boundedCoeffSeries O K := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact sum_mem fun k _ => mul_mem (sum_mem fun m _ =>
        mul_mem (hA _ (hn₁ τ i m)) (hfr _ ⟨c, fun n => hc m k n⟩)) (hA _ (hn₂ τ k j))
    choose d hd using hmem
    obtain ⟨D, hD⟩ := Finite.exists_le (fun p : ι × κ => d p.1 p.2)
    exact ⟨D, fun i j n => (hd i j n).trans (hD (i, j))⟩
  · have hmap : (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) =
        frob K l h • (1 : Matrix κ κ K⟦X⟧) := by
      have h1 : (F.mat (τ - 1) * Y).map (frob K l) = (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) :=
        Matrix.map_mul (f := (frob K l).toRingHom)
      rw [← h1, hF]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    calc F.mat τ * ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ))
        = (E K l e ^ n₁ * E K l e ^ n₂) • ((F.mat τ * P.mx τ) * Y.map (frob K l) * Q.mxInv τ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = (E K l e ^ n₁ * E K l e ^ n₂) •
          (Q.mx τ * ((F.mat (τ - 1)).map (frob K l) * Y.map (frob K l)) * Q.mxInv τ) := by
          rw [F.comm, Matrix.mul_assoc (Q.mx τ)]
      _ = (E K l e ^ (n₁ + n₂) * frob K l h) • (1 : Matrix κ κ K⟦X⟧) := by
          rw [hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mx_mul_mxInv, smul_smul, pow_add]

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  first | exact @GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | exact GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | (intros; apply GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHom
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.Hom

section Bounds

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_sum_le {s : Type} (t : Finset s) (f : s → K⟦X⟧) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k n, ‖coeff n (f k)‖ ≤ C) (n : ℕ) : ‖coeff n (∑ k ∈ t, f k)‖ ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k n) ih)

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply]
  refine norm_coeff_sum_le _ (fun k => Y i k * Z k j)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (fun k m => ?_) n
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun p => by rw [mul_one]; exact (ha i k p).trans (le_max_left _ _))
    (fun p => by rw [mul_one]; exact (hb k j p).trans (le_max_left _ _)) m

theorem bdd_frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frob K l f)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun n => ?_⟩
  rw [coeff_frob]
  split_ifs
  · exact hc _
  · simpa using (norm_nonneg _).trans (hc 0)

theorem bdd_map_frob (l : ℕ) [Fact l.Prime] {μ ν : Type} {Y : Matrix μ ν K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y.map (frob K l)) i j)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hY
  refine ⟨max c 0, fun i j n => ?_⟩
  rw [Matrix.map_apply, coeff_frob]
  split_ifs
  · exact (hc _ _ _).trans (le_max_left _ _)
  · simp

end Bounds

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_mem (l e : ℕ) {s : Type} [Finite s] (f : s → K⟦X⟧)
    (hf : ∀ x, f x ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ x, E K l e ^ N * f x ∈ A O K := by
  classical
  cases nonempty_fintype s
  choose n hn using fun x => mem_away.1 (hf x)
  refine ⟨Finset.univ.sup n, fun x => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ x))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn x)

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem map_frob_smul_one (l : ℕ) [Fact l.Prime] {μ : Type} [DecidableEq μ] (h : K⟦X⟧) :
    (h • (1 : Matrix μ μ K⟦X⟧)).map (frob K l) = frob K l h • (1 : Matrix μ μ K⟦X⟧) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mxInv_mul_mat (F : Hom P Q) (τ : ZMod a) :
    Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
  calc Q.mxInv τ * F.mat τ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
    _ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
        rw [F.comm, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]

theorem frob_ldiv_eq (F : Hom P Q) (τ : ZMod a) {h : K⟦X⟧} {Y : Matrix ι κ K⟦X⟧}
    (hY : Y * F.mat (τ - 1) = h • (1 : Matrix ι ι K⟦X⟧)) :
    P.mx τ * Y.map (frob K l) * Q.mxInv τ * F.mat τ = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
  have hφ : Y.map (frob K l) * (F.mat (τ - 1)).map (frob K l) = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
    rw [← map_frob_smul_one l h, ← hY]
    exact (Matrix.map_mul (f := ((frob K l : K⟦X⟧ →ₐ[K] K⟦X⟧) : K⟦X⟧ →+* K⟦X⟧))).symm
  rw [Matrix.mul_assoc, mxInv_mul_mat, ← Matrix.mul_assoc,
    Matrix.mul_assoc (P.mx τ) (Y.map (frob K l)), hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, P.mx_mul_mxInv]

end Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_frob_mem_ldivSet (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NeZero a] (κ : Type) [Fintype κ] [DecidableEq κ]
    (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : Hom P Q) :
    ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e (fun p : ZMod a × ι × ι => P.mx p.1 p.2.1 p.2.2)
    fun p => P.mx_mem _ _ _
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mxInv p.1 p.2.1 p.2.2) fun p => Q.mxInv_mem _ _ _
  refine ⟨N₁ + N₂, fun τ h ⟨hb, Y, hY, hYF⟩ => ⟨?_, ?_⟩⟩
  · exact bdd_mul (bdd_of_mem_A (pow_mem (E_mem l e (A O K)) _)) (bdd_frob l hb)
  · refine ⟨(E K l e ^ N₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ N₂ • Q.mxInv τ),
      bdd_matMul (bdd_matMul ⟨1, fun i j n => ?_⟩ (bdd_map_frob l hY)) ⟨1, fun i j n => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, i, j) n
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, i, j) n
    · simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [frob_ldiv_eq F τ hYF, smul_smul, smul_smul, pow_add]
      congr 1
      ring

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.frob_mem_ldivSet_target : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  exact GlobalTheory.BK.Hom.exists_pow_E_mul_frob_mem_ldivSet l e a ι κ P Q F
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  first | exact @GlobalTheory.BK.Hom.frob_mem_ldivSet_target | exact GlobalTheory.BK.Hom.frob_mem_ldivSet_target | (intros; apply GlobalTheory.BK.Hom.frob_mem_ldivSet_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  first | exact @GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | exact GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | (intros; apply GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.SliceLdiv

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem frobSlice_zero (l i : ℕ) : frobSlice l i (0 : K⟦X⟧) = 0 := by
  ext n; simp [coeff_frobSlice]

theorem frobSlice_sum {β : Type} (l i : ℕ) (s : Finset β) (g : β → K⟦X⟧) :
    frobSlice l i (∑ b ∈ s, g b) = ∑ b ∈ s, frobSlice l i (g b) := by
  ext n; simp [coeff_frobSlice, map_sum]

theorem frobSlice_mul_frob {l : ℕ} [Fact l.Prime] {i : ℕ} (hi : i < l) (z f : K⟦X⟧) :
    frobSlice l i (z * frob K l f) = frobSlice l i z * f := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  have hval : ∀ p q : ℕ, coeff (l * p + i) z * coeff q f =
      coeff (l * p + i) z * coeff (l * q) (frob K l f) := by
    intro p q
    rw [coeff_frob, if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q hl]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1 + i, l * p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq -
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hpq ⊢
    rw [← hpq, mul_add]; ring
  · rintro ⟨p, q⟩ - - ⟨p', q'⟩ - - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : p = p' := Nat.eq_of_mul_eq_mul_left hl (by omega)
    have h2' : q = q' := Nat.eq_of_mul_eq_mul_left hl h2
    rw [h1', h2']
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [coeff_frob] at hne
    split_ifs at hne with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have hq : q ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * q := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      have key : l * (n - q) + l * q = l * n := by rw [← mul_add, Nat.sub_add_cancel hq]
      have ha : a = l * (n - q) + i := by omega
      subst ha
      rw [Nat.mul_div_cancel_left q hl] at hne
      exact ⟨(n - q, q), by simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega,
        by simp only [coeff_frobSlice]; exact hne, rfl⟩
    · exact absurd (mul_zero _) hne
  · rintro ⟨p, q⟩ - -
    simp only [coeff_frobSlice]
    exact hval p q

theorem bdd_frobSlice (l i : ℕ) {z : K⟦X⟧} (hz : ∃ c : ℝ, ∀ n, ‖coeff n z‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frobSlice l i z)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem bdd_zero : ∃ c : ℝ, ∀ n, ‖coeff n (0 : K⟦X⟧)‖ ≤ c := ⟨0, fun n => by simp⟩

theorem bdd_sum {β : Type} (s : Finset β) (g : β → K⟦X⟧) (hg : ∀ b ∈ s, ∃ c : ℝ, ∀ n, ‖coeff n (g b)‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (∑ b ∈ s, g b)‖ ≤ c :=
  Finset.sum_induction g (fun f : K⟦X⟧ => ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c)
    (fun _ _ => Hom.bdd_add) bdd_zero hg

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {M : Matrix μ ν K⟦X⟧} {N : Matrix ν ρ K⟦X⟧}
    (hM : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) (hN : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (N i j)‖ ≤ c)
    (i : μ) (j : ρ) : ∃ c : ℝ, ∀ n, ‖coeff n ((M * N) i j)‖ ≤ c := by
  rw [Matrix.mul_apply]
  exact bdd_sum _ _ fun k _ => Hom.bdd_mul (hM i k) (hN k j)

theorem bdd_unif {μ ν : Type} [Finite μ] [Finite ν] {M : Matrix μ ν K⟦X⟧}
    (h : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n (M i j)‖ ≤ c := by
  choose c hc using h
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : μ × ν => c p.1 p.2)
  exact ⟨C, fun i j n => (hc i j n).trans (hC ⟨(i, j), rfl⟩)⟩

theorem exists_pow_E_mul_mem (l e : ℕ) {β : Type} [Finite β] (g : β → K⟦X⟧)
    (hg : ∀ b, g b ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ b, E K l e ^ N * g b ∈ A O K := by
  have := Fintype.ofFinite β
  choose n hn using fun b => (mem_away.1 (hg b))
  refine ⟨Finset.univ.sup n, fun b => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ b))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn b)

theorem frobSlice_mem_ldivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.ldivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × ι × ι => P.mxInv p.1 p.2.1 p.2.2) (fun p => P.mxInv_mem _ _ _)
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mx p.1 p.2.1 p.2.2) (fun p => Q.mx_mem _ _ _)
  refine ⟨N₁ + N₂, fun τ h hh i hi => ?_⟩
  obtain ⟨hhb, Y, ⟨cY, hcY⟩, hY⟩ := hh
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix ι κ K⟦X⟧,
      Z = (E K l e ^ N₁ • P.mxInv τ) * Y * (E K l e ^ N₂ • Q.mx τ) := ⟨_, rfl⟩
  have h1 : Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l) = h • P.mx τ := by
    rw [Matrix.mul_assoc, ← F.comm, ← Matrix.mul_assoc, hY, Matrix.smul_mul, Matrix.one_mul]
  have hZF : Z * (F.mat (τ - 1)).map (frob K l) =
      (E K l e ^ (N₁ + N₂) * h) • (1 : Matrix ι ι K⟦X⟧) := by
    have : Z * (F.mat (τ - 1)).map (frob K l) =
        E K l e ^ N₁ • E K l e ^ N₂ • (P.mxInv τ * (Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l))) := by
      simp only [hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      exact smul_comm _ _ _
    rw [this, h1, Matrix.mul_smul, P.mxInv_mul_mx]
    simp only [smul_smul, pow_add, mul_assoc]
  have hPb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₁ • P.mxInv τ) r k)‖ ≤ c := fun r k =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, r, k))
  have hQb : ∀ k c, ∃ c' : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₂ • Q.mx τ) k c)‖ ≤ c' := fun k c =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, k, c))
  have hYb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n (Y r k)‖ ≤ c := fun r k => ⟨cY, hcY r k⟩
  have hZb : ∀ r c, ∃ c' : ℝ, ∀ n, ‖coeff n (Z r c)‖ ≤ c' := fun r c => by
    rw [hZ]; exact bdd_matMul (bdd_matMul hPb hYb) hQb r c
  refine ⟨bdd_frobSlice l i (Hom.bdd_mul (bdd_of_mem_A (O := O) (pow_mem (E_mem l e (A O K)) _)) hhb),
    Z.map (frobSlice l i), bdd_unif fun r c => ?_, ?_⟩
  · rw [Matrix.map_apply]; exact bdd_frobSlice l i (hZb r c)
  · ext r c
    have hrc := congrFun (congrFun hZF r) c
    rw [Matrix.mul_apply] at hrc
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply] at hrc ⊢
    simp_rw [← frobSlice_mul_frob hi]
    rw [← frobSlice_sum, hrc, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_one]
    · rw [mul_zero, mul_zero, frobSlice_zero]

end GlobalTheory.BK.SliceLdiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.ldivSet (τ - 1) := by
  first | exact @GlobalTheory.BK.SliceLdiv.frobSlice_mem_ldivSet | exact GlobalTheory.BK.SliceLdiv.frobSlice_mem_ldivSet | (intros; apply GlobalTheory.BK.SliceLdiv.frobSlice_mem_ldivSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverse
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.TorsFree

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_le_one_of_mul {x g : K⟦X⟧} (hx : ∃ B : ℝ, ∀ n, ‖coeff n x‖ ≤ B)
    (hg : ∀ n, ‖coeff n g‖ ≤ 1) (hg1 : ∃ n, ‖coeff n g‖ = 1) (hgx : ∀ n, ‖coeff n (g * x)‖ ≤ 1) :
    ∀ n, ‖coeff n x‖ ≤ 1 := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hbdd : BddAbove (Set.range fun n => ‖coeff n x‖) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  set S := ⨆ n, ‖coeff n x‖ with hSdef
  have hxS : ∀ n, ‖coeff n x‖ ≤ S := fun n => le_ciSup hbdd n
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hxS 0)
  set d := Nat.find hg1 with hd
  have hgd : ‖coeff d g‖ = 1 := Nat.find_spec hg1
  have hlt : ∀ i < d, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne (hg i) (Nat.find_min hg1 hi)
  set θ : NNReal := (Finset.range d).sup fun i => ‖coeff i g‖₊ with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, Finset.sup_lt_iff (by simp)]
    intro i hi
    have := hlt i (Finset.mem_range.1 hi)
    rw [← NNReal.coe_lt_coe]; simpa using this
  have hθi : ∀ i < d, ‖coeff i g‖ ≤ (θ : ℝ) := fun i hi => by
    have : ‖coeff i g‖₊ ≤ θ := Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 hi)
    exact_mod_cast this
  have hθ0 : (0 : ℝ) ≤ θ := θ.2
  set Mx := max 1 ((θ : ℝ) * S) with hMx
  have hM0 : 0 ≤ Mx := le_trans zero_le_one (le_max_left _ _)
  have key : ∀ n, ‖coeff n x‖ ≤ Mx := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hmem : (d, n) ∈ Finset.HasAntidiagonal.antidiagonal (n + d) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact add_comm d n
    have hc := coeff_mul (n + d) g x
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x‖ ≤ Mx := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun p hp => ?_
      obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [norm_mul]
      rcases lt_trichotomy p.1 d with h | h | h
      · calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ θ * S :=
            mul_le_mul (hθi _ h) (hxS _) (norm_nonneg _) hθ0
          _ ≤ Mx := le_max_right _ _
      · exact absurd (Prod.ext h (by omega)) hne
      · have hj : p.2 < n := by omega
        calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ 1 * Mx :=
            mul_le_mul (hg _) (ih _ hj) (norm_nonneg _) zero_le_one
          _ = Mx := one_mul _
    have heq : coeff d g * coeff n x = coeff (n + d) (g * x) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x := by
      rw [hc]; ring
    have : ‖coeff n x‖ = ‖coeff d g * coeff n x‖ := by rw [norm_mul, hgd, one_mul]
    rw [this, heq, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hrest))
    exact (hgx _).trans (le_max_left _ _)
  have hSM : S ≤ Mx := ciSup_le key
  have hS1 : S ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : S ≤ θ * S := by
      rcases le_total 1 ((θ : ℝ) * S) with h3 | h3
      · rwa [hMx, max_eq_right h3] at hSM
      · rw [hMx, max_eq_left h3] at hSM; linarith
    have : (1 - (θ : ℝ)) * S ≤ 0 := by linarith
    have h4 : (0 : ℝ) < 1 - θ := by have := (NNReal.coe_lt_coe.2 hθ1); simp at this; linarith
    nlinarith
  exact fun n => (hxS n).trans hS1

end GlobalTheory.BK.TorsFree

namespace GlobalTheory.BK.Hom

open GlobalTheory.BK.TorsFree

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mem_imM_of_smul_mem (F : Hom P Q)
    (hg : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧
      Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧))
    (hl : ∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) {v : Vec K a κ} (hv : v ∈ Q.M) {f : K⟦X⟧}
    (hf0 : f ≠ 0) (hfv : f • v ∈ F.imM) : v ∈ F.imM := by
  unfold imM at hfv ⊢
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hfv
  rw [LinearMap.restrictScalars_apply] at hwv
  choose Y hYb hY using fun τ => (hl τ).2
  choose Y0 g hY0A hg1 hY0 using hg
  have hv' : ∀ τ i, v τ i ∈ A O K := fun τ => mem_tot.1 hv τ
  let x : Vec K a ι := fun τ => Y τ *ᵥ v τ
  have hfx : ∀ τ, f • x τ = w τ := by
    intro τ
    have h1 : f • v τ = F.mat τ *ᵥ w τ := by rw [← app_apply, hwv]; rfl
    change f • (Y τ *ᵥ v τ) = w τ
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, hY τ, one_smul, Matrix.one_mulVec]
  have hFx : F.app x = v := by
    funext τ i
    have h2 : f • F.app x τ = f • v τ := by
      rw [app_apply, ← Matrix.mulVec_smul, hfx τ, ← app_apply, hwv]; rfl
    exact mul_left_cancel₀ hf0 (congrFun h2 i)
  have hbx : ∀ τ i, ∃ B : ℝ, ∀ n, ‖coeff n (x τ i)‖ ≤ B := by
    intro τ i
    obtain ⟨c, hc⟩ := hYb τ
    refine ⟨max c 0, fun n => ?_⟩
    change ‖coeff n (∑ j, Y τ i j * v τ j)‖ ≤ max c 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun j _ => ?_
    have := norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (le_max_right c 0) zero_le_one (f := Y τ i j) (g := v τ j)
      (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _))
      (fun m => by rw [mul_one]; exact hv' τ j m) n
    rwa [mul_one, mul_one] at this
  have hgA : ∀ τ (i : ι), ∀ n, ‖coeff n (g τ)‖ ≤ 1 := by
    intro τ i
    have h5 : g τ = (Y0 τ * F.mat τ) i i := by rw [hY0 τ]; simp
    rw [h5]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (F.mem τ j i)
  have hgx : ∀ τ i, ∀ n, ‖coeff n (g τ * x τ i)‖ ≤ 1 := by
    intro τ i
    have h3 : g τ • x τ = Y0 τ *ᵥ v τ := by
      conv_rhs => rw [← hFx]
      rw [app_apply, Matrix.mulVec_mulVec, hY0 τ]
      first
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h4 : g τ * x τ i = (Y0 τ *ᵥ v τ) i := by rw [← h3]; rfl
    rw [h4]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (hv' τ j)
  have hxA : x ∈ P.M := mem_tot.2 fun τ i =>
    norm_coeff_le_one_of_mul (hbx τ i) (hgA τ i) (hg1 τ) (hgx τ i)
  exact Submodule.mem_map.2 ⟨x, hxA, by rw [LinearMap.restrictScalars_apply]; exact hFx⟩

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.coker_torsionFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hg hl v hv f _ hf0 hfv
  exact F.mem_imM_of_smul_mem hg hl hv hf0 hfv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM := by
  first | exact @GlobalTheory.BK.Hom.coker_torsionFree | exact GlobalTheory.BK.Hom.coker_torsionFree | (intros; apply GlobalTheory.BK.Hom.coker_torsionFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => GlobalTheory.T.coker_finite_length_of_primitive_divisor O K l e a ι κ P Q F hyp ?_, fun hyp => GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  first | exact @GlobalTheory.BK.Hom.finiteLength_coker_of_generic | exact GlobalTheory.BK.Hom.finiteLength_coker_of_generic | (intros; apply GlobalTheory.BK.Hom.finiteLength_coker_of_generic <;> assumption)
end
