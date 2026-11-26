module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExist
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastOfCoprime
open NumberField

namespace GlobalTheory.CoprimeUnitMultipliers

theorem exists_common_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : R → Prop) (h1 : U 1) (hm : ∀ a b, U a → U b → U (a * b))
    (M N : Submodule R V) (hM : M.FG) (h : ∀ x ∈ M, ∃ s, U s ∧ s • x ∈ N) :
    ∃ s, U s ∧ ∀ x ∈ M, s • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have key : ∀ T : Finset V, (∀ x ∈ T, ∃ s, U s ∧ s • x ∈ N) → ∃ s, U s ∧ ∀ x ∈ T, s • x ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1, by simp⟩
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, hm _ _ hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [mul_smul]; exact N.smul_mem _ hta
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (hsT x hx)
  obtain ⟨s, hs, hS⟩ := key S fun x hx => h x (Submodule.subset_span hx)
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem norm_natCast_of_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) :
    ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

theorem general {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p]) {N N' : ℕ}
    (L L₁ : Submodule (𝓞 E) (Fin N → E)) (L' L₁' : Submodule (𝓞 E) (Fin N' → E))
    (P : Matrix (Fin N) (Fin N) E) (P' : Matrix (Fin N') (Fin N') E) (hfg : L₁.FG)
    (s : ℕ) (hs : Nat.Coprime s p) (hL : ∀ x ∈ L₁, (s : E) • x ∈ L)
    (s' : ℕ) (hs' : Nat.Coprime s' p) (hL' : ∀ x ∈ L', (s' : E) • x ∈ L₁')
    (hdet : P.det ≠ 0)
    (hP : ∀ x ∈ L, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, t • x = ∑ a, c a • P.transpose a)
    (hP' : ∀ a, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ t • P'.transpose a ∈ L') :
    ∃ σ σ' : 𝓞 E, ‖ρ (σ : E)‖ = 1 ∧ ‖ρ (σ' : E)‖ = 1 ∧
      (∀ a : Fin N, ∀ x ∈ L₁, ∃ o : 𝓞 E, (o : E) = (σ : E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧
      ∀ b : Fin N', (fun i : Fin N' => (σ' : E) * P' i b) ∈ L₁' := by
  have h1 : ‖ρ ((1 : 𝓞 E) : E)‖ = 1 := by simp
  have hm : ∀ a b : 𝓞 E, ‖ρ (a : E)‖ = 1 → ‖ρ (b : E)‖ = 1 → ‖ρ ((a * b : 𝓞 E) : E)‖ = 1 := by
    intro a b ha hb
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb ⊢
    rw [map_mul, map_mul, norm_mul, ha, hb, one_mul]
  have hn : ∀ n : ℕ, Nat.Coprime n p → ‖ρ (((n : 𝓞 E)) : E)‖ = 1 := by
    intro n hn
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_of_coprime hn
  have hsm : ∀ {k : ℕ} (n : ℕ) (x : Fin k → E), (n : 𝓞 E) • x = (n : E) • x := by
    intro k n x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨σ, hσ, hσL⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm L₁
    (Submodule.span (𝓞 E) (Set.range P.transpose)) hfg (by
      intro x hx
      obtain ⟨t, ht, c, hc⟩ := hP _ (hL x hx)
      refine ⟨t * s, hm _ _ ht (hn s hs), ?_⟩
      rw [mul_smul, hsm, hc]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨σ', hσ', hσL'⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm
    (Submodule.span (𝓞 E) (Set.range P'.transpose)) L₁'
    (Submodule.fg_span (Set.finite_range _)) (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨t, ht, hta⟩ := hP' a
        refine ⟨s' * t, hm _ _ (hn s' hs') ht, ?_⟩
        rw [mul_smul, hsm]
        exact hL' _ hta
      | zero => exact ⟨1, h1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, htx⟩ := hx
        obtain ⟨u, hu, huy⟩ := hy
        refine ⟨t * u, hm _ _ ht hu, ?_⟩
        rw [smul_add]
        refine L₁'.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L₁'.smul_mem _ htx
        · rw [mul_smul]; exact L₁'.smul_mem _ huy
      | smul a x _ hx =>
        obtain ⟨t, ht, htx⟩ := hx
        exact ⟨t, ht, by rw [smul_comm]; exact L₁'.smul_mem _ htx⟩)
  refine ⟨σ, σ', hσ, hσ', fun a x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hσL x hx)
    refine ⟨c a, ?_⟩
    have e1 : P.mulVec (fun i => (c i : E)) = (σ : E) • x := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [RingOfIntegers.coe_eq_algebraMap σ, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : (fun i => (c i : E)) = (σ : E) • P⁻¹.mulVec x := by
      rw [← Matrix.mulVec_smul, ← e1, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
    have := congrFun e2 a
    simpa [Matrix.mulVec, dotProduct] using this
  · have := hσL' _ (Submodule.subset_span ⟨b, rfl⟩)
    convert this using 1
    funext i
    simp [Pi.smul_apply, Algebra.smul_def]

theorem exists_unit_multipliers : ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [inst : Fact (Nat.Prime p)] (ρ : (Formalism.BasicNotions.D7.host D).E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E)) (L' L₁' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)) (P : Matrix (Fin N) (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (P' : Matrix (Fin N') (Fin N') ((Formalism.BasicNotions.D7.host D).E)), Submodule.FG L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L P → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L' P' → ∃ (σ : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (σ' : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ' : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ (∀ (a : Fin N), ∀ x ∈ L₁, ∃ (o : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), (↑o : (Formalism.BasicNotions.D7.host D).E) = (↑σ : (Formalism.BasicNotions.D7.host D).E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧ ∀ (b : Fin N'), (fun (i : Fin N') ↦ (↑σ' : (Formalism.BasicNotions.D7.host D).E) * P' i b) ∈ L₁' := by
  intro D p inst ρ N N' L L₁ L' L₁' P P' hfg h h' hP hP'
  obtain ⟨s, hs, -, hL⟩ := h
  obtain ⟨s', hs', hL', -⟩ := h'
  exact general ρ L L₁ L' L₁' P P' hfg s hs hL s' hs' hL' hP.1 hP.2.2 hP'.2.1

end GlobalTheory.CoprimeUnitMultipliers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExist
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory

theorem locBasisW_clear_den : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first
  | exact @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | (apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExistStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_basis_unit_scalars_exist : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first | exact @GlobalTheory.locBasisW_clear_den | exact GlobalTheory.locBasisW_clear_den | (intros; apply GlobalTheory.locBasisW_clear_den <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem hOK_vecF : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  intro D X s L Λ hΛ hbij N N' A B p _ ι
  subst hΛ
  have hA : (0 : ℝ) < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L
  have hconj : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) := fun τ x =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) x
  have hL : Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area L.lattice.toAddSubgroup)⁻¹)
      (vecF D s A) (vecF D s B) =
      ∑ τ : X.Tau, TaylorLogMetric.embT D (s.iT τ) (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
    rw [GlobalTheory.FourthRootStd.area_eq]
    unfold Formalism.L2.Th1.GD.hOK Formalism.L2.AlgTh.hSc
    show ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i, ∑ j, _ = _
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hconj, vecF]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have h0 : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast
    field_simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]
  rw [← Equiv.sum_comp s.iT.symm]
  simp only [Equiv.apply_symm_apply]
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  rfl

end GlobalTheory.DFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlacesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualFrame_hermitian_form_trace_real_places : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  first | exact @GlobalTheory.DFrame.hOK_vecF | exact GlobalTheory.DFrame.hOK_vecF | (intros; apply GlobalTheory.DFrame.hOK_vecF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusD
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem pair_value_eq {D : D7} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]} {th : ℂ_[p]} (hth : th ≠ 0)
    {z₁ z₂ : Bool × HH D} {s₁ s₂ : D.host.E} (h₁ : ‖rho D ι z₁ s₁‖ = 1) (h₂ : ‖rho D ι z₂ s₂‖ = 1)
    (hc : ‖rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂‖ ≤ ‖th‖) {N : ℕ} {a b : Fin N} {X : D.host.E}
    (hX : X = s₁ * D.host.conj s₂ * (if a = b then 1 else 0)) :
    ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ (rho D ι z₁ s₁)⁻¹ * rho D ι z₁ X * (rho D ι z₂ s₂)⁻¹ =
      (if a = b then 1 else 0) + th * e := by
  have n₁ : rho D ι z₁ s₁ ≠ 0 := fun h => by simp [h] at h₁
  have n₂ : rho D ι z₂ s₂ ≠ 0 := fun h => by simp [h] at h₂
  by_cases hab : a = b
  · refine ⟨(rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂) / (rho D ι z₂ s₂ * th), ?_, ?_⟩
    · rw [norm_div, norm_mul, h₂, one_mul]
      exact div_le_one_of_le₀ hc (norm_nonneg _)
    · subst hX
      simp only [hab, if_true, mul_one, map_mul]
      field_simp
      ring
  · refine ⟨0, by simp, ?_⟩
    subst hX
    simp [hab]

theorem sum_pc_pc {D : D7} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ}
    (σ : Bool × HH D → 𝓞 D.host.E) (z₁ z₂ : Bool × HH D) (a₁ a₂ : Fin N)
    (F : (Bool × HH D) × Fin N → (Bool × HH D) × Fin N → ℂ_[p]) :
    ∑ l, ∑ l₂, pc D ι σ z₁ l a₁ * F l l₂ * pc D ι σ z₂ l₂ a₂ =
      (rho D ι z₁ (σ z₁ : D.host.E))⁻¹ * F (z₁, a₁) (z₂, a₂) * (rho D ι z₂ (σ z₂ : D.host.E))⁻¹ := by
  rw [Finset.sum_eq_single (z₁, a₁), Finset.sum_eq_single (z₂, a₂)]
  · simp [pc]
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem dual_local_bases_pair : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  intro D p _ ι th hth h2 N P σ hσ hP
  have key : ∀ t : HH D, (P (tauPl D (false, t)))⁻¹ = ((P (tauPl D (true, t))).map D.host.conj).transpose ∧
      (P (tauPl D (true, t)))⁻¹ * P (tauPl D (true, t)) = 1 := by
    intro t
    have h := hP t
    refine ⟨Matrix.inv_eq_left_inv h, ?_⟩
    apply Matrix.nonsing_inv_mul
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : (P (tauPl D (true, t))).det ≠ 0 := by
      intro h0
      have : ((P (tauPl D (true, t))).map D.host.conj).det = D.host.conj (P (tauPl D (true, t))).det := by
        simpa using (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) (P (tauPl D (true, t)))).symm
      rw [this, h0] at hd
      simp at hd
    exact isUnit_iff_ne_zero.mpr hd'
  refine ⟨fun t a₁ a₂ => ?_, fun t b₁ b₂ => ?_⟩
  · rw [sum_pc_pc ι σ (false, t) (true, t) a₁ a₂
      (fun l l₂ => rho D ι (false, t) (∑ j, rowL D P σ l j * D.host.conj (rowL D P σ l₂ j)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    obtain ⟨k₁, k₂⟩ := key t
    have e := congrFun (congrFun k₂ a₂) a₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e' := congrArg D.host.conj e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rowL, k₁, map_mul, map_sum, Matrix.transpose_apply, Matrix.map_apply] at e' ⊢
    have e'' : D.host.conj (if a₂ = a₁ then 1 else 0) = if a₁ = a₂ then 1 else 0 := by
      by_cases h : a₁ = a₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e', Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [sum_pc_pc ι σ (false, t) (true, t) b₁ b₂
      (fun l l₂ => rho D ι (false, t) (∑ i, colR D P σ l i * D.host.conj (colR D P σ l₂ i)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    have e := congrFun (congrFun (hP t) b₂) b₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e
    simp only [colR, map_mul]
    have e'' : (if b₂ = b₁ then (1 : D.host.E) else 0) = if b₁ = b₂ then 1 else 0 := by
      by_cases h : b₁ = b₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.DFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  first | exact @GlobalTheory.DFrame.dual_local_bases_pair | exact GlobalTheory.DFrame.dual_local_bases_pair | (intros; apply GlobalTheory.DFrame.dual_local_bases_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectors
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem frameM_coef_eq_chgB : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D p _ lm ι hι X s n N N' a r cκ c0 P P' σ σ' hσ hσ' hdet hsum i x
  unfold frameM
  have hJ : ∀ f : GlobalTheory.DFrame.JJ D n N N' → ℂ_[p], ∑ j, f j = ∑ α, ∑ l, ∑ l', f (α, l, l') := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hJ, Fintype.sum_sigma]
  simp only [GlobalTheory.DFrame.coef, GlobalTheory.DFrame.gc, GlobalTheory.DFrame.pc]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Finset.sum_eq_single x.1 (fun z _ hz => by simp [hz]) (by simp)]
  simp only [if_true, GlobalTheory.DFrame.vecF, GlobalTheory.DFrame.mat, GlobalTheory.DFrame.colR, GlobalTheory.DFrame.rowL, Matrix.of_apply, map_mul, RingEquiv.coe_toRingHom]
  have hsum' := hsum x.1 (s.iT i.1)
  simp only [hι] at hsum'
  have e : ∀ k, ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k)) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (cκ x.1 * r x.1 k * (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) =
      (cκ x.1 * (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) *
      (r x.1 k * ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k))) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hsum']
  by_cases h : s.iT i.1 = tauPl D x.1
  · rw [if_pos h, TaylorLogMetric.chgB, if_pos h.symm]
    simp only [h]
    set tp := tauPl D x.1 with htp
    have hm : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin m) D.host.E),
        Q.map (TaylorLogMetric.tauEmb D lm tp) = Q.map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      intro m Q; ext u v; simp [hι]
    have hinv : ((P tp).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)))⁻¹ =
        ((P tp)⁻¹).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x.1)), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hm, hm, hinv]
    clear e hsum' hJ hsum hm hinv
    have h1 := hσ x.1
    have h2 := hσ' x.1
    simp only [GlobalTheory.DFrame.rho, RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1 h2 ⊢
    simp only [Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← htp] at h1 h2 ⊢
    field_simp
    try ring
  · rw [if_neg h, TaylorLogMetric.chgB, if_neg (fun e => h e.symm)]
    simp

end GlobalTheory.DFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectorsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualFrame_columns_scaled_standard_vectors : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  first | exact @GlobalTheory.DFrame.frameM_coef_eq_chgB | exact GlobalTheory.DFrame.frameM_coef_eq_chgB | (intros; apply GlobalTheory.DFrame.frameM_coef_eq_chgB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRoot
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem GlobalTheory.DFrame.pairedBlock_diag : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  intro D p _ ι X s L sc n N N' a cκ r P P' σ σ' th hth hOK hvan hu hL hR t ab ab'
  obtain ⟨e, he, hE⟩ := Formalism.L2.Th1.GD.tripleTensorAlmostOrthonormal ℂ_[p] D.host.E (HH D) (GlobalTheory.DFrame.rho D ι)
    (Σ z : Bool × HH D, Fin (n z)) ((Bool × HH D) × Fin N) ((Bool × HH D) × Fin N')
    (fun α α' => a α.1 α.2 * D.host.conj (a α'.1 α'.2))
    (fun (l l₂ : (Bool × HH D) × Fin N) => ∑ j : Fin N, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j))
    (fun (q q₂ : (Bool × HH D) × Fin N') => ∑ i : Fin N', GlobalTheory.DFrame.colR D P' σ' q i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' q₂ i))
    N N' (GlobalTheory.DFrame.gc D cκ r) (GlobalTheory.DFrame.pc D ι σ) (GlobalTheory.DFrame.pc D ι σ') th
    (GlobalTheory.DFrame.uu D ι cκ r a) hth hvan (fun _ => rfl) hu hL hR t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← hE]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hOK]
  unfold GlobalTheory.DFrame.coef
  congr 2
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  simp only [GlobalTheory.DFrame.mat, Matrix.of_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRootStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualFrame_paired_blocks_diagonal_mod_root : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  first | exact @GlobalTheory.DFrame.pairedBlock_diag | exact GlobalTheory.DFrame.pairedBlock_diag | (intros; apply GlobalTheory.DFrame.pairedBlock_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem congr_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  intro D p _ hpd ι cE s δ hcE hδ hsδ hss hpair hK
  set th : ℂ_[p] := ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) with hth
  have hp0 : (0 : ℝ) < ‖(p : ℂ_[p])‖ := Formalism.L2.Th1.GD.norm_p_pos
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.GD.norm_p_lt_one
  have hsq : th ^ 2 = -(p : ℂ_[p]) := by
    rw [hth, ← map_pow, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ← hpd]
    simp
  have hnorm2 : ‖th‖ ^ 2 = ‖(p : ℂ_[p])‖ := by
    rw [← norm_pow, hsq, norm_neg]
  have hnth : ‖th‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm2, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : 1 < ‖th‖ ^ 2 := by nlinarith
    linarith
  · intro h
    rw [h, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  · intro t y
    have hp2 : p ≠ 2 := by
      have h := hypOdd_of_hostHyp D.host.hyp
      obtain ⟨-, -, h1, h2, h3⟩ := h
      omega
    have hI := Formalism.L2.Th1.GD.InertiaRam_proof p hp2 D.host.E s δ (rho D ι (false, t)) hδ hsδ hss
      (fun y hy => hK _ y hy)
    let y' : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv y
    have hy' : ((y' : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := rfl
    have h2 := hI.2.1 y'
    rw [hy'] at h2
    have htrue : rho D ι (true, t) (y : D.host.E) = rho D ι (false, t) (s (D.host.conj (y : D.host.E))) := by
      show ι (TaylorLogMetric.embT D (tauPl D (true, t)) (y : D.host.E)) = ι (TaylorLogMetric.embT D (tauPl D (false, t)) _)
      rw [hpair t, hcE]
    rw [htrue, hnth]
    exact h2

end GlobalTheory.DFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  first | exact @GlobalTheory.DFrame.congr_at_d | exact GlobalTheory.DFrame.congr_at_d | (intros; apply GlobalTheory.DFrame.congr_at_d <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtD
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.IntegralAtPlace

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  intro D p hpF hpd φ a ha
  obtain ⟨-, -, hqd, -, hd2⟩ := hypOdd_of_hostHyp D.host.hyp
  have hint : ∀ y : 𝓞 D.host.E, ‖φ (y : D.host.E)‖ ≤ 1 := fun y => by
    have h : IsIntegral ℤ (φ (y : D.host.E)) := by
      obtain ⟨f, hf, hx⟩ := RingOfIntegers.isIntegral_coe y
      refine ⟨f, hf, ?_⟩
      have := congrArg φ hx
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [RingHom.ext_int (φ.comp (algebraMap ℤ D.host.E)) (algebraMap ℤ ℂ_[p])] at this
    exact norm_le_one_of_isIntegral h
  let Q : Ideal (𝓞 D.host.E) :=
    { carrier := {y | ‖φ (y : D.host.E)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hmem : ∀ y, y ∈ Q ↔ ‖φ (y : D.host.E)‖ < 1 := fun y => Iff.rfl
  haveI hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
    · have h1 := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at h1
    · rw [hmem, show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * y from rfl, map_mul,
        norm_mul] at hxy
      by_contra hc
      push_neg at hc
      rw [hmem, hmem, not_lt, not_lt] at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  have hpQ : (p : 𝓞 D.host.E) ∈ Q := by
    rw [hmem]
    have e : ((p : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) := by simp
    rw [e, map_natCast]
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨z, hz, hden⟩ := GlobalTheory.AAUnitAway.exists_den D Q hpF.out (by rw [hpd]; exact UpperTheory.Small.d_not_mem D.host)
    (by rw [hpd]; exact hqd.symm) hpQ
  have hz1 : ‖φ (z : D.host.E)‖ = 1 := le_antisymm (hint z) (not_lt.1 ((hmem z).not.1 hz))
  obtain ⟨w, hw⟩ := hden a ha
  have := hint w
  rwa [hw, map_mul, norm_mul, hz1, mul_one] at this

end GlobalTheory.IntegralAtPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_le_one_host_base_module_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  first | exact @GlobalTheory.IntegralAtPlace.norm_le_one | exact GlobalTheory.IntegralAtPlace.norm_le_one | (intros; apply GlobalTheory.IntegralAtPlace.norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrime
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

open GlobalTheory.DFrame

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (D.host.conj x) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ x) :=
  D.host.conjE_apply (TaylorLogMetric.embT D τ) x

theorem tauEmb_eq_iota : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y) := by
  intro D p _ lm ι hι τ y
  have halg : TaylorLogMetric.embT D τ y ∈ TaylorLogMetric.Qbar :=
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  unfold TaylorLogMetric.tauEmb TaylorLogMetric.lamC
  rw [dite_eq_left halg, ← hι]

theorem outer_mem_YYl : ∀ (D : D7) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : D.host.E) (u : Fin N' → D.host.E) (w : Fin N → D.host.E), a ∈ D.host.AA0 → u ∈ L₁' → (∀ x ∈ L₁, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ j, w j * x j) → (Matrix.of fun i k => a * u i * w k : Matrix (Fin N') (Fin N) D.host.E) ∈ TaylorLogMetric.YYl D L₁ L₁' := by
  intro D N N' L₁ L₁' a u w ha hu hw
  refine Submodule.subset_span ⟨a, ha, Matrix.of fun i k => u i * w k, Submodule.subset_span ?_, ?_⟩
  · intro x hx
    obtain ⟨o, ho⟩ := hw x hx
    have : (Matrix.of fun i k => u i * w k).mulVec x = o • u := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply]
      rw [Algebra.smul_def]
      show _ = (o : D.host.E) * u i
      rw [ho, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]; exact L₁'.smul_mem o hu
  · ext i k; simp [Matrix.smul_apply, mul_assoc]

theorem smul_vecF_mem_laF : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (X : Fields) (s : Seam D X) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (M : Matrix (Fin N') (Fin N) D.host.E), M ∈ TaylorLogMetric.YYl D L₁ L₁' → ∀ ω ∈ TaylorLogMetric.lamOf D cc δ, ω • GlobalTheory.DFrame.vecF D s M ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
  intro D cc δ X s N N' L₁ L₁' M hM ω hω
  show (s.flatV N N') (ω • vecF D s M) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁'
  have : (s.flatV N N') (ω • vecF D s M) = ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) M := by
    funext τ i j
    simp [Seam.flatV, vecF, TaylorLogMetric.embV, TaylorLogMetric.tor0]
  rw [this]
  exact AddSubgroup.subset_closure ⟨ω, hω, M, hM, rfl⟩

theorem matH_act_adjoint : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (sc : ℝ) (e e' : 𝓞 D.host.E), (e' : D.host.E) = D.host.conj (e : D.host.E) → ∀ x y : DVar X.Tau N N' → ℂ, matH (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.act D s N N' e x) y = matH (Formalism.L2.AlgTh.hSc X.Tau N N' sc) x (GlobalTheory.DFrame.act D s N N' e' y) := by
  intro D X s N N' sc e e' he x y
  show (∑ i, ∑ j, act D s N N' e x i * Formalism.L2.AlgTh.hSc X.Tau N N' sc i j * (starRingEnd ℂ) (y j)) =
    ∑ i, ∑ j, x i * Formalism.L2.AlgTh.hSc X.Tau N N' sc i j * (starRingEnd ℂ) (act D s N N' e' y j)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.L2.AlgTh.hSc, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp only [act, LinearMap.coe_mk, AddHom.coe_mk, he, map_mul, embT_conj, Complex.conj_conj]
    ring
  · simp

theorem act_mem_laF : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (X : Fields) (s : Seam D X) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (e : 𝓞 D.host.E) (x : DVar X.Tau N N' → ℂ), x ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' → GlobalTheory.DFrame.act D s N N' e x ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
  intro D cc δ X s N N' L₁ L₁' e x hx
  show (s.flatV N N') (act D s N N' e x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁'
  have hx' : (s.flatV N N') x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := hx
  have key : ∀ w ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁',
      (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * w τ i j : TaylorLogMetric.VC D N N') ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨ω, hω, A, hA, rfl⟩ := hw
      have : (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) τ i j : TaylorLogMetric.VC D N N') =
          ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (e • A) := by
        funext τ i j
        simp only [TaylorLogMetric.embV, TaylorLogMetric.tor0, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
        rw [Algebra.smul_def, map_mul]
        show _ = ω * (TaylorLogMetric.embT D τ (e : D.host.E) * _)
        ring
      rw [this]
      exact AddSubgroup.subset_closure ⟨ω, hω, e • A, (TaylorLogMetric.YYl D L₁ L₁').smul_mem e hA, rfl⟩
    | zero =>
      have : (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (0 : TaylorLogMetric.VC D N N') τ i j : TaylorLogMetric.VC D N N') = 0 := by
        funext τ i j; simp
      rw [this]; exact (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').zero_mem
    | add w₁ w₂ _ _ h₁ h₂ =>
      have := (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').add_mem h₁ h₂
      convert this using 1
      funext τ i j; simp [mul_add]
    | neg w _ h =>
      have := (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').neg_mem h
      convert this using 1
      funext τ i j; simp
  have e1 : (s.flatV N N') (act D s N N' e x) = fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (s.flatV N N') x τ i j := by
    funext τ i j
    simp [Seam.flatV, act]
  rw [e1]; exact key _ hx'

end GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

namespace GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

open GlobalTheory.DFrame

theorem conj_conj' (D : D7) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  show D.host.φ₀ ((D.host.conj) ((D.host.conj) y)) = _
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj]

theorem sum_le_one {p : ℕ} [Fact p.Prime] {ι' : Type} (S : Finset ι') (f : ι' → ℂ_[p]) (h : ∀ i, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ S, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => h i)

theorem eigenframe_at_d : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt lm ι → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∃ u : HH D → ℂ_[p], (∀ t, ‖u t‖ ≤ 1) ∧ ∀ L₁ L₁', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p]) (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p])) (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)), Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D cc δ hcc hδ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hadm p _ lm hp ι hι cD hcD P P' κ hP hP' hκ
  obtain ⟨cE, sE, δE, hcE, hδ2, hcδ, hsδ, hss, hsc, hinj, hδc, hpair, hkur, hbij, hsg⟩ := GlobalTheory.T.inertiaInvolution_realPlacePairs D p hp ι
  have htau : ∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y) := tauEmb_eq_iota D p lm ι hι
  have htauR : ∀ z : Bool × HH D, TaylorLogMetric.tauEmb D lm (tauPl D z) = ⇑(rho D ι z) := fun z => funext fun y => htau _ y
  have heig := fun z : Bool × HH D => GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hcD p lm (tauPl D z)
  choose n r a hr ha hsum using heig
  set c0 : Bool × HH D → ℂ_[p] := fun z => TaylorLogMetric.lamC lm (cD (tauPl D z)) with hc0
  set cκ : Bool × HH D → ℂ_[p] := fun z => κ (tauPl D z) / c0 z with hcκdef
  have hcκ1 : ∀ z, ‖cκ z‖ ≤ 1 := by
    intro z
    simp only [hcκdef, norm_div]
    by_cases h0 : ‖c0 z‖ = 0
    · rw [h0, div_zero]; exact zero_le_one
    · exact div_le_one_of_le₀ (hκ _) (norm_nonneg _)
  have hcκ : ∀ z, cκ z * c0 z = κ (tauPl D z) := by
    intro z
    by_cases h0 : c0 z = 0
    · have h1 := hκ (tauPl D z)
      rw [show TaylorLogMetric.lamC lm (cD (tauPl D z)) = 0 from h0, norm_zero] at h1
      rw [h0, mul_zero]; exact (norm_le_zero_iff.1 h1).symm
    · simp only [hcκdef]; field_simp
  have hA0 : ∀ z (α α' : Σ z : Bool × HH D, Fin (n z)), ‖rho D ι z (a α.1 α.2 * D.host.conj (a α'.1 α'.2))‖ ≤ 1 := by
    intro z α α'
    rw [map_mul, norm_mul]
    refine mul_le_one₀ (GlobalTheory.T.padic_norm_le_one_host_base_module_at_d D p hp _ _ (ha _ _)) (norm_nonneg _) ?_
    exact GlobalTheory.T.padic_norm_le_one_host_base_module_at_d D p hp ((rho D ι z).comp (D.host.conj : D.host.E →+* D.host.E)) _ (ha _ _)
  have hgc : ∀ z α, ‖gc D cκ r z α‖ ≤ 1 := by
    intro z α
    unfold gc
    split_ifs
    · rw [norm_mul]; exact mul_le_one₀ (hcκ1 z) (norm_nonneg _) (hr _ _)
    · simp
  have hu : ∀ t, ‖uu D ι cκ r a t‖ ≤ 1 := by
    intro t
    unfold uu
    refine sum_le_one _ _ fun α => sum_le_one _ _ fun α' => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (hgc _ _) (norm_nonneg _) (hA0 _ _ _)) (norm_nonneg _) (hgc _ _)
  refine ⟨uu D ι cκ r a, hu, fun L₁ L₁' hadm₁ hL hL' => ?_⟩
  · have hPW : ∀ z, TaylorLogMetric.LocBasisW D (rho D ι z) L (P (tauPl D z)) := fun z => by
      have := hP.1 (tauPl D z); rwa [htauR] at this
    have hP'W : ∀ z, TaylorLogMetric.LocBasisW D (rho D ι z) L' (P' (tauPl D z)) := fun z => by
      have := hP'.1 (tauPl D z); rwa [htauR] at this
    have hden := fun z : Bool × HH D => GlobalTheory.T.local_basis_unit_scalars_exist D p (rho D ι z) N N' L L₁ L' L₁' (P (tauPl D z)) (P' (tauPl D z))
      hadm₁.2.2.1.1 hL hL' (hPW z) (hP'W z)
    choose σ σ' hσ hσ' hrow hcol using hden
    obtain ⟨⟨hth1, hth0⟩, hcong⟩ := GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d D p hp ι cE sE δE hcE hδ2 hsδ hss hpair hkur
    have hdualP : ∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1 := fun t => by
      have := hP.2.2 hp (tauPl D (false, t)); rwa [(hsg t).1] at this
    have hdualP' : ∀ t, ((P' (tauPl D (true, t))).map D.host.conj).transpose * P' (tauPl D (false, t)) = 1 := fun t => by
      have := hP'.2.2 hp (tauPl D (false, t)); rwa [(hsg t).1] at this
    have hσ0 : ∀ z, rho D ι z (σ z : D.host.E) ≠ 0 := fun z => norm_ne_zero_iff.1 (by rw [hσ z]; exact one_ne_zero)
    have hσ0' : ∀ z, rho D ι z (σ' z : D.host.E) ≠ 0 := fun z => norm_ne_zero_iff.1 (by rw [hσ' z]; exact one_ne_zero)
    have hframe := GlobalTheory.T.dualFrame_columns_scaled_standard_vectors D p lm ι htau X s n N N' a r cκ c0 P P' σ σ' hσ0 hσ0' (fun z => (hPW z).1) hsum
    have hfr : ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'),
        frameM (ι : ℂ →+* ℂ_[p]) (fun j => vecF D s (mat D a P P' σ σ' j)) (coef D ι cκ r σ σ') i x =
          κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
      intro i x
      rw [hframe]
      by_cases h : tauPl D x.1 = s.iT i.1
      · rw [hcκ, h]
      · simp [TaylorLogMetric.chgB, h]
    have hmem : ∀ j : JJ D n N N', mat D a P P' σ σ' j ∈ TaylorLogMetric.YYl D L₁ L₁' := by
      intro j
      refine outer_mem_YYl D N N' L₁ L₁' (a j.1.1 j.1.2) (colR D P' σ' j.2.2) (rowL D P σ j.2.1) (ha _ _) (hcol _ _) ?_
      intro x hx
      obtain ⟨o, ho⟩ := hrow j.2.1.1 j.2.1.2 x hx
      refine ⟨o, ?_⟩
      rw [ho, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [rowL]; ring
    have hsep : ∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)),
        ∑ α, gc D cκ r τ α * rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0 := by
      intro τ ρ hne α'
      rw [Fintype.sum_sigma]
      have h1 : ∀ z (k : Fin (n z)), gc D cκ r τ ⟨z, k⟩ * rho D ι ρ (a z k * D.host.conj (a α'.1 α'.2)) =
          if z = τ then cκ τ * rho D ι ρ (D.host.conj (a α'.1 α'.2)) * (r z k * rho D ι ρ (a z k)) else 0 := by
        intro z k
        unfold gc
        split_ifs with hz
        · subst hz; rw [map_mul]; ring
        · rw [zero_mul]
      simp only [h1]
      rw [Finset.sum_eq_single τ]
      · simp only [if_true, ← Finset.mul_sum]
        have := hsum τ (tauPl D ρ)
        rw [htauR] at this
        rw [this, if_neg (fun h => hne (hbij.1 h)), mul_zero]
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ τ) h
    have hd1 := (GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d D p ι _ hth0 hcong P σ hσ hdualP).1
    have hd2 := (GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d D p ι _ hth0 hcong P' σ' hσ' hdualP').2
    refine ⟨JJ D n N N', inferInstance, fun j => vecF D s (mat D a P P' σ σ' j), coef D ι cκ r σ σ', cE, sE, δE,
      rho D ι, act D s N N', ⟨hδ2, hcδ, hsδ, fun y => by rw [hcE (cE y), hcE y, conj_conj'], hss, hsc, ?_,
      fun τ ρ => by simp only [rho, RingHom.coe_comp, Function.comp_apply, hδc (tauPl D τ) (tauPl D ρ)],
      fun t y => by simp only [rho, RingHom.coe_comp, Function.comp_apply, hpair], fun τ y hy => hkur _ y hy,
      fun e e' he x y => matH_act_adjoint D X s N N' _ e e' (by rw [he, hcE]) x y,
      fun e x hx => act_mem_laF D cc δ X s N N' L₁ L₁' e x hx,
      fun j ω hω => smul_vecF_mem_laF D cc δ X s N N' L₁ L₁' _ (hmem j) ω (by rw [← hlat]; exact hω), ?_, ?_,
      GlobalTheory.T.dualFrame_paired_blocks_diagonal_mod_root D p ι X s _ _ n N N' a cκ r P P' σ σ' _ hth1 (fun A B => GlobalTheory.T.dualFrame_hermitian_form_trace_real_places D X s _ _ hlat hbij N N' A B p ι) hsep
        hu hd1 hd2⟩, hfr⟩
    · intro z z' h
      apply hinj
      refine RingHom.ext fun y => ι.injective ?_
      have := congrArg (fun f : D.host.E →+* ℂ_[p] => f y) h
      simpa [rho] using this
    · intro j x
      unfold coef GlobalTheory.DFrame.pc
      rw [norm_mul, norm_mul]
      refine mul_le_one₀ (mul_le_one₀ (hgc _ _) (norm_nonneg _) ?_) (norm_nonneg _) ?_
      · split_ifs
        · rw [norm_inv, hσ]; simp
        · simp
      · split_ifs
        · rw [norm_inv, hσ']; simp
        · simp
    · intro e x i
      have hact : ∀ i' : DVar X.Tau N N', (act D s N N' e) (Pi.single i' 1) i =
          if i = i' then TaylorLogMetric.embT D (s.iT i.1) (e : D.host.E) else 0 := by
        intro i'
        simp only [act, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, mul_ite, mul_one, mul_zero]
      simp only [hfr, Formalism.L2.Th1.GD.mapVec, hact]
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
      by_cases h : tauPl D x.1 = s.iT i.1
      · rw [← h]; rfl
      · simp [TaylorLogMetric.chgB, h]

end GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrimeStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLocalBases_eigenframe_at_ramifiedPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt lm ι → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∃ u : HH D → ℂ_[p], (∀ t, ‖u t‖ ≤ 1) ∧ ∀ L₁ L₁', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p]) (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p])) (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)), Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  first | exact @GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | exact GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | (intros; apply GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d <;> assumption)
end
