module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShifted
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShifted
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.OneSide

section Abstract

variable {n : ℕ} {Y S M : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup M] [Module ℂ M]

theorem exists_shift (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (hA : Formalism.REAL.GlRel A) (hB : Formalism.REAL.GlRel B) (L : Y → M →ₗ[ℂ] S) (lam : Fin n → Fin n → ℂ)
    (h : ∀ i j y f, A i j (L y f) = L y (B i j f + lam i j • f)) :
    ∃ c : ℂ, ∀ i j y f, A i j (L y f) =
      L y ((B i j + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) f) := by
  by_cases h0 : ∀ y f, L y f = 0
  · exact ⟨0, fun i j y f => by rw [h0, h0, map_zero]⟩
  push Not at h0
  obtain ⟨y, f, h0⟩ := h0
  have key : ∀ i j k l, (if j = k then lam i l else 0) = (if l = i then lam k j else 0) := by
    intro i j k l
    have h1 : (A i j * A k l - A k l * A i j) (L y f) = L y ((B i j * B k l - B k l * B i j) f) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, h, map_add (f := _), map_smul, map_sub, smul_add]
      module
    rw [hA, hB] at h1
    have h2 : ((if j = k then lam i l else 0) - (if l = i then lam k j else 0)) • L y f = 0 := by
      rw [sub_smul]
      split_ifs at h1 ⊢ <;>
        simp only [LinearMap.sub_apply, LinearMap.zero_apply, h, map_add (f := _), map_smul, map_sub, map_zero,
          zero_smul] at h1 ⊢ <;>
        linear_combination (norm := module) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0)
  rcases n with _ | n
  · exact ⟨0, fun i => i.elim0⟩
  refine ⟨lam 0 0, fun i j y f => ?_⟩
  rw [h]
  by_cases c : i = j
  · subst c
    have := key i 0 0 i
    simp only [if_true] at this
    simp [this]
  · have := key i i i j
    simp only [if_true, if_neg (Ne.symm c)] at this
    simp [this, c]

theorem prod_intertwine (L : M →ₗ[ℂ] S) : ∀ (k : ℕ) (a : Fin k → Module.End ℂ S) (b : Fin k → Module.End ℂ M),
    (∀ i f, a i (L f) = L (b i f)) → ∀ f, (List.ofFn a).prod (L f) = L ((List.ofFn b).prod f)
  | 0, _, _, _, f => by simp
  | k + 1, a, b, e, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      prod_intertwine L k _ _ fun i => e i.succ, e]

theorem gelfA_intertwine (L : M →ₗ[ℂ] S) (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (h : ∀ i j f, A i j (L f) = L (B i j f)) (k : ℕ) (f : M) :
    GlobalTheory.SmoothForms.gelfA A k (L f) = L (GlobalTheory.SmoothForms.gelfA B k f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_intertwine L _ _ _ (fun _ => h _ _) f

end Abstract

theorem gelf_kernel : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  intro D θ hθ V Y M _ _ κ hκ τ Q hQ hd
  choose lam hlam using hd
  have hR : ∀ X (hX : X ∈ lieAt V τ) f y, Rder θ V τ X (κ f y) = κ (Q X f + lam X hX • f) y :=
    fun X hX f y => funext fun g => (hlam X hX f y g).deriv
  have hC : ∀ Z, ∃ l : ℂ, ∀ f y, RderC θ V τ Z (κ f y) = κ (Q Z f + l • f) y := by
    intro Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    refine ⟨lam _ h1 + Complex.I * lam _ h2, fun f y => ?_⟩
    rw [RderC, hR _ h1, hR _ h2]
    have e := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    generalize lam _ h1 = a
    generalize lam _ h2 = b
    generalize (1 / 2 : ℂ) • (Z + conjAt V τ Z) = P at e ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) = P' at e ⊢
    rw [← e]
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply]
    module
  choose l hl using hC
  let L : Y → M →ₗ[ℂ] SmFun θ V := fun y =>
    LinearMap.codRestrict (SmFun θ V) ((LinearMap.proj y).comp κ) fun f => hκ f y
  obtain ⟨c, hc⟩ := exists_shift _ _ (glRel_derEnd hθ V τ) hQ L (fun i j => l (Matrix.single i j 1))
    fun i j y f => Subtype.ext (hl _ f y)
  refine ⟨c, fun k f y => ?_⟩
  have := gelfA_intertwine (L y) _ (fun i j => Q (Matrix.single i j 1) +
    if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) (fun i j => hc i j y) k f
  exact (GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (L y f)).trans (congrArg Subtype.val this)

end GlobalTheory.Mem.Lift.OneSide

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShiftedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  first | exact @GlobalTheory.Mem.Lift.OneSide.gelf_kernel | exact GlobalTheory.Mem.Lift.OneSide.gelf_kernel | (intros; apply GlobalTheory.Mem.Lift.OneSide.gelf_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayForms
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CuspDeriv

theorem continuous_deriv_of_bounded {G : Type} [TopologicalSpace G] {f f₁ f₂ : G → ℝ → ℂ}
    (hf : ∀ t, Continuous fun g => f g t) (h₁ : ∀ g t, HasDerivAt (f g) (f₁ g t) t)
    (h₂ : ∀ g t, HasDerivAt (f₁ g) (f₂ g t) t) {B : ℝ} (hB : ∀ g t, ‖f₂ g t‖ ≤ B) : Continuous fun g => f₁ g 0 := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB g₀ 0)
  obtain ⟨h, h0, hh⟩ : ∃ h : ℝ, 0 < h ∧ (B + B) * h < ε :=
    ⟨ε / (B + B + 1), by positivity, by rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith⟩
  have hc : Continuous fun g => ‖f g h - f g₀ h‖ + ‖f g 0 - f g₀ 0‖ + (B + B) * h * h :=
    ((((hf h).sub continuous_const).norm).add ((hf 0).sub continuous_const).norm).add continuous_const
  have := (hc.tendsto g₀).eventually_lt_const (u := h * ε) (by simp only [sub_self, norm_zero, zero_add]; nlinarith)
  filter_upwards [this] with g hg
  have key := mul_norm_deriv_le (f := fun t => f g t - f g₀ t) (f₁ := fun t => f₁ g t - f₁ g₀ t)
    (f₂ := fun t => f₂ g t - f₂ g₀ t) (fun t => (h₁ g t).sub (h₁ g₀ t)) (fun t => (h₂ g t).sub (h₂ g₀ t)) h0.le
    (B := B + B) fun t _ => (norm_sub_le _ _).trans (add_le_add (hB g t) (hB g₀ t))
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (key.trans_lt hg) h0.le

theorem cuspForm_mem_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F,
    IsCuspForm θ V F → F ∈ Decay θ V := by
  intro hP D θ hθ V F ⟨ha, hc⟩
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hd : ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) → IsRapidDecay θ V (word θ V l F) :=
    isRapidDecay_foldr_Rder hP hθ ha.toIsAutFun ha.smooth ha.growth hc
  refine ⟨ha.smooth, ha.left, fun l hl => ⟨?_, hd l hl⟩⟩
  induction l with
  | nil => exact ha.cont
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (by simp [hq])
    have hs : word θ V l F ∈ SmFun θ V :=
      (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
        fun q hq => linOnSm_Rder (hl' q hq)).mem F ha.smooth
    obtain ⟨B, hB⟩ := (hd (p :: p :: l) (List.forall_mem_cons.2 ⟨hp, hl⟩)).bounded
    have := continuous_deriv_of_bounded (f := fun g t => word θ V l F (g * oneP θ V p.1 p.2 t))
      (fun t => (ih hl').comp (continuous_mul_const _)) (hasDerivAt_oneP hθ hp (hasDerivAt_Rder hs hp))
      (hasDerivAt_oneP hθ hp (hasDerivAt_Rder (Rder_mem hs hp) hp)) fun g t => hB _
    simp only [oneP_zero hθ, mul_one] at this
    exact this

end GlobalTheory.Mem.CuspDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F, IsCuspForm θ V F → F ∈ Decay θ V := by
  first | exact @GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | exact GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | (intros; apply GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Lift

theorem IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by
  obtain ⟨hx, hd, hc⟩ := h
  have e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l') := by
    noncomm_ring
  have e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l) := by
    noncomm_ring
  rw [e1, e2, hc, hc, hx k' k, hd l' l]
  split_ifs <;> simp

theorem glRel_of_isCCR (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]

end GlobalTheory.Mem.Lift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelationsStatement
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEq
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Capelli

variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}

def trAlg (M : Matrix (Fin n) (Fin n) A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range fun k : ℕ => (M ^ (k + 1)).trace)

theorem trace_pow_mem (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : (M ^ k).trace ∈ trAlg M := by
  cases k with
  | zero => simpa using natCast_mem (trAlg M) n
  | succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩

theorem trAlg_le {M : Matrix (Fin n) (Fin n) A} {S : Subalgebra ℂ A} (h : ∀ k, (M ^ (k + 1)).trace ∈ S) :
    trAlg M ≤ S := Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)

theorem trAlg_shift_le (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by
  have key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M := by
    intro k
    induction k with
    | zero => intro j; simpa using trace_pow_mem M j
    | succ k ih =>
      intro j
      rw [pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]
      exact add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)
  exact trAlg_le fun k => by simpa using key (k + 1) 0

theorem trAlg_shift (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by
  refine le_antisymm (trAlg_shift_le M s c) ?_
  have h := trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))
  rwa [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right] at h

theorem adjoin_gelfA (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by
  rw [trAlg]
  congr 2
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  rfl

section CCR

variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_one (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]
  · by_cases h : i = l <;> simp [h]

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_pow (p : ℕ) (a : Fin m) (l i j : Fin n) :
    D a l * ((X * D) ^ p) i j = ((X * D) ^ p) i j * D a l
      + ∑ r ∈ Finset.range p, ((X * D) ^ r) i l * (D * (X * D) ^ (p - (r + 1))) a j := by
  induction p generalizing i with
  | zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ p ih =>
    have h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) =
        (X * D) i k * ((X * D) ^ p) k j * D a l
        + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j
          + if i = l then D a k * ((X * D) ^ p) k j else 0) := fun k => by
      rw [← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]
      simp only [mul_assoc, ite_mul, zero_mul]
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']
    simp only [h1, Finset.sum_add_distrib]
    congr 2
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]
    · by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]

omit [Algebra ℂ A] in
include hdd hdx in
theorem trace_rec (p : ℕ) :
    ((D * X) ^ (p + 1)).trace = ((X * D) ^ (p + 1)).trace + (m : A) * ((X * D) ^ p).trace
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * ((D * X) ^ (p - (r + 1) + 1)).trace := by
  have hN : ∀ q : ℕ, (D * X) ^ (q + 1) = D * (X * D) ^ q * X := fun q => by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  have hY : ∀ a j, (D * (X * D) ^ p) a j = ∑ u, ((X * D) ^ p) u j * D a u
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * (D * (X * D) ^ (p - (r + 1))) a j := fun a j => by
    rw [Matrix.mul_apply]
    simp only [comm_pow X D hdd hdx, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [trace, diag_apply, Finset.sum_mul]
  have hT : ∀ q : ℕ, ((D * X) ^ (q + 1)).trace = ∑ a, ∑ j, (D * (X * D) ^ q) a j * X j a := fun q => by
    rw [hN]; rfl
  have hE : ∀ u j, ∑ a, D a u * X j a = (X * D) j u + if j = u then (m : A) else 0 := fun u j => by
    simp only [hdx, Finset.sum_add_distrib, Matrix.mul_apply]
    by_cases h : j = u <;> simp [h]
  simp only [hT]
  simp only [hY, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  · rw [Finset.sum_comm]
    have : ∀ j, ∑ a, ∑ u, ((X * D) ^ p) u j * (D a u * X j a)
        = ∑ u, ((X * D) ^ p) u j * (X * D) j u + (m : A) * ((X * D) ^ p) j j := fun j => by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hE, mul_add, Finset.sum_add_distrib]
      simp [Nat.cast_comm]
    simp only [this, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, pow_succ]; rfl
    · simp only [trace, diag_apply, Finset.mul_sum]
  · rw [Finset.sum_comm (s := Finset.range p)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

include hdd hdx in
theorem trAlg_mul_comm : trAlg (X * D) = trAlg (D * X) := by
  apply le_antisymm
  · have key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X) := fun p => by
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        cases p with
        | zero => simpa using natCast_mem (trAlg (D * X)) n
        | succ p =>
          have h := trace_rec X D hdd hdx p
          rw [add_assoc, ← sub_eq_iff_eq_add] at h
          rw [← h]
          refine sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega)))
            (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))
          have := Finset.mem_range.1 hr
          omega
    exact trAlg_le fun k => key _
  · refine trAlg_le fun p => ?_
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rw [trace_rec X D hdd hdx p]
      refine add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _)))
        (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))
      have := Finset.mem_range.1 hr
      omega

end CCR

theorem adjoin_gelfA_dual_pair : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  intro A _ _ n m x d h c c'
  obtain ⟨-, hdd, hdx⟩ := h
  let X : Matrix (Fin n) (Fin m) A := Matrix.of fun i a => x (i, a)
  let D : Matrix (Fin m) (Fin n) A := Matrix.of fun a i => d (i, a)
  have hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0 := fun a l i b => by
    have := hdx (i, b) (l, a)
    rw [sub_eq_iff_eq_add'] at this
    simpa [X, D] using this
  have h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)
      = (1 : ℂ) • (X * D) + c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]
  have h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)
      = (-1 : ℂ) • (D * X) + (c' + n) • 1 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]
    by_cases hab : a = b
    · subst hab
      simp [X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]
      abel
    · simp [X, D, hab, Ne.symm hab]
  rw [adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]
  exact trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'

end GlobalTheory.Mem.Capelli
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEqStatement
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  first | exact @GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | exact GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair | (intros; apply GlobalTheory.Mem.Capelli.adjoin_gelfA_dual_pair <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D}

theorem IsKerSys.lift (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {V W : HSp D} {M : Type} [AddCommGroup M]
    [Module ℂ M] {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ} (hF : IsCuspForm θ V F) (f : M) :
    (∀ h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ IsAutFunSm θ W fun h => ∫ g in 𝓕, κ f g h * F g ∂μ := by
  have hD := GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms hP D θ hθ V F hF
  obtain ⟨h1, h2, ⟨N, h3⟩, h4⟩ := GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hD
  let L : M → GA D W → ℂ := fun f h => ∫ g in 𝓕, κ f g h * F g ∂μ
  have hd : ∀ f τ, ∀ X ∈ lieAt W τ, ∃ f', ∀ h,
      HasDerivAt (fun t : ℝ => L f (h * oneP θ W τ X t)) (L f' h) 0 := fun f τ X hX =>
    (hκ.derW τ X hX f).imp fun f' e => h4 τ X hX f f' e
  refine ⟨h1 f, ⟨fun γ hγ h => ?_, ?_, h2 f⟩, ?_, GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite D θ hθ V W M κ hκ μ 𝓕 hq F hD hF.1.zfin f, ?_⟩
  · have := fun g => hκ.left f 1 (one_mem _) γ hγ g h
    simp only [one_mul] at this
    simp only [this]
  · obtain ⟨U, U', -, hU', e⟩ := hκ.level f
    refine ⟨U', hU', fun k a b h => ?_⟩
    have := fun g => e 1 (one_mem _) (one_mem _) k a b g h
    simp only [mul_one] at this
    simp only [this]
  · refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ W (Set.range L) ?_ ?_ _ ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact h2 f
    · rintro _ ⟨f, rfl⟩ τ X hX
      obtain ⟨f', e⟩ := hd f τ X hX
      exact ⟨_, ⟨f', rfl⟩, e⟩
  · obtain ⟨K, hK⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ W
    refine ⟨K * N, fun l hl x => ?_⟩
    have hw : ∃ f', l.foldr (fun p φ => Rder θ W p.1 p.2 φ) (L f) = L f' := by
      induction l with
      | nil => exact ⟨f, rfl⟩
      | cons p l ih =>
        obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨f'', e'⟩ := hd f' p.1 p.2 (hl p List.mem_cons_self)
        exact ⟨f'', by rw [List.foldr_cons, e]; exact funext fun h => (e' h).deriv⟩
    obtain ⟨f', e⟩ := hw
    obtain ⟨C, hC⟩ := h3 f'
    obtain ⟨C', hC'⟩ := hK x
    refine ⟨|C| * C' ^ N, fun g hg => ?_⟩
    rw [show (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) = L f from rfl, e]
    refine (hC _).trans ?_
    rw [pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)

def matLin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun X := ∑ i, ∑ j, X i j • E i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

theorem matLin_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (i j : Fin n) :
    matLin E (Matrix.single i j 1) = E i j := by
  simp [matLin, Matrix.single, ite_and]

theorem isKerSys_thKer (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : GlobalTheory.Ker.IsWeak ψ S T om) (hc : OmCont ψ S T om) :
    IsKerSys θ S T (thKer ψ S T om) := by
  have cont : ∀ f, Continuous fun p : GA D S × GA D T => thKer ψ S T om f p.1 p.2 := fun f => hc f.1 f.2 0
  have left : ∀ f, ∀ γ ∈ GQ S, ∀ δ ∈ GQ T, ∀ g h, thKer ψ S T om f (γ * g) (δ * h) = thKer ψ S T om f g h := by
    intro f γ hγ δ hδ g h
    have e : om (γ * g, δ * h) = om (γ, δ) * om (g, h) := by rw [← map_mul]; rfl
    change om (γ * g, δ * h) f.1 0 = om (g, h) f.1 0
    rw [e]
    exact hw.om_aut γ hγ δ hδ _ (hw.om_pres _ _ f.2)
  have level : ∀ f, ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧
      IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → ∀ g h,
        thKer ψ S T om f (g * k) (h * k') = thKer ψ S T om f g h := by
    intro f
    obtain ⟨U, U', a, b, e⟩ := GlobalTheory.T.exists_open_level_fixing_theta_function D ψ hψ S T om hw hc f.1 f.2
    refine ⟨U, U', a, b, fun k h1 h2 k' h3 h4 g h => ?_⟩
    have e' : om (g * k, h * k') = om (g, h) * om (k, k') := by rw [← map_mul]; rfl
    change om (g * k, h * k') f.1 0 = om (g, h) f.1 0
    rw [e', mul_apply_eq_comp, e k h1 h2 k' h3 h4]
  obtain ⟨x, d, hx⟩ := GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra D ψ hψ S T om hw hc θ hθ
  have derV : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ X t) h) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.2 X hX).elim fun _ e => ⟨_, e f⟩
  have derW : ∀ τ, ∀ X ∈ lieAt T τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.1 X hX).elim fun _ e => ⟨_, e f⟩
  refine ⟨cont, left, level, ?_, derV, derW, fun τ => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints D ψ hψ S T om hw θ hθ
    obtain ⟨N', hN'⟩ := GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair D θ hθ S T N
    exact ⟨N', fun f => hN' _ (left f) (level f) fun x y =>
      (hN f.1 f.2 x y).imp fun C e a ha b hb => e a ha b hb 0⟩
  · have sT : ∀ f g, thKer ψ S T om f g ∈ SmFun θ T := fun f g => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ T (Set.range fun f => thKer ψ S T om f g) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_right g)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derW τ X hX f
        exact ⟨_, ⟨f', rfl⟩, e g⟩
    have sS : ∀ f h, swapKer (thKer ψ S T om) f h ∈ SmFun θ S := fun f h => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ S (Set.range fun f => swapKer (thKer ψ S T om) f h) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_left h)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derV τ X hX f
        exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.T.glRel_of_canonicalCommutationRelations _ _ _ (x τ) (d τ) (hx τ).1
    obtain ⟨c, e1⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ T _ _ (thKer ψ S T om) sT τ (matLin fun i j => ∑ a, x τ (i, a) * d τ (j, a))
      (by simpa only [matLin_single] using g1) (hx τ).2.1
    obtain ⟨c', e2⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ S _ _ (swapKer (thKer ψ S T om)) sS τ
      (matLin fun a b => -∑ i, x τ (i, b) * d τ (i, a)) (by simpa only [matLin_single] using g2)
      fun Y hY => ((hx τ).2.2 Y hY).imp fun _ e f h g => e f g h
    simp only [matLin_single] at e1 e2
    exact ⟨_, _, e2, e1, (GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq _ _ _ (x τ) (d τ) (hx τ).1 c c').symm⟩

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem exists_thKer {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) {V W : HSp D}
    {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank) :
    ∃ om, GlobalTheory.Ker.IsWeak ψ V W om ∧ OmCont ψ V W om ∧
      ∀ Φ, ∃ f, ∀ g h, Wf.ker V W χ χ' Φ g h = thKer ψ V W om f g h := by
  obtain ⟨om, H, e⟩ := GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta D ψ hψ V W χ χ' _ ha hr (Wf.core.weil V W χ χ' ha)
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine ⟨om, GlobalTheory.Ker.isWeak_of_datum H, H.om_cont, fun Φ => ⟨⟨fun x => Φ.1 (toTWsmall V W x), ?_⟩, fun g h => ?_⟩⟩
  · have := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
    simp only [hE] at this
    exact this
  · have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm

theorem liftAut : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAut D := by
  intro hP D θ hθ ψ hψ Wf V W χ χ' ha μ 𝓕 hq Φ F hF
  rcases lt_or_gt_of_ne ha.1 with hr | hr
  · obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha hr
    obtain ⟨f, e⟩ := e Φ
    simp only [e]
    exact (isKerSys_thKer hθ hψ hw hc).lift hP hθ hq hF f
  · have ha' : admitted W V χ' χ := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
    obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha' hr
    have hΦ := (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 ha.1 (mem_ThS.1 Φ.2)
    obtain ⟨f, e⟩ := e ⟨_, mem_ThS.2 hΦ⟩
    have e' : ∀ g h, Wf.ker V W χ χ' Φ g h = swapKer (thKer ψ W V om) f g h := fun g h =>
      (Wf.om_swap V W χ χ' ha g h Φ ⟨_, mem_ThS.2 hΦ⟩ (fun _ => rfl) 0).symm.trans (e h g)
    simp only [e']
    have hk := isKerSys_thKer hθ hψ hw hc
    have hs : IsKerSys θ V W (swapKer (thKer ψ W V om)) := by
      refine ⟨fun f => (hk.cont f).comp continuous_swap, fun f γ hγ δ hδ g g' =>
        hk.left f δ hδ γ hγ g' g, ?_, ?_, ?_, ?_, ?_⟩
      · intro f
        obtain ⟨U, U', hU, hU', hk'⟩ := hk.level f
        exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' =>
          hk' k' hk1' hk2' k hk1 hk2 g' g⟩
      · obtain ⟨N, hN⟩ := hk.growth
        refine ⟨N, fun f => ?_⟩
        obtain ⟨C, hC⟩ := hN f
        refine ⟨C, fun g g' => ?_⟩
        have hb := hC g' g
        rw [mul_comm (height θ W g' : ℝ)] at hb
        exact hb
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derW τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derV τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ
        obtain ⟨a, b, ha, hb, hab⟩ := hk.cap τ
        exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩
    exact hs.lift hP hθ hq hF f

end GlobalTheory.Mem.Lift

end
