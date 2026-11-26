module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckCasSplit

open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem hpk_row (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by
  have hi := i.2
  by_cases h : r ≤ i.1 ∧ i.1 ≤ r + k
  · refine ⟨i, if i.1 = r + k then -1 else 1, by split_ifs <;> simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · refine ⟨⟨2 * r + k - i.1, by omega⟩, 1, by simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  obtain ⟨j₀, s, hs, h1, h2⟩ := hpk_row k r i
  simp only [Matrix.mul_apply, h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, hs]
  · simp [hij, Ne.symm hij]

theorem flip_facts {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by
  constructor
  · simp only [Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem reH_lie (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  simp only [reH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h3, h4]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  abel_nf
  simp

theorem imH_lie (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  simp only [imH, sub_neg_eq_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h3, h4]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul, add_comm (Yᴴ * _), neg_add_cancel]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem diff_entry {F : FRep k r} (hF : F.OK) {X : Mx k r} (hX : InLieHpk k r X) (c d : F.ι) :
    HasDerivAt (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) (F.dR X c d) 0 := by
  have h1 : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) 1 := by simp [PI.UpqRep.inUH]
  obtain ⟨U, G, hU, h1U, hG, hfG⟩ := hF.smooth c d 1 h1
  have hd : HasDerivAt (fun t => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex 1 X
  exact (hasDerivAt_local (A := {g | PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g}) (f := fun g => F.ρ g c d)
    (ex_mem_of_lie hX) (ex_zero X) hd hU h1U hG hfG).differentiableAt.hasDerivAt

theorem dR_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) {X : Mx k r} (hX : InLieHpk k r X) :
    (F.tens F').dR X = F.dR X ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dR X := by
  ext ⟨c, c'⟩ ⟨d, d'⟩
  have h := ((diff_entry hF hX c d).mul (diff_entry hF' hX c' d')).deriv
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hF.one, hF'.one] at h
  exact h

theorem dC_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) (Y : Mx k r) :
    (F.tens F').dC Y = F.dC Y ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC Y := by
  simp only [FRep.dC, dR_tens hF hF' (reH_lie Y), dR_tens hF hF' (imH_lie Y), Matrix.add_kronecker,
    Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add]
  abel

section Lin

set_option linter.unusedSectionVars false

variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem mAct_apply (A : Matrix κ ι ℂ) (x : ι → V) (c : κ) : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_add (A B : Matrix ι ι ℂ) : (mAct (A + B) : Module.End ℂ (ι → V)) = mAct A + mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, add_smul, Finset.sum_add_distrib]

theorem mAct_sum {α : Type} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    (mAct (∑ a ∈ s, A a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, mAct (A a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, Matrix.sum_apply, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem mAct_mul (A B : Matrix ι ι ℂ) : (mAct A * mAct B : Module.End ℂ (ι → V)) = mAct (A * B) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [Module.End.mul_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem dOp_mul (S T : Module.End ℂ V) : (dOp ι (S * T) : Module.End ℂ (ι → V)) = dOp ι S * dOp ι T := rfl

theorem dOp_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [dOp]

theorem left_factor_action_mul (f g : Module.End ℂ (ι → V)) :
    (on1 (f * g) : Module.End ℂ (ι × κ → V)) = on1 f * on1 g := rfl

theorem right_factor_action_mul (f g : Module.End ℂ (κ → V)) :
    (on2 (f * g) : Module.End ℂ (ι × κ → V)) = on2 f * on2 g := rfl

theorem left_factor_action_add (f g : Module.End ℂ (ι → V)) :
    (on1 (f + g) : Module.End ℂ (ι × κ → V)) = on1 f + on1 g := rfl

theorem right_factor_action_add (f g : Module.End ℂ (κ → V)) :
    (on2 (f + g) : Module.End ℂ (ι × κ → V)) = on2 f + on2 g := rfl

theorem left_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (ι → V)) :
    (on1 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on1 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1]

theorem right_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (κ → V)) :
    (on2 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on2 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2]

theorem left_factor_action_diag_op (T : Module.End ℂ V) : (on1 (dOp ι T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem right_factor_action_diag_op (T : Module.End ℂ V) : (on2 (dOp κ T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem left_factor_action_kronecker (A : Matrix ι ι ℂ) :
    (on1 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct (A ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem right_factor_action_kronecker (A : Matrix κ κ ℂ) :
    (on2 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct ((1 : Matrix ι ι ℂ) ⊗ₖ A) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem expand {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by
  nth_rewrite 1 [← h1]
  rw [← h2]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  abel

end Lin

theorem casSplit : CasSplit := by
  intro k r F F' U hF hF'
  simp only [cas, cas1, cas2, casR, L, left_factor_action_sum, right_factor_action_sum, left_factor_action_mul, right_factor_action_mul, left_factor_action_add, right_factor_action_add, left_factor_action_diag_op, right_factor_action_diag_op,
    left_factor_action_kronecker, right_factor_action_kronecker, dC_tens hF hF', mAct_add, dOp_sum, dOp_mul, two_smul]
  refine expand (fun a b => dOp (F.ι × F'.ι) (U.dC (Matrix.single a b 1)))
    (fun a b => mAct (F.dC (Matrix.single a b 1) ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ)))
    (fun a b => mAct ((1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC (Matrix.single a b 1))) _ ?_ ?_
  · simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]
  · rw [Finset.sum_comm]
    simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]

end GlobalTheory.CompanionTheory.ZuckCasSplit

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CasimirSplitting : CasSplit := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | exact GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | (intros; apply GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.BesselMapSm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dsLin : DsLin := by
  intro n Hm H _ _ _ σ hσ u hu
  have h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm := hσ.grp.2.1
  obtain ⟨U, F, hUo, h1U, hF, hfF⟩ := hu 1 h1
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm := fun t => ex_mem_of_lie hX t
  have hd : HasDerivAt (fun t : ℝ => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex (1 : Mat n) X
  have hl := hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF
  exact hl.deriv

end GlobalTheory.CompanionTheory.BesselMapSm
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinearStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesLinear : DsLin := by
  first | exact @GlobalTheory.CompanionTheory.BesselMapSm.dsLin | exact GlobalTheory.CompanionTheory.BesselMapSm.dsLin | (intros; apply GlobalTheory.CompanionTheory.BesselMapSm.dsLin <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckTens

open scoped Matrix.Norms.Elementwise

theorem okTens : OKTens := by
  intro k r F F' hF hF'
  refine ⟨?_, ?_, ?_, ?_⟩
  · show F.ρ 1 ⊗ₖ F'.ρ 1 = 1
    rw [hF.one, hF'.one, Matrix.one_kronecker_one]
  · intro g hg h hh
    show F.ρ (g * h) ⊗ₖ F'.ρ (g * h) = (F.ρ g ⊗ₖ F'.ρ g) * (F.ρ h ⊗ₖ F'.ρ h)
    rw [hF.mul g hg h hh, hF'.mul g hg h hh, Matrix.mul_kronecker_mul]
  · rintro ⟨c, c'⟩ ⟨d, d'⟩ g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hF.smooth c d g₀ hg₀
    obtain ⟨U', f', hU', hgU', hf', hfe'⟩ := hF'.smooth c' d' g₀ hg₀
    refine ⟨U ∩ U', fun x => f x * f' x, hU.inter hU', ⟨hgU, hgU'⟩,
      (hf.mono Set.inter_subset_left).mul (hf'.mono Set.inter_subset_right), ?_⟩
    intro g hg hin
    have h1 := hfe g hg.1 hin
    have h2 := hfe' g hg.2 hin
    show F.ρ g c d * F'.ρ g c' d' = f g * f' g
    simp only at h1 h2
    rw [h1, h2]
  · obtain ⟨C, hC⟩ := hF.growth
    obtain ⟨C', hC'⟩ := hF'.growth
    refine ⟨C * C', ?_⟩
    rintro g hg ⟨c, c'⟩ ⟨d, d'⟩
    show ‖F.ρ g c d * F'.ρ g c' d'‖ ≤ C * C' * Formalism.FourierDecayAlt.B.gN g ^ (F.deg + F'.deg)
    have h1 := hC g hg c d
    have h2 := hC' g hg c' d'
    rw [norm_mul, pow_add]
    calc _ ≤ (C * Formalism.FourierDecayAlt.B.gN g ^ F.deg) * (C' * Formalism.FourierDecayAlt.B.gN g ^ F'.deg) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.ZuckTens
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegralStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TensorPowerIntegral : OKTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckStdD

theorem dR_std (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r false).dR X = X := by
  ext c d
  exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv

theorem dR_dual (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r true).dR X = -Xᵀ := by
  ext c d
  have h := (PI.ComplexConjugateDerivative.exp_entry (-X) d c).deriv
  have e : (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) =
      fun t : ℝ => (NormedSpace.exp ((t : ℂ) • (-X))) d c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
    simp [dualM]
  show deriv (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0 = _
  rw [e, h]
  rfl

theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    reH k r Y + Complex.I • imH k r Y = Y := by
  unfold reH imH
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
  rw [smul_smul, hI, ← smul_add]
  have : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y := by
    intro Z; rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

theorem stdD : StdD := by
  intro k r Y
  constructor
  · unfold FRep.dC
    rw [dR_std, dR_std]
    exact reH_add_imH k r Y
  · unfold FRep.dC
    rw [dR_dual, dR_dual]
    conv_rhs => rw [← reH_add_imH k r Y]
    rw [Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]

end GlobalTheory.CompanionTheory.ZuckStdD
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferentialStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StandardDifferential : StdD := by
  first | exact @GlobalTheory.CompanionTheory.ZuckStdD.stdD | exact GlobalTheory.CompanionTheory.ZuckStdD.stdD | (intros; apply GlobalTheory.CompanionTheory.ZuckStdD.stdD <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactor
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuFactor

theorem exists_factor {S E V : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : S →ₗ[ℂ] E) (B : S →ₗ[ℂ] V) (C : ℝ)
    (hb : ∀ v, ‖B v‖ ≤ C * ‖J v‖) : ∃ T : E →L[ℂ] V, ∀ v, B v = T (J v) := by
  have hker : LinearMap.ker J ≤ LinearMap.ker B := fun v hv => by
    have := hb v
    rw [LinearMap.mem_ker.1 hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let g : LinearMap.range J →ₗ[ℂ] V := ((LinearMap.ker J).liftQ B hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hg : ∀ v : S, g ⟨J v, LinearMap.mem_range_self J v⟩ = B v := fun v => by
    show (LinearMap.ker J).liftQ B hker (J.quotKerEquivRange.symm ⟨J v, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  have hgb : ∀ y : LinearMap.range J, ‖g y‖ ≤ C * ‖y‖ := by
    rintro ⟨_, v, rfl⟩
    exact (congrArg norm (hg v)).le.trans (hb v)
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exist_extension_of_finiteDimensional_range (g.mkContinuous _ hgb)
  refine ⟨T, fun v => ?_⟩
  have := congrArg (fun f => f ⟨J v, LinearMap.mem_range_self J _⟩) hT
  exact (hg v).symm.trans this

theorem factor : Factor := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB
  obtain ⟨C, Ws, hW, hC⟩ := hB.bd
  have h := hσ.rep
  have hI : ∀ i : Fin Ws.length, LieWd Hm (Ws.get i) := fun i => hW _ (List.get_mem Ws i)
  have hL : ∀ i : Fin Ws.length, LieW (UH Hm) (Ws.get i) := fun i X hX t => ex_mem_of_lie (hI i X hX) t
  let S : Submodule ℂ H :=
    { carrier := {v | IsSm (UH Hm) σ v}
      add_mem' := fun ha hb => IsSm.add ha hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ ha => IsSm.smul ha c }
  let J : S →ₗ[ℂ] (Fin Ws.length → H) :=
    { toFun := fun v i => dsW σ (Ws.get i) v
      map_add' := fun a b => funext fun i => dsW_add h a.2 b.2 (hL i)
      map_smul' := fun c a => funext fun i => dsW_smul h a.2 c (hL i) }
  let B' : S →ₗ[ℂ] V :=
    { toFun := fun v => B v
      map_add' := fun a b => hB.add _ a.2 _ b.2
      map_smul' := fun c a => hB.smul c _ a.2 }
  have hb : ∀ v : S, ‖B' v‖ ≤ (|C| * Ws.length) * ‖J v‖ := fun v => by
    have h1 : (Ws.map fun w => ‖dsW σ w (v : H)‖).sum ≤ Ws.length * ‖J v‖ := by
      have := List.sum_le_card_nsmul (Ws.map fun w => ‖dsW σ w (v : H)‖) ‖J v‖ (by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hw
        exact norm_le_pi_norm (J v) i)
      rwa [List.length_map, nsmul_eq_mul] at this
    have h0 : 0 ≤ (Ws.map fun w => ‖dsW σ w (v : H)‖).sum :=
      List.sum_nonneg fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc ‖B' v‖ ≤ C * _ := hC _ v.2
      _ ≤ |C| * (Ws.length * ‖J v‖) := mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
      _ = _ := by ring
  obtain ⟨T, hT⟩ := exists_factor J B' _ hb
  refine ⟨Ws.length, Ws.get, fun i => T.comp (ContinuousLinearMap.single ℂ (fun _ => H) i), hI, fun v hv => ?_⟩
  have h2 : B v = T (J ⟨v, hv⟩) := hT ⟨v, hv⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, ← Finset.univ_sum_single (J ⟨v, hv⟩), map_sum]
  rfl

end GlobalTheory.CompanionTheory.BmuFactor

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjoint
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjoint
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

namespace GlobalTheory.CompanionTheory.BmuDsAd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ex_mul_eq {y : Mat n} (hy : IsUnit y) (X : Mat n) (t : ℝ) :
    ex X t * y = y * ex (y⁻¹ * X * y) t := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : (t : ℂ) • (y⁻¹ * X * y) = y⁻¹ * ((t : ℂ) • X) * y := by
    simp [Matrix.mul_smul, Matrix.smul_mul]
  unfold ex
  rw [h1, Matrix.exp_conj' _ _ hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem lie_conj {Hm y X : Mat n} (hy : IsUnit y) (hyH : yᴴ * Hm * y = Hm) (hX : Lie Hm X) :
    Lie Hm (y⁻¹ * X * y) := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : Hm * y⁻¹ = yᴴ * Hm := by
    calc Hm * y⁻¹ = yᴴ * Hm * y * y⁻¹ := by rw [hyH]
      _ = yᴴ * Hm := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : y⁻¹ᴴ * Hm = Hm * y := by
    calc y⁻¹ᴴ * Hm = y⁻¹ᴴ * (yᴴ * Hm * y) := by rw [hyH]
      _ = (y * y⁻¹)ᴴ * (Hm * y) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hm * y := by rw [h1]; simp
  unfold Lie at hX ⊢
  calc (y⁻¹ * X * y)ᴴ * Hm + Hm * (y⁻¹ * X * y)
      = yᴴ * Xᴴ * (y⁻¹ᴴ * Hm) + (Hm * y⁻¹) * X * y := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = yᴴ * (Xᴴ * Hm + Hm * X) * y := by
        rw [h2, h3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem dsAd : DsAd := by
  intro n Hm H _ _ _ σ hσ y hy W hW
  have hyu : IsUnit y := by
    have hyH : yᴴ * Hm * y = Hm := hy
    have h1 : (Hm * yᴴ * Hm) * y = 1 := by
      rw [Matrix.mul_assoc Hm, Matrix.mul_assoc Hm, hyH, hσ.sq]
    exact (Matrix.isUnit_iff_isUnit_det y).2 (Matrix.isUnit_det_of_left_inverse h1)
  have hyH : yᴴ * Hm * y = Hm := hy
  have hL : ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y) := by
    intro W hW Z hZ
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hZ
    exact lie_conj hyu hyH (hW X hX)
  refine ⟨hL W hW, fun u hu => ?_⟩
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieWd Hm W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX : Lie Hm X := hW X List.mem_cons_self
    have hX' : ∀ t, ex (y⁻¹ * X * y) t ∈ UH Hm := fun t => ex_mem_of_lie (lie_conj hyu hyH hX) t
    have hs : IsSm (UH Hm) σ (dsW σ (W.map fun X => y⁻¹ * X * y) u) :=
      hu.dsW hσ.rep fun Z hZ t => ex_mem_of_lie (hL W hW' Z hZ) t
    rw [List.map_cons, dsW_cons, dsW_cons, ih hW',
      apply_ds hσ.rep hX' hy (hs.differentiableAt hσ.rep hX')]
    unfold ds
    congr 1
    ext t
    rw [← hσ.rep.apply_mul (ex_mem_of_lie hX t) hy, ex_mul_eq hyu]

end GlobalTheory.CompanionTheory.BmuDsAd
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjointStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesAdjoint : DsAd := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsAd.dsAd | exact GlobalTheory.CompanionTheory.BmuDsAd.dsAd | (intros; apply GlobalTheory.CompanionTheory.BmuDsAd.dsAd <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckMatHom

theorem mAct_coord {ι ι' V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct, LinearMap.sum_apply]

theorem mAct_mAct {ι ι' ι'' V : Type} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (x : ι → V) :
    mAct A (mAct B x) = mAct (A * B) x := by
  funext c
  simp only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem dOp_mAct {ι ι' V V' : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (A : Matrix ι' ι ℂ) (T : V →ₗ[ℂ] V') (x : ι → V) :
    dOp ι' T (mAct A x) = mAct A (dOp ι T x) := by
  funext c
  have h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e) := fun _ _ _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, mAct_coord, map_sum, map_smul]

theorem dsigW_eq_prod {k r : ℕ} (U : URep k r) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)), LieWd k r W → ∀ v : U.R.smSub,
      PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W (v : U.R.H) = ((W.map U.dsig).prod v : U.R.H)
  | [], _, _ => rfl
  | X :: W, hW, v => by
    have ih := dsigW_eq_prod U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      URep.dsig_coe U (hW X List.mem_cons_self), ← ih]
    rfl

theorem matHom : MatHom := by
  intro k r F F' U A hA
  refine ⟨fun W hW => ⟨∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖, [W], ?_, fun x => ?_⟩, fun g hg => ?_⟩
  · intro W' hW'
    rw [List.mem_singleton.1 hW']
    exact hW
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change ∑ c : F'.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((mAct A x c : U.R.smSub) : U.R.H)‖ ≤
      (∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖) *
        ∑ e : F.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((x e : U.R.smSub) : U.R.H)‖
    simp only [dsigW_eq_prod U W hW]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mAct_coord, map_sum, Submodule.coe_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [map_smul, Submodule.coe_smul, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Finset.single_le_sum
      (f := fun e => ‖(((W.map U.dsig).prod (x e) : U.R.smSub) : U.R.H)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
  · refine LinearMap.ext fun x => ?_
    change mAct A (mAct (F.ρ g) (dOp F.ι (U.sig g) x)) = mAct (F'.ρ g) (dOp F'.ι (U.sig g) (mAct A x))
    rw [dOp_mAct, mAct_mAct, mAct_mAct, hA g hg]

end GlobalTheory.CompanionTheory.ZuckMatHom

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHomStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MatrixHom : MatHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckMatHom.matHom | exact GlobalTheory.CompanionTheory.ZuckMatHom.matHom | (intros; apply GlobalTheory.CompanionTheory.ZuckMatHom.matHom <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckUIso

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

theorem isSm_map (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {v : H} (hv : IsSm G σ v) :
    IsSm G σ' (e v) :=
  (SmOn.clm hv (e.restrictScalars ℝ)).congr fun g hg => (he g hg v).symm

theorem ds_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by
  have h1 := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.differentiableAt h hX).hasDerivAt
  have h2 : (fun t => σ' (ex X t) (e v)) = (e.restrictScalars ℝ) ∘ fun t => σ (ex X t) v := by
    ext t; exact (he _ (hX t) v).symm
  unfold ds
  rw [h2, h1.deriv]; rfl

theorem dsW_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x))
    {v : H} (hv : IsSm G σ v) : ∀ {W : List (Mat n)}, LieW G W → dsW σ' W (e v) = e (dsW σ W v)
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, dsW_cons, dsW_map h e he hv hW',
      ds_map h e he (hW X List.mem_cons_self) (hv.dsW h hW')]

end Gen

variable {k r : ℕ}

def res (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H) (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) :
    U.R.smSub →ₗ[ℂ] U'.R.smSub :=
  (e : U.R.H →ₗ[ℂ] U'.R.H).restrict fun v hv => isSm_map (G := GG k r) e he (v := v) hv

theorem res_coe (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (v : U.R.smSub) :
    (res U U' e he v : U'.R.H) = e v := rfl

theorem isHom_res (F : FRep k r) (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (hn : ∀ x, ‖e x‖ = ‖x‖) :
    IsHom (F, U) (F, U') (dOp F.ι (res U U' e he)) := by
  constructor
  · intro W hW
    refine ⟨1, [W], by simpa using hW, fun x => le_of_eq ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, sn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dsigW_eq', dsigW_eq']
    change ‖dsW U'.R.σ W (e (x c : U.R.H))‖ = _
    rw [dsW_map U.repOn e he (v := (x c : U.R.H)) (x c).2 (fun X hX t => ex_mem_of_lie (hW X hX) t), hn]
  · intro g hg
    have h1 : res U U' e he ∘ₗ U.sig g = U'.sig g ∘ₗ res U U' e he := by
      ext v
      simp only [LinearMap.comp_apply, res_coe, URep.sig_coe _ hg, he g hg]
    refine LinearMap.ext fun x => funext fun c => ?_
    have h2 : ∀ d, res U U' e he (U.sig g (x d)) = U'.sig g (res U U' e he (x d)) :=
      fun d => LinearMap.congr_fun h1 (x d)
    simp [CompanionTheory.Zuck.act, mAct, dOp, h2]

theorem uIso : UIso := by
  rintro k r F U U' ⟨e, he⟩
  have he' : ∀ g ∈ GG k r, ∀ x, e.symm (U'.R.σ g x) = U.R.σ g (e.symm x) := fun g hg x => by
    apply e.injective
    rw [he g hg, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨dOp F.ι (res U U' (e.toContinuousLinearEquiv : U.R.H →L[ℂ] U'.R.H) he),
    dOp F.ι (res U' U (e.symm.toContinuousLinearEquiv : U'.R.H →L[ℂ] U.R.H) he'),
    isHom_res F U U' _ he e.norm_map, isHom_res F U' U _ he' e.symm.norm_map, ?_, ?_⟩
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.symm_apply_apply _)
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.apply_symm_apply _)

end GlobalTheory.CompanionTheory.ZuckUIso

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIsoStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.UnitaryIso : UIso := by
  first | exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso | exact GlobalTheory.CompanionTheory.ZuckUIso.uIso | (intros; apply GlobalTheory.CompanionTheory.ZuckUIso.uIso <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckCount

theorem casG_polar {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    casG (addSet μ J) + casG (μ + Pi.single s 1) + (2 - casG μ) - casG (addSet μ J + Pi.single s 1)
      = if s ∈ J then 0 else 2 := by
  have h : ∑ a, ((addSet μ J a) ^ 2 + ((μ + Pi.single s 1 : Fin n → ℝ) a) ^ 2 - μ a ^ 2
      - ((addSet μ J + Pi.single s 1 : Fin n → ℝ) a) ^ 2) = if s ∈ J then -2 else 0 := by
    rw [Finset.sum_eq_single s]
    · simp only [addSet, Pi.add_apply, Pi.single_eq_same]
      split_ifs <;> ring
    · intro b _ hb
      simp only [addSet, Pi.add_apply, Pi.single_eq_of_ne hb]
      ring
    · simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  unfold casG
  split_ifs at h ⊢ <;> linarith

theorem addSet_insert {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) (hs : s ∉ J) :
    addSet μ J + Pi.single s 1 = addSet μ (insert s J) := by
  funext a
  by_cases ha : a = s
  · subst ha
    simp [addSet, hs]
  · simp [addSet, ha]

theorem addSet_eq_iff {n : ℕ} (μ : Fin n → ℝ) (J I : Finset (Fin n)) (s : Fin n) :
    addSet μ J + Pi.single s 1 = addSet μ I ↔ s ∉ J ∧ I = insert s J := by
  constructor
  · intro h
    have hs : s ∉ J := by
      intro hs
      have := congrFun h s
      simp only [addSet, Pi.add_apply, Pi.single_eq_same, if_pos hs] at this
      split_ifs at this <;> linarith
    refine ⟨hs, ?_⟩
    rw [addSet_insert μ J s hs] at h
    ext a
    have := congrFun h a
    simp only [addSet, add_right_inj] at this
    by_cases h1 : a ∈ I <;> by_cases h2 : a ∈ insert s J <;> simp_all
  · rintro ⟨hs, rfl⟩
    exact addSet_insert μ J s hs

theorem casG_polar_complex {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    (casG (addSet μ J) : ℂ) + (casG (μ + Pi.single s 1) : ℂ) + (2 - (casG μ : ℂ))
      - (casG (addSet μ J + Pi.single s 1) : ℂ) = if s ∈ J then 0 else 2 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (casG_polar μ J s)
  split_ifs at h ⊢ <;> (push_cast at h; exact h)

theorem count : Count := by
  intro n m μ _ par w
  have hw : ∀ p, w p (par p) = if p.2 ∈ p.1.1 then 0 else 2 := fun p => casG_polar_complex μ p.1.1 p.2
  refine ⟨fun I => ?_, fun ν hν => ?_⟩
  · have h1 : ∀ p ∈ univ.filter (fun p => par p = addSet μ I.1), w p (addSet μ I.1) = 2 := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      rw [← hp', hw, if_neg ((addSet_eq_iff μ p.1.1 I.1 p.2).1 hp').1]
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    have hc : (univ.filter (fun p => par p = addSet μ I.1)).card = I.1.card := by
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        have := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        rw [this.2]; exact Finset.mem_insert_self _ _
      · intro p hp q hq hpq
        have h1 := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        have h2 := (addSet_eq_iff μ q.1.1 I.1 q.2).1 (Finset.mem_filter.1 hq).2
        have hpq' : p.2 = q.2 := hpq
        refine Prod.ext (Subtype.ext ?_) hpq'
        rw [← Finset.erase_insert h1.1, ← Finset.erase_insert h2.1, ← h1.2, ← h2.2, hpq']
      · intro s hs
        refine ⟨(⟨I.1.erase s, ?_⟩, s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        · rw [Finset.card_erase_of_mem hs, I.2]; rfl
        · exact (addSet_eq_iff μ _ I.1 s).2 ⟨Finset.notMem_erase _ _, (Finset.insert_erase hs).symm⟩
    rw [hc, I.2, nsmul_eq_mul]
    push_cast
    ring
  · refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).2
    rw [← hp', hw, if_pos]
    by_contra hs
    refine hν ⟨insert p.2 p.1.1, ?_⟩ ?_
    · rw [Finset.card_insert_of_notMem hs, p.1.2]
    · rw [← hp']; exact (addSet_insert μ _ _ hs).symm

end GlobalTheory.CompanionTheory.ZuckCount
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBoundStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CountingBound : Count := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCount.count | exact GlobalTheory.CompanionTheory.ZuckCount.count | (intros; apply GlobalTheory.CompanionTheory.ZuckCount.count <;> assumption)
end
end
