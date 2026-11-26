module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowsSumEqDivisorSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassP
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassPStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | exact GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.DerivExpansion

theorem tsum_inv_cube : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = 0 := by
  have h : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = -∑' m : ℤ, 1 / (m : ℂ) ^ 3 := by
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
    rw [← tsum_neg]
    congr 1
    funext b
    simp only [Equiv.neg_apply, Int.cast_neg]
    change 1 / ((-(b : ℂ)) ^ 3) = -(1 / (b : ℂ) ^ 3)
    rw [show (-(b : ℂ)) ^ 3 = -((b : ℂ) ^ 3) by ring, div_neg]
  linear_combination h / 2

theorem row_eq (N : ℕ) [NeZero N] (j : ZMod N) :
    ∑' m : ℤ, 1 / (((j.val : ℂ)) / N + m) ^ 3 =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (ch N j * (1 + ch N j) / (1 - ch N j) ^ 3) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have hc : ch N 0 = 1 := by simp [ch]
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, zero_add, hc, sub_self]
    rw [tsum_inv_cube]
    simp
  · set w : ℂ := ((j.val : ℂ)) / N with hw
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have him : w.im = 0 := by simp [hw, -ZMod.natCast_val]
    have hnot : ∀ n : ℤ, w ≠ n := by
      intro n hn
      rw [hw, div_eq_iff hN] at hn
      have hz : (j.val : ℤ) = n * N := by exact_mod_cast hn
      have h1 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj ((ZMod.val_eq_zero j).mp h))
      have h2 : j.val < N := ZMod.val_lt j
      have h1' : (0 : ℤ) < j.val := by exact_mod_cast h1
      have h2' : (j.val : ℤ) < N := by exact_mod_cast h2
      rcases le_or_gt n 0 with h | h
      · nlinarith
      · nlinarith
    have hc : ch N j = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
      rw [hw]
      unfold ch
      congr 1
      ring
    rw [hc]
    exact (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger w him hnot).2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  intro N _ x
  unfold HasQ
  intro τ
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 2 τ x _ (by norm_num) (GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP τ (tors N τ x))
  set q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set c0 : ℂ := if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0 with hc0
  have h0 : cSum N 2 (-1) x 0 = 0 := by simp [cSum]
  have hT' : HasSum (fun k : ℕ => cSum N 2 (-1) x k * q ^ k) T := by
    have e1 : ((-1 : ℂ)) ^ (2 + 1) = -1 := by norm_num
    simpa only [e1] using hT
  have hsum : HasSum (fun n : ℕ => cD N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N))
      (c0 + T) := by
    have hA : HasSum (fun n : ℕ => if n = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    convert hA.add hT' using 1
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / N) = q ^ n := by
      rw [hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [cD, h0, hc0]
    · simp [cD, hn]
  convert hsum using 1
  have hrow : (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (2 + 1) else 0) =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * c0 := by
    rw [hc0]
    split_ifs
    · exact row_eq N (x 1)
    · simp
  have hf : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [hrow, hf] at hS
  simp only [wpd]
  rw [div_eq_iff (pow_ne_zero 3 hπ)]
  linear_combination (-2) * hS

end GlobalTheory.WpFam.DerivExpansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  first | exact @GlobalTheory.WpFam.DerivExpansion.main | exact GlobalTheory.WpFam.DerivExpansion.main | (intros; apply GlobalTheory.WpFam.DerivExpansion.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeGramLocal

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem del_im_of_differentiableAt {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by
  have hR : DifferentiableAt ℝ F z := hF.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun x => conj (F x)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hR
  have e : (fun x => ((F x).im : ℂ)) = fun x => (1 / (2 * I)) • (F x - conj (F x)) := by
    funext x; rw [im_eq_sub_conj, smul_eq_mul]; ring
  rw [e, del_const_smul _ (hR.fun_sub hc), ContinuousLinearMap.smul_apply, del_sub hR hc,
    ContinuousLinearMap.sub_apply, del_conj, dbar_eq_zero hF, del_eq_fderiv hF]
  simp

theorem ddbar_im_of_contDiffAt {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by
  have h := leviForm_re_eq_zero (f := fun x => -I * F x) (contDiffAt_const.mul hF)
  have e : (fun x => ((F x).im : ℂ)) = fun x => (((-I * F x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e]; exact h

theorem contDiffAt_im_of_analyticAt {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z :=
  (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp z (hF.contDiffAt.restrict_scalars ℝ)

end General

def locLog (w₀ w : ℂ) : ℂ := Complex.log (w / w₀) + Complex.log w₀

theorem exp_locLog {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by
  rw [locLog, exp_add, exp_log (slitPlane_ne_zero h), exp_log h0, div_mul_cancel₀ _ h0]

theorem hasDerivAt_locLog {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w :=
  (((hasDerivAt_id w).div_const w₀).clog h).add_const _

end GlobalTheory.HodgeGramLocal

namespace GlobalTheory.HodgeGramLocal

variable {n a g : ℕ}

def locEntry (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (j k : Fin g) (x : Fin n → ℂ) : ℂ :=
  τ₀ x j k + ∑ i, locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i)) / (2 * Real.pi * I) *
    ((B i j k : ℤ) : ℂ)

theorem isOpen_polydisc (n : ℕ) : IsOpen (polydisc n 1) := by
  rw [show polydisc n 1 = ⋂ k, {z : Fin n → ℂ | ‖z k‖ < 1} by ext; simp [polydisc]]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const

theorem hodgeGram_local (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  intro z hz
  let V : Set (Fin n → ℂ) := {x | x ∈ polydisc n 1 ∧
    ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane}
  have hVo : IsOpen V := by
    have h2 : IsOpen {x : Fin n → ℂ |
        ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)
    exact (isOpen_polydisc n).inter h2
  have hzV : z ∈ V := ⟨hz.1, fun i => by rw [div_self (hz.2 i)]; exact one_mem_slitPlane⟩
  have hV : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

  have hterm : ∀ (j k : Fin g) (i : Fin a) (x : Fin n → ℂ), x ∈ V →
      HasFDerivAt (fun y : Fin n → ℂ => locLog (z (Fin.castLE ha i)) (y (Fin.castLE ha i)) /
        (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ))
        ((1 / z (Fin.castLE ha i) / (x (Fin.castLE ha i) / z (Fin.castLE ha i)) /
          (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k i x hx => by
      have h1 := ((hasDerivAt_locLog (hx.2 i)).div_const (2 * (Real.pi : ℂ) * I)).mul_const
        ((B i j k : ℤ) : ℂ)
      have h2 : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE ha i))
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
        hasFDerivAt_apply _ _
      exact h1.comp_hasFDerivAt x h2
  have hτ : ∀ j k, ∀ x ∈ V, HasFDerivAt (fun y => τ₀ y j k) (fderiv ℂ (fun y => τ₀ y j k) x) x :=
    fun j k x hx => ((hP.holo j k).differentiableAt ((isOpen_polydisc n).mem_nhds hx.1)).hasFDerivAt
  have hloc : ∀ j k, ∀ x ∈ V, HasFDerivAt (locEntry ha τ₀ B z j k)
      (fderiv ℂ (fun y => τ₀ y j k) x + ∑ i, (1 / z (Fin.castLE ha i) /
        (x (Fin.castLE ha i) / z (Fin.castLE ha i)) / (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k x hx => (hτ j k x hx).add (HasFDerivAt.fun_sum fun i _ => hterm j k i x hx)
  have hdiff : ∀ j k, DifferentiableOn ℂ (locEntry ha τ₀ B z j k) V := fun j k x hx =>
    (hloc j k x hx).differentiableAt.differentiableWithinAt
  have hF : ∀ j k, AnalyticAt ℂ (locEntry ha τ₀ B z j k) z := fun j k =>
    ReciprocityTheory.AnForm.Osgood.osgood n V _ hVo (hdiff j k) z hzV
  have heq : ∀ x ∈ V, hodgeGram ha τ₀ B x = of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) := by
    intro x hx
    have hL : ∀ i, exp ((fun i => locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i))) i) =
        x (Fin.castLE ha i) := fun i => exp_locLog (hz.2 i) (hx.2 i)
    rw [hodgeGram, ← im_period ha τ₀ B x _ hL]
    ext j k
    simp [period, locEntry, Matrix.sum_apply]
  have hev : hodgeGram ha τ₀ B =ᶠ[𝓝 z] fun x => of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) :=
    Filter.eventually_of_mem hV heq
  have hev' : ∀ j k, (fun x => hodgeGram ha τ₀ B x j k) =ᶠ[𝓝 z]
      fun x => ((locEntry ha τ₀ B z j k x).im : ℂ) := fun j k =>
    Filter.eventually_of_mem hV fun x hx => by
      show hodgeGram ha τ₀ B x j k = _
      rw [heq x hx]; rfl
  refine ⟨fun j k => (contDiffAt_im_of_analyticAt (hF j k)).congr_of_eventuallyEq (hev' j k),
    fun ξ => ?_, fun ξ η => ?_⟩
  · rw [mdel_congr hev]
    ext j k
    simp only [mdel_apply, of_apply]
    rw [del_im_of_differentiableAt (hF j k).differentiableAt, (hloc j k z hzV).fderiv]
    simp [Matrix.sum_apply, div_self (hz.2 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · ext j k
    rw [mddbar_apply, ddbar_congr (hev' j k),
      ddbar_im_of_contDiffAt ((hF j k).contDiffAt)]
    rfl

end GlobalTheory.HodgeGramLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPartStatement
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B → ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧ (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) • ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) + ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) • ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧ ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  first | exact @GlobalTheory.HodgeGramLocal.hodgeGram_local | exact GlobalTheory.HodgeGramLocal.hodgeGram_local | (intros; apply GlobalTheory.HodgeGramLocal.hodgeGram_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSum
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp [hfdef, latticeEquivProd_symm_coe, hω₁, hω₂]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg, Function.comp_apply]
  ring

end GlobalTheory.WpFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSumStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.G2_add_weierstrassP_row_sum : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | exact GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_value_q_expansion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionB.main | exact GlobalTheory.WpFam.ExpansionB.main | (intros; apply GlobalTheory.WpFam.ExpansionB.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FiniteTypeColimit

noncomputable def diagram (A : CommRingCat.{0}) : Finset A ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin ℤ (t : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 (leOfHom h)))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inclusions (A : CommRingCat.{0}) : diagram A ⟶ (Functor.const (Finset A)).obj A where
  app t := CommRingCat.ofHom (Algebra.adjoin ℤ (t : Set A)).val.toRingHom
  naturality _ _ _ := rfl

noncomputable def isColimit (A : CommRingCat.{0}) : IsColimit (Cocone.mk A (inclusions A)) := by
  classical
  haveI : ReflectsColimit (diagram A) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.finiteType (A : CommRingCat.{0}) (t : Finset A) :
    Algebra.FiniteType ℤ ((_root_.GlobalTheory.FiniteTypeColimit.diagram A).obj t) := by
  have h : (Algebra.adjoin ℤ (t : Set A)).FG := Subalgebra.fg_adjoin_finset t
  have := (Subalgebra.fg_iff_finiteType _).1 h
  change Algebra.FiniteType ℤ (CommRingCat.of (Algebra.adjoin ℤ (t : Set A)))
  convert this


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType : ∀ A : CommRingCat.{0},
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (ι : D ⟶ (Functor.const J).obj A),
      Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) :=
  fun A => ⟨Finset A, inferInstance, inferInstance, _root_.GlobalTheory.FiniteTypeColimit.diagram A,
    _root_.GlobalTheory.FiniteTypeColimit.inclusions A, ⟨_root_.GlobalTheory.FiniteTypeColimit.isColimit A⟩,
    _root_.GlobalTheory.FiniteTypeColimit.finiteType A⟩

end GlobalTheory.FiniteTypeColimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRingsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filteredColimit_finiteType_int_rings : ∀ A : CommRingCat.{0}, ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj A), Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) := by
  first | (exact @GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (exact GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (intros; apply GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElements
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

instance forgetPreservesSmall :
    PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{1}) :=
  preservesFilteredColimitsOfSize_shrink.{0, 1, 0, 1} _

theorem preservesFilteredColimits_iff_elements :
    ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ T) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, N.map (c.ι.app j) y = x) ∧ ∀ j (y : N.obj (D.obj j)), N.map (c.ι.app j) y = 0 → ∃ (k : J) (f : j ⟶ k), N.map (D.map f) y = 0 := by
  intro T _ N
  constructor
  · intro hN J _ _ D c hc
    have h1 : IsColimit (N.mapCocone c) := isColimitOfPreserves N hc
    have h2 : IsColimit ((forget AddCommGrpCat.{1}).mapCocone (N.mapCocone c)) :=
      isColimitOfPreserves (forget AddCommGrpCat.{1}) h1
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit h2 x
      exact ⟨j, y, hy⟩
    · have h3 := (Types.FilteredColimit.isColimit_eq_iff' h2 y 0).1 (by
        change N.map (c.ι.app j) y = N.map (c.ι.app j) 0
        rw [hy, map_zero])
      obtain ⟨k, f, hf⟩ := h3
      refine ⟨k, f, ?_⟩
      have : N.map (D.map f) y = N.map (D.map f) 0 := hf
      rw [this, map_zero]
  · intro h
    constructor
    intro J _ _
    constructor
    intro D
    constructor
    intro c hc
    obtain ⟨hs, hi⟩ := h J D c hc
    haveI : ReflectsColimit (D ⋙ N) (forget AddCommGrpCat.{1}) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    refine ⟨isColimitOfReflects (forget AddCommGrpCat.{1}) ?_⟩
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i (x y : N.obj (D.obj i)) hxy => ?_)
    · obtain ⟨j, y, hy⟩ := hs x
      exact ⟨j, y, hy.symm⟩
    · have hxy' : N.map (c.ι.app i) (x - y) = 0 := by
        have : (N.map (c.ι.app i)).hom x = (N.map (c.ι.app i)).hom y := hxy
        change (N.map (c.ι.app i)).hom (x - y) = 0
        rw [AddMonoidHom.map_sub, this, sub_self]
      obtain ⟨k, f, hf⟩ := hi i (x - y) hxy'
      refine ⟨k, f, ?_⟩
      change (N.map (D.map f)).hom x = (N.map (D.map f)).hom y
      have hf' : (N.map (D.map f)).hom (x - y) = 0 := hf
      rw [AddMonoidHom.map_sub, sub_eq_zero] at hf'
      exact hf'

end GlobalTheory.EtC.FilteredElements
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ T) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, N.map (c.ι.app j) y = x) ∧ ∀ j (y : N.obj (D.obj j)), N.map (c.ι.app j) y = 0 → ∃ (k : J) (f : j ⟶ k), N.map (D.map f) y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (exact GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (intros; apply GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro A
    change (RingHom.id A).Etale ∧ (RingHom.id A).FaithfullyFlat
    exact ⟨RingHom.Etale.of_bijective Function.bijective_id,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  · intro A B C f g hf hg
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties : (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧ (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧ ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B := by
  first | (exact @GlobalTheory.EtC.etFF_basic) | (exact GlobalTheory.EtC.etFF_basic) | (intros; apply GlobalTheory.EtC.etFF_basic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC
open GlobalTheory.EtC

namespace GlobalTheory.AICIff
open Polynomial

theorem root_mem_range {D K : Type} [CommRing D] [Nontrivial D] [CommRing K] [IsDomain K] [Algebra D K]
    (h : AIC D) : ∀ (n : ℕ) (p : D[X]), p.Monic → p.natDegree = n →
      ∀ x : K, aeval x p = 0 → ∃ y : D, algebraMap D K y = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hn x hx
    rw [eq_one_of_monic_natDegree_zero hp hn] at hx
    simp at hx
  | succ n ih =>
    intro p hp hn x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := (mul_divByMonic_eq_iff_isRoot).2 ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (hfac.symm ▸ hp)
    have hqn : (p /ₘ (X - C a)).natDegree = n := by
      have := (monic_X_sub_C a).natDegree_mul hq
      rw [hfac, natDegree_X_sub_C] at this
      omega
    rw [← hfac, map_mul] at hx
    rcases mul_eq_zero.1 hx with h0 | h0
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C] at h0
      exact (sub_eq_zero.1 h0).symm
    · exact ih _ hq hqn x h0

theorem aic_iff : ∀ (D : Type) [CommRing D] [IsDomain D],
    AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  intro D _ _
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [isIntegrallyClosed_iff (FractionRing D)]
      rintro x ⟨p, hp, hx⟩
      exact root_mem_range h _ p hp rfl x (by rwa [aeval_def])
    · apply IsAlgClosed.of_exists_root
      intro f hf hirr
      have hdeg : 0 < f.natDegree :=
        hf.natDegree_pos.2 (fun h1 => hirr.not_isUnit (h1 ▸ isUnit_one))
      have hinj := IsFractionRing.injective D (FractionRing D)
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors D) f
      set g := IsLocalization.integerNormalization (nonZeroDivisors D) f with hg
      have hc : algebraMap D (FractionRing D) b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb0
      have hgmap : g.map (algebraMap D (FractionRing D)) = C (algebraMap D (FractionRing D) b) * f := by
        rw [hb, Algebra.smul_def]; rfl
      have hgdeg : g.natDegree = f.natDegree := by
        rw [← natDegree_map_eq_of_injective hinj g, hgmap, natDegree_C_mul hc]
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, natDegree_zero] at hgdeg; omega
      obtain ⟨a, ha⟩ := h (integralNormalization g) (monic_integralNormalization hg0)
        (by rw [natDegree_integralNormalization]; omega)
      have hl : algebraMap D (FractionRing D) g.leadingCoeff ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap D (FractionRing D)), hinj.eq_iff]
        exact leadingCoeff_ne_zero.2 hg0
      refine ⟨algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff, ?_⟩
      have key := integralNormalization_eval₂_leadingCoeff_mul (p := g) (by omega)
        (algebraMap D (FractionRing D))
        (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) g.leadingCoeff)
      rw [mul_div_cancel₀ _ hl, eval₂_at_apply, ha, map_zero, ← eval_map, hgmap, eval_mul, eval_C] at key
      have := key.symm
      simpa [hl, hc] using this
  · rintro ⟨h1, h2⟩ p hp hpos
    have hd : (p.map (algebraMap D (FractionRing D))).degree ≠ 0 := by
      refine ne_of_gt (natDegree_pos_iff_degree_pos.1 ?_)
      rw [hp.natDegree_map]; exact hpos
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
    have hint : IsIntegral D x := ⟨p, hp, by rwa [IsRoot, eval_map] at hx⟩
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, IsFractionRing.injective D (FractionRing D) ?_⟩
    rw [map_zero, ← eval₂_at_apply, ← eval_map]
    exact hx

end GlobalTheory.AICIff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  first | (exact @GlobalTheory.AICIff.aic_iff) | (exact GlobalTheory.AICIff.aic_iff) | (intros; apply GlobalTheory.AICIff.aic_iff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBounds
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section
namespace GlobalTheory.PoincareBounds

def pdiag {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : ℝ :=
  if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2

theorem poincareGram_eq {n : ℕ} (a : ℕ) (z : Fin n → ℂ) :
    poincareGram a z = diagonal fun k => ((pdiag a z k : ℝ) : ℂ) := rfl

theorem pdiag_nonneg {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : 0 ≤ pdiag a z k := by
  unfold pdiag; split_ifs <;> positivity

theorem gnorm_diag_sq {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 ≤ d k) (ξ : Fin n → ℂ) :
    gnorm (diagonal fun k => ((d k : ℝ) : ℂ)) ξ ^ 2 = ∑ k, d k * ‖ξ k‖ ^ 2 := by
  have hP : (diagonal fun k => ((d k : ℝ) : ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro k; exact_mod_cast hd k
  rw [gnorm_sq hP, form_eq_sum]
  simp only [diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (ξ k), mul_assoc, mul_conj, ← ofReal_mul, ofReal_re, normSq_eq_norm_sq]

theorem norm_mul_tlog_lt {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) :
    0 < ‖w‖ * tlog w ∧ ‖w‖ * tlog w < 1 := by
  have hx : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine ⟨mul_pos hx (tlog_pos h0 h1), ?_⟩
  have hl := Real.abs_log_mul_self_lt ‖w‖ hx h1.le
  have hpi : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have e : ‖w‖ * tlog w = -(Real.log ‖w‖ * ‖w‖) / (2 * Real.pi) := by
    unfold tlog; ring
  rw [e, div_lt_one (by linarith)]
  have := neg_le_abs (Real.log ‖w‖ * ‖w‖)
  linarith

theorem half_le_pdiag {n a : ℕ} (ha : a ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1) {z : Fin n → ℂ}
    (hz : z ∈ punctured ha ρ) (k : Fin n) : 1 / 2 ≤ pdiag a z k := by
  unfold pdiag
  split_ifs with hk
  · have h0 : z k ≠ 0 := hz.2 ⟨k, hk⟩
    obtain ⟨hp, hl⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have hs : ‖z k‖ ^ 2 * tlog (z k) ^ 2 = (‖z k‖ * tlog (z k)) ^ 2 := by ring
    rw [hs]
    have h2 : 0 < (‖z k‖ * tlog (z k)) ^ 2 := by positivity
    have h3 : (‖z k‖ * tlog (z k)) ^ 2 < 1 := by nlinarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  · exact le_rfl

theorem pdiag_term_le {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (ξ : Fin n → ℂ) (k : Fin n) :
    pdiag a z k * ‖ξ k‖ ^ 2 ≤ gnorm (poincareGram a z) ξ ^ 2 := by
  rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg a z)]
  exact Finset.single_le_sum (f := fun k => pdiag a z k * ‖ξ k‖ ^ 2)
    (fun j _ => mul_nonneg (pdiag_nonneg a z j) (by positivity)) (Finset.mem_univ k)

theorem poincare_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ,
    (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧
      ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤
        2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  intro n a ha ρ hρ z hz
  refine ⟨?_, fun ξ => ⟨fun k => ?_, fun i => ?_⟩⟩
  · rw [poincareGram_eq, posSemidef_diagonal_iff]
    intro k; exact_mod_cast pdiag_nonneg a z k
  · have h1 := pdiag_term_le a z ξ k
    have h2 := half_le_pdiag ha hρ hz k
    have hG := gnorm_nonneg (poincareGram a z) ξ
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * gnorm (poincareGram a z) ξ ^ 2 := by nlinarith
    nlinarith
  · set k := Fin.castLE ha i with hkdef
    have hk : k.val < a := i.2
    have h0 : z k ≠ 0 := hz.2 i
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have h1 := pdiag_term_le a z ξ k
    have hd : pdiag a z k = 1 / (2 * (‖z k‖ * tlog (z k)) ^ 2) := by
      unfold pdiag; rw [if_pos hk]; ring
    rw [hd] at h1
    set s := ‖z k‖ * tlog (z k)
    set G := gnorm (poincareGram a z) ξ
    have hG : 0 ≤ G := gnorm_nonneg _ _
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * s ^ 2 * G ^ 2 := by
      have hs2 : 0 < 2 * s ^ 2 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2] at h1
      linarith
    nlinarith [mul_nonneg hp.le hG]

end GlobalTheory.PoincareBounds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBoundsStatement
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareMetric_punctured_polydisc_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ, (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧ ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  first | exact @GlobalTheory.PoincareBounds.poincare_bounds | exact GlobalTheory.PoincareBounds.poincare_bounds | (intros; apply GlobalTheory.PoincareBounds.poincare_bounds <;> assumption)
end
end
