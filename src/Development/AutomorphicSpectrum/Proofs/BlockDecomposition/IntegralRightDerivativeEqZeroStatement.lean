module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZeroStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZero
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff
open PositivityTheory.RgBcC (GLs Rd)
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.SkewInt

open scoped Matrix.Norms.Operator in
theorem exp_entry_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem exp_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n)) (NormedSpace.exp (t • X) * X) t := by
  have : HasDerivAt (fun s : ℝ => (fun i j => (NormedSpace.exp (s • X) : Mat n) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • X) * X : Mat n) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry_hasDerivAt X t i j
  exact this

theorem curve_hasDerivAt {n : ℕ} (k X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => k * (NormedSpace.exp (s • X) : Mat n)) (k * NormedSpace.exp (t • X) * X) t := by
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ k)
  have h := L.hasFDerivAt.comp_hasDerivAt t (exp_hasDerivAt X t)
  have e : L (NormedSpace.exp (t • X) * X) = k * NormedSpace.exp (t • X) * X := by
    rw [Matrix.mul_assoc]
    rfl
  exact h.congr_deriv e

theorem exp_mem_unitary {n : ℕ} {X : Mat n} (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp (t • X) : Mat n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, hX, smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem integral_Rd_skew : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  intro n _ _ κ _ _ u hu X hX
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hmem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
    (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  let kt : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp (t • X), exp_mem_unitary hX t⟩
  have hval : ∀ (y : Matrix.unitaryGroup (Fin n) ℂ) (t : ℝ),
      y.1 * (NormedSpace.exp (t • X) : Mat n) = (y * kt t).1 := fun _ _ => rfl
  have hcv : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k.1 := continuous_subtype_val
  have hRd := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hu
  have cU : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => u k.1 :=
    hu.continuousOn.comp_continuous hcv hmem
  have cR : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rd X u k.1 :=
    hRd.continuousOn.comp_continuous hcv hmem
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn cR.continuousOn
  have key := GlobalTheory.CompanionTheory.RCalc.ByParts.integral_deriv_eq_zero (μ := κ) (V := ℂ)
    (F := fun t y => u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (F' := fun t y => Rd X u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (K := Set.univ) isCompact_univ (ε := 1) one_pos C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro t _
    simp only [hval]
    exact cU.comp (continuous_mul_const (kt t))
  · simp only [hval]
    exact cR.comp (continuous_mul_const (kt 0))
  · intro y t _
    have hg : y.1 * (NormedSpace.exp (t • X) : Mat n) ∈ GLs n := by
      rw [hval]
      exact hmem _
    have h := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg).hasFDerivAt.comp_hasDerivAt t
      (curve_hasDerivAt y.1 X t)
    exact h
  · intro y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y _
    simp only [hval]
    exact hC _ (Set.mem_univ _)
  · intro t _
    simp only [hval]
    have h0 : kt 0 = 1 := by
      apply Subtype.ext
      simp [kt]
    rw [h0]
    simp only [mul_one]
    exact integral_mul_right_eq_self (fun y : Matrix.unitaryGroup (Fin n) ℂ => u y.1) (kt t)

end GlobalTheory.CompanionTheory.ModelS.SkewInt
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_derivative_eq_zero : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | exact GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew | (intros; apply GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LowerIff
theorem UpperTheory.Reformulated.B.Re1.lower_iff :
    ∀ {n : ℕ} (P : Fin n → Prop) [inst : DecidablePred P],
    (∀ (a b : Fin n), a ≤ b → P b → P a) → ∀ (b : Fin n), P b ↔ (↑b : ℕ) < (Finset.filter P Finset.univ).card := by
  intro n P _ h b
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp P (fun i j hij => h j i hij)).symm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.ReversedBlocks

variable {n : ℕ}

theorem lower_iff (P : Fin n → Prop) [DecidablePred P] (hP : ∀ a b, a ≤ b → P b → P a) (b : Fin n) :
    P b ↔ (b : ℕ) < (univ.filter P).card :=
  _root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b

def lowC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

def topC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b ≤ lev a).card

theorem lt_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b < lev a ↔ (b : ℕ) < lowC lev a :=
  lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b

theorem le_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b ≤ lev a ↔ (b : ℕ) < topC lev a :=
  lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b

theorem high_add_topC (lev : Fin n → ℕ) (a : Fin n) :
    (univ.filter fun b => lev a < lev b).card + topC lev a = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  unfold topC
  exact h

def rv (lev : Fin n → ℕ) (a : Fin n) : ℕ := lowC lev a + (topC lev a - 1) - a

theorem rv_bounds {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) :
    lowC lev a ≤ a ∧ (a : ℕ) < topC lev a ∧ rv lev a + a + 1 = lowC lev a + topC lev a := by
  have h1 : ¬ (a : ℕ) < lowC lev a := fun h => lt_irrefl _ ((lt_iff hm a a).2 h)
  have h2 : (a : ℕ) < topC lev a := (le_iff hm a a).1 le_rfl
  unfold rv
  omega

theorem rv_lt {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rv lev a < n := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have := high_add_topC lev a
  omega

def rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : Fin n := ⟨rv lev a, rv_lt hm a⟩

theorem lev_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : lev (rf hm a) = lev a := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  apply le_antisymm
  · exact (le_iff hm a _).2 (by simp only [rf]; omega)
  · exact not_lt.1 fun h => by
      have := (lt_iff hm a _).1 h
      simp only [rf] at this
      omega

theorem rf_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rf hm (rf hm a) = a := by
  have hl := lev_rf hm a
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  obtain ⟨k1, k2, k3⟩ := rv_bounds hm (rf hm a)
  have e1 : lowC lev (rf hm a) = lowC lev a := by simp only [lowC, hl]
  have e2 : topC lev (rf hm a) = topC lev a := by simp only [topC, hl]
  apply Fin.ext
  have e3 : ((rf hm a : Fin n) : ℕ) = rv lev a := rfl
  have e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a) := rfl
  omega

theorem exists_perm_yZ : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
      (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  intro n lam lev h
  obtain ⟨hm, hc⟩ := h
  refine ⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩
  have hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a := rfl
  rw [hv]
  have hl : lam (rf hm a) = lam a := hc _ _ (lev_rf hm a)
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have h4 := high_add_topC lev a
  have c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ) := by exact_mod_cast h3
  have c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ) := by exact_mod_cast h4
  have e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ) := rfl
  have hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ) := rfl
  simp only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]
  push_cast
  rw [hlow]
  linear_combination (-1 : ℂ) * c3 - c4

end GlobalTheory.CompanionTheory.ModelS.ReversedBlocks
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfCharStatement
open PositivityTheory.RgBcC (infOf)
open PositivityTheory.RgBcC.RealD (IsLev)

theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
      ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
        (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 -
          ((a : ℕ) : ℂ) = infOf lam false (σ a) :=
  GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FMem

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun g : Mat n => g a b) :=
  contDiff_apply_apply ℝ a b

theorem contDiff_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → Matrix ι ι ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ fun g => M g a b) : ContDiff ℝ ∞ fun g => (M g).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => h _ _

theorem contDiff_lm (j : Fin n) : ContDiff ℝ ∞ (lm j) :=
  contDiff_det_of_entries fun _ _ => contDiff_entry _ _

theorem contDiff_gm (j : Fin n) : ContDiff ℝ ∞ (gm j) := by
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)

theorem zpow_contDiffOn {f : Mat n → ℂ} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s)
    (h : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℝ ∞ (fun x => f x ^ m) s := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)


open scoped ComplexOrder in
theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : gm j g ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0 :=
    (Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1 := by
    have h2 := Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id
    have hi : Function.Injective (ini j) := Fin.castLE_injective _
    rw [Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi] at h2
    exact h2.symm
  have hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  apply hv
  calc v = (((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ) *ᵥ v := by
        rw [hBA, Matrix.one_mulVec]
    _ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem muZ_antitone {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlam : Antitone lam) (hlev : Monotone lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : lev a ≤ lev b := hlev hab
  have c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

theorem dif_nonneg_of_antitone {v : Fin n → ℤ} (h : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ dif v j := by
  have hnext : j ≤ (⟨j + 1, hj⟩ : Fin n) := Fin.le_def.mpr (Nat.le_succ _)
  simpa only [dif, dite_eq_left hj, sub_nonneg] using h hnext

theorem lm_ne_zero (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) {g : Mat n} (hg : g ∈ GLs n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by
      have := j.isLt
      simp only [Fintype.card_fin]
      omega⟩
  have e : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [e]
  exact hg

end GlobalTheory.CompanionTheory.ModelS.FMem

namespace GlobalTheory.CompanionTheory.ModelS


open FMem in
theorem fRaw_mem_SmF : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  intro n lam hlam lev hlev
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have key : ContDiffOn ℝ ∞
      (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n) := by
    refine contDiffOn_prod fun j _ => ContDiffOn.mul ?_
      (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)
    by_cases hj : (j : ℕ) + 1 < n
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)
      simp only [hk, zpow_natCast]
      exact ((contDiff_lm j).pow k).contDiffOn
    · exact zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _
  exact key.congr fun g hg => Set.indicator_of_mem hg _

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmoothStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_smooth : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | exact GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | (intros; apply GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.KHerm

variable {n : ℕ}

def skA (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

def skB (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b Complex.I + Matrix.single b a Complex.I)

theorem skA_skew (a b : Fin n) : (skA a b)ᴴ = -skA a b := by
  ext i j
  simp only [skA, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem skB_skew (a b : Fin n) : (skB a b)ᴴ = -skB a b := by
  ext i j
  simp only [skB, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have h1 : (Kf a b h).1 g = (e1 DR a b h).1 g - (f1 DR b a h).1 g := by
    simp [Kf, e2, sub_eq_add_neg]
  rw [h1, orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, liftOneFormsToCompatible_apply b a h hg]
  simp only [Eu, Rd, skA, skB, Pi.smul_apply, Pi.add_apply, ite_true, Bool.false_eq_true, ite_false,
    Matrix.mul_smul, mul_sub, mul_add, map_smul, map_sub, map_add, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem Rd_neg (X : Mat n) (f : Mat n → ℂ) (g : Mat n) : Rd (-X) f g = -Rd X f g := by
  simp [Rd]

theorem Kf_apply_swap (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf b a h).1 g = -Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have hA : skA b a = -skA a b := by
    simp only [skA, ← smul_neg, neg_sub]
  have hB : skB b a = skB a b := by
    simp only [skB, add_comm]
  rw [Kf_apply b a h hg, hA, hB, Rd_neg]

theorem Rd_conj_mul (X : Mat n) {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (fun g => conj (x g) * y g) g = conj (Rd X x g) * y g + conj (x g) * Rd X y g := by
  have dx := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hx hg).hasFDerivAt
  have dy := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hy hg).hasFDerivAt
  have dc : HasFDerivAt (fun g => conj (x g)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ x g)) g :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp g dx
  have hm : HasFDerivAt (fun g => conj (x g) * y g) _ g := dc.mul dy
  simp only [Rd]
  rw [hm.fderiv]
  change conj (x g) * fderiv ℝ y g (g * X) + y g * conj (fderiv ℝ x g (g * X)) = _
  ring

theorem conj_mul_smooth {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n)) :
    ContDiffOn ℝ ∞ (fun g => conj (x g) * y g) (GLs n) :=
  (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hx).mul hy

section Int

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

omit [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] in
theorem cont_on_unit {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => f k.1 :=
  hf.comp_continuous continuous_subtype_val fun k => unit_mem k

theorem integrable_of_cont {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Int

end GlobalTheory.CompanionTheory.ModelS.KHerm


open GlobalTheory.CompanionTheory.ModelS.KHerm in
theorem GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  intro n _ _ κ _ hI a b x y
  have hx := x.2.1
  have hy := y.2.1
  have i1 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (Rd X x.1 k.1) * y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hx).continuousOn)).mul (cont_on_unit hy.continuousOn))
  have i2 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * Rd X y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp (cont_on_unit hx.continuousOn)).mul
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hy).continuousOn))
  have key : ∀ X : Mat n, Xᴴ = -X → (∫ k, conj (Rd X x.1 k.1) * y.1 k.1 ∂κ) + ∫ k, conj (x.1 k.1) * Rd X y.1 k.1 ∂κ = 0 := by
    intro X hX
    rw [← integral_add (i1 X) (i2 X), ← hI _ (conj_mul_smooth hx hy) X hX]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => (Rd_conj_mul X hx hy (unit_mem k)).symm)
  have L : ipK κ (Kf a b x) y = (∫ k, conj (Rd (skA a b) x.1 k.1) * y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (Rd (skB a b) x.1 k.1) * y.1 k.1 ∂κ := by
    rw [← integral_const_mul, ← integral_add (i1 _) ((i1 _).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply a b x (unit_mem k), map_sub, map_mul, Complex.conj_I]
    ring
  have R : ipK κ x (Kf b a y) = -((∫ k, conj (x.1 k.1) * Rd (skA a b) y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (x.1 k.1) * Rd (skB a b) y.1 k.1 ∂κ) := by
    rw [← integral_const_mul, ← integral_add (i2 _) ((i2 _).const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply_swap a b y (unit_mem k)]
    ring
  rw [L, R]
  linear_combination key _ (skA_skew a b) + Complex.I * key _ (skB_skew a b)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2Statement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_action_skew_adjoint_l2 : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | exact GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | (intros; apply GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizer
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TorCent

theorem finite_roots_of_unity (M : Type) [Field M] [NumberField M] :
    {ζ : M | ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_
  rintro ζ ⟨k, hk, h⟩
  refine ⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩
  have h1 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  exact (Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le

theorem exists_distinct_roots {M : Type} [Field M] {n : ℕ} (A : Matrix (Fin n) (Fin n) M)
    (hs : A.charpoly.Separable) (hsp : A.charpoly.Splits) :
    ∃ z : Fin n → M, Function.Injective z ∧ A.charpoly = ∏ a, (X - C (z a)) := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 hsp
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  refine ⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩
  rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r),
    Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]

theorem eq_diagonal_of_commute {M : Type} [Field M] {n : ℕ} {z : Fin n → M}
    (hz : Function.Injective z) {F : Matrix (Fin n) (Fin n) M}
    (h : F * diagonal z = diagonal z * F) : F = diagonal fun i => F i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have h2 : F i j * (z j - z i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))

theorem finite_torsion_centralizer : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  intro E _ _ n N hsep
  let M := N.val.charpoly.SplittingField
  haveI : NumberField M := NumberField.of_module_finite E M
  let f : E →+* M := algebraMap E M
  let A : Matrix (Fin n) (Fin n) M := N.val.map f
  have hA : A.charpoly = N.val.charpoly.map f := charpoly_map _ _
  have hs : A.charpoly.Separable := by rw [hA]; exact hsep.map
  have hsp : A.charpoly.Splits := by rw [hA]; exact SplittingField.splits _
  obtain ⟨z, hz, hprod⟩ := exists_distinct_roots A hs hsp
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs
    (by rw [charpoly_diagonal, hprod])
  let B : Matrix (Fin n) (Fin n) M := x.val
  let Bi : Matrix (Fin n) (Fin n) M := (x⁻¹).val
  have hBB : B * Bi = 1 := by simp [B, Bi]
  have hBB' : Bi * B = 1 := by simp [B, Bi]
  have hx' : diagonal z * B = B * A := hx
  have hx2 : Bi * diagonal z = A * Bi := by
    calc Bi * diagonal z = Bi * (diagonal z * B) * Bi := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  let F : GL (Fin n) E → Matrix (Fin n) (Fin n) M := fun g => B * g.val.map f * Bi
  have hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g := by
    intro g hg
    have h1 : g.val * N.val = N.val * g.val := congrArg Units.val hg
    have h2 : g.val.map f * A = A * g.val.map f := by
      simp only [A]
      rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    simp only [F]
    calc B * g.val.map f * Bi * diagonal z = B * (g.val.map f * A) * Bi := by
          rw [Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = diagonal z * (B * g.val.map f * Bi) := by
          rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc, Matrix.mul_assoc]
  have hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k) := by
    intro g k
    induction k with
    | zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [F, Units.val_mul]
      rw [Matrix.map_mul]
      calc B * (g ^ k).val.map f * Bi * (B * g.val.map f * Bi)
          = B * (g ^ k).val.map f * (Bi * B) * g.val.map f * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let φ : GL (Fin n) E → Fin n → M := fun g i => F g i i
  have hfin := Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M
  refine Set.Finite.of_injOn (f := φ) ?_ ?_ hfin
  · rintro g ⟨hg, ho⟩ i
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
    refine ⟨k, hk, ?_⟩
    have h1 : F g ^ k = 1 := by
      rw [hFpow, hgk]; simp [F, hBB, Matrix.map_one]
    rw [eq_diagonal_of_commute hz (hFc g hg), diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [φ] using h2
  · rintro g ⟨hg, -⟩ g' ⟨hg', -⟩ e
    have h1 : F g = F g' := by
      rw [eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]
      exact congrArg diagonal e
    have h2 : g.val.map f = g'.val.map f := by
      have h3 : Bi * F g * B = Bi * F g' * B := by rw [h1]
      have h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y := fun Y => by
        calc Bi * (B * Y * Bi) * B = (Bi * B) * Y * (Bi * B) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      simpa only [F, h4] using h3
    refine Units.ext ?_
    ext i j
    exact f.injective (congrFun (congrFun h2 i) j)

end GlobalTheory.CompanionTheory.TorCent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizerStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_centralizer_alt : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | exact GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | (intros; apply GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariant
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  delta lm
  rw [h, Matrix.det_mul]

theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  delta gm lm
  rw [rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring

theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  delta gm
  rw [h, Matrix.det_one]

theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    delta muZ
    simp only [hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    delta yZ
    simp only [hlam, hmu]
  delta dif
  constructor
  · simp only [dite_eq_left h, hmu, sub_self]
  · simp only [dite_eq_left h, hy, sub_self]

theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  delta fRaw
  simp only [Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push Not at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariantStatement
open PositivityTheory.RgBcC (GLs)
open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (Pb fRaw)

theorem _root_.GlobalTheory.T.inducedFunction_parabolic_equivariant :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
      ∀ p ∈ Pb lev, ∀ g ∈ GLs n, fRaw lam lev (p * g) = fRaw lam lev p * fRaw lam lev g :=
  GlobalTheory.CompanionTheory.ModelS.FMul.fRaw_mul
end
end
