module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace DblVan

theorem vecMul_inv_inl {E : Type} [Field E] {N : ℕ} {γ : M2 E N} (hγ : IsUnit γ.det)
    {u : Fin N ⊕ Fin N → E} (hu : u ∈ botSpan γ) (a : Fin N) : (u ᵥ* γ⁻¹) (Sum.inl a) = 0 := by
  change u ∈ Submodule.span E (Set.range fun b : Fin N => γ (Sum.inr b)) at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx

    have hrow : (γ (Sum.inr b) ᵥ* γ⁻¹) (Sum.inl a) = (γ * γ⁻¹) (Sum.inr b) (Sum.inl a) := rfl
    rw [hrow, Matrix.mul_nonsing_inv γ hγ, Matrix.one_apply_ne (by simp)]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.smul_vecMul, Pi.smul_apply, hx, smul_zero]

theorem heisH_zero_apply_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (b : Matrix (Fin n) (Fin N) E) (ψ : Matrix (Fin n) (Fin N) E → ℂ) : heisH 0 b ψ 0 = ψ 0 := by
  simp [heisH, cc]

theorem toCols_eq_zero {E : Type} [Field E] {n N : ℕ} {γ T : M2 E N} (hγ : IsUnit γ.det)
    {ξ : Fin N → E} (hu : Sum.elim ξ 0 ᵥ* T ∈ botSpan γ) (v : Fin n → E) :
    (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹).toCols₁ = 0 := by
  ext k a
  rw [Matrix.toCols₁_apply, Matrix.zero_apply]

  have hrow : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T) k =
      v k • (Sum.elim ξ 0 ᵥ* T) := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vecMulVec_apply,
      Finset.mul_sum, mul_assoc]
  have hentry : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹) k
      (Sum.inl a) = ((v k • (Sum.elim ξ 0 ᵥ* T)) ᵥ* γ⁻¹) (Sum.inl a) := by
    rw [← hrow]; rfl
  rw [hentry]
  exact vecMul_inv_inl hγ (Submodule.smul_mem _ _ hu) a

end DblVan


open DblVan in
theorem weil_dbl_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂ ξ hker γ hγ hξ
  obtain ⟨s, a, hsum, hkill⟩ := hker
  have hΨ : IsType X.Ψ := X.cmType
  have hγu : IsUnit γ.det := (HAct.group_part hγ).1

  have hSBd : ∀ ψ : TF n g, IsSB ψ → IsSB (dbl X bas idx ψ φ₂) := fun ψ hψ =>
    (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn ψ φ₂ hψ h₂).1
  have hΦ := hSBd φ₁ h₁
  have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have hwadd : ∀ f f' : Matrix (Fin n) (Fin r) E → ℂ, IsSB f → IsSB f' →
      weil X.Ψ γ (f + f') = weil X.Ψ γ f + weil X.Ψ γ f' := fun f f' hf hf' =>
    ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.1 f' hf').2
  have hwsmul : ∀ (c : ℂ) (f : Matrix (Fin n) (Fin r) E → ℂ), IsSB f →
      weil X.Ψ γ (c • f) = c • weil X.Ψ γ f := fun c f hf =>
    (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.2.1 c

  have hdbl0 : dbl X bas idx (0 : TF n g) φ₂ = 0 := by
    have h := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1 0 1
    rwa [zero_smul, one_smul, zero_mul, zero_smul] at h
  have hw0 : weil X.Ψ γ (0 : Matrix (Fin n) (Fin r) E → ℂ) = 0 := by
    have h := hwsmul 0 _ hΦ
    rwa [zero_smul, zero_smul] at h

  have hone : ∀ v : Fin n → E, weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) 0 =
      weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 := by
    intro v
    have h3 := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.2 (vecMulVec v ξ) 0
    rw [(hG 0 φ₂ h₂).2.1] at h3
    rw [h3, (GlobalTheory.T.hermitianHeisenbergOperator_laws E X.Ψ hΨ n r hn _ _ _ hΦ).2.2 γ hγ, Matrix.fromCols_toCols,
      DblVan.toCols_eq_zero hγu hξ v, DblVan.heisH_zero_apply_zero]

  have hlin : ∀ t : Finset (Fin n → E),
      IsSB (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) ∧
      weil X.Ψ γ (dbl X bas idx (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) φ₂) =
        ∑ v ∈ t, a v • weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨isSB_zero, by rw [Finset.sum_empty, Finset.sum_empty, hdbl0, hw0]⟩
    | insert w t hw ih =>
      obtain ⟨hS, hval⟩ := ih
      have hGw := (hG (vecMulVec w ξ) φ₁ h₁).1
      have hcGw := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hGw hGw).2.1 (a w)
      rw [Finset.sum_insert hw, Finset.sum_insert hw]
      refine ⟨(isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hcGw hS).1, ?_⟩
      have hI := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hcGw h₂
      have hJ := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hGw h₂
      have hsm : dbl X bas idx (a w • heisG X bas (vecMulVec w ξ) φ₁) φ₂ =
          a w • dbl X bas idx (heisG X bas (vecMulVec w ξ) φ₁) φ₂ := by
        have h := hJ.2.1 (a w) 1
        rwa [one_smul, map_one, mul_one] at h
      rw [(hI.1 _ hS).1, hwadd _ _ (hSBd _ hcGw) (hSBd _ hS), hval, hsm,
        hwsmul _ _ (hSBd _ hGw)]

  have hmain := (hlin s).2
  rw [hkill, hdbl0, hw0] at hmain
  have h0 := congrFun hmain 0
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hone,
    ← Finset.sum_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left hsum

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZeroStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_doubledTestFunction_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  first | exact @GlobalTheory.SW.weil_dbl_zero_eq_zero | exact GlobalTheory.SW.weil_dbl_zero_eq_zero | (intros; apply GlobalTheory.SW.weil_dbl_zero_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraph
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraph
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem kZero_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom)
    (h₂ : x₂ ∈ X.dom) (z₁ w : Fin n → Fin g → ℂ) : kZero X idx x₁ x₂ z₁ w ≠ 0 := by
  unfold kZero
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero h₁ h₂ τ)
    (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

private theorem isUn_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : IsUn X (1 : GL (Fin r) E) := by
  unfold IsUn
  intro x y
  simp

theorem eisTerm_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  intro E _ _ _ r X g bas idx n hs hn γ hγ φ₁ φ₂ h₁ h₂ x₁ hx₁ x₂ hx₂ z₁ w

  obtain ⟨hsb₂, hth₂, -⟩ := wG_laws E r X g bas idx n hs hn γ hγ φ₂ h₂
  have hγx₂ : lact γ x₂ ∈ X.dom := IsUn.lact_mem hγ hx₂
  obtain ⟨hT, hZ', -⟩ := dblZ_mem_Hn E r X x₁ hx₁ (lact γ x₂) hγx₂
  have hZ : dblZ X x₁ x₂ ∈ Hn X.Ψ r := (dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂).2.1

  obtain ⟨hU, a, ha, hact⟩ := iota_act_dbl E r X g bas idx n hs hn 1 γ (isUn_one' X) hγ
  obtain ⟨hA, hzz⟩ := hact x₁ hx₁ x₂ hx₂
  have e1 : lact (1 : GL (Fin r) E) x₁ = x₁ := UnAct.lact_one' x₁
  simp only [e1] at hA hzz

  obtain ⟨hΦ, hΦd, -⟩ := DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  obtain ⟨hΦ', hΦ'd, -⟩ :=
    DblEx.dbl_spec E r X g bas idx n hs hn φ₁ (wG X bas idx γ φ₂) h₁ hsb₂
  obtain ⟨hW, hWT, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hT n r hn (iota X 1 γ) hU (dbl X bas idx φ₁ φ₂) hΦ

  have key : ∀ u v : Fin n → Fin g → ℂ,
      thH X.Ψ (weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) =
        a * thH X.Ψ (dbl X bas idx φ₁ (wG X bas idx γ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) := by
    intro u v
    obtain ⟨hz, hz', hk⟩ := hzz u v
    have d1 := hΦd x₁ hx₁ x₂ hx₂ u v
    have d2 := hΦ'd x₁ hx₁ (lact γ x₂) hγx₂ u v
    have t2 : thA X bas idx (wG X bas idx γ φ₂) (lact γ x₂) = thA X bas idx φ₂ x₂ :=
      hth₂ x₂ hx₂
    rw [t2, d1] at d2
    have tw := hWT (dblZ X x₁ x₂) hZ (dblz X idx x₁ x₂ u v) (dblz' X idx x₁ x₂ u v)
    rw [hA, ← hz, ← hz'] at tw
    have hK' := kZero_ne_zero X idx hx₁ hγx₂ u v
    apply mul_left_cancel₀ hK'
    rw [tw, ← mul_assoc, hk, mul_assoc, d2]
    ring

  have hW' : weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) =
      a • dbl X bas idx φ₁ (wG X bas idx γ φ₂) := by
    refine (thH_summable_and_inj E X.Ψ hT n r _ hW _ hZ').2 _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ hΦ' hΦ').2.1 a) ?_
    intro z z'
    obtain ⟨u, v, rfl, rfl⟩ := DblEx.dblz_surj E r X g idx n x₁ hx₁ (lact γ x₂) hγx₂ z z'
    rw [key u v]
    unfold thH
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left]

  obtain ⟨-, -, hk⟩ := hzz z₁ w
  have hK := kZero_ne_zero X idx hx₁ hx₂ z₁ w
  have hH : hFac X.Ψ (iota X 1 γ) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w)
      (dblz' X idx x₁ x₂ z₁ w) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact mul_ne_zero ha hK hk.symm
  unfold eisTerm
  rw [hW', Pi.smul_apply, smul_eq_mul, ← mul_inv_cancel_right₀ hH
    (kZero X idx x₁ (lact γ x₂) z₁ w), hk]
  field_simp

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraphStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinSeries_term_unitary_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  first | exact @GlobalTheory.SW.eisTerm_graph | exact GlobalTheory.SW.eisTerm_graph | (intros; apply GlobalTheory.SW.eisTerm_graph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivConstMul
open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Real Topology
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.KernSum

section Tame

variable {ι : Type} {a : ι → ℝ}

def Tame (a x : ι → ℝ) : Prop := ∀ c : ℝ, 0 ≤ c → Summable fun i => a i * Real.exp (c * x i)

theorem Tame.of_le_max (ha : ∀ i, 0 ≤ a i) {x y z : ι → ℝ} (hx : Tame a x) (hy : Tame a y)
    {k : ℝ} (hk : 0 ≤ k) (h : ∀ i, z i ≤ k * x i ∨ z i ≤ k * y i) : Tame a z := by
  intro c hc
  refine ((hx (c * k) (mul_nonneg hc hk)).add (hy (c * k) (mul_nonneg hc hk))).of_nonneg_of_le
    (fun i => mul_nonneg (ha i) (Real.exp_pos _).le) fun i => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (ha i)
  rcases h i with h | h
  · refine le_add_of_le_of_nonneg (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hc
  · refine le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hc

theorem Tame.add (ha : ∀ i, 0 ≤ a i) {x y : ι → ℝ} (hx : Tame a x) (hy : Tame a y) :
    Tame a fun i => x i + y i :=
  hx.of_le_max ha hy zero_le_two fun i => by
    rcases le_total (x i) (y i) with h | h
    · right; linarith
    · left; linarith

theorem Tame.abs (ha : ∀ i, 0 ≤ a i) {x : ι → ℝ} (hx : Tame a x) (hy : Tame a fun i => -x i) :
    Tame a fun i => |x i| :=
  hx.of_le_max ha hy zero_le_one fun i => by
    rcases abs_cases (x i) with h | h
    · left; linarith [h.1]
    · right; linarith [h.1]

theorem Tame.sum (ha : ∀ i, 0 ≤ a i) (h0 : Summable a) {κ : Type} (s : Finset κ) {x : κ → ι → ℝ}
    (hx : ∀ k, Tame a (x k)) : Tame a fun i => ∑ k ∈ s, x k i := by
  classical
  induction s using Finset.induction_on with
  | empty => intro c _; simpa using h0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hx k).add ha ih

end Tame

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem exists_majorant {ι : Type} (A : ι → ℂ) (B : ι → W →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (h : ∀ v, Summable fun i => A i * cexp (B i v v)) (R : ℝ) :
    ∃ u : ι → ℝ, Summable u ∧ ∀ i v, ‖v‖ ≤ R → ‖A i * cexp (B i v v)‖ ≤ u i := by
  have ha : ∀ i, 0 ≤ ‖A i‖ := fun i => norm_nonneg _
  have h0 : Summable fun i => ‖A i‖ := by simpa using (h 0).norm
  have h1 (ζ : ℂ) (t : W) : Tame (fun i => ‖A i‖) fun i => (ζ * B i t t).re := by
    intro c _
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((c : ℂ) * ζ) two_pos
    refine (h (s • t)).norm.congr fun i => ?_
    rw [norm_mul, norm_exp]
    congr 2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← sq, hs, mul_assoc, re_ofReal_mul]
  have h2 (t : W) : Tame (fun i => ‖A i‖) fun i => ‖B i t t‖ := by
    have e1 := Tame.abs ha (h1 1 t) (by simpa using h1 (-1) t)
    have e2 := Tame.abs ha (h1 I t) (by simpa using h1 (-I) t)
    refine (e1.add ha e2).of_le_max ha e1 zero_le_one fun i => Or.inl ?_
    simpa using norm_le_abs_re_add_abs_im (B i t t)
  let b := Module.finBasis ℂ W
  let K : ℝ := ‖b.equivFunL.toContinuousLinearMap‖ * |R|
  have h3 := Tame.sum ha h0 Finset.univ fun j => Tame.sum ha h0 Finset.univ fun k =>
    (h2 (b j + b k)).add ha (h2 (b j - b k))
  refine ⟨_, h3 (K * K) (mul_self_nonneg K), fun i v hv => ?_⟩
  rw [norm_mul, norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((re_le_norm _).trans ?_)) (ha i)
  have hK (j) : ‖b.repr v j‖ ≤ K :=
    ((norm_le_pi_norm (b.equivFunL v) j).trans (b.equivFunL.toContinuousLinearMap.le_opNorm v)).trans
      (mul_le_mul_of_nonneg_left (hv.trans (le_abs_self R)) (norm_nonneg _))
  have e : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k * B i (b j) (b k) := by
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e' : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k *
      ((B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k)) / 4) := by
    have e2 := e
    rw [Finset.sum_comm] at e2
    rw [← add_self_div_two (B i v v), congrArg₂ (· + ·) e e2, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  rw [e', Finset.mul_sum]
  refine norm_sum_le_of_le _ fun j _ => ?_
  rw [Finset.mul_sum]
  refine norm_sum_le_of_le _ fun k _ => ?_
  rw [norm_mul, norm_mul]
  refine mul_le_mul (mul_le_mul (hK j) (hK k) (norm_nonneg _) ((norm_nonneg _).trans (hK j))) ?_
    (norm_nonneg _) (mul_self_nonneg K)
  rw [norm_div]
  have := norm_sub_le (B i (b j + b k) (b j + b k)) (B i (b j - b k) (b j - b k))
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  linarith [norm_nonneg (B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k))]

variable {σ : Type}

noncomputable def bd (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W × W → ℂ) : ℂ :=
  I2.polyDeriv P u (fun z => I2.polyDeriv Q u (fun w => F (z, w)) 0) 0

theorem bd_hasSum (P Q : MvPolynomial σ ℂ) (u : σ → W) {ι : Type} {F : ι → W × W → ℂ}
    {S : W × W → ℂ} (hF : ∀ i p, AnalyticAt ℂ (F i) p) (hS : ∀ p, HasSum (fun i => F i p) (S p))
    (hu : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧ ∀ i p, ‖p‖ ≤ R → ‖F i p‖ ≤ u i) :
    (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun i => bd P Q u (F i)) (bd P Q u S) := by
  obtain rfl : S = fun p => ∑' i, F i p := funext fun p => (hS p).tsum_eq.symm
  have hd : ∀ i, DifferentiableOn ℂ (F i) Set.univ := fun i p _ =>
    (hF i p).differentiableAt.differentiableWithinAt
  have hle : ∀ x ∈ (Set.univ : Set (W × W)), ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i := fun x _ => by
    obtain ⟨u, h1, h2⟩ := hu (‖x‖ + 1)
    exact ⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (by simp), u, h1,
      fun i z hz => h2 i z (mem_ball_zero_iff.1 hz).le⟩
  have ha : ∀ p, AnalyticAt ℂ (fun p => ∑' i, F i p) p := fun p =>
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ
      (SCV.differentiableOn_tsum_of_locally_normal isOpen_univ hd hle) p trivial
  refine ⟨ha, ?_⟩
  simp only [bd, KernSym.polyDeriv_polyDeriv P Q u ha, KernSym.polyDeriv_polyDeriv P Q u (hF _),
    lineDerivList_eq_iteratedFDeriv (ha _), lineDerivList_eq_iteratedFDeriv (hF _ _)]
  refine hasSum_sum fun m _ => hasSum_sum fun m' _ => HasSum.mul_left _ ?_
  exact (ContinuousMultilinearMap.apply ℂ _ ℂ _).hasSum
    (SCV.hasSum_iteratedFDeriv_of_locally_normal isOpen_univ hd hle _ (Set.mem_univ 0))

omit [FiniteDimensional ℂ W] in
theorem bd_add (P Q : MvPolynomial σ ℂ) (u : σ → W) {F G : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) (hG : ∀ p, AnalyticAt ℂ G p) :
    bd P Q u (fun p => F p + G p) = bd P Q u F + bd P Q u G := by
  have h : ∀ p, AnalyticAt ℂ (fun p => F p + G p) p := fun p => (hF p).add (hG p)
  rw [bd, bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF,
    KernSym.polyDeriv_polyDeriv P Q u hG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [← mul_add, ← lineDerivList_add (hF 0) (hG 0)]

omit [FiniteDimensional ℂ W] in
theorem bd_sum (P Q : MvPolynomial σ ℂ) (u : σ → W) {κ : Type} (s : Finset κ) {F : κ → W × W → ℂ}
    (hF : ∀ k p, AnalyticAt ℂ (F k) p) :
    bd P Q u (fun p => ∑ k ∈ s, F k p) = ∑ k ∈ s, bd P Q u (F k) := by
  have h : ∀ p, AnalyticAt ℂ (fun p => ∑ k ∈ s, F k p) p := fun p =>
    Finset.analyticAt_fun_sum _ fun k _ => hF k p
  simp only [bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u (hF _),
    lineDerivList_sum s fun k _ => hF k 0, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]

omit [FiniteDimensional ℂ W] in
theorem bd_const_mul (P Q : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) : bd P Q u (fun p => c * F p) = c * bd P Q u F := by
  have h : ∀ p, AnalyticAt ℂ (fun p => c * F p) p := fun p => analyticAt_const.mul (hF p)
  rw [bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  have := congrFun (lineDerivList_const_smul (List.map (fun s => (u s, 0)) (KernSym.lst m) ++
    List.map (fun s => (0, u s)) (KernSym.lst m')) c F) 0
  simp only [smul_eq_mul] at this
  rw [this]; ring

omit [FiniteDimensional ℂ W] in
theorem polyDeriv_const_mul (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {F : W → ℂ}
    (hF : AnalyticAt ℂ F 0) : I2.polyDeriv P u (fun p => c * F p) 0 = c * I2.polyDeriv P u F 0 := by
  rw [KernSym.polyDeriv_eq_sum_list _ _ hF,
    KernSym.polyDeriv_eq_sum_list _ _ (F := fun p => c * F p) (analyticAt_const.mul hF),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have := congrFun (lineDerivList_const_smul (List.map u (KernSym.lst m)) c F) 0
  simp only [smul_eq_mul] at this
  rw [this]; ring

variable [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W]

theorem analyticAt_conj {h : W → ℂ} (hh : ∀ p, AnalyticAt ℂ h p) (p : W) :
    AnalyticAt ℂ (fun w => conj (h (star w))) p := by
  refine SCV.analyticAt_iff_eventually_differentiableAt.2 (.of_forall fun q => ?_)
  simpa [Function.comp_def] using (hh (star q)).differentiableAt.star_star

theorem bd_prod (P Q : MvPolynomial σ ℂ) (u : σ → W) (hu : ∀ s, star (u s) = u s) {f h : W → ℂ}
    (hf : ∀ p, AnalyticAt ℂ f p) (hh : ∀ p, AnalyticAt ℂ h p) :
    bd P (barP Q) u (fun p => f p.1 * conj (h (star p.2))) =
      I2.polyDeriv P u f 0 * conj (I2.polyDeriv Q u h 0) := by
  have h1 : I2.polyDeriv (barP Q) u (fun w => conj (h (star w))) 0 = conj (I2.polyDeriv Q u h 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [KernSym.polyDeriv_eq_sum_list _ _ (analyticAt_conj hh 0),
      KernSym.polyDeriv_eq_sum_list _ _ (hh 0), map_sum, barP,
      MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [KernSym.lineDerivList_conj _ (by
      simp only [List.mem_map]
      rintro v ⟨s, -, rfl⟩
      exact hu s), MvPolynomial.coeff_map, map_mul]
    simp only [star_zero]
  simp only [bd, polyDeriv_const_mul _ _ _ (analyticAt_conj hh 0), h1]
  simp only [mul_comm (f _)]
  rw [polyDeriv_const_mul _ _ _ (hf 0), mul_comm]

private noncomputable def quadPoint {r : ℕ} (κ : ℂ) (G S A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := (κ / 4) • ((A⁻¹ * S * A)ᵀ * G)

private noncomputable def quadMatrix {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (-(τ.1 X.κ0 / 2) * (τ.1 X.κ0 / 2)) •
    ((aLin X x₁ x₂ τ)⁻¹ᵀ * X.Gm.map τ.1 *
      (imH (quadPoint (τ.1 X.κ0) (X.Gm.map τ.1) (-sgnM X) (aLin X x₁ x₂ τ)))⁻¹ *
      X.Gm.map τ.1 * (aAnti X x₁ x₂ τ)⁻¹)

private theorem kZero_quad_expansion {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r g n : ℕ} (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ *
        cexp (Real.pi * ∑ k, KernSym.mixV X idx τ (w k) (z k) ⬝ᵥ
          quadMatrix X x₁ x₂ τ *ᵥ KernSym.mixV X idx τ (z k) (w k)) := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : dblZ X x₁ x₂ τ = quadPoint (τ.1 X.κ0) (X.Gm.map τ.1) (-sgnM X)
      (aLin X x₁ x₂ τ) := by
    rw [quadPoint, sgnM, diagonal_neg]
    rfl
  rw [h, quadMatrix]
  change ((τ.1 X.κ0 / 2) • (((aLin X x₁ x₂ τ)⁻¹ *ᵥ KernSym.mixV X idx τ (w k) (z k)) ᵥ* X.Gm.map τ.1)) ⬝ᵥ
    (imH (quadPoint (τ.1 X.κ0) (X.Gm.map τ.1) (-sgnM X) (aLin X x₁ x₂ τ)))⁻¹ *ᵥ
    ((-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ (aAnti X x₁ x₂ τ)⁻¹ *ᵥ KernSym.mixV X idx τ (z k) (w k))) = _
  rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_mulVec, dotProduct_smul, smul_smul,
    mul_comm, ← vecMul_transpose, ← dotProduct_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem kZero_quad {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x₁ x₂ : Frame X.Ψ r) :
    ∃ (A : ℂ) (B : ((Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ)) →ₗ[ℂ]
      ((Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ)) →ₗ[ℂ] ℂ),
      ∀ p, kZero X idx x₁ x₂ p.1 p.2 = A * cexp (B p p) := by
  have ha (τ) (z w z' w' : Fin g → ℂ) : KernSym.mixV X idx τ (z + z') (w + w') =
      KernSym.mixV X idx τ z w + KernSym.mixV X idx τ z' w' := by
    funext a; simp only [KernSym.mixV, Pi.add_apply]; split_ifs <;> rfl
  have hs (τ) (c : ℂ) (z w : Fin g → ℂ) : KernSym.mixV X idx τ (c • z) (c • w) =
      c • KernSym.mixV X idx τ z w := by
    funext a; simp only [KernSym.mixV, Pi.smul_apply]; split_ifs <;> rfl
  refine ⟨∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹,
    LinearMap.mk₂ ℂ (fun p q => ∑ τ : X.Ψ, Real.pi * ∑ k,
    KernSym.mixV X idx τ (p.2 k) (p.1 k) ⬝ᵥ quadMatrix X x₁ x₂ τ *ᵥ
      KernSym.mixV X idx τ (q.1 k) (q.2 k)) ?_ ?_ ?_ ?_, fun p => ?_⟩
  rotate_right
  · rw [kZero_quad_expansion, Finset.prod_mul_distrib, ← Complex.exp_sum]
    rfl
  · intro p p' q
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, add_dotProduct,
      Finset.sum_add_distrib, mul_add]
  · intro c p q
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, smul_dotProduct, smul_eq_mul,
      Finset.mul_sum, mul_left_comm c]
  · intro p q q'
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, mulVec_add, dotProduct_add,
      Finset.sum_add_distrib, mul_add]
  · intro c p q
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, mulVec_smul, dotProduct_smul,
      smul_eq_mul, Finset.mul_sum, mul_left_comm c]

end GlobalTheory.SW.KernSum
end

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace KernSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}

theorem isSB_wG (γ : GL (Fin r) E) (φ : TF n g) : IsSB (wG X bas idx γ φ) := by
  unfold wG
  split_ifs with h
  · exact h.choose_spec.1
  · exact isSB_zero

theorem ip_smul_right {φ ψ : TF n g} (hφ : IsSB φ) (hψ : IsSB ψ) (c : ℂ) :
    ip φ (c • ψ) = ip φ ψ * conj c := by
  obtain ⟨-, -, -, hcψ, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) ψ ψ hψ hψ
  obtain ⟨-, -, hprod, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) φ _ hφ hcψ
  obtain ⟨-, -, -, -, -, hsmul, -⟩ := GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hprod hprod
  have e : (fun x => φ x * conj ((c • ψ) x)) = conj c • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  unfold ip
  rw [e, hsmul, mul_comm]
  rfl

theorem hasSum_eis (hb : IsSympl X bas) (hn : Even n) (h4 : 4 * r < n) {M : ℕ}
    {Δ : Subgroup (GL (Fin r) E)} {𝓛 : Set (Lt E r)} {Φ : Lt E r → Lt E n → TF n g}
    {μ : GL (Fin r) E → Lt E r → ℂ} (hS : IsSystem X bas idx M Δ 𝓛 Φ μ) {a : ℂ}
    (ha : ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂)
    {L₁ L₂ : Lt E r} (h₁ : L₁ ∈ 𝓛) (h₂ : L₂ ∈ 𝓛) {x₁ x₂ : Frame X.Ψ r} (hx₁ : x₁ ∈ X.dom)
    (hx₂ : x₂ ∈ X.dom) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) (z w : Fin n → Fin g → ℂ) :
    HasSum (fun γ : Δ => a * ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ) * conj (μ γ L₂) *
        kZero X idx x₁ (lact γ x₂) z w)
      (kZero X idx x₁ x₂ z w * eis X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)) := by
  set φ₁ := Φ L₁ Λ with hφ₁def
  set φ₂ := Φ L₂ Λ with hφ₂def
  have hφ₁ : IsSB φ₁ := hS.sb L₁ h₁ Λ hΛ
  have hφ₂ : IsSB φ₂ := hS.sb L₂ h₂ Λ hΛ
  have hψ : IsSB (dbl X bas idx φ₁ φ₂) := (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hb hn φ₁ φ₂ hφ₁ hφ₂).1
  obtain ⟨hT, hZ, -⟩ := GlobalTheory.SW.dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂
  have hsum := (GlobalTheory.SW.eis_automorphy_linear E X.Ψ hT n r hn h4 _ hψ _ hZ).1
    (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)
  have hU := (hsum.of_norm.hasSum).mul_left (kZero X idx x₁ x₂ z w)
  have hun1 : IsUn X (1 : GL (Fin r) E) := by
    intro u v
    simp
  let lagOf : Δ → Lag E r := fun γ =>
    ⟨botSpan (iota X 1 γ), iota X 1 γ, DblPair.iota_mem X hun1 (hS.un γ γ.2), rfl⟩
  have hinj : Function.Injective lagOf := by
    intro γ γ' h
    have h' : botSpan (iota X 1 (γ : GL (Fin r) E)) = botSpan (iota X 1 (γ' : GL (Fin r) E)) :=
      congrArg Subtype.val h
    exact Subtype.ext ((GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic E r X).1 γ γ' (hS.un γ γ.2) (hS.un γ' γ'.2) h')
  have hterm : ∀ γ : GL (Fin r) E, IsUn X γ → ∀ U : Lag E r, botSpan (iota X 1 γ) = U.1 →
      kZero X idx x₁ x₂ z w * eisTerm X.Ψ U.2.choose (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w) =
      a * ip φ₁ (wG X bas idx γ φ₂) * kZero X idx x₁ (lact γ x₂) z w := by
    intro γ hγ U hUγ
    have e1 := (GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E X.Ψ hT n r hn _ hψ).2 U.2.choose U.2.choose_spec.1 (iota X 1 γ)
      (DblPair.iota_mem X hun1 hγ) (U.2.choose_spec.2.trans hUγ.symm) _ hZ
      (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w)
    have e2 := GlobalTheory.T.eisensteinSeries_term_unitary_graph E r X g bas idx n hb hn γ hγ φ₁ φ₂ hφ₁ hφ₂ x₁ hx₁ x₂ hx₂ z w
    have e3 := ha φ₁ _ hφ₁ (isSB_wG (X := X) (bas := bas) (idx := idx) γ φ₂)
    rw [e1, e2, e3]
  have hzero : ∀ U ∉ Set.range lagOf, kZero X idx x₁ x₂ z w * eisTerm X.Ψ U.2.choose
      (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z w) (dblz' X idx x₁ x₂ z w) = 0 := by
    intro U hU'
    rcases (GlobalTheory.T.maximalIsotropic_doubled_graph_or_isotropic E r X).2 U with ⟨γ, hγ, hUγ⟩ | ⟨ξ, hξ0, hξ, hmem⟩
    · have hγΔ : γ ∉ Δ := fun hΔ => hU' ⟨⟨γ, hΔ⟩, Subtype.ext hUγ⟩
      have e1 := hterm γ hγ U hUγ
      have e2 := hS.supp γ hγ hγΔ L₁ h₁ L₂ h₂ Λ hΛ
      rw [e1, e2]
      ring
    · have hw : weil X.Ψ U.2.choose (dbl X bas idx φ₁ φ₂) 0 = 0 :=
        GlobalTheory.T.weil_doubledTestFunction_zero_eq_zero E r X g bas idx n hb hn φ₁ φ₂ hφ₁ hφ₂ ξ (hS.cusp ξ hξ0 hξ L₁ h₁ Λ hΛ)
          U.2.choose U.2.choose_spec.1 (by rw [U.2.choose_spec.2]; exact hmem)
      unfold eisTerm
      rw [hw]
      ring
  have hmain := (hinj.hasSum_iff hzero).2 hU
  unfold eis
  convert hmain using 1
  funext γ
  have hΦ' : IsSB (Φ (mapL γ L₂) Λ) := hS.sb _ (hS.stab γ γ.2 L₂ h₂) Λ hΛ
  have e1 := hterm γ (hS.un γ γ.2) (lagOf γ) rfl
  have e2 := (hS.mu γ γ.2 L₂ h₂).2 Λ hΛ
  have e3 := ip_smul_right hφ₁ hΦ' (μ γ L₂)
  simp only [Function.comp_apply]
  rw [e1, e2, e3]
  ring

end KernSum

private theorem analyticAt_mul_cexp_bilin_diag {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (A : ℂ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (p : V) :
    AnalyticAt ℂ (fun v => A * cexp (B v v)) p := by
  let B' : V →L[ℂ] V →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B)
  have h0 : AnalyticAt ℂ (fun v : V => (v, v)) p := analyticAt_id.prod analyticAt_id
  have h1 : AnalyticAt ℂ (fun v : V => B' v v) p := AnalyticAt.comp (g := fun x : V × V => B' x.1 x.2)
    (f := fun v : V => (v, v)) (B'.analyticAt_bilinear (p, p)) h0
  exact analyticAt_const.mul h1.cexp

private theorem analyticAt_and_hasSum_bd_of_hasSum_gaussian {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {σ : Type} (P Q : MvPolynomial σ ℂ) (u : σ → W) {ι : Type}
    (F : ι → W × W → ℂ) (S : W × W → ℂ) (A : ι → ℂ) (B : ι → (W × W) →ₗ[ℂ] (W × W) →ₗ[ℂ] ℂ)
    (hF : ∀ i p, F i p = A i * cexp (B i p p)) (hS : ∀ p, HasSum (fun i => F i p) (S p)) :
    (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun i => KernSum.bd P Q u (F i)) (KernSum.bd P Q u S) := by
  have hFa : ∀ i p, AnalyticAt ℂ (F i) p := by
    intro i p
    have e : F i = fun v => A i * cexp (B i v v) := funext (hF i)
    rw [e]
    exact analyticAt_mul_cexp_bilin_diag (A i) (B i) p
  refine KernSum.bd_hasSum P Q u hFa hS fun R => ?_
  have hsum : ∀ v, Summable fun i => A i * cexp (B i v v) := by
    intro v
    have e : (fun i => A i * cexp (B i v v)) = fun i => F i v := funext fun i => (hF i v).symm
    rw [e]
    exact (hS v).summable
  obtain ⟨v, hv, hle⟩ := KernSum.exists_majorant A B hsum R
  refine ⟨v, hv, fun i p hp => ?_⟩
  rw [hF i p]
  exact hle i p hp

private theorem analyticAt_mul_conj_comp_star_prod {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W] {f h : W → ℂ}
    (hf : ∀ p, AnalyticAt ℂ f p) (hh : ∀ p, AnalyticAt ℂ h p) (p : W × W) :
    AnalyticAt ℂ (fun q : W × W => f q.1 * conj (h (star q.2))) p := by
  have h1 : AnalyticAt ℂ (fun q : W × W => f q.1) p := (hf p.1).comp analyticAt_fst
  have h2 : AnalyticAt ℂ (fun q : W × W => conj (h (star q.2))) p :=
    (KernSum.analyticAt_conj hh p.2).comp analyticAt_snd
  exact h1.mul h2

private theorem bd_sum_prod_lemma_4 {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W] {σ : Type}
    (P : MvPolynomial σ ℂ) (u : σ → W) (hu : ∀ s, star (u s) = u s) {κ : Type} [Fintype κ]
    (wv : κ → ℂ) (f h : κ → W → ℂ) (hf : ∀ k p, AnalyticAt ℂ (f k) p)
    (hh : ∀ k p, AnalyticAt ℂ (h k) p) :
    (∀ p, AnalyticAt ℂ (fun q : W × W => ∑ k, wv k * (f k q.1 * conj (h k (star q.2)))) p) ∧
      KernSum.bd P (barP P) u (fun q : W × W => ∑ k, wv k * (f k q.1 * conj (h k (star q.2)))) =
        ∑ k, wv k * (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (f k) 0 *
          conj (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (h k) 0)) := by
  have hA : ∀ k p, AnalyticAt ℂ (fun q : W × W => wv k * (f k q.1 * conj (h k (star q.2)))) p :=
    fun k p => analyticAt_const.mul (analyticAt_mul_conj_comp_star_prod (hf k) (hh k) p)
  refine ⟨fun p => ?_, ?_⟩
  · have h1 := Finset.analyticAt_sum (𝕜 := ℂ) (Finset.univ : Finset κ) fun k _ => hA k p
    rw [Finset.sum_fn] at h1
    exact h1
  · rw [KernSum.bd_sum P (barP P) u Finset.univ fun k => hA k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [KernSum.bd_const_mul P (barP P) u (wv k) fun p => analyticAt_mul_conj_comp_star_prod (hf k) (hh k) p,
      KernSum.bd_prod P P u hu (hf k) (hh k)]


open KernSum in
theorem kernel_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * r < n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ a : ℂ, a ≠ 0 ∧ ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ), ∀ (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') → InvFam P → ∀ L₁ ∈ 𝓛, ∀ L₂ ∈ 𝓛, ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, HasSum (fun γ : Δ => a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂) * kern X hr idx P x₁ (lact γ x₂)) (classSum M (fun Λ => ∑ j, thP X hr bas idx (Φ L₁ Λ) (P j) x₁ * conj (thP X hr bas idx (Φ L₂ Λ) (P j) x₂))) := by
  intro E _ _ _ r X g q0 hr bas idx n hb hn h4 M Δ 𝓛 Φ μ hM hS
  obtain ⟨a, ha0, b, -, hab⟩ := GlobalTheory.T.doubledHermitianTestFunction_zero_and_norm E r X g bas idx n hb hn
  refine ⟨a, ha0, ?_⟩
  intro c c' m P hP hInv L₁ h₁ L₂ h₂ x₁ hx₁ x₂ hx₂
  have ha : ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂ :=
    fun φ₁ φ₂ e₁ e₂ => (hab φ₁ φ₂ e₁ e₂).1
  have hT : IsType X.Ψ := Base.isType_data X
  have : Fintype (Cls E n M) := @Fintype.ofFinite _ (finite_cls_and_stab E n M hM).1
  have hcs : ∀ f : Lt E n → ℂ, classSum M f =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * f (Quot.out cl).1 :=
    fun f => finsum_eq_sum_of_fintype _
  have hu : ∀ s : Harm.Var X.Ψ q0 X.p0 (Fin n), star (letterDir X hr idx s) = letterDir X hr idx s := by
    intro s
    funext k i
    unfold letterDir
    simp only [Pi.star_apply, Pi.single_apply]
    split_ifs
    · simp only [Pi.single_apply]
      split_ifs <;> simp
    · simp
  have hφ : ∀ (L : Lt E r), L ∈ 𝓛 → ∀ cl : Cls E n M, IsSB (Φ L (Quot.out cl).1) :=
    fun L hL cl => hS.sb L hL _ (Quot.out cl).2
  have hthA : ∀ (j : Fin m) (L : Lt E r), L ∈ 𝓛 → ∀ cl : Cls E n M, ∀ x ∈ X.dom, ∀ p,
      AnalyticAt ℂ (thA X bas idx (Φ L (Quot.out cl).1) x) p := by
    intro j L hL cl x hx p
    exact (GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight E r X g q0 hr bas idx n hb hn c c' _ (hφ L hL cl) (P j) (hP j)).2.2.2
      x hx p (Set.mem_univ p)
  have hq := fun γ : Δ => KernSum.kZero_quad (n := n) X idx x₁ (lact (γ : GL (Fin r) E) x₂)
  choose A B hAB using hq
  have hK0 : ∀ γ : Δ, ∀ p, AnalyticAt ℂ (fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) q.1 q.2) p := by
    intro γ p
    have e : (fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
        kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) q.1 q.2) = fun q => A γ * cexp (B γ q q) :=
      funext (hAB γ)
    rw [e]
    exact analyticAt_mul_cexp_bilin_diag (A γ) (B γ) p
  obtain ⟨S, hSd⟩ : ∃ S : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) → ℂ, ∀ p, S p =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * (kZero X idx x₁ x₂ p.1 p.2 *
        eis X.Ψ (dbl X bas idx (Φ L₁ (Quot.out cl).1) (Φ L₂ (Quot.out cl).1)) (dblZ X x₁ x₂)
          (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2)) := ⟨_, fun p => rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) → ℂ, ∀ p, T p =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) *
        (thA X bas idx (Φ L₁ (Quot.out cl).1) x₁ p.1 *
          conj (thA X bas idx (Φ L₂ (Quot.out cl).1) x₂ (star p.2))) := ⟨_, fun p => rfl⟩
  have hpt : ∀ p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ), HasSum (fun γ : Δ =>
      (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
        kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) (S p) := by
    intro p
    have h := hasSum_sum (s := (Finset.univ : Finset (Cls E n M))) fun cl _ =>
      (KernSum.hasSum_eis hb hn h4 hS ha h₁ h₂ hx₁ hx₂ (Quot.out cl).2 p.1 p.2).mul_left
        (wt M (Quot.out cl).1 : ℂ)
    have e : ∀ γ : Δ, (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) *
        conj (μ γ L₂)) * kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2 =
        ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) * (a * ip (Φ L₁ (Quot.out cl).1)
          (Φ (mapL γ L₂) (Quot.out cl).1) * conj (μ γ L₂) *
            kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := by
      intro γ
      rw [hcs, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cl _ => ?_
      ring
    simp only [e]
    rw [hSd p]
    exact h
  have hHS : ∀ j, (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun γ : Δ =>
      KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) (fun p =>
        (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
          kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2))
      (KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S) := by
    intro j
    refine analyticAt_and_hasSum_bd_of_hasSum_gaussian (P j) (barP (P j)) (letterDir X hr idx) _ S
      (fun γ => (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) * A γ)
      B (fun γ p => ?_) hpt
    beta_reduce
    rw [hAB γ p]
    ring
  have eT : T = fun q : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      ∑ cl : Cls E n M, (fun cl => (wt M (Quot.out cl).1 : ℂ)) cl *
        ((fun cl => thA X bas idx (Φ L₁ (Quot.out cl).1) x₁) cl q.1 *
          conj ((fun cl => thA X bas idx (Φ L₂ (Quot.out cl).1) x₂) cl (star q.2))) :=
    funext hTd
  have hTP := fun j : Fin m => bd_sum_prod_lemma_4 (P j) (letterDir X hr idx) hu
    (fun cl : Cls E n M => (wt M (Quot.out cl).1 : ℂ))
    (fun cl => thA X bas idx (Φ L₁ (Quot.out cl).1) x₁)
    (fun cl => thA X bas idx (Φ L₂ (Quot.out cl).1) x₂)
    (fun cl => hthA j L₁ h₁ cl x₁ hx₁) (fun cl => hthA j L₂ h₂ cl x₂ hx₂)
  have hTa : ∀ j : Fin m, ∀ p, AnalyticAt ℂ T p := by
    intro j p
    rw [eT]
    exact (hTP j).1 p
  have hTj : ∀ j : Fin m, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T =
      ∑ cl : Cls E n M, (wt M (Quot.out cl).1 : ℂ) *
        (thP X hr bas idx (Φ L₁ (Quot.out cl).1) (P j) x₁ *
          conj (thP X hr bas idx (Φ L₂ (Quot.out cl).1) (P j) x₂)) := by
    intro j
    rw [eT]
    exact (hTP j).2
  obtain ⟨R, hAdm⟩ := hS.adm L₁ h₁ L₂ h₂
  have hheat := GlobalTheory.T.isHeat_swd_of_adm E X.Ψ hT n r hn h4 M R _ hAdm
  have hsw : ∀ Z ∈ Hn X.Ψ r, swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) Z 0 0 = 0 :=
    fun Z hZ => GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt E X.Ψ hT n r hn h4 M R _ hAdm Z hZ
  have hrn : r ≤ n := by omega
  have h0 := GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution E r X g q0 hr idx n m P hrn hInv _ hheat hsw x₁ hx₁ x₂ hx₂
  have hTS : (fun p => T p + (-1) * S p) = fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) =>
      kZero X idx x₁ x₂ p.1 p.2 * swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ))
        (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2) := by
    funext p
    have e : swd X.Ψ M (fun Λ => dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ p.1 p.2) (dblz' X idx x₁ x₂ p.1 p.2) = classSum M (fun Λ =>
          thH X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2)
            (dblz' X idx x₁ x₂ p.1 p.2) -
          eis X.Ψ (dbl X bas idx (Φ L₁ Λ) (Φ L₂ Λ)) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ p.1 p.2)
            (dblz' X idx x₁ x₂ p.1 p.2)) := rfl
    rw [hTd p, hSd p, e, hcs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun cl _ => ?_
    have hD := (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hb hn _ _ (hφ L₁ h₁ cl) (hφ L₂ h₂ cl)).2.1
      x₁ hx₁ x₂ hx₂ p.1 p.2
    have hst : star p.2 = fun k i => conj (p.2 k i) := rfl
    rw [hst, hD]
    ring
  have hsplit : ∀ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx)
      (fun p => T p + (-1) * S p) = KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T +
        (-1) * KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
    intro j
    have e1 := KernSum.bd_add (P j) (barP (P j)) (letterDir X hr idx) (hTa j)
      (fun p => (analyticAt_const.mul ((hHS j).1 p) : AnalyticAt ℂ (fun q => (-1 : ℂ) * S q) p))
    have e2 := KernSum.bd_const_mul (P j) (barP (P j)) (letterDir X hr idx) (-1) ((hHS j).1)
    rw [← e2]
    exact e1
  have hzero : ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx)
      (fun p => T p + (-1) * S p) = 0 := by
    rw [hTS]
    exact h0
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum] at hzero
  have hval : classSum M (fun Λ => ∑ j, thP X hr bas idx (Φ L₁ Λ) (P j) x₁ *
      conj (thP X hr bas idx (Φ L₂ Λ) (P j) x₂)) =
      ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
    have e : ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) T =
        ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) S := by
      linear_combination hzero
    rw [← e, hcs]
    simp only [hTj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cl _ => ?_
    rw [Finset.mul_sum]
  have hfun : ∀ γ : Δ, a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) *
      conj (μ γ L₂) * kern X hr idx P x₁ (lact (γ : GL (Fin r) E) x₂) =
      ∑ j, KernSum.bd (P j) (barP (P j)) (letterDir X hr idx) (fun p =>
        (a * classSum M (fun Λ => ip (Φ L₁ Λ) (Φ (mapL γ L₂) Λ)) * conj (μ γ L₂)) *
          kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := by
    intro γ
    have e : kern X hr idx P x₁ (lact (γ : GL (Fin r) E) x₂) = ∑ j, KernSum.bd (P j)
        (barP (P j)) (letterDir X hr idx)
          (fun p => kZero X idx x₁ (lact (γ : GL (Fin r) E) x₂) p.1 p.2) := rfl
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (KernSum.bd_const_mul (P j) (barP (P j)) (letterDir X hr idx) _ (hK0 γ)).symm
  simp only [hfun]
  rw [hval]
  exact hasSum_sum fun j _ => (hHS j).2

end GlobalTheory.SW
