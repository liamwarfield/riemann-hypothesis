module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartBallExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def InOrbit (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (y : Frame X.Ψ r) : Prop :=
  ∃ z : V (nd X), ‖z‖ ≤ R ∧ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x z) b)


open Classical in
noncomputable def ext (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (η : V (nd X) → ℝ) (y : Frame X.Ψ r) : ℝ :=
  if h : InOrbit X x R y then η h.choose else 0

theorem uniq (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) {z z' : V (nd X)} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (h : lact γ (rmul (cpt X x z) b) = lact γ' (rmul (cpt X x z') b')) : z = z' := by
  have h1 : lact (γ'⁻¹ * γ) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
    rw [← IW.lact_lact, h, IW.lact_lact, inv_mul_cancel, IW.lact_one]
  have h2 : lact (γ'⁻¹ * γ) (cpt X x z) = rmul (cpt X x z') (IW.bmul X b' (IW.binv X b)) := by
    rw [← IW.rmul_rmul, ← h1, IW.lact_rmul, IW.rmul_binv X _ hb]
  have h3 := hinj _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) z z' hz hz' _
    (IW.bmul_mem X hb' (IW.binv_mem X hb)) h2
  rw [h3, IW.lact_one] at h1
  exact (KU.cpt_inj X ho hb hb' h1).1

theorem ext_val (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    (η : V (nd X) → ℝ) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {z : V (nd X)} (hz : ‖z‖ ≤ R) : ext X x R η (lact γ (rmul (cpt X x z) b)) = η z := by
  have hP : InOrbit X x R (lact γ (rmul (cpt X x z) b)) := ⟨z, hz, γ, hγ, b, hb, rfl⟩
  unfold ext
  rw [dite_eq_left hP]
  obtain ⟨hz', γ', hγ', b', hb', he⟩ := hP.choose_spec
  rw [uniq X ho hinj hγ' hγ hb' hb hz' hz he.symm]

theorem ext_zero (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (η : V (nd X) → ℝ) {y : Frame X.Ψ r}
    (hy : ¬ InOrbit X x R y) : ext X x R η y = 0 := by
  unfold ext
  rw [dite_eq_right hy]

end GlobalTheory.ChartBallExt


open GlobalTheory.ChartBallExt in
theorem GlobalTheory.chartBall_extend_by_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  intro E _ _ _ r X x R ho _ hinj η
  refine ⟨ext X x R η, ?_, ?_, ?_, ?_⟩
  · intro γ hγ b hb z hz
    exact ext_val X ho hinj η hγ hb hz
  · intro y hy
    refine ext_zero X η ?_
    rintro ⟨z, hz, γ, hγ, b, hb, e⟩
    exact hy ⟨γ, hγ, b, hb, z, hz, e⟩
  · intro γ hγ y
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b, hb, rfl⟩ := hy
      rw [IW.lact_lact, ext_val X ho hinj η (X.Γ.mul_mem hγ hγ0) hb hz, ext_val X ho hinj η hγ0 hb hz]
    · have hy' : ¬ InOrbit X x R (lact γ y) := by
        rintro ⟨z, hz, γ0, hγ0, b, hb, e⟩
        refine hy ⟨z, hz, γ⁻¹ * γ0, X.Γ.mul_mem (X.Γ.inv_mem hγ) hγ0, b, hb, ?_⟩
        rw [← IW.lact_lact, ← e, IW.lact_lact, inv_mul_cancel, IW.lact_one]
      rw [ext_zero X η hy, ext_zero X η hy']
  · intro y b hb
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b0, hb0, rfl⟩ := hy
      rw [← IW.lact_rmul, IW.rmul_rmul, ext_val X ho hinj η hγ0 (IW.bmul_mem X hb0 hb) hz,
        ext_val X ho hinj η hγ0 hb0 hz]
    · have hy' : ¬ InOrbit X x R (rmul y b) := by
        rintro ⟨z, hz, γ0, hγ0, b0, hb0, e⟩
        refine hy ⟨z, hz, γ0, hγ0, IW.bmul X b0 (IW.binv X b), IW.bmul_mem X hb0 (IW.binv_mem X hb), ?_⟩
        rw [← IW.rmul_rmul, IW.lact_rmul, ← e, IW.rmul_binv X y hb]
      rw [ext_zero X η hy, ext_zero X η hy']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariantStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBall_extend_by_zero_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  first | exact @GlobalTheory.chartBall_extend_by_zero | exact GlobalTheory.chartBall_extend_by_zero | (intros; apply GlobalTheory.chartBall_extend_by_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

open Matrix

namespace GlobalTheory.PlaneSU

open Formalism.UG

theorem cT_cT_invol {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) {m p : Type}
    (P : Matrix m p R) : cT c (cT c P) = P := by
  ext i j; simp [cT, hc]

theorem eq_emb_of_fix {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) R) (hJ : IsUnit J.det) (A : Matrix (Fin M) (Fin 2) R)
    (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R) (hBA : B * A = 1)
    (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H) (G : Matrix (Fin M) (Fin M) R)
    (hG : cT c G * J * G = J) (hN : G * (1 - A * B) = 1 - A * B) :
    G = emb A B (B * G * A) ∧ cT c (B * G * A) * H * (B * G * A) = H := by
  set N := 1 - A * B with hNdef
  have hBN : B * N = 0 := by
    rw [hNdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  have hcN : cT c N = 1 - cT c B * cT c A := by
    rw [hNdef, cT_sub, cT_one, cT_mul]
  have hNJ : cT c N * J = J - cT c B * H * B := by
    rw [hcN, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have hNJA : cT c N * J * A = 0 := by
    rw [hNJ, Matrix.sub_mul, h2, Matrix.mul_assoc, hBA, Matrix.mul_one, sub_self]
  have hNJN : cT c N * J * N = J * N := by
    rw [hNJ, Matrix.sub_mul, Matrix.mul_assoc (cT c B * H), hBN, Matrix.mul_zero, sub_zero]
  have hAJA : cT c A * J * A = H := by
    rw [h1, Matrix.mul_assoc, hBA, Matrix.mul_one]
  have hAJN : cT c A * J * N = 0 := by
    rw [h1, Matrix.mul_assoc, hBN, Matrix.mul_zero]
  set W := N * G * A with hWdef
  have hcW : cT c W = cT c A * cT c G * cT c N := by
    rw [hWdef, cT_mul, cT_mul, Matrix.mul_assoc]
  have hWJA : cT c W * J * A = 0 := by
    rw [hcW, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c N), hNJA, Matrix.mul_zero]
  have hWJN : cT c W * J * N = 0 := by
    have e1 : cT c W * J * N = cT c A * cT c G * (cT c N * J * N) := by
      rw [hcW]; simp only [Matrix.mul_assoc]
    have e2 : cT c G * (J * N) = J * N := by
      calc cT c G * (J * N) = cT c G * (J * (G * N)) := by rw [hN]
        _ = (cT c G * J * G) * N := by simp only [Matrix.mul_assoc]
        _ = J * N := by rw [hG]
    rw [e1, hNJN, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, hAJN]
  have hsplit : A * B + N = 1 := by rw [hNdef]; abel
  have hWJ : cT c W * J = 0 := by
    calc cT c W * J = cT c W * J * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = cT c W * J * A * B + cT c W * J * N := by
          rw [Matrix.mul_add]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hWJA, hWJN, Matrix.zero_mul, add_zero]
  have hcW0 : cT c W = 0 := by
    calc cT c W = cT c W * J * J⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.mul_one]
      _ = 0 := by rw [hWJ, Matrix.zero_mul]
  have hW0 : W = 0 := by
    rw [← cT_cT_invol c hc W, hcW0]; ext i j; simp [cT]
  set X := B * G * A with hXdef
  have hGA : G * A = A * X := by
    calc G * A = (A * B + N) * G * A := by rw [hsplit, Matrix.one_mul]
      _ = A * X + W := by rw [hXdef, hWdef]; simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * X := by rw [hW0, add_zero]
  refine ⟨?_, ?_⟩
  · calc G = G * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = G * A * B + G * N := by rw [Matrix.mul_add, Matrix.mul_assoc]
      _ = A * X * B + N := by rw [hGA, hN]
      _ = emb A B X := by
          rw [emb, hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  · calc cT c X * H * X = cT c X * (cT c A * J * A) * X := by rw [hAJA]
      _ = cT c (A * X) * J * (A * X) := by rw [cT_mul c A X]; simp only [Matrix.mul_assoc]
      _ = cT c (G * A) * J * (G * A) := by rw [hGA]
      _ = cT c A * (cT c G * J * G) * A := by rw [cT_mul c G A]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hG, hAJA]

end GlobalTheory.PlaneSU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitaryStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) R), IsUnit J.det → ∀ (A : Matrix (Fin M) (Fin 2) R) (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R), B * A = 1 → Formalism.UG.cT c A * J = H * B → J * A = Formalism.UG.cT c B * H → ∀ G : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c G * J * G = J → G * (1 - A * B) = 1 - A * B → G = emb A B (B * G * A) ∧ Formalism.UG.cT c (B * G * A) * H * (B * G * A) = H := by
  first | exact @GlobalTheory.PlaneSU.eq_emb_of_fix | exact GlobalTheory.PlaneSU.eq_emb_of_fix | (intros; apply GlobalTheory.PlaneSU.eq_emb_of_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulus
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory
open Complex ComplexConjugate

theorem wdb_normSq_div {n : ℕ} (ρ : ℝ) (j : Fin n) (z : V n) :
    wdb n j (fun w : V n => (((‖w‖ ^ 2 / ρ ^ 2 : ℝ)) : ℂ)) z = z j / (ρ ^ 2 : ℝ) := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_smul ((ρ ^ 2)⁻¹ : ℝ)
  have e : (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) = fun w => ((ρ ^ 2)⁻¹ : ℝ) • ‖w‖ ^ 2 := by
    funext w; simp [smul_eq_mul, div_eq_inv_mul]
  have hv : HasFDerivAt (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (((ρ ^ 2)⁻¹ : ℝ) • (2 • innerSL ℝ z)) z := by
    rw [e]; exact h1
  unfold wdb
  rw [fderiv_ofReal_apply hv.differentiableAt, fderiv_ofReal_apply hv.differentiableAt, hv.fderiv]
  simp only [bas, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have hr : ∀ x y : V n, inner ℝ x y = re (inner ℂ x y) := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [hr, hr, inner_smul_right,
    EuclideanSpace.inner_single_right]
  rw [div_eq_mul_inv (z j), ← Complex.ofReal_inv]
  generalize (ρ ^ 2)⁻¹ = r
  apply Complex.ext <;> simp <;> ring

theorem wdb_cutoff_sq_le : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  intro χ A hχ h01 h1 h0 hA n ρ hρ z ξ
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hv : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) z :=
    by
    have := (differentiableAt_id (x := z)).norm_sq ℝ
    simpa [div_eq_mul_inv] using this.mul_const ((ρ ^ 2)⁻¹)
  set t := ‖z‖ ^ 2 / ρ ^ 2 with ht
  have hw : ∀ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z =
      ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) := by
    intro j
    rw [wdb_ofReal_comp (k := χ) (v := fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (hdχ _) hv,
      wdb_normSq_div]
  simp_rw [hw]
  have hsum : ∑ j, ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ) (ξ j) =
      ((deriv χ t : ℝ) : ℂ) / ((ρ ^ 2 : ℝ) : ℂ) * ∑ j, z j * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  split_ifs with hann
  · have hCS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
      calc ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖z j‖ * ‖ξ j‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_conj]
        _ ≤ (∑ j, ‖z j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    have hz : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hann.2.le 2
    have hS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 :=
      hCS.trans (mul_le_mul_of_nonneg_right hz (Finset.sum_nonneg fun j _ => by positivity))
    have hd : |deriv χ t| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
    have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hρ2, mul_pow, div_pow]
    calc |deriv χ t| ^ 2 / (ρ ^ 2) ^ 2 * ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2
        ≤ A ^ 2 / (ρ ^ 2) ^ 2 * (ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) := by gcongr
      _ = A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by field_simp
  · have hd0 : deriv χ t = 0 := by
      rcases not_and_or.mp hann with h | h
      · push_neg at h
        have ht4 : t ≤ 1 / 4 := by
          rw [ht, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg z]
        apply IsLocalMax.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h1 t ht4]; exact (h01 s).2
      · push_neg at h
        have ht1 : 1 ≤ t := by
          rw [ht, le_div_iff₀ (by positivity)]; nlinarith
        apply IsLocalMin.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h0 t ht1]; exact (h01 s).1
    rw [hd0]; simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulusStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarDeriv_cutoff_normSq_bound_annulus : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.wdb_cutoff_sq_le | exact GlobalTheory.wdb_cutoff_sq_le | (intros; apply GlobalTheory.wdb_cutoff_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFacts
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

open Matrix

section PlaneFacts

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

theorem planeFacts_hE_conj (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) : σ (hE σ J x y) = hE σ J y x := by
  unfold hE Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem planeFacts_cTJ_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k : Fin 2) (j : Fin M) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) k j = ∑ i, σ (![e₁, e₂] k i) * J i j := by
  simp [Matrix.mul_apply, Formalism.UG.cT, planeA]

theorem planeFacts_gram_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k l : Fin 2) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J * planeA e₁ e₂) k l = hE σ J (![e₁, e₂] k) (![e₁, e₂] l) := by
  rw [Matrix.mul_apply]
  simp_rw [planeFacts_cTJ_apply]
  simp only [planeA, Matrix.of_apply, hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

theorem planeFacts_mulVec_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (v : Fin M → E) (k : Fin 2) :
    ((Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) *ᵥ v) k = hE σ J (![e₁, e₂] k) v := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [planeFacts_cTJ_apply]
  simp only [hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

theorem planeB_facts : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ ∧ σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ ∧ planeB σ J e₁ e₂ * planeA e₁ e₂ = 1 ∧ Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J = planeH σ J e₁ e₂ * planeB σ J e₁ e₂ ∧ J * planeA e₁ e₂ = Formalism.UG.cT (σ : E →+* E) (planeB σ J e₁ e₂) * planeH σ J e₁ e₂ ∧ ∀ v : Fin M → E, (planeB σ J e₁ e₂).mulVec v = 0 ↔ (hE σ J e₁ v = 0 ∧ hE σ J e₂ v = 0) := by
  intro F E _ _ _ σ hσ M J hJ e₁ e₂ h12 h1 h2
  have hc := planeFacts_hE_conj σ hσ J hJ.1
  have h21 : hE σ J e₂ e₁ = 0 := by rw [← hc, h12, map_zero]
  have s1 : σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ := hc _ _
  have s2 : σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ := hc _ _
  set a₁ := hE σ J e₁ e₁ with ha₁
  set a₂ := hE σ J e₂ e₂ with ha₂
  set A := planeA e₁ e₂ with hA
  have gram : Formalism.UG.cT (σ : E →+* E) A * J * A = planeH σ J e₁ e₂ := by
    ext k l
    rw [planeFacts_gram_apply]
    fin_cases k <;> fin_cases l <;> simp [planeH, h12, h21, ha₁, ha₂]
  have dd : Matrix.diagonal ![a₁⁻¹, a₂⁻¹] * Matrix.diagonal ![a₁, a₂] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have dd' : Matrix.diagonal ![a₁, a₂] * Matrix.diagonal ![a₁⁻¹, a₂⁻¹] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have cTJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    ext i j; simp [Formalism.UG.cT, hJ.1]
  have cTcT : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have cTd : Formalism.UG.cT (σ : E →+* E) (Matrix.diagonal ![a₁⁻¹, a₂⁻¹]) = Matrix.diagonal ![a₁⁻¹, a₂⁻¹] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.UG.cT, map_inv₀, s1, s2]
  refine ⟨s1, s2, ?_, ?_, ?_, ?_⟩
  · unfold planeB
    rw [← ha₁, ← ha₂, ← hA]
    have gram' : Formalism.UG.cT (σ : E →+* E) A * (J * A) = planeH σ J e₁ e₂ := by rw [← Matrix.mul_assoc, gram]
    simp only [Matrix.mul_assoc]
    rw [gram']
    unfold planeH
    rw [← ha₁, ← ha₂, dd]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, dd', Matrix.one_mul]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTJ, cTcT, cTd, Matrix.mul_assoc, Matrix.mul_assoc A, dd, Matrix.mul_one]
  · intro v
    have hv : ∀ k, (planeB σ J e₁ e₂ *ᵥ v) k = ![a₁⁻¹, a₂⁻¹] k * hE σ J (![e₁, e₂] k) v := by
      intro k
      unfold planeB
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, planeFacts_mulVec_apply]
    constructor
    · intro h
      have k0 := hv 0
      have k1 := hv 1
      rw [h] at k0 k1
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at k0 k1
      exact ⟨(mul_eq_zero.mp k0.symm).resolve_left (inv_ne_zero h1),
        (mul_eq_zero.mp k1.symm).resolve_left (inv_ne_zero h2)⟩
    · rintro ⟨z1, z2⟩
      funext k
      rw [hv]
      fin_cases k <;> simp [z1, z2]

end PlaneFacts

end GlobalTheory.PlaneSU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFactsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ ∧ σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ ∧ planeB σ J e₁ e₂ * planeA e₁ e₂ = 1 ∧ Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J = planeH σ J e₁ e₂ * planeB σ J e₁ e₂ ∧ J * planeA e₁ e₂ = Formalism.UG.cT (σ : E →+* E) (planeB σ J e₁ e₂) * planeH σ J e₁ e₂ ∧ ∀ v : Fin M → E, (planeB σ J e₁ e₂).mulVec v = 0 ↔ (hE σ J e₁ v = 0 ∧ hE σ J e₂ v = 0) := by
  first | exact @GlobalTheory.PlaneSU.planeB_facts | exact GlobalTheory.PlaneSU.planeB_facts | (intros; apply GlobalTheory.PlaneSU.planeB_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOrigin
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviOriginMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chain_drop (r p : ℕ) (f : ℕ → ℝ) (g : ℝ)
    (hg : ∀ i, i + 1 < r → i + 1 ≠ p → g ≤ f i - f (i + 1)) :
    ∀ n i, i + n < r → (∀ k, i < k → k ≤ i + n → k ≠ p) → (n : ℝ) * g ≤ f i - f (i + n) := by
  intro n
  induction n with
  | zero => intro i _ _; simp
  | succ n ih =>
    intro i hr hk
    have h1 := ih i (by omega) (fun k h1 h2 => hk k h1 (by omega))
    have h2 := hg (i + n) (by omega) (hk _ (by omega) (by omega))
    have e : i + (n + 1) = i + n + 1 := by omega
    rw [e]
    push_cast
    linarith

theorem coeff_la {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) (hp0 : 0 < X.p0) (hpr : X.p0 < r)
    (hg0 : 0 ≤ g)
    (h1 : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b)
    (h2 : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a)
    (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    g ≤ sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - la τ a) := by
  set f : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0 with hf
  have hfa : ∀ c : Fin r, f c = la τ c := fun c => by simp [hf, c.isLt]
  have hg : ∀ i, i + 1 < r → i + 1 ≠ X.p0 → g ≤ f i - f (i + 1) := by
    intro i hi hip
    have := h1 τ ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl hip
    simpa [hf, hi, show i < r by omega] using this
  have hch := chain_drop r X.p0 f g hg
  have hab' : (b : ℕ) < a := hab
  have hsame : (∀ k, (b : ℕ) < k → k ≤ b + ((a : ℕ) - b) → k ≠ X.p0) → g ≤ (la τ b : ℝ) - la τ a := by
    intro hk
    have := hch ((a : ℕ) - b) b (by omega) hk
    have e : (b : ℕ) + ((a : ℕ) - b) = a := by omega
    rw [e, hfa, hfa] at this
    have hn : (1 : ℝ) ≤ (((a : ℕ) - b : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (a : ℕ) - b by omega)
    nlinarith
  rcases GlobalTheory.CurvMargin.coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
  · rw [e]; exact hsame (fun k _ hk => by omega)
  · rw [e]; exact hsame (fun k hk _ => by omega)
  · rw [e]

    have hA := hch ((r - 1) - a) a (by omega) (fun k hk _ => by omega)
    have hB := hch (b : ℕ) 0 (by omega) (fun k _ hk => by omega)
    have eA : (a : ℕ) + ((r - 1) - a) = r - 1 := by omega
    rw [eA, hfa] at hA
    rw [zero_add] at hB
    have hB' := hB
    rw [hfa] at hB'
    have h0 := h2 τ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have f0 : f 0 = (la τ ⟨0, by omega⟩ : ℝ) := by simp [hf, show 0 < r by omega]
    have fr : f (r - 1) = (la τ ⟨r - 1, by omega⟩ : ℝ) := by simp [hf, show r - 1 < r by omega]
    have hn1 : (0 : ℝ) ≤ (((r - 1 - a : ℕ)) : ℝ) * g := by positivity
    have hn2 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) * g := by positivity
    rw [fr] at hA
    rw [f0] at hB'
    linarith

theorem coeff_blk {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    0 ≤ sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ∧
    sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ≤ 1 := by
  have hab' : (b : ℕ) < a := hab
  unfold GlobalTheory.CurvMargin.blockWt sgn
  by_cases ha : (a : ℕ) < X.p0
  · have hb : (b : ℕ) < X.p0 := hab'.trans ha
    simp [ha, hb]
  · by_cases hb : (b : ℕ) < X.p0
    · simp [ha, hb]
    · simp [ha, hb]

theorem coeff_kap {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    sgn X.p0 a * sgn X.p0 b * ((kapW X τ b : ℝ) - kapW X τ a) ≤ 2 * r := by
  have hab' : (b : ℕ) < a := hab
  have ha : (a : ℕ) < r := a.isLt
  have hk : ((kapW X τ b : ℝ) - kapW X τ a) = 2 * (b : ℝ) - 2 * (a : ℝ) := by
    simp [kapW]
  rw [hk]
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hba : (b : ℝ) < a := by exact_mod_cast hab'
  have har : (a : ℝ) < r := by exact_mod_cast ha
  unfold sgn
  split_ifs <;> nlinarith

theorem levi_margin_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  intro E _ _ _ r X la x g bb hp0 hpr ho hg0 hbb h1 h2 ξ
  have hs : ∑ j, ‖ξ j‖ ^ 2 = ∑ e : Ent X, ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 :=
    ((Fintype.equivFin (Ent X)).sum_comp (fun j => ‖ξ j‖ ^ 2)).symm
  rw [GlobalTheory.LeviZero.levi_phla_zero r X la x ho ξ, GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
  have c1 := coeff_la X la g hp0 hpr hg0 h1 h2 τ a b hab
  have c2 := coeff_blk X τ a b hab
  have c3 := coeff_kap X τ a b hab
  set N := ‖ξ (Fintype.equivFin (Ent X) ⟨τ, ⟨(a, b), hab⟩⟩)‖ ^ 2
  have hN : 0 ≤ N := by positivity
  simp only at c1 c2 c3 ⊢
  nlinarith [mul_nonneg hbb hN, mul_nonneg (mul_nonneg hbb c2.1) hN, mul_nonneg (sub_nonneg.2 c2.2) (mul_nonneg hbb hN),
    mul_nonneg (sub_nonneg.2 c1) hN, mul_nonneg (sub_nonneg.2 c3) hN]

end GlobalTheory.LeviOriginMargin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOriginStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviMargin_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  first | exact @GlobalTheory.LeviOriginMargin.levi_margin_origin | exact GlobalTheory.LeviOriginMargin.levi_margin_origin | (intros; apply GlobalTheory.LeviOriginMargin.levi_margin_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChart
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_inv_lact (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  rw [KU.lact_lact X, inv_mul_cancel, KU.lact_one X]

theorem lact_lact_inv (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ (lact γ⁻¹ y) = y := by
  rw [KU.lact_lact X, mul_inv_cancel, KU.lact_one X]

theorem local_form (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (ρ R : ℝ) (η : V (nd X) → ℝ)
    (ψ : Frame X.Ψ r → ℝ) (hρR : ρ < R) (hR : ∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x)
    (hψ : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (h0 : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) →
      ψ y = 0)
    (hloc : ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X),
        ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b))
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    (∀ᶠ y' in 𝓝 y, ψ y' = 0) ∨
    ∃ (γ : GL (Fin r) E) (zOf : Frame X.Ψ r → V (nd X)) (U : Set (Frame X.Ψ r)),
      IsOpen U ∧ lact γ⁻¹ y ∈ U ∧ DifferentiableOn ℂ zOf U ∧
      ∀ᶠ y' in 𝓝 y, ψ y' = η (zOf (lact γ⁻¹ y')) := by
  by_cases hS : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)
  · right
    obtain ⟨γ, hγ, b, hb, z, hz, rfl⟩ := hS
    obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x hx
    have hUo : IsOpen {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hzO : z ∈ OmF X x := hR z (hz.trans hρR.le)
    have hmem : lact γ⁻¹ (lact γ (rmul (cpt X x z) b)) ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} := by
      rw [lact_inv_lact]
      exact ⟨OntoS.dom_rmul X hzO hb, (hinv z hzO b hb).1⟩
    refine ⟨γ, zOf, _, hUo, hmem, hzd, ?_⟩
    have hcont : ContinuousAt (fun y' => lact γ⁻¹ y') (lact γ (rmul (cpt X x z) b)) :=
      (KU.cont_lact X γ⁻¹).continuousAt
    have hU' : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), lact γ⁻¹ y' ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      hcont.preimage_mem_nhds (hUo.mem_nhds hmem)
    have hzc : ContinuousAt (fun y' => zOf (lact γ⁻¹ y')) (lact γ (rmul (cpt X x z) b)) :=
      ContinuousAt.comp (f := fun y' => lact γ⁻¹ y')
        ((hzd.differentiableAt (hUo.mem_nhds hmem)).continuousAt) hcont
    have hval : zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b))) = z := by
      rw [lact_inv_lact]; exact (hinv z hzO b hb).2.1
    have h2 : ‖zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b)))‖ < R := by
      rw [hval]; exact lt_of_le_of_lt hz hρR
    have hnear : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), ‖zOf (lact γ⁻¹ y')‖ < R :=
      hzc.norm.eventually_lt continuousAt_const h2
    filter_upwards [hU', hnear] with y' hy'U hy'n
    obtain ⟨hy'd, hy'Δ⟩ := hy'U
    obtain ⟨-, hbO, heq⟩ := hsplit _ hy'd hy'Δ
    have hy' : y' = lact γ (rmul (cpt X x (zOf (lact γ⁻¹ y'))) (bOf (lact γ⁻¹ y'))) := by
      rw [← heq, lact_lact_inv]
    conv_lhs => rw [hy']
    exact hψ γ hγ _ hbO _ hy'n.le
  · left
    filter_upwards [hloc y hy hS] with y' hy'
    exact h0 y' hy'

end GlobalTheory.PeakWeightSmooth

namespace GlobalTheory.PeakWeightSmooth

theorem measurable_and_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  intro E _ _ _ r X x ρ R η ψ hx hρR hR hη hψ h0 hloc
  classical
  have hS_dom : ∀ y, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → y ∈ X.dom := by
    rintro y ⟨γ, hγ, b, hb, z, hz, rfl⟩
    exact KU.lact_dom X hγ (OntoS.dom_rmul X (hR z (hz.trans hρR.le)) hb)
  have hcont : ∀ y ∈ X.dom, ContinuousAt ψ y := by
    intro y hy
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc hy with h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · exact (continuousAt_const (y := (0 : ℝ))).congr (h.mono fun _ h => h.symm)
    · have : ContinuousAt (fun y' => η (zOf (lact γ⁻¹ y'))) y :=
        hη.continuous.continuousAt.comp (((hzd.differentiableAt (hUo.mem_nhds hyU)).continuousAt).comp
          (KU.cont_lact X γ⁻¹).continuousAt)
      exact this.congr (hev.mono fun _ h => h.symm)
  have hzero : ∀ y, y ∉ X.dom → ψ y = 0 := fun y hy => h0 y (fun h => hy (hS_dom y h))
  constructor
  · have heq : ψ = X.dom.piecewise ψ (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ X.dom
      · simp [Set.piecewise, hy]
      · simp [Set.piecewise, hy, hzero y hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise (fun y hy => (hcont y hy).continuousWithinAt)
      continuousOn_const (IW.isOpen_dom X).measurableSet
  · intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    have hc : ContinuousAt (cpt X x) w := (IW.cpt_diff X x).continuous.continuousAt
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc (y := cpt X x w) hw with
      h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · have h' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = 0 := hc.eventually h
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h'
    · have hg : Differentiable ℂ (fun w' => lact γ⁻¹ (cpt X x w')) := by
        have e : (fun w' => lact γ⁻¹ (cpt X x w')) = cpt X (lact γ⁻¹ x) := by
          funext w'; rw [KU.cpt_lact]
        rw [e]; exact IW.cpt_diff X _
      have hN : (fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U ∈ 𝓝 w :=
        hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hyU)
      have hΦd : DifferentiableOn ℂ (fun w' => zOf (lact γ⁻¹ (cpt X x w')))
          ((fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U) :=
        hzd.comp hg.differentiableOn (fun _ h => h)
      have hΦ : ContDiffAt ℂ ∞ (fun w' => zOf (lact γ⁻¹ (cpt X x w'))) w :=
        GlobalTheory.SCV.contDiffAt_of_differentiableOn hΦd hN _
      have hev' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = η (zOf (lact γ⁻¹ (cpt X x w'))) := hc.eventually hev
      exact ((hη.contDiffAt).comp w (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev'

end GlobalTheory.PeakWeightSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantExtensionMeasurableContDiffOnChartStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantExtension_measurable_contDiffOn_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  first | exact @GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn | exact GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn | (intros; apply GlobalTheory.PeakWeightSmooth.measurable_and_contDiffOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SaturationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
def adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (τ : Ψ) (a c : Fin r) : ℂ :=
  (Matrix.adjugate (mat k τ) * mat w τ) a c

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl


omit [NumberField E] [IsCMField E] in
theorem adjEnt_rmul {Ψ : Finset (E →+* ℂ)} (k b : Frame Ψ r) (hb : b ∈ Bor Ψ r) (τ : Ψ) (a c : Fin r)
    (hca : c < a) : adjEnt k (rmul k b) τ a c = 0 := by
  have h1 : mat (rmul k b) τ = mat k τ * mat b τ := rfl
  rw [adjEnt, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.smul_mul, mat, (hb τ).2 a c hca]


omit [NumberField E] [IsCMField E] in
theorem exists_of_adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (hk : ∀ τ, (mat k τ).det ≠ 0)
    (hw : ∀ τ, (mat w τ).det ≠ 0) (h0 : ∀ τ a c, c < a → adjEnt k w τ a c = 0) :
    ∃ b ∈ Bor Ψ r, w = rmul k b := by
  refine ⟨fun τ => ((mat k τ)⁻¹ * mat w τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · show ((mat k τ)⁻¹ * mat w τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hk τ)) (hw τ)
  · show ((mat k τ)⁻¹ * mat w τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply]
    have := h0 τ a c hca
    rw [adjEnt] at this
    rw [this, smul_zero]
  · funext τ
    show mat w τ = mat k τ * ((mat k τ)⁻¹ * mat w τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hk τ))]

omit [NumberField E] [IsCMField E] in
theorem continuous_mat {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f : α → Frame Ψ r}
    (hf : Continuous f) (τ : Ψ) : Continuous fun p => mat (f p) τ :=
  (continuous_apply τ).comp hf

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_mat continuous_id τ)

omit [NumberField E] [IsCMField E] in
theorem continuous_adjEnt {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f g : α → Frame Ψ r}
    (hf : Continuous f) (hg : Continuous g) (τ : Ψ) (a c : Fin r) :
    Continuous fun p => adjEnt (f p) (g p) τ a c :=
  (((continuous_mat hf τ).matrix_adjugate).matrix_mul (continuous_mat hg τ)).matrix_elem a c

theorem eventually_not_mem_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) →
    ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) →
    ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y' = lact γ (rmul (cpt X x z) b) := by
  intro E _ _ _ r X x ρ hΩ y hy hny
  have hcpt : Continuous (cpt X x) := (GlobalTheory.InterpCompare.differentiable_chart X x).continuous
  have hK : IsCompact (Metric.closedBall (0 : V (nd X)) ρ) := isCompact_closedBall 0 ρ
  have key : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
      ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, p.1 ≠ lact γ (rmul (cpt X x p.2) b) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    have hk : cpt X x z ∈ X.dom := hΩ z hz'
    obtain ⟨U, hU, U', hU', hfin⟩ := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X y hy _ hk
    have h1 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z), p.1 ∈ U ∧ cpt X x p.2 ∈ U' := by
      refine Filter.Eventually.and (continuous_fst.continuousAt.preimage_mem_nhds hU) ?_
      exact (hcpt.comp continuous_snd).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
        ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0 := by
      refine (Filter.eventually_all_finite hfin).2 fun δ hδ => ?_
      have hopen : IsOpen {p : Frame X.Ψ r × V (nd X) |
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0} := by
        simp only [Set.setOf_exists]
        refine isOpen_iUnion fun τ => isOpen_iUnion fun a => isOpen_iUnion fun c => ?_
        by_cases hca : c < a
        · simp only [hca, true_and]
          exact isOpen_ne_fun (continuous_adjEnt (hcpt.comp continuous_snd)
            ((continuous_lact δ).comp continuous_fst) τ a c) continuous_const
        · simp [hca]
      refine hopen.mem_nhds ?_
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hcon
      have hdk : ∀ τ, (mat (cpt X x z) τ).det ≠ 0 := fun τ => (hk τ).1
      have hdw : ∀ τ, (mat (lact δ y) τ).det ≠ 0 := by
        intro τ h0
        have e : y = lact δ⁻¹ (lact δ y) := by rw [lact_lact, inv_mul_cancel, lact_one]
        have : (mat y τ).det = 0 := by
          rw [e]
          show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ y) τ).det = 0
          rw [Matrix.det_mul, h0, mul_zero]
        exact (hy τ).1 this
      obtain ⟨b, hb, hwb⟩ := exists_of_adjEnt _ _ hdk hdw hcon
      refine hny ⟨δ⁻¹, X.Γ.inv_mem hδ.1, b, hb, z, hz', ?_⟩
      rw [← hwb, lact_lact, inv_mul_cancel, lact_one]
    filter_upwards [h1, h2] with p hp1 hp2
    intro γ hγ b hb he
    have hδ : γ⁻¹ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b} := by
      refine ⟨X.Γ.inv_mem hγ, p.1, hp1.1, cpt X x p.2, hp1.2, b, hb, ?_⟩
      rw [he, lact_lact, inv_mul_cancel, lact_one]
    obtain ⟨τ, a, c, hca, hne⟩ := hp2 _ hδ
    apply hne
    rw [he, lact_lact, inv_mul_cancel, lact_one]
    exact adjEnt_rmul _ _ hb τ a c hca
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun y' z => ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, y' ≠ lact γ (rmul (cpt X x z) b)) key] with y' hy'
  rintro ⟨γ, hγ, b, hb, z, hz, he⟩
  exact hy' z (by simpa using hz) γ hγ b hb he

end GlobalTheory.SaturationClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturationStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_not_mem_chartBall_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) → ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b) := by
  first | exact @GlobalTheory.SaturationClosed.eventually_not_mem_saturation | exact GlobalTheory.SaturationClosed.eventually_not_mem_saturation | (intros; apply GlobalTheory.SaturationClosed.eventually_not_mem_saturation <;> assumption)
end
end
