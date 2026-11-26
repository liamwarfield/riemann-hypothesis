module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ColumnValue

theorem dmonOf_zero_index {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (g : PS k 1 d) : DmonOf F u 0 g = g := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, ih]; rfl

theorem dmonOf_smul {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (c : k) (g : PS k 1 d) :
    DmonOf F u mo (c • g) = C c * DmonOf F u mo g := by
  rw [smul_eq_C_mul]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, DerivEndo.iterate_dof_C_mul]

theorem column_value {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : FB.toK k (f * w ^ m) * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      FB.toK k f * FB.expS k ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0)) := by
    have e : FB.toK k (f * w ^ m) = FB.toK k f * FB.toK k w ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hw, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0))) = algebraMap R k r := by
    intro mo
    rcases eq_or_ne mo 0 with rfl | hmo
    · exact ⟨0, I.zero_mem, by rw [dmonOf_zero_index, nt_const_smul, cA, mul_zero, map_zero]⟩
    · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 hmo
      obtain ⟨t, ht⟩ := canonGauge_dmonOf_hL_integral R d O k B h hh w0 ι u hβ mo
      refine ⟨(m : R) * ((∏ l, α l ^ mo l) * t), I.mul_mem_left _ (I.mul_mem_right _
        (Ideal.prod_mem I (Finset.mem_univ l) (I.pow_mem_of_mem (hI l) _ (Nat.pos_of_ne_zero hl)))), ?_⟩
      rw [dmonOf_smul, map_mul, constantCoeff_C,
        (invariantDeriv_along_endo R d O k B a).2 ι _ (fun l => algebraMap R k (α l)) hα mo, ← ht]
      simp only [map_mul, map_prod, map_pow, map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cA, mul_zero]) hφ f mo
  refine ⟨constantCoeff (DmonOf B.G.F u mo f) + r, ?_, ?_⟩
  · rw [add_sub_right_comm]
    exact I.add_mem (constantCoeff_dmonOf_sub_mem R d B.G.F I ι u y f hf mo) hr
  · unfold FB.nabVal
    rw [hG, PullbackColumn.dpolyOf_monomial_one]
    exact e

end GlobalTheory.ColumnValue

namespace GlobalTheory

open ColumnValue

theorem nabVal_columns_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw I ι _ u α hI hα hβ n f y hf P
  choose s hs he using fun (mo : ι × Fin n →₀ ℕ) (b : Fin n) =>
    column_value B h hh w0 a N m w hw I u α hI hα hβ (f b) (fun l => y (l, b)) (fun l => hf l b) (colM mo b)
  refine ⟨∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b -
    MvPolynomial.eval y P * ∏ b, constantCoeff (f b), ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo _ => ?_
    rw [mul_assoc, ← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b)
  · rw [add_sub_cancel]
    simp only [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponent
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casKLe_io_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  intro M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise (N s) n ε (F s) M (Fin n) E
    (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s)
    (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n)
    (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _)
    (by
      intro a b _
      simp [Matrix.conjTranspose_single])
    (by
      intro x
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h1 : ∀ a b : Fin n,
          ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2 := by
        intro a b
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro j _ hj
            simp [Matrix.single, hj.symm]
          · simp
        · intro i _ hi
          simp [Matrix.single, hi.symm]
        · simp
      calc _ ≤ ∑ _a : Fin n, ∑ b : Fin n, ‖x b‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            split_ifs
            · exact (h1 a b).le
            · positivity
        _ = _ := by simp)
    (by
      intro a b _ j w
      have h := congrFun (hT.io_comm s a b w) j
      simp only [dualTens] at h
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [h, Finset.sum_eq_single a]
      · by_cases hj : j = b
        · subst hj
          simp
        · simp [hj, Matrix.single, Ne.symm hj]
      · intro i _ hi
        simp [Matrix.single, hi.symm]
      · simp)
    y hy d
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponentStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirBound_embedded_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  first | exact @GlobalTheory.casKLe_io_component | exact GlobalTheory.casKLe_io_component | (intros; apply GlobalTheory.casKLe_io_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwo
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_io_pr_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  intro M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d
  obtain ⟨hc, hwt⟩ := hw
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos s
    exact_mod_cast this
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE hF hT h0 hc s c
    have h2 := GlobalTheory.T.compactCasimirBound_embedded_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h2
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by linarith)
    push_cast
    nlinarith
  · have h1 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c
    have h2 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d
    have e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [e]
    exact h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_glModule_proj_components_level_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  first | exact @GlobalTheory.lev_io_pr_single | exact GlobalTheory.lev_io_pr_single | (intros; apply GlobalTheory.lev_io_pr_single <;> assumption)
end
end
