module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplexStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutant
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_tau_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  intro L _ _ _ n a ι _ _ b P hA τ v hv w
  classical
  have hS := GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight L n a ι b P hA v hv w
  refine Submodule.span_mono ?_ hS
  rintro x ⟨γ₀, hγ, rfl⟩
  obtain ⟨_, hmul⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P hA
  set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef
  have hBv : B.val = γ₀.val.map τ := rfl
  set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
    if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef
  have hU := isUPt_ratPt γ₀ hγ
  have hR : IsUPt R := by
    intro σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, conj_conj]
      simp only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]
    · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', conj_conj]))
        · exact h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))
      simp only [R, if_neg h, if_neg h']
      exact hU σ
  have hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    exact hU τ
  have hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ := by
    funext σ
    have hne := conjugate_ne_self τ
    by_cases h1 : σ = τ
    · subst h1
      simp [tauPt, R, hBv, ratPt]
    · by_cases h2 : σ = ComplexEmbedding.conjugate τ
      · subst h2
        simp only [tauPt, if_neg h1, if_true, R, or_true, mul_one]
        rw [hinv, Matrix.transpose_transpose]
      · simp [tauPt, R, h1, h2]
  have hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ) := by
    intro A
    funext σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · simp [R, h]
    · have h1 : σ ≠ τ := fun e => h (Or.inl e)
      have h2 : σ ≠ ComplexEmbedding.conjugate τ := fun e => h (Or.inr e)
      simp [tauPt, h1, h2]
  refine ⟨B, evM P (upt R), ?_, ?_⟩
  · intro A
    rw [evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]
  · rw [hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]

end GlobalTheory.AlgWtHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightSpanTranslatesFactorCommutantStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_span_translates_factor_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  first | exact @GlobalTheory.AlgWtHW.span_tau_commutant | exact GlobalTheory.AlgWtHW.span_tau_commutant | (intros; apply GlobalTheory.AlgWtHW.span_tau_commutant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasis
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem evM_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  intro L _ _ _ n a ι _ _ b P ι' _ _ b' P' hP hP' τ B

  have key : ∀ x, evM P' x - b'.toMatrix b * evM P x * b.toMatrix b' =
      Matrix.of fun i j => MvPolynomial.eval x (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) := by
    intro x
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evM, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) =
        b'.toMatrix b * evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * b.toMatrix b' := by
    intro γ₀ h
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h
    have e1 := hP γ γ₀ hγ
    have e2 := hP' γ γ₀ hγ
    have e3 := (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b') (c := b') (b' := b) (c' := b) (f := a.ρ γ)).symm
    have f1 : evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
      rw [e1]; rfl
    have f2 : evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b' b' (a.ρ γ) := by
      rw [e2]; rfl
    rw [f1, f2, e3]
  have hz : ∀ i j, MvPolynomial.eval (evPt τ B) (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) = 0 := by
    intro i j
    rw [evPt_eq_upt]
    refine GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n _ ?_ (tauPt τ B) (isUPt_tauPt τ B)
    intro γ₀ h
    have := congrArg (fun M => M i j) (key (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))))
    simp only [hrat γ₀ h, sub_self] at this
    simpa using this.symm
  rw [← sub_eq_zero, key]
  ext i j
  simpa using hz i j

end GlobalTheory.AlgWtHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasisStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  first | exact @GlobalTheory.AlgWtHW.evM_change_of_basis | exact GlobalTheory.AlgWtHW.evM_change_of_basis | (intros; apply GlobalTheory.AlgWtHW.evM_change_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwap
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwapStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  first | exact @GlobalTheory.isWt_comp_swap | exact GlobalTheory.isWt_comp_swap | (intros; apply GlobalTheory.isWt_comp_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedB
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedB
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.DomLEOfSle

noncomputable def diagU {n : ℕ} (u : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (u i : ℂ)), Matrix.diagonal (fun i => ((u i)⁻¹ : ℂˣ)),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

lemma diag_commute {n : ℕ} (D E : GL (Fin n) ℂ) (hD : D.val.IsDiag) (hE : E.val.IsDiag) :
    D * E = E * D := by
  ext1
  simp only [Units.val_mul]
  rw [← hD.diagonal_diag, ← hE.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have := congrArg Complex.re h
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

end GlobalTheory.AlgWtHW.DomLEOfSle

namespace GlobalTheory.AlgWtHW.DomLEOfSle

theorem domLE_of_mem_Sle : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ),
    IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  intro n ι _ _ Φ hΦ μ lam w hw hw0 hS
  by_contra hnot
  let J := {D : GL (Fin n) ℂ // D.val.IsDiag}
  let T : J → Module.End ℂ (ι → ℂ) := fun D => Matrix.toLin' (Φ D.1)
  have hc : ∀ a b : J, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    have e : ∀ A B : Matrix ι ι ℂ, Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B) :=
      fun A B => by rw [Matrix.toLin'_mul]; rfl
    simp only [T]
    rw [e, e, ← hΦ.mul, ← hΦ.mul, diag_commute a.1 b.1 a.2 b.2]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let χ : (Fin n → ℤ) → J → ℂ := fun ν D => ∏ i, (D.1.val i i) ^ (ν i)
  let E : (J → ℂ) → Submodule ℂ (ι → ℂ) := fun c => ⨅ D, (T D).maxGenEigenspace (c D)
  have hmem : ∀ ν v, IsWtVec Φ ν v → v ∈ E (χ ν) := by
    intro ν v hv
    refine Submodule.mem_iInf _ |>.mpr fun D => ?_
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simp only [T, Matrix.toLin'_apply]
    exact hv D.1 D.2
  have hχinj : ∀ ν ν', χ ν = χ ν' → ν = ν' := by
    intro ν ν' h
    funext i
    let u : Fin n → ℂˣ := Function.update 1 i (Units.mk0 2 two_ne_zero)
    have hD : (diagU u).val.IsDiag := by
      show (Matrix.diagonal _).IsDiag
      exact Matrix.isDiag_diagonal _
    have key := congrFun h ⟨diagU u, hD⟩
    have hprod : ∀ ν'' : Fin n → ℤ, χ ν'' ⟨diagU u, hD⟩ = (2 : ℂ) ^ (ν'' i) := by
      intro ν''
      simp only [χ, diagU, Matrix.diagonal_apply_eq]
      rw [Finset.prod_eq_single i]
      · simp [u]
      · intro j _ hj
        simp [u, Function.update_of_ne hj]
      · simp
    rw [hprod, hprod] at key
    exact two_zpow_inj key
  have hle : Sle Φ lam ≤ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := by
    unfold Sle
    rw [Submodule.span_le]
    rintro v ⟨ν, hν, hv⟩
    have hne : χ ν ≠ χ μ := by
      intro h
      have := hχinj _ _ h
      subst this
      exact hnot hν
    exact (le_iSup₂ (f := fun (c : J → ℂ) (_ : c ≠ χ μ) => E c) (χ ν) hne) (hmem ν v hv)
  have hdis := hind (χ μ)
  have h1 : w ∈ E (χ μ) := hmem μ w hw
  have h2 : w ∈ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := hle hS
  exact hw0 ((Submodule.disjoint_def.mp hdis) w h1 h2)

end GlobalTheory.AlgWtHW.DomLEOfSle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedBStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ), IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  first | exact @GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | exact GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitone
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AlgWtHW
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField Finset

section
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sle_mulVec {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ} (hM : ∀ A, M * Φ A = Φ A * M)
    (lam : Fin n → ℤ) {x : ι → ℂ} (hx : x ∈ Sle Φ lam) : M *ᵥ x ∈ Sle Φ lam := by
  have h : Sle Φ lam ≤ (Sle Φ lam).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨ν, hν, hw⟩
    refine Submodule.subset_span ⟨ν, hν, fun D hD => ?_⟩
    show Φ D *ᵥ (M *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw D hD, Matrix.mulVec_smul]
    rfl
  exact h hx

theorem filter_succ (i : Fin n) : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) =
    insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem not_mem_filter_self (i : Fin n) : i ∉ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
  simp

theorem domLE_antisymm {μ lam : Fin n → ℤ} (h1 : DomLE μ lam) (h2 : DomLE lam μ) : μ = lam := by
  have hs : ∀ k : ℕ, ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), lam i := fun k => le_antisymm (h1.2 k) (h2.2 k)
  funext i
  have h := hs ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i), hs i] at h
  linarith

theorem le_of_domLE_swap {lam : Fin n → ℤ} {i j : Fin n} (hij : i < j)
    (h : DomLE (lam ∘ Equiv.swap i j) lam) : lam j ≤ lam i := by
  have h1 := h.2 ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i)] at h1
  have h2 : ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), (lam ∘ Equiv.swap i j) l =
      ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), lam l := by
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl
    have hli : l ≠ i := fun e => by rw [e] at hl; omega
    have hlj : l ≠ j := fun e => by rw [e] at hl; rw [Fin.lt_def] at hij; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [h2] at h1
  simp only [Function.comp, Equiv.swap_apply_left] at h1
  linarith

end

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem algWeight_space_nontrivial (a : AlgWt L n) : Nontrivial a.W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := a.irr
  exact bot_ne_top (α := Subrepresentation a.ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem beig_of_hwAt {a : AlgWt L n} {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
      (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (v : ι → ℂ),
      Agrees a b P ∧ IsBEig (fun B => evM P (evPt τ B)) v lam := by
  obtain ⟨ι, i1, i2, b, P, hP, v, hv, hB⟩ := h
  exact ⟨ι, i1, i2, b, P, v, hP, hv, hB⟩

theorem domLE_of_agrees {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) {v : ι → ℂ} {lam μ : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P (evPt τ B)) v lam) (hμ : IsWt (fun B => evM P (evPt τ B)) μ) :
    DomLE μ lam := by
  obtain ⟨w, hw0, hw⟩ := hμ
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  refine GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy n ι _ hR μ lam w hw hw0 ?_
  have hspan := GlobalTheory.T.algebraicWeight_span_translates_factor_commutant L n a ι b P hP τ v hv.1 w
  refine (Submodule.span_le.2 ?_) hspan
  rintro x ⟨B, M, hM, rfl⟩
  have e : evM P (evPt τ B) *ᵥ (M *ᵥ v) = M *ᵥ (evM P (evPt τ B) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  rw [e]
  exact sle_mulVec hM lam (GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector n ι _ hR v lam hv B)

theorem isWt_of_beig {ι : Type} [Fintype ι] {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {v : ι → ℂ} {lam : Fin n → ℤ}
    (h : IsBEig Φ v lam) : IsWt Φ lam :=
  ⟨v, h.1, fun D hD => h.2 D (fun i j hij => hD (ne_of_gt hij))⟩

theorem beig_transport {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {b' : Module.Basis ι' ℂ a.W} {P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) (hP' : Agrees a b' P') {v' : ι' → ℂ} {lam : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P' (evPt τ B)) v' lam) :
    IsBEig (fun B => evM P (evPt τ B)) (b.toMatrix b' *ᵥ v') lam := by
  have hC : b'.toMatrix b * b.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' b
  refine ⟨fun h0 => hv.1 ?_, fun B hB => ?_⟩
  · have := congrArg (fun x => b'.toMatrix b *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, hC] using this
  · show evM P (evPt τ B) *ᵥ (b.toMatrix b' *ᵥ v') = _
    rw [GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis L n a ι' b' P' ι b P hP' hP τ B, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hC,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have := hv.2 B hB
    simp only at this
    rw [this, Matrix.mulVec_smul]

theorem hw_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  intro L _ _ _ n a τ
  have hanti : ∀ lam, a.HWAt τ lam → Antitone lam := by
    intro lam h
    obtain ⟨ι, _, _, b, P, v, hP, hv⟩ := beig_of_hwAt h
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hlt
    · rw [e]
    · exact le_of_domLE_swap hlt (domLE_of_agrees hP hv
        (GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ) lam (isWt_of_beig hv) i j))
  refine ⟨?_, hanti⟩
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  haveI := algWeight_space_nontrivial a
  haveI := b.index_nonempty
  obtain ⟨v, lam, hv⟩ := GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ)
  refine ⟨lam, ⟨ι, inferInstance, inferInstance, b, P, hP, v, hv.1, hv.2⟩, fun lam' h' => ?_⟩
  obtain ⟨ι', _, _, b', P', v', hP', hv'⟩ := beig_of_hwAt h'
  have hv'' := beig_transport hP hP' hv'
  exact domLE_antisymm (domLE_of_agrees hP hv (isWt_of_beig hv'')) (domLE_of_agrees hP hv'' (isWt_of_beig hv))

end

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  first | exact @GlobalTheory.AlgWtHW.hw_exists_unique_antitone | exact GlobalTheory.AlgWtHW.hw_exists_unique_antitone | (intros; apply GlobalTheory.AlgWtHW.hw_exists_unique_antitone <;> assumption)
end
