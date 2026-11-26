module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastStepVac

theorem last_step : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hω hv t k hk
  have hm := D.R.two_le_m
  have hk' : (k : ℕ) + 1 = D.R.m := by omega
  have he := GlobalTheory.InnerSteps.exp_chrStep R.toLevCh hL t k
  rw [hk'] at he
  refine ⟨⟨_, _, hω t, he⟩, ?_⟩
  have hr : (Yc D (D.R.m - 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.InnerSteps.stepVec_vac
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) hr (hv t)
  exact ⟨h1, h2, h3⟩

end GlobalTheory.LastStepVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  first | exact @GlobalTheory.LastStepVac.last_step | exact GlobalTheory.LastStepVac.last_step | (intros; apply GlobalTheory.LastStepVac.last_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinear
noncomputable section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

namespace GlobalTheory.CompactHowe.PolyTensor

open MvPolynomial

variable {ι σ : Type} [Fintype ι]

def prodRename [DecidableEq ι] :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    fun i => (rename (Prod.mk i) : MvPolynomial σ ℂ →ₐ[ℂ] _).toLinearMap

theorem prodRename_apply [DecidableEq ι] (P : ι → MvPolynomial σ ℂ) :
    prodRename P = ∏ i, rename (Prod.mk i) (P i) := by
  simp [prodRename]

theorem sum_mapDomain_apply (a : ι → σ →₀ ℕ) (j : ι) (s : σ) :
    (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) (j, s) = a j s := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Prod.fst ht)
  · simp

theorem prod_rename_monomial (a : ι → σ →₀ ℕ) :
    (∏ i, rename (Prod.mk i) (monomial (a i) (1 : ℂ)) : MvPolynomial (ι × σ) ℂ)
      = monomial (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

def res (α : ι × σ →₀ ℕ) (i : ι) : σ →₀ ℕ :=
  Finsupp.comapDomain (Prod.mk i) α (Prod.mk_right_injective i).injOn

theorem res_sum (a : ι → σ →₀ ℕ) : res (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) = a := by
  funext j
  ext s
  exact sum_mapDomain_apply a j s

theorem sum_res (α : ι × σ →₀ ℕ) : ∑ i, Finsupp.mapDomain (Prod.mk i) (res α i) = α := by
  ext ⟨j, s⟩
  exact sum_mapDomain_apply (res α) j s

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial (ι × σ) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials (ι × σ) ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ι → MvPolynomial σ ℂ) :
    tens I (∏ i, rename (Prod.mk i) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  have key : (tens I).compMultilinearMap prodRename
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun _ => basisMonomials σ ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, prodRename_apply, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply]
    rw [prod_rename_monomial]
    have := (basisMonomials (ι × σ) ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1))
      (∑ i, Finsupp.mapDomain (Prod.mk i) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [prodRename_apply] using this

omit [Fintype ι] in
theorem tprod_ne_zero [Finite ι] (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) :
    PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

omit [Fintype ι] in
theorem substF_rename {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (i : ι) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    substF h g (rename (Prod.mk i) P) = rename (Prod.mk i) (subst2 (h i) (g i) P) := by
  have key : (substF h g).comp (rename (Prod.mk i)) = (rename (Prod.mk i)).comp (subst2 (h i) (g i)) := by
    refine algHom_ext fun p => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rename_X, substF_X, subst2_X, map_sum, map_mul, rename_C]
  exact congrArg (fun f => f P) key

theorem exists_tensor : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  intro ι _ N n A B _ _ _ _ I hI
  classical
  refine ⟨tens I, ?_, ?_⟩
  · have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
      intro i
      by_contra hc
      push Not at hc
      exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
    choose P v hPv using hex
    intro h0
    have h1 := tens_prod I P
    rw [h0] at h1
    have h2 := congrArg (fun f => f (PiTensorProduct.tprod ℂ v)) h1
    simp only [LinearMap.zero_apply, PiTensorProduct.map_tprod] at h2
    exact tprod_ne_zero _ hPv h2.symm
  · intro c h g a b hab
    have key : ∀ Q : ι → MvPolynomial (Fin N × Fin n) ℂ,
        (tens I ((∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i)))) ∘ₗ PiTensorProduct.map a
          = PiTensorProduct.map b ∘ₗ tens I (∏ i, rename (Prod.mk i) (Q i)) := by
      intro Q
      have e : (∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i))
          = ∏ i, rename (Prod.mk i) (c i • subst2 (h i) (g i) (Q i)) := by
        simp only [map_prod, substF_rename, map_smul, Finset.prod_smul]
      rw [e, tens_prod, tens_prod, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      exact LinearMap.ext fun v => hab i (Q i) v
    intro P x
    induction P using MvPolynomial.induction_on' with
    | monomial α r =>
      have e : (monomial α r : MvPolynomial (ι × Fin N × Fin n) ℂ)
          = r • ∏ i, rename (Prod.mk i) (monomial (res α i) (1 : ℂ)) := by
        rw [prod_rename_monomial, sum_res, smul_monomial, smul_eq_mul, mul_one]
      have := congrArg (fun f => f x) (key fun i => monomial (res α i) 1)
      simp only [LinearMap.comp_apply] at this
      rw [e, map_smul (substF h g), smul_comm, map_smul (tens I), LinearMap.smul_apply, this, map_smul (tens I),
        LinearMap.smul_apply, map_smul]
    | add p q hp hq =>
      rw [map_add (f := _), smul_add, map_add (f := _), LinearMap.add_apply, hp, hq, map_add (tens I),
        LinearMap.add_apply, map_add]

end GlobalTheory.CompactHowe.PolyTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinearStatement
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  first | exact @GlobalTheory.CompactHowe.PolyTensor.exists_tensor | exact GlobalTheory.CompactHowe.PolyTensor.exists_tensor | (intros; apply GlobalTheory.CompactHowe.PolyTensor.exists_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactHowe.LastStep

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

def inFr (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * g * (M.fr τ)⁻¹

theorem inFr_one (M : DSModel V S) (τ : D.what₂.Tau) : inFr M τ 1 = 1 := by
  rw [inFr, Matrix.mul_one, Matrix.mul_nonsing_inv _ (fr_det M τ)]

theorem det_inFr (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (inFr M τ g).det = g.det := by
  rw [inFr, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.det_one, one_mul]

theorem inFr_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : inFr M τ g ∈ UJset (M.ε τ) := by
  have h : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := Matrix.mul_nonsing_inv _ (fr_det M τ)
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (inFr M τ g)ᴴ * Formalism.REAL.Jm (M.ε τ) * inFr M τ g = Formalism.REAL.Jm (M.ε τ)
  calc (inFr M τ g)ᴴ * Formalism.REAL.Jm (M.ε τ) * inFr M τ g
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [inFr, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [M.fr_gram, h, ← M.fr_gram]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem cart_eq_one (M : DSModel V S) (h : ∀ τ, M.ε τ = allPos V.rank) : cart M = fun _ => 1 := by
  funext τ
  rw [cart, h, Jm_allPos, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem isCartan_one (M : DSModel V S) (h : ∀ τ, M.ε τ = allPos V.rank) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) 1 := by
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, ← M.fr_gram, h, Jm_allPos]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

def polAct (M : DSModel V S) (M' : DSModel W S') (x₁ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (φ : PolF D W.rank V.rank) : PolF D W.rank V.rank :=
  (∏ τ, (inFr M' τ (h τ)).det ^ x₁ τ * (inFr M τ (g τ)).det ^ x₃ τ) •
    substF (fun τ => inFr M' τ (h τ)) (fun τ => ((inFr M τ (g τ))⁻¹)ᵀ) φ

theorem totalDegree_polAct (M : DSModel V S) (M' : DSModel W S') (x₁ x₃ : D.what₂.Tau → ℤ) (g h φ) :
    (polAct M M' x₁ x₃ g h φ).totalDegree ≤ φ.totalDegree :=
  (MvPolynomial.totalDegree_smul_le _ _).trans (totalDegree_substF_le _ _ _)

theorem om_ptOf {k : Fin D.R.m} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) (hV : V.SigOK) (hW : W.SigOK)
    (M : DSModel V S) (M' : DSModel W S') (hε : ∀ τ, M.ε τ = allPos V.rank) (hε' : ∀ τ, M'.ε τ = allPos W.rank)
    (x₁ x₃ : D.what₂.Tau → ℤ) (h1 : ∀ τ, (x₁ τ : ℚ) = expS D k τ + (V.rank : ℚ) / 2)
    (h3 : ∀ τ, (x₃ τ : ℚ) = -((W.rank : ℚ) / 2 + expT D k τ))
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsStepWeil k ψ V W ω) {f : WO V W → ℂ}
    (hf : IsVacVec ψ θ M M' f) {g : GA D V} (hg : g ∈ GinfC V) {h : GA D W} (hh : h ∈ GinfC W) (φ : PolF D W.rank V.rank) :
    ω (g, h) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f
      (polAct M M' x₁ x₃ (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt W h)) φ) := by
  obtain ⟨χS, χT, hw, he⟩ := hω
  have hv := hf.vac
  unfold ptOf
  rw [cart_eq_one M hε, cart_eq_one M' hε'] at hv ⊢
  have e1 := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χS χT ω hw hθ hV hW (fun _ => 1) (isCartan_one M hε) (isCartan_one M' hε')
    _ _ (fun τ => (he τ).1) (fun τ => (he τ).2) x₁ (fun τ => x₁ τ - V.rank) x₃ h1
    (fun τ => by push_cast; rw [h1]; ring)
    (fun τ => by
      have := congrArg (fun q : ℚ => (q : ℂ)) (h3 τ)
      simp only [Matrix.trace_one, Fintype.card_fin]
      push_cast at this
      exact this)
    f hf.theta hv g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χS χT ω hw hθ (fun _ => 1) (fun _ => 1) (onb M)
    (fun τ => onb M τ * inFr M τ (compAt θ τ (Formalism.L2.Theta.mt V g))) (fun _ => 1) (fun _ => 1) (onb M')
    (fun τ => onb M' τ * inFr M' τ (compAt θ τ (Formalism.L2.Theta.mt W h))) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ)])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M' τ)]) f hf.theta φ).2
  rw [e2, e1, GlobalTheory.FiniteFock.pureTensorO_smul, GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D ψ θ V W hw.std hθ _ _ _ _ f hf.theta, polAct, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) + 1) = 1 := by module
  rw [det_inFr, det_inFr, a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one,
    _root_.one_zpow, mul_one]

open Classical in
theorem compAt_atTau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ g))) = Function.update (fun _ => 1) τ g := by
  have h := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  funext ρ
  by_cases e : ρ = τ
  · subst e
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne e]
    exact h.2.2 ρ e

theorem compAt_one (θ : InfFam D) : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V 1)) = fun _ => 1 :=
  funext fun ρ => GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ (inFr M τ 1) = 1 := by
  rw [inFr_one]
  exact (M.ds τ).2.2.1.1.1

open Classical in
theorem map_update (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    PiTensorProduct.map (fun ρ => (M.σ ρ (inFr M ρ (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ)) : M.H ρ →ₗ[ℂ] M.H ρ)) =
      actT M τ g := by
  unfold actT
  congr 1
  funext ρ
  by_cases e : ρ = τ
  · subst e
    rw [Function.update_self, Function.update_self]
    rfl
  · rw [Function.update_of_ne e, Function.update_of_ne e, rep_one]
    rfl

theorem map_one' (M : DSModel V S) :
    PiTensorProduct.map (fun ρ => (M.σ ρ (inFr M ρ 1) : M.H ρ →ₗ[ℂ] M.H ρ)) = LinearMap.id := by
  rw [← PiTensorProduct.map_id]
  congr 1
  funext ρ
  rw [rep_one]
  rfl

open Classical in
theorem update_mem (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (ρ : D.what₂.Tau) : Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ ∈
      Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  by_cases e : ρ = τ
  · subst e
    rwa [Function.update_self]
  · rw [Function.update_of_ne e]
    exact GlobalTheory.PointAtPlaceHom.one_mem_UH _


open Classical in
theorem exists_it (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK) (hW : W.SigOK)
    (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha
  have hp := fun τ => GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 hn ν n1 n2 n3 n4 using fun τ => (hp τ).2.2
  have m := fun τ => GlobalTheory.T.allPositive_model_finiteDimensional_compactType D V _ M τ (hε τ)
  have m' := fun τ => GlobalTheory.T.allPositive_model_finiteDimensional_compactType D W _ M' τ (hε' τ)
  have hl := fun τ =>
    haveI := (m τ).1
    haveI := (m' τ).1
    GlobalTheory.T.exists_local_howe_contraction_compact_unitary W.rank V.rank (hn τ) (ν τ) (x₁ τ) (x₃ τ) _ _ (M.H τ) (M.σ τ) (M'.H τ) (M'.σ τ) (n1 τ) (n2 τ) (n3 τ) (n4 τ)
      (m τ).2.2.1 (m τ).2.2.2 (m' τ).2.2.1 (m' τ).2.2.2
  choose I I0 hI using hl
  obtain ⟨J, J0, hJ⟩ := GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear D.what₂.Tau W.rank V.rank M'.H M.H I I0
  have key : ∀ (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → (∀ τ, h τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) → ∀ φ x,
      J (polAct M M' x₁ x₃ g h φ) (PiTensorProduct.map (fun τ => (M'.σ τ (inFr M' τ (h τ)) : M'.H τ →ₗ[ℂ] M'.H τ)) x) =
        PiTensorProduct.map (fun τ => (M.σ τ (inFr M τ (g τ)) : M.H τ →ₗ[ℂ] M.H τ)) (J φ x) := fun g h hg hh =>
    hJ _ _ _ _ _ fun τ P v => hI τ _ (hε' τ ▸ inFr_mem M' τ (hh τ)) _ (hε τ ▸ inFr_mem M τ (hg τ)) P v
  obtain ⟨It, hIt⟩ := GlobalTheory.T.exists_realIntertwiner_of_compactGroup_intertwiner D V W _ _ θ M M' J
    (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h)) hθ
    (fun τ => ⟨(m τ).1, (m τ).2.1⟩) (fun τ => ⟨(m' τ).1, (m' τ).2.1⟩) J0
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _)
    (fun τ g hg φ x => by
      have := key _ (fun _ => 1) (update_mem τ hg) (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) φ x
      rwa [map_update, map_one'] at this)
    (fun τ h hh φ x => by
      have := key (fun _ => 1) _ (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) (update_mem τ hh) φ x
      rwa [map_update, map_one'] at this)
  refine ⟨It, fun ω f hω hf => hIt ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf) (fun τ g hg φ => ?_) fun τ h hh φ => ?_⟩
  · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
    rwa [compAt_atTau hθ τ hg, compAt_one] at this
  · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
    rwa [compAt_atTau hθ τ hh, compAt_one] at this

theorem lastStep_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX ∧ ∃ It, ({ R with ItX := It } : RealDat D A Ks).chain_ItX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hω hv
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  refine ⟨fun t P => ?_, ?_⟩
  · exact (GlobalTheory.OrientedHeis.om_pureTensorO D R.ψ R.θ _ _ _ _ (R.ωX t) (hω t) hM.inf _ (cart (R.MY (D.R.m - 1))) _
      (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ 1) * onb (R.MY (D.R.m - 1)) τ) _ (cart R.MX) _
      (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ 1) * onb R.MX τ) 1 1
      (fun τ => by rw [congrFun (compAt_one R.θ) τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [congrFun (compAt_one R.θ) τ, Matrix.one_mul, Matrix.mul_one])
      (fun _ => rfl) (fun _ => rfl) (R.vX t) (hS t).2.theta P).1
  · obtain ⟨It, hIt⟩ := exists_it k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
      (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ
    exact ⟨It, fun t => hIt (R.ωX t) (R.vX t) (hS t).1 (hS t).2⟩

end GlobalTheory.CompactHowe.LastStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwinerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_lastStep_real_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX ∧ ∃ It, ({ R with ItX := It } : RealDat D A Ks).chain_ItX := by
  first | exact @GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner | exact GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner | (intros; apply GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner <;> assumption)
end
