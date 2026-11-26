module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.InvMulSelfMatrixDoubled
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Tpar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {p q r : Type} [Fintype q] (M : Matrix p q E) (N : Matrix q r E) :
    incM F (M * N) = incM F M * incM F N := Matrix.map_mul

theorem incM_add {p q : Type} (M N : Matrix p q E) : incM F (M + N) = incM F M + incM F N :=
  Matrix.map_add _ (map_add _) M N

theorem incM_transpose {p q : Type} (M : Matrix p q E) : incM F Mᵀ = (incM F M)ᵀ := rfl

theorem incM_one {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_diagCols (n : ℕ) : incM F (diagCols (Fin n) : Matrix _ _ E) = diagCols (Fin n) := by
  simp only [incM, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_fromCols {p q r : Type} (M : Matrix p (q ⊕ r) E) :
    incM F M = Matrix.fromCols (incM F M.toCols₁) (incM F M.toCols₂) := by
  conv_lhs => rw [← Matrix.fromCols_toCols M]
  exact Matrix.fromCols_map _ _ _

theorem incM_map_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem dbl_incM {q : Type} [Fintype q] [DecidableEq q] (J : Matrix q q E) : dbl (incM F J) = incM F (dbl J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp

variable {n : ℕ} {Y : Spc F E n}

theorem frame_xy {b : GL (Fin n ⊕ Fin n) E} (h : IsFrame2 σ Y b) :
    b.1.toCols₁ᵀ * dbl Y.J * b.1.toCols₂.map σ = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := h
  rw [← Matrix.fromCols_toCols b.1, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map,
    Matrix.fromRows_mul_fromCols] at hε
  exact (Matrix.fromBlocks_inj.1 hε).2.1

theorem frame_xy_A {b : GL (Fin n ⊕ Fin n) E} (h : IsFrame2 σ Y b) :
    (incM F b.1.toCols₁)ᵀ * dbl (incM F Y.J) * (incM F b.1.toCols₂).map (cA σ) = 1 := by
  rw [incM_map_cA, dbl_incM, ← incM_transpose, ← incM_mul, ← incM_mul, frame_xy h, incM_one]

theorem inv_mul_self_matrix_doubled (x : G2 σ Y) : mat2 x⁻¹ * mat2 x = 1 :=
  Units.inv_mul x.1

theorem inFrame_mul {b : GL (Fin n ⊕ Fin n) E} {x : G2 σ Y} {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (hx : inFrame b x = N) : mat2 x * incM F b.1 = incM F b.1 * N := by
  rw [← hx, inFrame]
  simp only [← Matrix.mul_assoc, ← incM_mul, Units.mul_inv, incM_one, Matrix.one_mul]

theorem inv_mul_frame {x : G2 σ Y} {Bm N N' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (hx : mat2 x * Bm = Bm * N) (hN : N * N' = 1) : mat2 x⁻¹ * Bm = Bm * N' :=
  calc mat2 x⁻¹ * Bm = mat2 x⁻¹ * Bm * (N * N') := by rw [hN, Matrix.mul_one]
    _ = mat2 x⁻¹ * (mat2 x * Bm) * N' := by rw [hx]; simp only [Matrix.mul_assoc]
    _ = Bm * N' := by rw [← Matrix.mul_assoc, inv_mul_self_matrix_doubled, Matrix.one_mul]

theorem par_of {p q : Type} [Fintype p] [Fintype q] [DecidableEq q] {X : Matrix p p (AE F E)} {D : Matrix p q (AE F E)}
    {T0 T0i P : Matrix q q (AE F E)} (hT : T0 * T0i = 1) (h : X * (D * T0) = D * T0 * P) :
    X * D = D * (T0 * P * T0i) :=
  calc X * D = X * (D * T0) * T0i := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hT, Matrix.mul_one]
    _ = D * (T0 * P * T0i) := by rw [h]; simp only [Matrix.mul_assoc]

theorem hTens_eq {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E') (JB : Matrix β β E') (x y : Matrix α β E') :
    hTens c JA JB x y = Matrix.trace (x * JB * (y.map c)ᵀ * JAᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

variable {m : ℕ}

theorem symp_N (X : Matrix (Fin m) (Fin n) (AE F E)) (β T0 : Matrix (Fin n) (Fin n) (AE F E))
    (By : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (JA : Matrix (Fin m) (Fin m) (AE F E))
    (JB : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hf : ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T0)ᵀ * JB * By.map (cA σ) = 1) :
    symp (R := AF F) (cA σ) (-1) JA JB (-(X * βᵀ * T0ᵀ) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) (X * Byᵀ) =
      Algebra.trace (AF F) (AE F E) (Matrix.trace (β * (Xᵀ * JA * X.map (cA σ)))) := by
  rw [symp, hTens_eq]
  congr 1
  have e1 : -(X * βᵀ * T0ᵀ) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ * JB * ((X * Byᵀ).map (cA σ))ᵀ * JAᵀ =
      -(X * βᵀ * (((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * T0)ᵀ * JB * By.map (cA σ)) * (X.map (cA σ))ᵀ * JAᵀ) := by
    rw [Matrix.map_mul, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose, Matrix.transpose_mul]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  rw [e1, hf, Matrix.mul_one, Matrix.trace_neg, neg_one_mul, neg_neg, ← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (JA * X.map (cA σ)) β Xᵀ, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Tpar

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Tpar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {ψ : AddChar (AF F) ℂ}
  {dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) κ} {χ : Chr F E}
  {om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)} {S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)}
  {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}

theorem rho_rho (a b : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) (φ : (κ → AF F) → ℂ) :
    dd.rho ψ a (dd.rho ψ b φ) =
      ψ (⅟(2 : AF F) * symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J)) a b) • dd.rho ψ (a + b) φ := by
  rw [dd.form]
  funext x
  simp only [Darboux.rho, schr, map_add (f := _), Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul,
    Prod.fst_add, Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-((dd.e a).1 ⬝ᵥ (dd.e b).2)) * invOf_mul_self (2 : AF F)

theorem l_shift (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))))
    (Z : Matrix (Fin m) (Fin n) (AE F E)) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ + w) Φ) =
      ψ (-(⅟(2 : AF F) * symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))
        (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) w)) * l (dd.rho ψ w Φ) := by
  have e1 := congrArg l (rho_rho (dd := dd) (ψ := ψ) (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) w Φ)
  have mem : dd.rho ψ w Φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ
  rw [map_smul, smul_eq_mul] at e1
  have e2 := (h.kill Z _ mem).symm.trans e1
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem l_rho_om (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (x : G2 σ Y)
    (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ u (om x Φ)) = l (om x (dd.rho ψ (u * (mat2 x⁻¹)ᵀ) Φ)) := by
  apply congrArg l
  convert (h.weil.2.1.impl x (u * (mat2 x⁻¹)ᵀ) Φ hΦ).symm using 1
  congr 2
  simp only [actB]
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  change u = u * (mat2 x * mat2 x⁻¹)ᵀ
  rw [show mat2 x * mat2 x⁻¹ = 1 from Units.mul_inv x.1, Matrix.transpose_one, Matrix.mul_one]
  all_goals rfl

theorem l_om_par (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {x : G2 σ Y}
    {t : GL (Fin n) (AE F E)} (hx : IsPar x t) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    l (om x φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) * l φ := by
  rw [h.weil.2.2 l h.adm h.kill x t hx φ hφ, modu_norm, Fintype.card_fin]

theorem l_rho_S (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) (g : UA σ A.J)
    (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    l (dd.rho ψ u (S g Φ)) = l (dd.rho ψ (mat g⁻¹ * u) Φ) := by
  have e : S g (dd.rho ψ (mat g⁻¹ * u) Φ) = dd.rho ψ (mat g * (mat g⁻¹ * u)) (S g Φ) := h.lin.impl g _ Φ hΦ
  rw [← Matrix.mul_assoc, show mat g * mat g⁻¹ = 1 from Units.mul_inv g.1, Matrix.one_mul] at e
  have mem : dd.rho ψ (mat g⁻¹ * u) Φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ Φ hΦ
  rw [← e, h.fix g _ mem]

theorem psi_rat (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))))
    (a c : Matrix (Fin m) (Fin n ⊕ Fin n) E) :
    ψ (-(⅟(2 : AF F) * symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) a) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) c))) = 1 := by
  obtain ⟨y, z, hyz⟩ := h.rat a
  obtain ⟨y', z', hyz'⟩ := h.rat c
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := invOf_eq_right_inv (by
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one])
  have hd : ∀ u v : κ → F, (fun i => algebraMap F (AF F) (u i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v i)) =
      algebraMap F (AF F) (u ⬝ᵥ v) := fun u v => by simp [dotProduct]
  unfold incM at hyz hyz'
  rw [dd.form, hyz, hyz']
  simp only [hd, h2, ← map_sub, ← map_mul, ← map_neg]
  exact hψ.2.1 _

end PositivityTheory.SiegelWeilFormula.Tpar

end
