module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsSkewUnit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.DetLast
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinOneOneMem

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IwaTransport
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IncMInvmul
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.GramInvSmul
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

set_option linter.unusedSectionVars false

section Generic

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι] (c : S →ₐ[R] S)

theorem map_mul_c (A B : Matrix ι ι S) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul

theorem gram_inv {H J : Matrix ι ι S} (M : GL ι S) (hM : M.1ᵀ * H * M.1.map c = J) :
    (M⁻¹).1ᵀ * J * (M⁻¹).1.map c = H := by
  subst hM
  have h1 : (M⁻¹).1ᵀ * M.1ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : M.1.map c * (M⁻¹).1.map c = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c c, Units.mul_inv]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  calc (M⁻¹).1ᵀ * (M.1ᵀ * H * M.1.map c) * (M⁻¹).1.map c
      = ((M⁻¹).1ᵀ * M.1ᵀ) * H * (M.1.map c * (M⁻¹).1.map c) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem conj_mem {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) {y : GL ι S}
    (hy : y ∈ UG c H₀) : M * y * M⁻¹ ∈ UG c H := by
  have hy' : (y : Matrix ι ι S)ᵀ * H₀ * (y : Matrix ι ι S).map c = H₀ := hy
  have hmid : (y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c
      = M.1ᵀ * H * M.1.map c := by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, hy']
  have key : (M⁻¹).1ᵀ * ((y : Matrix ι ι S)ᵀ * (M.1ᵀ * H * M.1.map c) * (y : Matrix ι ι S).map c)
      * (M⁻¹).1.map c = H := by
    rw [hmid]
    exact PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M rfl
  show ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S)ᵀ * H * ((M * y * M⁻¹ : GL ι S) : Matrix ι ι S).map c = H
  simp only [Units.val_mul, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.Ldexb.map_mul_c]
  simpa only [Matrix.mul_assoc] using key

theorem gram_inv_smul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : Sˣ) (hM : M.1ᵀ * H * M.1.map c = (s : S) • H₀) :
    (M⁻¹).1ᵀ * H₀ * (M⁻¹).1.map c = ((s⁻¹ : Sˣ) : S) • H := by
  have h := PositivityTheory.SiegelWeilFormula.Ldexb.gram_inv c M hM
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  rw [← h, smul_smul, Units.inv_mul, one_smul]

def cj {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) : UG c H :=
  ⟨M * z.1 * M⁻¹, conj_mem c M s hM z.2⟩

theorem cj_val {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    (cj c M s hM z).1 = M * z.1 * M⁻¹ := rfl

theorem cj_mul {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z z' : UG c H₀) :
    cj c M s hM (z * z') = cj c M s hM z * cj c M s hM z' := by
  apply Subtype.ext
  show M * ((z : GL ι S) * (z' : GL ι S)) * M⁻¹ = (M * (z : GL ι S) * M⁻¹) * (M * (z' : GL ι S) * M⁻¹)
  group

theorem cj_inv {H H₀ : Matrix ι ι S} (M : GL ι S) (s : S) (hM : M.1ᵀ * H * M.1.map c = s • H₀) (z : UG c H₀) :
    cj c M s hM z⁻¹ = (cj c M s hM z)⁻¹ := by
  apply Subtype.ext
  show M * (z : GL ι S)⁻¹ * M⁻¹ = (M * (z : GL ι S) * M⁻¹)⁻¹
  group

end Generic

section Unitary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_unitary (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1) (X : Matrix ι ι ℂ) (hX : X * Xᴴ = 1) :
    (Matrix.diagonal d * X * Matrix.diagonal (star d)) * (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ = 1 := by
  have h1 : Matrix.diagonal (star d) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd i
  have h2 : Matrix.diagonal d * Matrix.diagonal (star d) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hd i
  have e : (Matrix.diagonal d * X * Matrix.diagonal (star d))ᴴ
      = Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_star, Matrix.mul_assoc]
  rw [e]
  calc Matrix.diagonal d * X * Matrix.diagonal (star d) * (Matrix.diagonal d * (Xᴴ * Matrix.diagonal (star d)))
      = Matrix.diagonal d * X * (Matrix.diagonal (star d) * Matrix.diagonal d) * Xᴴ * Matrix.diagonal (star d) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal d * Matrix.diagonal (star d) := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc (Matrix.diagonal d) X, hX, Matrix.mul_one]
    _ = 1 := h2

end Unitary

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

def incGL (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) b

theorem incGL_val (b : GL (Fin n ⊕ Fin n) E) : (incGL (F := F) b).1 = incM F b.1 := rfl

theorem incGL_inv (b : GL (Fin n ⊕ Fin n) E) : (incGL (F := F) b)⁻¹ = incGL b⁻¹ := (map_inv _ _).symm

theorem incM_tr {α β : Type} (X : Matrix α β E) : incM F Xᵀ = (incM F X)ᵀ := Matrix.transpose_map

theorem incM_cA {α β : Type} (X : Matrix α β E) : (incM F X).map (cA σ) = incM F (X.map σ) := by ext; rfl

theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext (i | i) (j | j) <;> simp [incM, dbl]

theorem incM_mulT {α β γ : Type} [Fintype β] (X : Matrix α β E) (Z : Matrix β γ E) :
    incM F (X * Z) = incM F X * incM F Z := Matrix.map_mul

theorem incM_invmul (b : GL (Fin n ⊕ Fin n) E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← incM_mulT, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_A {J : Matrix (Fin n) (Fin n) E} {b : GL (Fin n ⊕ Fin n) E} {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E}
    (h : b.1ᵀ * dbl J * b.1.map σ = G) :
    (incGL (F := F) b).1ᵀ * dbl (incM F J) * (incGL b).1.map (cA σ) = incM F G := by
  rw [incGL_val, incM_cA, ← incM_dbl, ← incM_tr, ← incM_mulT, ← incM_mulT, h]

def dgv (u : AE F E) : Fin n ⊕ Fin n → AE F E := Sum.elim (fun _ => u) (fun _ => 1)

def dgU (r : (AE F E)ˣ) : GL (Fin n ⊕ Fin n) (AE F E) where
  val := Matrix.diagonal (dgv (r : AE F E))
  inv := Matrix.diagonal (dgv ((r⁻¹ : (AE F E)ˣ) : AE F E))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp [dgv]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp [dgv]

theorem dgU_val (r : (AE F E)ˣ) : (dgU (n := n) r).1 = Matrix.diagonal (dgv (r : AE F E)) := rfl

theorem dgU_inv_val (r : (AE F E)ˣ) : ((dgU (n := n) r)⁻¹).1 = Matrix.diagonal (dgv ((r⁻¹ : (AE F E)ˣ) : AE F E)) := rfl

theorem dg_jeps (r : (AE F E)ˣ) (ε ε₀ : ℤˣ)
    (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E)) :
    (dgU (n := n) r).1ᵀ * incM F (Ald.jeps n ε) * (dgU r).1.map (cA σ) = (r : AE F E) • incM F (Ald.jeps n ε₀) := by
  rw [dgU_val, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _)]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [dgv, Ald.jeps, incM, Matrix.diagonal_mul, Matrix.mul_diagonal, hij] <;> rw [hr, mul_comm]

def MU (b b₀ : GL (Fin n ⊕ Fin n) E) (r : (AE F E)ˣ) : GL (Fin n ⊕ Fin n) (AE F E) := incGL b * dgU r * incGL b₀⁻¹

theorem MU_gram {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E} {ε ε₀ : ℤˣ}
    (he : b.1ᵀ * dbl Y.J * b.1.map σ = Ald.jeps n ε) (he₀ : b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n ε₀)
    (r : (AE F E)ˣ) (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E)) :
    (MU b b₀ r).1ᵀ * dbl (incM F Y.J) * (MU b b₀ r).1.map (cA σ) = (r : AE F E) • dbl (incM F Y₀.J) := by
  have h1 := gram_A (F := F) he
  have h0 := gram_inv (cA σ) (incGL (F := F) b₀) (gram_A (F := F) he₀)
  rw [incGL_inv] at h0
  simp only [MU, Units.val_mul, Matrix.transpose_mul, map_mul_c]
  calc (incGL b₀⁻¹).1ᵀ * ((dgU r).1ᵀ * (incGL b).1ᵀ) * dbl (incM F Y.J) *
        ((incGL b).1.map (cA σ) * (dgU r).1.map (cA σ) * (incGL b₀⁻¹).1.map (cA σ)) =
      (incGL b₀⁻¹).1ᵀ * ((dgU r).1ᵀ * ((incGL b).1ᵀ * dbl (incM F Y.J) * (incGL b).1.map (cA σ)) * (dgU r).1.map (cA σ)) *
        (incGL b₀⁻¹).1.map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, dg_jeps r ε ε₀ hr, Matrix.mul_smul, Matrix.smul_mul, h0]

theorem inFrame_cj {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E} (r : (AE F E)ˣ)
    (hM : (MU b b₀ r).1ᵀ * dbl (incM F Y.J) * (MU b b₀ r).1.map (cA σ) = (r : AE F E) • dbl (incM F Y₀.J))
    (z : G2 σ Y₀) :
    inFrame b (cj (cA σ) (MU b b₀ r) (r : AE F E) hM z : G2 σ Y) = (dgU r).1 * inFrame b₀ z * ((dgU r)⁻¹).1 := by
  show incM F (b⁻¹).1 * (MU b b₀ r * z.1 * (MU b b₀ r)⁻¹).1 * incM F b.1 =
    (dgU r).1 * (incM F (b₀⁻¹).1 * z.1.1 * incM F b₀.1) * ((dgU r)⁻¹).1
  simp only [MU, mul_inv_rev, incGL_inv, inv_inv, Units.val_mul, incGL_val]
  simp only [Matrix.mul_assoc]
  rw [incM_invmul, Matrix.mul_one, ← Matrix.mul_assoc (incM F (b⁻¹).1), incM_invmul, Matrix.one_mul]

theorem dg_entry (r : (AE F E)ˣ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (i j : Fin n ⊕ Fin n) :
    ((dgU r).1 * X * ((dgU r)⁻¹).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) i j = dgv (r : AE F E) i * X i j * dgv ((r⁻¹ : (AE F E)ˣ) : AE F E) j := by
  rw [dgU_val, dgU_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dg_fin (r : (AE F E)ˣ)
    (hrf : ∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : ∀ i j, finOne F • X i j ∈ intHat F E) (i j : Fin n ⊕ Fin n) :
    finOne F • ((dgU r).1 * X * ((dgU r)⁻¹).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) i j ∈ intHat F E := by
  rw [dg_entry]
  refine (Frame.mem_intHat _).2 fun v => ?_
  have hx := (Frame.mem_intHat _).1 (hX i j) v
  rw [map_mul, map_mul]
  refine mul_mem (mul_mem ?_ hx) ?_
  · rcases i with i | i
    · exact (hrf v).1
    · simp only [dgv, Sum.elim_inr, map_one]; exact one_mem _
  · rcases j with j | j
    · exact (hrf v).2
    · simp only [dgv, Sum.elim_inr, map_one]; exact one_mem _

theorem dg_arch (r : (AE F E)ˣ) (π : AE F E →+* ℂ) (hri : ‖π (r : AE F E)‖ = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : X.map π * (X.map π)ᴴ = 1) :
    ((dgU r).1 * X * ((dgU r)⁻¹).1).map π * (((dgU r).1 * X * ((dgU r)⁻¹).1).map π)ᴴ = 1 := by
  have h0 : π (r : AE F E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hri; exact zero_ne_one hri
  have h2 : star (π (r : AE F E)) * π (r : AE F E) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hri]; simp
  have hinv : π ((r⁻¹ : (AE F E)ˣ) : AE F E) = star (π (r : AE F E)) := by
    have h1 : π (r : AE F E) * π ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact mul_left_cancel₀ h0 (h1.trans (by rw [mul_comm]; exact h2.symm))
  have e : ((dgU r).1 * X * ((dgU r)⁻¹).1).map π =
      Matrix.diagonal (fun i => π (dgv (r : AE F E) i)) * X.map π * Matrix.diagonal (star fun i => π (dgv (r : AE F E) i)) := by
    rw [Matrix.map_mul, Matrix.map_mul, dgU_val, dgU_inv_val, Matrix.diagonal_map (map_zero π),
      Matrix.diagonal_map (map_zero π)]
    congr 2
    funext i
    rcases i with i | i
    · simp only [dgv, Sum.elim_inl, Pi.star_apply, hinv]
    · simp [dgv]
  rw [e]
  refine diag_unitary _ (fun i => ?_) _ hX
  rcases i with i | i
  · exact h2
  · simp [dgv]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {n : ℕ}

theorem iwa_transport {B : Base F E} (hσ : ∀ z, σ (σ z) = z) {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E}
    {ε ε₀ : ℤˣ} (hb : IsFrame2 σ Y b) (hb₀ : IsFrame2 σ Y₀ b₀) (he : b.1ᵀ * dbl Y.J * b.1.map σ = Ald.jeps n ε)
    (he₀ : b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n ε₀) (r : (AE F E)ˣ)
    (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E))
    (hrf : ∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v)
    (hri : ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1) {K₀ : Subgroup (G2 σ Y₀)} (hK₀ : IsStdK (σ := σ) (Y := Y₀) B b₀ K₀)
    (hI : ∀ x : G2 σ Y₀, ∃ p t, IsPar p t ∧ ∃ k ∈ K₀, x = p * k) {K : Subgroup (G2 σ Y)}
    (hK : IsStdK (σ := σ) (Y := Y) B b K) : ∀ x : G2 σ Y, ∃ p t, IsPar p t ∧ ∃ k ∈ K, x = p * k := by
  have hM := MU_gram (F := F) he he₀ r hr
  have hM' := gram_inv_smul (cA σ) (MU b b₀ r) r hM
  intro x
  let y : G2 σ Y₀ := cj (cA σ) (MU b b₀ r)⁻¹ ((r⁻¹ : (AE F E)ˣ) : AE F E) hM' x
  obtain ⟨p₀, t₀, hp₀, k₀, hk₀, hy⟩ := hI y
  have hx : x = cj (cA σ) (MU b b₀ r) (r : AE F E) hM y := Subtype.ext (by simp only [y, cj_val]; group)
  rw [hy, cj_mul] at hx
  obtain ⟨hpf, -⟩ := par_to hb₀ hp₀
  have hpf' : ParF b (cj (cA σ) (MU b b₀ r) (r : AE F E) hM p₀ : G2 σ Y) := by
    unfold ParF
    rw [inFrame_cj]
    ext i j
    have := congrFun (congrFun hpf i) j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this ⊢
    rw [dg_entry, this, mul_zero, zero_mul]
  obtain ⟨t, ht, -⟩ := par_of hb hpf'
  refine ⟨_, t, ht, _, ?_, hx⟩
  obtain ⟨harch, hfin⟩ := (hK₀ k₀).1 hk₀
  refine (hK _).2 ⟨fun w => ?_, ?_⟩
  · rw [inFrame_cj]; exact dg_arch r _ (hri w) _ (harch w)
  · rintro k' (rfl | rfl) i j
    · rw [inFrame_cj]; exact dg_fin r hrf _ (hfin k₀ (Set.mem_insert _ _)) i j
    · rw [← cj_inv, inFrame_cj]; exact dg_fin r hrf _ (hfin k₀⁻¹ (Set.mem_insert_of_mem _ rfl)) i j

end PositivityTheory.SiegelWeilFormula.Ldexb

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


omit [NumberField F] [NumberField E] in
theorem eps_neg {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {ε : ℤˣ}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : ((ε : ℤ) : E) = -1 := by
  have hD : ((dbl J).map σ)ᵀ = -dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]
  set G := bᵀ * dbl J * b.map σ with hG
  have hs : (G.map σ)ᵀ = -G := by
    rw [hG, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_map]
    have e : (⇑σ ∘ ⇑σ) = id := funext hc
    rw [e, Matrix.map_id, hD, show (bᵀ.map σ)ᵀ = b.map σ by rw [Matrix.transpose_map, Matrix.transpose_transpose]]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have := congrFun (congrFun hs (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  rw [hb] at this
  simpa [Matrix.fromBlocks] using this

theorem eps_neg_unit {ε : ℤˣ} (h : ((ε : ℤ) : E) = -1) : ε = -1 := by
  rcases Int.units_eq_one_or ε with e | e
  · exfalso
    rw [e] at h
    have : (2 : E) = 0 := by
      have h' : ((1 : ℤ) : E) = -1 := by exact_mod_cast h
      push_cast at h'
      linear_combination h'
    exact two_ne_zero this
  · exact e

theorem hgtPull : Ald.HgtPull := by
  intro F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ
  have hB := d.ok.good
  have hσ : ∀ z, σ (σ z) = z := UnitA.sig_sig hB.cm
  refine ⟨fun x => ?_, val_pull h hJ hb⟩
  obtain ⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩ := exists_eigenvalueGLOne_eq_cuspidalLabel_gen hB hn
  obtain ⟨ε, he⟩ := hb.1
  have hK : IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j) := Ald.kStd F E σ d n h Y b j hb hJ
  rcases hs with ⟨-, hY⟩ | ⟨-, hY⟩
  ·
    have hε : ε = -1 := eps_neg_unit (eps_neg hn hσ hY he)
    subst hε
    obtain ⟨r, hr, hrf, hri⟩ := exists_skewUnit hB
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x
    rw [hr]; push_cast; ring
  ·
    have hε : ε = 1 := eps_unit (eps_one hn hσ hY he)
    subst hε
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x
    · simp
    · simp only [Units.val_one, inv_one, map_one]; exact ⟨one_mem _, one_mem _⟩
    · simp

end PositivityTheory.SiegelWeilFormula.Ldexb

end
