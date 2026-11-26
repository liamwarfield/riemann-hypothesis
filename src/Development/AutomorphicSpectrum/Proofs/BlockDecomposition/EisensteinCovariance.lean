module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplementSubspace
noncomputable def UpperTheory.Reformulated.B.ComplementSubspace.IsCompl :
    {K : Type} → [Field K] → {n r : ℕ} → Matrix (Fin r) (Fin n) K → Matrix (Fin n) (Fin n) K → Prop :=
    fun {K : Type} [Field K] {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) ↦
      IsUnit a.det ∧ ∀ (i : Fin n) (hi : (↑i : ℕ) < r), a i = c (⟨(↑i : ℕ), hi⟩ : Fin r)

namespace ComplementBasis

private lemma basis_sub {K : Type} [Field K] {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ c : Fin (Module.finrank K U) → (Fin n → K),
      LinearIndependent K c ∧ Submodule.span K (Set.range c) = U := by
  let b := Module.finBasis K U
  refine ⟨fun i => (b i : Fin n → K), ?_, ?_⟩
  · exact b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => (b i : Fin n → K)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

end ComplementBasis

open ComplementBasis in
theorem UpperTheory.Reformulated.B.ComplementSubspace.main :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (U : Submodule K (Fin n → K)),
      ∃ (c : Matrix (Fin (Module.finrank K ↥U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
        (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ UpperTheory.Reformulated.B.ComplementSubspace.IsCompl c a := by
  intro K _ n U
  obtain ⟨c, hcli, hcsp⟩ := basis_sub U
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨w, hwli, hwsp⟩ := basis_sub W
  have hrm : Module.finrank K U + Module.finrank K W = n := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    rw [Module.finrank_fin_fun] at this
    omega
  let a : Matrix (Fin n) (Fin n) K := fun i =>
    if h : (i : ℕ) < Module.finrank K U then c ⟨i, h⟩ else w ⟨(i : ℕ) - Module.finrank K U, by have := i.2; omega⟩
  refine ⟨c, a, ⟨hcli, hcsp⟩, ?_, ?_⟩
  · let e : Fin (Module.finrank K U) ⊕ Fin (Module.finrank K W) ≃ Fin n := finSumFinEquiv.trans (finCongr hrm)
    have hg : LinearIndependent K (Sum.elim c w) := by
      apply LinearIndependent.sum_type hcli hwli
      rw [hcsp, hwsp]; exact hUW.disjoint
    have hae : (fun i => a i) ∘ e = Sum.elim c w := by
      funext x
      rcases x with j | k
      · simp [e, a]
      · simp [e, a]
    have hla : LinearIndependent K (fun i => a i) := by
      rw [← linearIndependent_equiv e, hae]; exact hg
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp hla
  · intro i hi
    simp [a, hi]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupInductionGenerators
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Transfer

section Field

variable {F₀ : Type} [Field F₀] {n : ℕ}

theorem block_matrix_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose {R : Type} (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E)ᵀ = blk4 Aᵀ Cᵀ Bᵀ Eᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_mul (σ : F₀ →+* F₀) {N : ℕ} (g h : Matrix (Fin N) (Fin N) F₀) : cT σ (g * h) = cT σ h * cT σ g := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_blk4 (σ : F₀ →+* F₀) (A B C E : Matrix (Fin n) (Fin n) F₀) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, block_matrix_map, blockMatrixTwoByTwoFin_transpose]

theorem cT_zero (σ : F₀ →+* F₀) : cT σ (0 : Matrix (Fin n) (Fin n) F₀) = 0 := by
  ext i j; simp [cT]

theorem cT_one (σ : F₀ →+* F₀) : cT σ (1 : Matrix (Fin n) (Fin n) F₀) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]

theorem cT_neg (σ : F₀ →+* F₀) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (-x) = -cT σ x := by
  ext i j; simp [cT]

theorem cT_cT {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (cT σ x) = x := by
  ext i j; simp [cT, hσ]

theorem isUnit_det_cT (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (cT σ a).det := by
  have e : (cT σ a).det = σ a.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e]; exact ha.map σ

theorem mA_isUnit_det (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (mA σ a).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 a⁻¹ 0 0 (cT σ a)) ?_
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv _ ha
  have h2 : (cT σ a)⁻¹ * cT σ a = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_cT σ ha)
  rw [mA, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, block_matrix_one]

theorem nB_isUnit_det (b : Matrix (Fin n) (Fin n) F₀) : IsUnit (nB b).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 1 (-b) 0 1) ?_
  rw [nB, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem Jm_isUnit_det : IsUnit (EC.Jm F₀ n).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 0 (-1) 1 0) ?_
  rw [EC.Jm, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem mA_isUnitary {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) :
    IsUnitary σ (EC.Jm F₀ n) (mA σ a) := by
  have h1 : cT σ a * (cT σ a)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_cT σ ha)
  have h2 : cT σ (cT σ a)⁻¹ * a = 1 := by
    have h := congrArg (cT σ) h1
    rwa [cT_mul, cT_cT hσ, cT_one] at h
  unfold IsUnitary EC.Jm mA
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, h1, h2]

theorem nB_isUnitary {σ : F₀ →+* F₀} {b : Matrix (Fin n) (Fin n) F₀} (hb : cT σ b = b) :
    IsUnitary σ (EC.Jm F₀ n) (nB b) := by
  unfold IsUnitary EC.Jm nB
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, hb, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, add_neg_cancel]

theorem Jm_isUnitary (σ : F₀ →+* F₀) : IsUnitary σ (EC.Jm F₀ n) (EC.Jm F₀ n) := by
  unfold IsUnitary EC.Jm
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, cT_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel]

theorem isUnitary_mul {σ : F₀ →+* F₀} {N : ℕ} {J g h : Matrix (Fin N) (Fin N) F₀} (hg : IsUnitary σ J g)
    (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul]
  calc cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hg, hh]

end Field

variable {D : D7} {n : ℕ}

theorem sig_sig (x : D.host.E) :
    (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x :=
  star_star x

theorem cT_sig_eq {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

theorem map_mA (a : Matrix (Fin n) (Fin n) D.host.E) :
    (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a).map (incA D) =
      blk4 (rat a) 0 0 (adj (rat a⁻¹)) := by
  change (blk4 a 0 0 (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) = _
  rw [block_matrix_map, cT_sig_eq, ← Matrix.conjTranspose_nonsing_inv, ← rat_conjTranspose]
  simp only [Matrix.map_zero _ (map_zero (incA D))]
  rfl

theorem map_nB (b : Matrix (Fin n) (Fin n) D.host.E) :
    (nB b).map (incA D) = blk4 1 (rat b) 0 1 := by
  change (blk4 1 b 0 1).map (incA D) = _
  rw [block_matrix_map]
  show blk4 (rat 1) (rat b) (rat 0) (rat 1) = _
  rw [rat_one, rat_zero]

theorem map_Jm : (EC.Jm D.host.E n).map (incA D) = blk4 0 1 (-1) 0 := by
  rw [EC.Jm, block_matrix_map]
  show blk4 (rat 0) (rat 1) (rat (-1)) (rat 0) = _
  simp only [rat_zero, rat_one, rat_neg]

theorem ratPts_transfer : RatPts → ∀ (D : D7) (n : ℕ), FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n → ∀ S : G D n → Prop, (∀ g h, S g → S h → S (g * h)) → (∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → S g) → (∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → S g) → (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → S g) → ∀ γ ∈ GF D n, S γ := by
  intro hR D n hF S hmul hm hn hw γ hγ
  obtain ⟨h1, h2, -⟩ := hR D n
  obtain ⟨g, hgu, hgU, hg⟩ := h1 γ hγ
  let T : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E → Prop := fun M =>
    IsUnit M.det ∧ IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (EC.Jm D.host.E n) M ∧
      ∀ γ' : G D n, mat γ' = M.map (incA D) → S γ'
  have hprod : ∀ M₁ M₂, T M₁ → T M₂ → T (M₁ * M₂) := by
    rintro M₁ M₂ ⟨u₁, U₁, s₁⟩ ⟨u₂, U₂, s₂⟩
    refine ⟨by rw [Matrix.det_mul]; exact u₁.mul u₂, isUnitary_mul U₁ U₂, fun γ' e => ?_⟩
    obtain ⟨γ₁, -, e₁⟩ := h2 M₁ u₁ U₁
    obtain ⟨γ₂, -, e₂⟩ := h2 M₂ u₂ U₂
    have e' : γ' = γ₁ * γ₂ := mat_injective' (by rw [e, mat_mul', e₁, e₂, Matrix.map_mul])
    rw [e']
    exact hmul _ _ (s₁ _ e₁) (s₂ _ e₂)
  have hmA : ∀ a : Matrix (Fin n) (Fin n) D.host.E, IsUnit a.det →
      T (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a) := by
    intro a ha
    refine ⟨mA_isUnit_det _ ha, mA_isUnitary sig_sig ha, fun γ' e => ?_⟩
    let a' : GL (Fin n) (AE D) := ⟨rat a, rat a⁻¹,
      by rw [← rat_mul, Matrix.mul_nonsing_inv _ ha, rat_one],
      by rw [← rat_mul, Matrix.nonsing_inv_mul _ ha, rat_one]⟩
    exact hm γ' a' (e.trans (map_mA a))
  have hnB : ∀ b : Matrix (Fin n) (Fin n) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) b = b → T (nB b) := by
    intro b hb
    refine ⟨nB_isUnit_det b, nB_isUnitary hb, fun γ' e => hn γ' (rat b) ?_ (e.trans (map_nB b))⟩
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hJ : T (EC.Jm D.host.E n) :=
    ⟨Jm_isUnit_det, Jm_isUnitary _, fun γ' e => hw γ' (e.trans map_Jm)⟩
  exact (hF T hprod hmA hnB hJ g hgu hgU).2.2 γ hg

end GlobalTheory.CompanionTheory.EisCovar.Transfer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationCovarianceLevi
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

variable {D : D7} {n : ℕ}

theorem heis_apply (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (v : Mx D V.rank (n + n)) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V v Φ z =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (yPart v))) + halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) *
        Φ (z + xPart v) := rfl

theorem mat_inv_levi (g : G D n) (a : GL (Fin n) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  have h3 : blk4 (a⁻¹).1 0 0 (adj a.1) * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]
    exact block_matrix_one
  calc mat g⁻¹ = (blk4 (a⁻¹).1 0 0 (adj a.1) * mat g) * mat g⁻¹ := by rw [h3, Matrix.one_mul]
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem trace_inner_levi (V : HSp D) (z y : Mx D V.rank n) (a : Mx D n n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul z a : Mx D V.rank n) y) =
      Matrix.trace (GlobalTheory.StdUnn.inner V z (HMul.hMul y (adj a) : Mx D V.rank n)) := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trace_inner_levi_both (V : HSp D) (x y : Mx D V.rank n) (a : GL (Fin n) (AE D)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul x (a⁻¹).1 : Mx D V.rank n) (HMul.hMul y (adj a.1) : Mx D V.rank n)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x y) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]

theorem covAt_levi : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g a hg v Φ Ψ hΨ
  have hinv := mat_inv_levi g a hg
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (xPart v) (a⁻¹).1 := by
    rw [hinv, x_part_mul_block, Matrix.mul_zero, add_zero]
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (yPart v) (adj a.1) := by
    rw [hinv, y_part_mul_block, Matrix.mul_zero, zero_add]
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  funext z
  rw [hW.levi g a hg Ψ z, hΨ]
  rw [heis_apply, heis_apply, hx, hy, hW.levi g a hg Φ, trace_inner_levi V z (yPart v) a.1, trace_inner_levi_both]
  have e3 : HMul.hMul (z + HMul.hMul (xPart v) (a⁻¹).1 : Mx D V.rank n) a.1 =
      (HMul.hMul z a.1 + xPart v : Mx D V.rank n) := by
    rw [Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3]
  ring

end GlobalTheory.CompanionTheory.EisCovar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatImpliesFieldGeneration
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.FieldGenPf

open GlobalTheory.CompanionTheory.BruhatCell (cT_mul cT_one cT_zero cT_neg cT_cT isUnit_det_cT cT_inv cT_blk4 cT_eId cT_extB
  eId_mul_eId exists_blockMatrixTwoByTwoFin_eq is_siegel_parabolic_block_iff unitary_mul blockMatrixTwoByTwoFin_injective)

variable {K : Type} [Field K]

theorem exists_rows {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ (c : Matrix (Fin (Module.finrank K U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
      (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ IsCompl c a :=
  _root_.UpperTheory.Reformulated.B.ComplementSubspace.main U

theorem siegel_factor (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {p : Matrix (Fin (n + n)) (Fin (n + n)) K} (hp : IsUnitary σ (Jm K n) p) (hs : IsSiegelP p) :
    ∃ X A : Matrix (Fin n) (Fin n) K, cT σ X = X ∧ IsUnit A.det ∧ p = nB X * mA σ A := by
  obtain ⟨A, B, C, E, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq p
  obtain rfl := (is_siegel_parabolic_block_iff A B C E).1 hs
  unfold IsUnitary EC.Jm at hp
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at hp
  obtain ⟨-, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective hp
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add,
    Matrix.neg_mul, neg_inj, neg_zero] at h2 h3 h4
  have hEA : cT σ E * A = 1 := h3
  have hAE : cT σ A * E = 1 := h2
  have hA : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hEA
  have hinv : (cT σ A)⁻¹ = E := Matrix.inv_eq_right_inv hAE
  have hAE' : A * cT σ E = 1 := mul_eq_one_comm.1 hEA
  have hEA' : E * cT σ A = 1 := mul_eq_one_comm.1 hAE
  have hBE : cT σ B * E = cT σ E * B := by
    have := h4
    rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at this
    exact this
  refine ⟨B * cT σ A, A, ?_, hA, ?_⟩
  · rw [cT_mul, cT_cT σ hσ]
    calc A * cT σ B = A * cT σ B * (E * cT σ A) := by rw [hEA', Matrix.mul_one]
      _ = A * (cT σ B * E) * cT σ A := by simp only [Matrix.mul_assoc]
      _ = (A * cT σ E) * B * cT σ A := by rw [hBE]; simp only [Matrix.mul_assoc]
      _ = B * cT σ A := by rw [hAE', Matrix.one_mul]
  · unfold nB mA
    rw [submatrix_fromBlocks_mul, hinv]
    simp [Matrix.mul_assoc, hAE]

theorem wr_word {n : ℕ} (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) :
    blk4 (1 - e) e (-e) (1 - e) =
      blk4 1 e 0 1 * blk4 0 1 (-1) 0 * blk4 1 e 0 1 * blk4 0 (-1) 1 0 * blk4 1 e 0 1 := by
  have s1 : blk4 1 e 0 1 * blk4 0 1 (-1) 0 = blk4 (-e) 1 (-1) 0 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s2 : blk4 (-e) 1 (-1) 0 * blk4 1 e 0 1 = blk4 (-e) (1 - e) (-1) (-e) := by
    rw [submatrix_fromBlocks_mul]; simp [he, sub_eq_add_neg, add_comm]
  have s3 : blk4 (-e) (1 - e) (-1) (-e) * blk4 0 (-1) 1 0 = blk4 (1 - e) e (-e) 1 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s4 : blk4 (1 - e) e (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
    have h0 : (-e + 1) * e = 0 := by simp [Matrix.add_mul, he]
    rw [submatrix_fromBlocks_mul]; simp [Matrix.sub_mul, he, h0, sub_eq_add_neg, add_comm]
  rw [s1, s2, s3, s4]

theorem Jm_mul_mA_neg (σ : K →+* K) (n : ℕ) :
    Jm K n * mA σ (-1 : Matrix (Fin n) (Fin n) K) = blk4 0 (-1) 1 0 := by
  have h : (cT σ (-1 : Matrix (Fin n) (Fin n) K))⁻¹ = -1 := by
    rw [cT_neg, cT_one]; exact Matrix.inv_eq_right_inv (by simp)
  unfold EC.Jm mA
  rw [h, submatrix_fromBlocks_mul]; simp

theorem unitary_inv (σ : K →+* K) {N : ℕ} {J r : Matrix (Fin N) (Fin N) K} (hd : IsUnit r.det)
    (hr : IsUnitary σ J r) : IsUnitary σ J r⁻¹ := by
  unfold IsUnitary at *
  have h1 : cT σ r⁻¹ * cT σ r = 1 := by
    rw [cT_inv σ hd]; exact Matrix.nonsing_inv_mul _ (isUnit_det_cT σ hd)
  have h2 : r * r⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc cT σ r⁻¹ * J * r⁻¹ = cT σ r⁻¹ * (cT σ r * J * r) * r⁻¹ := by rw [hr]
    _ = (cT σ r⁻¹ * cT σ r) * J * (r * r⁻¹) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem fieldGen_of_bruhat : Bruhat → ∀ (K : Type) [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → (2 : K) ≠ 0 →
    ∀ n : ℕ, FieldGen K σ n := by
  intro hB K _ σ hσ h2 n T hmul hm hn hJ g hg hu
  choose c a hc ha using exists_rows (K := K) (n := n)
  obtain ⟨hrep, hex⟩ := hB K σ hσ h2 n c hc a ha
  obtain ⟨⟨U, b, hb⟩, hq, -⟩ := hex g hg hu
  obtain ⟨hrd, hru⟩ := hrep U b hb
  have hq' : IsSiegelP (g * (repMat σ b (a U))⁻¹) := hq
  have hTw : ∀ r, T (wr K n r) := by
    intro r
    have hne : ∀ r, T (nB (eId K n r)) := fun r => hn _ (cT_eId σ n r)
    have hJi : T (blk4 0 (-1) 1 0) := by
      rw [← Jm_mul_mA_neg σ n]
      refine hmul _ _ hJ (hm _ ?_)
      rw [Matrix.det_neg, Matrix.det_one]
      simp
    unfold wr
    rw [wr_word _ (eId_mul_eId n r)]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hne r) hJ) (hne r)) hJi) (hne r)
  have hTrep : T (repMat σ b (a U)) :=
    hmul _ _ (hmul _ _ (hTw _) (hn _ (by rw [cT_extB, hb]))) (hm _ (ha U).1)
  obtain ⟨X, A, hX, hA, hp⟩ := siegel_factor σ hσ (unitary_mul σ hu (unitary_inv σ hrd hru)) hq'
  have hTp : T (g * (repMat σ b (a U))⁻¹) := by
    rw [hp]; exact hmul _ _ (hn X hX) (hm A hA)
  have e : g = g * (repMat σ b (a U))⁻¹ * repMat σ b (a U) := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hrd, Matrix.mul_one]
  rw [e]
  exact hmul _ _ hTp hTrep

end GlobalTheory.CompanionTheory.EisCovar.FieldGenPf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_covariance : PositivityTheory.GramSchwartzFunctions.EC.Covar := by
  first | exact @GlobalTheory.CompanionTheory.EisCovar.covar | exact GlobalTheory.CompanionTheory.EisCovar.covar | (intros; apply GlobalTheory.CompanionTheory.EisCovar.covar <;> assumption)
end
