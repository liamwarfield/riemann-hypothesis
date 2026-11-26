module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.SW.thH_summable_and_inj : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin N) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
      (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ x Z z z')‖) ∧
      ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
        (∀ z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thH Ψ ψ Z z z') → φ = ψ := by
  intro E _ _ _ Ψ hΨ n N φ hφ Z hZ
  obtain ⟨hbij, hup, hsurj, hdict, hSB⟩ := _root_.GlobalTheory.SW.thH_eq_thS_dictionary E Ψ hΨ n N
  classical
  have hexp : ∀ (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
      (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ),
      cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ (_root_.GlobalTheory.SW.ofQ m) Z z z') =
        cexp (π * I * ∑ k, (_root_.GlobalTheory.SW.qv (m k) ⬝ᵥ
          (_root_.GlobalTheory.SW.tauOf Ψ Z) *ᵥ _root_.GlobalTheory.SW.qv (m k) +
          2 * _root_.GlobalTheory.SW.qv (m k) ⬝ᵥ (_root_.GlobalTheory.SW.zetaOf Ψ z z') k)) := by
    intro z z' m
    have h := hdict (fun x => if x = _root_.GlobalTheory.SW.ofQ m then 1 else 0) Z z z'
    unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS at h
    rw [tsum_eq_single (_root_.GlobalTheory.SW.ofQ m), tsum_eq_single m] at h
    · simpa using h
    all_goals (intro b hb; simp [hbij.1.eq_iff, hb])
  refine ⟨fun z z' => ?_, fun ψ hψ hθ => ?_⟩
  · rw [← (Equiv.ofBijective _ hbij).summable_iff]
    have hs := _root_.GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) _ (hup Z hZ)
      (_root_.GlobalTheory.SW.zetaOf Ψ z z')
    refine hs.congr fun m => ?_
    simp only [Function.comp_apply, Equiv.ofBijective_apply, hexp]
  · have h := _root_.GlobalTheory.SW.eq_of_thS_eq _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
      (fun m => ψ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) ((hSB ψ).1 hψ) _ (hup Z hZ)
      (fun ζ => by
        obtain ⟨z, z', rfl⟩ := hsurj ζ
        rw [← hdict, ← hdict]
        exact hθ z z')
    funext x
    obtain ⟨m, rfl⟩ := hbij.2 x
    exact congrFun h m
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTheta_summable_and_determines_testFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * expo Ψ x Z z z')‖) ∧ ∀ ψ, IsSB ψ → (∀ z z', thH Ψ φ Z z z' = thH Ψ ψ Z z z') → φ = ψ := by
  first | exact @GlobalTheory.SW.thH_summable_and_inj | exact GlobalTheory.SW.thH_summable_and_inj | (intros; apply GlobalTheory.SW.thH_summable_and_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HermComp

variable {N : ℕ}

theorem _root_.GlobalTheory.SW.HermComp.row_rel (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.SW.HermComp

private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl

theorem _root_.GlobalTheory.SW.transH_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubMulConjTranspose
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem norm_det_le_add_posSemidef (A P : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (hP : P.PosSemidef) : ‖A.det‖ ≤ ‖(A + P).det‖ := by
  have h1 : imH (I • A) = A := by
    have := imH_add_I_smul 0 A hA.1
    simpa [imH] using this
  have h := (norm_det_denom_mono N 1 0 (I • A) P (by simp) (by simpa using Matrix.PosDef.one)
    (by rwa [h1]) hP).2
  simpa [← smul_add, det_smul] using h

theorem star_dotProduct_self_eq_sum (x : Fin N → ℂ) :
    star x ⬝ᵥ x = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']

theorem posSemidef_sub_mul_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self X)
    simp [IsHermitian]
  · have h1 : star x ⬝ᵥ (X * Xᴴ) *ᵥ x = star (Xᴴ *ᵥ x) ⬝ᵥ (Xᴴ *ᵥ x) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, smul_eq_mul, ← ofReal_mul,
      ← ofReal_sub, Complex.zero_le_real, sub_nonneg]
    have h2 : ∀ a, ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ B ^ 2 * (N * ∑ b, ‖x b‖ ^ 2) := by
      intro a
      have h3 : ‖(Xᴴ *ᵥ x) a‖ ≤ B * ∑ b, ‖x b‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le Finset.univ fun b => Xᴴ a b * x b).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, conjTranspose_apply, norm_star]
        exact mul_le_mul_of_nonneg_right (hX b a) (norm_nonneg _)
      have h4 : (∑ b, ‖x b‖) ^ 2 ≤ N * ∑ b, ‖x b‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => ‖x b‖)
      calc ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ (B * ∑ b, ‖x b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = B ^ 2 * (∑ b, ‖x b‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (sq_nonneg B)
    refine (Finset.sum_le_sum fun a _ => h2 a).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem denom_mul_conjTranspose (C D X : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hX : X.IsHermitian) (δ : ℝ) :
    (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ =
      (C * X + D) * (C * X + D)ᴴ + ((δ : ℂ) ^ 2) • (C * Cᴴ) := by
  have h1 : D * Cᴴ = C * Dᴴ := by simpa using h.eq
  have h2 : star (I * δ : ℂ) = -(I * δ) := by simp
  have h3 : (δ : ℂ) ^ 2 = -((I * δ) * (I * δ)) := by
    have : I * δ * (I * δ) = (I * I) * (δ : ℂ) ^ 2 := by ring
    rw [this, I_mul_I]; ring
  rw [h3]
  generalize (I * δ : ℂ) = t at h2 ⊢
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, conjTranspose_one, hX.eq, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1]
  module

theorem norm_det_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, star_def, Complex.mul_conj']
  simp

theorem norm_det_denom_compare :
    ∀ (N : ℕ) (δ B : ℝ), 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C D Z : Matrix (Fin N) (Fin N) ℂ, (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → (∀ a b, ‖(Z + Zᴴ) a b‖ ≤ B) → c * ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ≤ ‖(C * Z + D).det‖ ∧ ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 = (C * Cᴴ + D * Dᴴ).det.re := by
  intro N δ B hδ
  set K : ℝ := (N : ℝ) ^ 2 * (B / 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := δ ^ 2 / (2 * δ ^ 2 + 1 + 2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 0 ≤ 1 - 2 * c := by
    rw [hc, sub_nonneg, ← mul_div_assoc, div_le_one (by positivity)]
    linarith
  have hc2 : 0 ≤ δ ^ 2 - c - 2 * c * K := by
    have : c * (2 * δ ^ 2 + 1 + 2 * K) = δ ^ 2 := by rw [hc]; field_simp
    nlinarith [mul_pos hc0 (pow_pos hδ 2)]
  refine ⟨Real.sqrt (c ^ N), by positivity, fun C D Z h hp hZ hB => ?_⟩
  have hG : (C * Cᴴ + D * Dᴴ).det =
      ((‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 : ℝ) : ℂ) := by
    have := denom_mul_conjTranspose C D 0 h isHermitian_zero 1
    rw [← norm_det_mul_conjTranspose]
    simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at this
    rw [this, add_comm]
  refine ⟨?_, by rw [hG, ofReal_re]⟩
  set X : Matrix (Fin N) (Fin N) ℂ := (2⁻¹ : ℂ) • (Z + Zᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp [hXdef, IsHermitian, add_comm]
  have hXB : ∀ a b, ‖X a b‖ ≤ B / 2 := by
    intro a b
    have := hB a b
    rw [hXdef, Matrix.smul_apply, norm_smul]
    simp only [norm_inv, Complex.norm_ofNat]
    linarith
  have hone : ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hδ)
  have him : imH (X + (I * δ) • 1) = (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [mul_smul, imH_add_I_smul _ _ hone.1, imH, hX.eq]
    simp
  have hZe : X + (I * δ) • 1 + I • (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = Z := by
    have h2 : I * (2 * I)⁻¹ = 2⁻¹ := by field_simp
    rw [smul_sub, imH, smul_smul, smul_smul, h2, hXdef]
    module
  have hm := (norm_det_denom_mono N C D (X + (I * δ) • 1) _ h hp (by rwa [him]) hZ).2
  rw [hZe] at hm
  refine le_trans ?_ hm
  have hP : ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)).PosSemidef := by
    refine (((posSemidef_self_mul_conjTranspose _).smul ?_).add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)).add
      (((posSemidef_sub_mul_conjTranspose X _ hXB).mul_mul_conjTranspose_same C).smul ?_) |>.add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)
    · exact Complex.zero_le_real.2 hc1
    · exact Complex.zero_le_real.2 hc2
    · exact Complex.zero_le_real.2 (by positivity)
    · exact Complex.zero_le_real.2 hc0.le
  have hd := norm_det_le_add_posSemidef _ _ (hp.smul (Complex.zero_lt_real.2 hc0)) hP
  have he : (c : ℂ) • (C * Cᴴ + D * Dᴴ) + ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)) =
      (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ := by
    rw [denom_mul_conjTranspose C D X h hX]
    push_cast
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  rw [he, norm_det_mul_conjTranspose, det_smul, hG, ← ofReal_pow, ← ofReal_mul, norm_real,
    norm_real, Fintype.card_fin, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hd
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

end GlobalTheory.SW
end
