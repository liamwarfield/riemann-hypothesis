module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipEquivariantBlockDiagonalColumnSubstitu

@[expose] public section

attribute [-instance] UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipRowsIntegralGLInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqChar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.FFunLeftInv
open GlobalTheory.SplitFlip

theorem fFun_transpose_mul_of_mem_KO : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ μ _ σ ν Ψ u hu h
  classical
  let P : Matrix A A k → Matrix D D k := fun X => (fromBlocks X 0 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
  have hP : ∀ X Y, P X * P Y = P (X * Y) := fun X Y => by
    simp only [P, Matrix.submatrix_mul_equiv, fromBlocks_multiply]; simp
  have hP1 : P 1 = 1 := by simp [P, fromBlocks_one]
  let m : GL D k := ⟨P u.valᵀ, P (u⁻¹).valᵀ, by rw [hP, ← transpose_mul, Units.inv_mul, transpose_one, hP1],
    by rw [hP, ← transpose_mul, Units.mul_inv, transpose_one, hP1]⟩
  set h' : GL D k := invT m * h with hh'
  have e1 : u.valᵀ * (X0 k σ * (invT h).val) = X0 k σ * (invT h').val := by
    rw [hh', map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, X0, Matrix.mul_apply, eq_comm]
  have e2 : Y0 k σ * h'.val = Y0 k σ * h.val := by
    rw [hh', Units.val_mul, ← Matrix.mul_assoc]
    congr 1
    ext i j
    rw [invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [m, P, Y0, Matrix.mul_apply, eq_comm]
    rw [Matrix.one_apply]
    simp [eq_comm]
  have e3 : gdet h' = (gdet u)⁻¹ * gdet h := by
    rw [hh', gdet_mul, gdet_invT]
    congr 2
    ext
    simp [m, P, Matrix.GeneralLinearGroup.val_det_apply, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  have hv : valuation k ((gdet u)⁻¹ : kˣ) = 1 := by
    rw [← map_inv]; exact valuation_gdet_of_mem_KO (inv_mem hu)
  rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, e3, apow_mul, apow_of_valuation_eq_one hv, map_mul, Units.val_mul, map_inv]
  have : (ν (gdet u) : ℂ) * ((ν (gdet u))⁻¹ : ℂˣ) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val)) * this

end GlobalTheory.FFunLeftInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (u : GL A k), u ∈ KO k A → ∀ h : GL D k,
      (ν (gdet u) : ℂ) * fFun μ σ ν Ψ (u.valᵀ * (X0 k σ * (invT h).val)) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | exact GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO | (intros; apply GlobalTheory.FFunLeftInv.fFun_transpose_mul_of_mem_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPrimFrameGlMulIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.PrimFrameLeft

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]

theorem row_mul_eq_sum (M : Matrix A A k) (Y : Matrix A D k) (i : A) :
    (M * Y).row i = ∑ l, M i l • Y.row l := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply, Matrix.row]

theorem span_O_row_mul_le (M : Matrix A A k) (hM : ∀ i j, M i j ∈ 𝒪[k]) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (M * Y).row) ≤ Submodule.span 𝒪[k] (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ (⟨M i l, hM i l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)

theorem span_k_row_mul_le (M : Matrix A A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (M * Y).row) ≤ Submodule.span k (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_O_row_gl_mul (g : GL A k) (hg : g ∈ KO k A) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (g.val * Y).row) = Submodule.span 𝒪[k] (Set.range Y.row) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  refine le_antisymm (span_O_row_mul_le _ h1 Y) ?_
  have := span_O_row_mul_le _ h2 (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem span_k_row_gl_mul (g : GL A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (g.val * Y).row) = Submodule.span k (Set.range Y.row) := by
  refine le_antisymm (span_k_row_mul_le _ Y) ?_
  have := span_k_row_mul_le (g⁻¹).val (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem mem_matLat_iff_span_le (Λ : Submodule 𝒪[k] (D → k)) (Y : Matrix A D k) :
    Y ∈ matLat A Λ ↔ Submodule.span 𝒪[k] (Set.range Y.row) ≤ Λ := by
  rw [Submodule.span_le, mem_matLat]
  exact ⟨fun h => by rintro _ ⟨i, rfl⟩; exact h i, fun h i => h ⟨i, rfl⟩⟩

theorem isPrimFrame_gl_mul_iff (Λ : Submodule 𝒪[k] (D → k)) (g : GL A k) (hg : g ∈ KO k A)
    (Y : Matrix A D k) : IsPrimFrame Λ (g.val * Y) ↔ IsPrimFrame Λ Y := by
  have hrank : (g.val * Y).rank = Y.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  unfold IsPrimFrame
  rw [hrank, mem_matLat_iff_span_le, mem_matLat_iff_span_le, span_O_row_gl_mul g hg, span_k_row_gl_mul]

end GlobalTheory.PrimFrameLeft
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.ResSumInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hne : ((ϖ : k)) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ((a : k) - b) = (ϖ : k) ^ e * c := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) hc
      simpa using this
    rw [hc']
    have : (((ϖ ^ e)⁻¹ : kˣ) : k) * ((ϖ : k) ^ e * c) = c := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [this]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hY l j)

theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hM1, hM2⟩ := (mem_KO_iff M).1 hM
  set c : k := (((ϖ ^ e)⁻¹ : kˣ) : k) with hc
  have hint : ∀ (S : A → B → Res k e) i j, (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S => mul_mem_int hM1 (liftRes_mem S)
  let φ : (A → B → Res k e) → (A → B → Res k e) := fun S i j =>
    Ideal.Quotient.mk _ (⟨(M.val * liftRes S) i j, hint S i j⟩ : 𝒪[k])
  have h1 : ∀ S i j, c * (liftRes (φ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have := (mk_eq_iff hϖ e (Quotient.out (φ S i j)) ⟨(M.val * liftRes S) i j, hint S i j⟩).1
      (Ideal.Quotient.mk_out _)
    exact this
  have hinj : Function.Injective φ := by
    intro S S' h
    have hd : ∀ i j, c * ((M.val * liftRes S) i j - (M.val * liftRes S') i j) ∈ 𝒪[k] := fun i j =>
      (mk_eq_iff hϖ e ⟨_, hint S i j⟩ ⟨_, hint S' i j⟩).1 (congrFun (congrFun h i) j)
    have hD : ∀ i j, (c • (M.val * liftRes S - M.val * liftRes S')) i j ∈ 𝒪[k] := fun i j => by
      simpa [mul_sub] using hd i j
    have hL : c • (liftRes S - liftRes S') = (M⁻¹).val * (c • (M.val * liftRes S - M.val * liftRes S')) := by
      rw [Matrix.mul_smul, ← Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    funext i j
    have hij : c * (((Quotient.out (S i j) : 𝒪[k]) : k) - ((Quotient.out (S' i j) : 𝒪[k]) : k)) ∈ 𝒪[k] := by
      have := mul_mem_int hM2 hD i j
      rw [← hL] at this
      simpa [liftRes, mul_sub] using this
    have := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2 hij
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← Fintype.sum_bijective φ hbij (fun S => f ((ϖ ^ e)⁻¹ • liftRes (φ S))) (fun S => f ((ϖ ^ e)⁻¹ • liftRes S)) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsm : ∀ N : Matrix A B k, (ϖ ^ e)⁻¹ • N = c • N := fun N => rfl
  rw [hsm, hsm, Matrix.mul_smul]
  have : c • liftRes (φ S) = c • (M.val * liftRes S) + c • (liftRes (φ S) - M.val * liftRes S) := by
    rw [← smul_add, add_sub_cancel]
  rw [this, hf]
  intro i j
  simpa [mul_sub] using h1 S i j

end GlobalTheory.ResSumInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ), IsUnif ϖ → ∀ f : Matrix A B k → ℂ, (∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z) →
    ∀ M : GL A k, M ∈ KO k A →
      ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) = ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  first | exact @GlobalTheory.ResSumInv.sum_res_mul_left | exact GlobalTheory.ResSumInv.sum_res_mul_left | (intros; apply GlobalTheory.ResSumInv.sum_res_mul_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipRowsIntegralGLInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.SquareFlipRows

theorem squareFlip_one_rows : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by

  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ u hu X
  have hM : (invT u⁻¹).val = u.valᵀ := by rw [invT_val, inv_inv]
  have hMK : invT u⁻¹ ∈ KO k A := invT_mem_KO (inv_mem hu)
  have hdep : HasDepth ϖ e (blockLat ϖ e (Assignment.two.block D₁ D₂))
      (phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    have h1 := (FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e (Assignment.one.block D₁ D₂) hϖ hψ).1 Φ hΦ
    have h2 := @FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' (D₁ ⊕ D₂) _ _ _ _ _ _ μ (by assumption) σ ν ϖ e
      (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν h1
    rw [← compl_block_one, ← latA_blockLat]; exact h2
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hφu : ∀ Y, (ν (gdet u) : ℂ) * phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) (u.valᵀ * Y) =
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) Y := by
    intro Y
    classical
    rw [phiA, phiA, ← hM, GlobalTheory.PrimFrameLeft.isPrimFrame_gl_mul_iff _ _ hMK]
    by_cases hY : IsPrimFrame (latA ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))) Y
    · rw [if_pos hY, if_pos hY]
      obtain ⟨h, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hY.1
      rw [hM]
      exact GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char μ σ ν _ u hu h
    · rw [if_neg hY, if_neg hY, mul_zero]
  have hb : ∀ (Q : D₁ ⊕ D₂ → Prop), (∀ j ∈ Assignment.two.block D₁ D₂, Q j) ↔ ∀ c, Q (Sum.inr c) := by
    intro Q
    refine ⟨fun h c => h _ (by simp [Assignment.block]), fun h j hj => ?_⟩
    cases j with
    | inl c => simp [Assignment.block] at hj
    | inr c => exact h c
  set X' : Matrix A (D₁ ⊕ D₂) k := fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂) with hX'
  have hcond : (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X' i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]) := by
    simp only [hb]
    have := mul_mul_mem_matLat_iff (inv_mem hu) (one_mem (KO k D₂)) X.toCols₂
    rw [mem_matLat_stdLat, mem_matLat_stdLat, Units.val_one, Matrix.mul_one] at this
    simpa [hX', Matrix.toCols₂] using this
  have hset : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      setCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) =
        u.valᵀ * setCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [hM]
    ext i j
    rcases j with c | c
    · simp [setCols, Assignment.block, hX', Matrix.mul_apply, Matrix.toCols₁]
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      first | rfl | exact Matrix.mul_apply | (erw [Matrix.mul_apply]; simp)
  have hsub : X'.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) =
      (u⁻¹).val * X.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) := by
    ext i ⟨j, hj⟩
    rcases j with c | c
    · simp [Assignment.block] at hj
    · simp [hX', Matrix.mul_apply, Matrix.toCols₂]
  have hpair : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      pairCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = pairCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [pairCols_eq_trace, pairCols_eq_trace, hsub, hM, transpose_mul, ← Matrix.mul_assoc, trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  unfold squareFlip
  rw [compl_block_one, invFourierSum_inv_apply, invFourierSum_inv_apply]
  by_cases hX : ∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]
  · rw [if_pos hX, if_pos (hcond.2 hX)]
    set φ := phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
    have hg : ∀ Z Z' : Matrix A (Assignment.two.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) →
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) (Z + Z') =
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) Z := by
      intro Z Z' hZ'
      have e1 : setCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          setCols (Assignment.two.block D₁ D₂) X' Z + setCols (Assignment.two.block D₁ D₂) 0 Z' := by
        ext i j; by_cases h : j ∈ Assignment.two.block D₁ D₂ <;> simp [setCols, h]
      have e2 : pairCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          pairCols (Assignment.two.block D₁ D₂) X' Z + pairCols (Assignment.two.block D₁ D₂) X' Z' := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      have e3 : pairCols (Assignment.two.block D₁ D₂) X' Z' ∈ 𝒪[k] :=
        Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (hZ' i j) (hcond.2 hX i j j.2)
      simp only
      rw [e1, e2, hdep.2, AddChar.map_add_eq_mul, triv _ e3, mul_one]
      apply FourierDepth.mem_matLat_smul_blockLat.2
      constructor
      · intro i j hj
        simpa [setCols, hj] using hZ' i ⟨j, hj⟩
      · intro i j hj
        simp [setCols, hj]
    have key := GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left ϖ e hϖ (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) hg (invT u⁻¹) hMK
    beta_reduce at key
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hset, hpair, ← mul_assoc, hφu]
  · rw [if_neg hX, if_neg (mt hcond.1 hX), mul_zero]

end GlobalTheory.SquareFlipRows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipRowsIntegralGLInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareFlip_rows_integralGL_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by
  first | exact @GlobalTheory.SquareFlipRows.squareFlip_one_rows | exact GlobalTheory.SquareFlipRows.squareFlip_one_rows | (intros; apply GlobalTheory.SquareFlipRows.squareFlip_one_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
open GlobalTheory.SplitFlip

namespace GlobalTheory.FlipPathPairwise

def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2

theorem srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega

theorem pairwise_of_isPath {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise

end GlobalTheory.FlipPathPairwise


open GlobalTheory.FlipPathPairwise in
theorem GlobalTheory.SplitFlip.isPath_flipPath : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquareStatement
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → IsPath (flipPath i j γ) := by
  first | exact @GlobalTheory.SplitFlip.isPath_flipPath | exact GlobalTheory.SplitFlip.isPath_flipPath | (intros; apply GlobalTheory.SplitFlip.isPath_flipPath <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
namespace GlobalTheory.SplitFlip

def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem pathInnerDiff_tgt (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring

theorem IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise

theorem IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])

theorem src_flipEdge_pathInner (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]

theorem mem_innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩

end GlobalTheory.SplitFlip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquareStatement
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  first | exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath | exact GlobalTheory.SplitFlip.mem_innerVertices_flipPath | (intros; apply GlobalTheory.SplitFlip.mem_innerVertices_flipPath <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipGridPathAtSquareSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipGridPathAtSquareSplit
namespace GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip

def vdiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vdiff_tgt (e : Edge) : vdiff e.tgt = vdiff e.src + 1 := by
  cases e <;> simp [vdiff] <;> push_cast <;> ring

theorem pairwise_of_isPath : ∀ {γ : List Edge}, IsPath γ → γ.Pairwise (fun a b => vdiff a.src < vdiff b.src)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    unfold IsPath at h
    rw [List.isChain_cons_cons] at h
    have ih : (b :: l).Pairwise (fun a b => vdiff a.src < vdiff b.src) :=
      pairwise_of_isPath (γ := b :: l) (show IsPath (b :: l) from h.2)
    have hab : vdiff a.src < vdiff b.src := by
      have := vdiff_tgt a; rw [h.1] at this; omega
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hc)

theorem nodup_of_isPath {γ : List Edge} (h : IsPath γ) : γ.Nodup :=
  (pairwise_of_isPath h).imp fun hab heq => by subst heq; exact lt_irrefl _ hab

end GlobalTheory.SplitFlip.PathSplit

namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit

theorem flipPath_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  intro γ i j hγ hp
  obtain ⟨l₁, l₂, rfl⟩ := hp
  have hnd := nodup_of_isPath hγ
  refine ⟨l₁, l₂, rfl, ?_⟩
  have hfix : ∀ l : List Edge, Edge.theta i j ∉ l → Edge.ex i j ∉ l →
      l.map (fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e) = l :=
    fun l h1 h2 => by
      refine (List.map_congr_left fun e he => ?_).trans (List.map_id l)
      have e1 : e ≠ .theta i j := fun h => h1 (h ▸ he)
      have e2 : e ≠ .ex i j := fun h => h2 (h ▸ he)
      simp [e1, e2]
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨_, _, hd1⟩, _, hd2⟩ := hnd
  have a1 : Edge.theta i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have a2 : Edge.ex i j ∉ l₁ := fun h => hd1 _ h _ (by simp) rfl
  have b1 : Edge.theta i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  have b2 : Edge.ex i j ∉ l₂ := fun h => hd2 _ (by simp) _ h rfl
  simp only [flipPath, List.map_append, hfix l₁ a1 a2, hfix l₂ b1 b2]
  simp

end GlobalTheory.SplitFlip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipGridPathAtSquareSplitStatement
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipGridPathAtSquare_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧ flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  first | exact @GlobalTheory.SplitFlip.flipPath_split | exact GlobalTheory.SplitFlip.flipPath_split | (intros; apply GlobalTheory.SplitFlip.flipPath_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FlipAdm

theorem isPath_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    IsPath (flipPath i j γ) := GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare hγ h

theorem exists_split {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := GlobalTheory.T.flipGridPathAtSquare_split hγ h

theorem not_touch {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner hγ h

theorem innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) :=
  GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare hγ h

end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem squareFlip_const_mul {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D]
    [DecidableEq D] (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ)
    (P : Finset D) (c : ℂ) (Φ : Matrix A' D k → ℂ) (X : Matrix A D k) :
    squareFlip μ σ ψ ν ϖ e P (fun Z => c * Φ Z) X = c * squareFlip μ σ ψ ν ϖ e P Φ X := by
  have hs : ∀ (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k), smallF μ ν (c • Ψ) Y = c * smallF μ ν Ψ Y := by
    intro Ψ Y
    simp only [smallF, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hf : ∀ (Ψ : Matrix A' D k → ℂ) (Y : Matrix A D k), fFun μ σ ν (c • Ψ) Y = c * fFun μ σ ν Ψ Y := by
    intro Ψ Y
    unfold fFun
    split_ifs
    · rw [hs]; ring
    · simp
  have h1 : ∀ Ψ : Matrix A' D k → ℂ, phiA μ σ ν ϖ e (blockLat ϖ e P) (c • Ψ) = c • phiA μ σ ν ϖ e (blockLat ϖ e P) Ψ := by
    intro Ψ
    funext Y
    simp only [phiA, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [hf]
    · simp
  have h0 : (fun Z => c * Φ Z) = c • Φ := rfl
  rw [h0, squareFlip, map_smul, h1, map_smul]
  rfl

variable {G : Grid k}

theorem toCols₁_mul_fromBlocks {m n o : Type} [Fintype n] [Fintype o] (Z : Matrix m (n ⊕ o) k) (A : Matrix n n k)
    (D : Matrix o o k) : (Z * fromBlocks A 0 0 D).toCols₁ = Z.toCols₁ * A := by
  ext r c; simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₁]

theorem toCols₂_mul_fromBlocks {m n o : Type} [Fintype n] [Fintype o] (Z : Matrix m (n ⊕ o) k) (A : Matrix n n k)
    (D : Matrix o o k) : (Z * fromBlocks A 0 0 D).toCols₂ = Z.toCols₂ * D := by
  ext r c; simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₂]

theorem joinA_moveArgs (i j : ℕ) (g : G.VertexGroup) (x : G.Args) :
    G.joinA i j (G.moveArgs .one g x) =
      fromCols ((g (i + 1, j + 1)).valᵀ * (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₁)
        (((g (i + 1, j + 1))⁻¹).val * (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₂) := by
  have e1 : (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₁ =
      x (.ex i (j + 1)) * (invT (g (i, j + 1))).val := by
    simp [Grid.joinA, fromCols_mul_fromBlocks]
  have e2 : (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₂ =
      (x (.theta (i + 1) j))ᵀ * (g (i + 1, j)).val := by
    simp [Grid.joinA, fromCols_mul_fromBlocks]
  rw [e1, e2]
  simp only [Grid.joinA, Grid.moveArgs, Assignment.read, invT_inv_val, Matrix.transpose_mul, Matrix.transpose_transpose,
    invT_val, Matrix.mul_assoc]

theorem sliceB_pathAct (γ : List Edge) (i j : ℕ) (g : G.VertexGroup) (hg : g (i, j) = 1) (T : G.Args → ℂ)
    (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k) :
    G.sliceB i j (G.pathAct .one γ g T) x Z = (γ.map (G.edgeFactor .one g)).prod *
      G.sliceB i j T (G.moveArgs .one g x) (Z * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) := by
  simp only [Grid.sliceB, Grid.pathAct]
  congr 2
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  funext b
  by_cases hb : b = .ex i j
  · subst hb
    simp only [Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val]
    simp [hg, toCols₂_mul_fromBlocks, Matrix.transpose_mul]
  · by_cases hb' : b = .theta i j
    · subst hb'
      simp only [Function.update_of_ne hne, Function.update_self, Grid.moveArgs, Assignment.read]
      simp [hg, toCols₁_mul_fromBlocks]
    · simp only [Grid.moveArgs, Function.update_of_ne hb, Function.update_of_ne hb']

theorem pathAct_mulSingle_of_not_touch {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T)
    (X : ℕ × ℕ) (hX : ∀ b ∈ γ, b.src ≠ X ∧ b.tgt ≠ X) (u : GL (Fin (G.rank X)) k) :
    G.pathAct .one γ (Pi.mulSingle X u) T = T := by
  funext x
  have h1 : (γ.map (G.edgeFactor .one (Pi.mulSingle X u))).prod = 1 := List.prod_eq_one fun c hc => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
    simp [Grid.edgeFactor, Pi.mulSingle_eq_of_ne (hX b hb).1, Pi.mulSingle_eq_of_ne (hX b hb).2, hap]
  rw [Grid.pathAct, h1, one_mul]
  refine hT.1 fun b hb => ?_
  simp [Grid.moveArgs, Pi.mulSingle_eq_of_ne (hX b hb).1, Pi.mulSingle_eq_of_ne (hX b hb).2]

theorem edgeFactor_square (i j : ℕ) (g : G.VertexGroup) (hg : g (i, j) = 1) (hK : ∀ Y, g Y ∈ KO k _) :
    G.edgeFactor .one g (.ex i (j + 1)) * G.edgeFactor .one g (.theta (i + 1) j) *
        ((G.nu i j (gdet (g (i, j + 1))) : ℂ) * (G.nu i j (gdet (g (i + 1, j))) : ℂ)) =
      G.edgeFactor .one g (.theta i j) * G.edgeFactor .one g (.ex i j) * (G.nu i j (gdet (g (i + 1, j + 1))) : ℂ) := by
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, map_one, hap]
  simp only [Grid.kappa, Grid.blockChar, Grid.nu, gdet, map_one, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_one, one_mul]
  field_simp
end
end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {G : Grid k}

theorem pathAct_flipTensor {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e)
    {i j : ℕ} (hν : CondLE ϖ e (G.nu i j)) {J : G.Level} (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k)))
    (hJK : J (i, j) ≤ KO k _) (l₁ l₂ : List Edge) {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) T) (g : G.VertexGroup) (hg : g (i, j) = 1)
    (hK : ∀ Y, g Y ∈ KO k _) :
    G.pathAct .one (l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂) g (G.flipTensor .one ψ ϖ e i j J T) =
      G.flipTensor .one ψ ϖ e i j J (G.pathAct .one (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) g T) := by
  have hJ' := isOpen_map_invT hJ hJK
  haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2
  funext x
  set Φ := G.sliceB i j T (G.moveArgs .one g x) with hΦ
  have hN : IsNatDatum ϖ e Φ := isNatDatum_sliceB hT (by simp) (by simp) _
  have hM₁ : invT (g (i, j + 1)) ∈ KO k _ := invT_mem_KO (hK _)
  have hM₂ : g (i + 1, j) ∈ KO k _ := hK _
  have hcol := GlobalTheory.T.squareFlip_equivariant_blockDiagonal_columnSubstitution (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e hϖ hψ he hν
    Φ hN _ hM₁ _ hM₂ (G.joinA i j x)
  have hrow := GlobalTheory.T.squareFlip_rows_integralGL_invariant (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e hϖ hψ he hν
    Φ hN _ (hK (i + 1, j + 1))
    (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val)
  have hsl : G.sliceB i j (G.pathAct .one (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) g T) x =
      fun Z => ((l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂).map (G.edgeFactor .one g)).prod *
        Φ (Z * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) :=
    funext fun Z => sliceB_pathAct _ i j g hg T x Z
  have hsc := edgeFactor_square i j g hg hK
  simp only [Grid.flipTensor, Grid.pathAct]
  rw [hsl, squareFlip_const_mul, hcol, joinA_moveArgs, ← hΦ]
  have hrow' := (eq_inv_mul_iff_mul_eq₀ (Units.ne_zero _)).2 hrow
  rw [hrow']
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [gdet_invT, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  generalize squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e
    (Assignment.one.block _ _) Φ (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) = S
  have h1 := Units.ne_zero (G.nu i j (gdet (g (i, j + 1))))
  have h2 := Units.ne_zero (G.nu i j (gdet (g (i + 1, j))))
  have h3 := Units.ne_zero (G.nu i j (gdet (g (i + 1, j + 1))))
  field_simp
  linear_combination ((l₁.map (G.edgeFactor .one g)).prod * (l₂.map (G.edgeFactor .one g)).prod * S) * hsc

end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm

theorem isAdmissible_flip : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e →
    ∀ (St : Γ.PiLocalization₂) (x : ℕ × ℕ), CondLE ϖ e (Γ.nu x.1 x.2) → PassesThrough x.1 x.2 St.path →
    (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
    St.IsAdmissible .one ϖ e → (St.flip .one ψ ϖ e x).IsAdmissible .one ϖ e := by
  intro k _ _ _ _ _ _ Γ ψ ϖ e hϖ hψ he St x hν hpt hlev hadm
  obtain ⟨i, j⟩ := x
  obtain ⟨γ, J, T⟩ := St
  obtain ⟨hpath, -, htens, hinv⟩ := hadm
  simp only at hν hpt hlev hpath htens hinv
  obtain ⟨l₁, l₂, hγ, hfl⟩ := exists_split hpath hpt
  have h1 : Edge.theta i j ∈ γ := hpt.subset (by simp)
  have h2 : Edge.ex i j ∈ γ := hpt.subset (by simp)
  refine ⟨isPath_flipPath hpath hpt, fun X _ => ?_, isTensor_flipTensor hϖ hψ he hν (hlev (i, j)).1 (hlev (i, j)).2 h1 h2 htens,
    fun X hX u hu => ?_⟩
  · by_cases hXW : X = (i + 1, j + 1)
    · subst hXW
      simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_self]
      exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_of_ne hXW]
      exact hlev X
  · simp only [Grid.PiLocalization₂.flip] at hX hu ⊢
    obtain ⟨hX1, hX2⟩ := innerVertices_flipPath hpath hpt X hX
    have huK : u ∈ KO k _ := by
      by_cases hXW : X = (i + 1, j + 1)
      · subst hXW; simpa [Grid.flipLevel] using hu
      · rw [Grid.flipLevel, Function.update_of_ne hXW] at hu; exact (hlev X).2 hu
    have hg1 : (Pi.mulSingle X u : Γ.VertexGroup) (i, j) = 1 := Pi.mulSingle_eq_of_ne (Ne.symm hX1) _
    have hgK : ∀ Y, (Pi.mulSingle X u : Γ.VertexGroup) Y ∈ KO k _ := fun Y => by
      by_cases hY : Y = X
      · subst hY; simpa using huK
      · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
    rw [hfl]
    subst hγ
    rw [pathAct_flipTensor hϖ hψ he hν (hlev (i, j)).1 (hlev (i, j)).2 l₁ l₂ htens _ hg1 hgK]
    congr 1
    by_cases hXW : X = (i + 1, j + 1)
    · subst hXW
      exact pathAct_mulSingle_of_not_touch htens _ (not_touch hpath hpt) u
    · rw [Grid.flipLevel, Function.update_of_ne hXW] at hu
      exact hinv X (hX2 hXW) u hu

end GlobalTheory.FlipAdm
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e →
    ∀ (St : Γ.PiLocalization₂) (x : ℕ × ℕ), CondLE ϖ e (Γ.nu x.1 x.2) → PassesThrough x.1 x.2 St.path →
    (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
    St.IsAdmissible .one ϖ e → (St.flip .one ψ ϖ e x).IsAdmissible .one ϖ e := by
  first | exact @GlobalTheory.FlipAdm.isAdmissible_flip | exact GlobalTheory.FlipAdm.isAdmissible_flip | (intros; apply GlobalTheory.FlipAdm.isAdmissible_flip <;> assumption)
end
