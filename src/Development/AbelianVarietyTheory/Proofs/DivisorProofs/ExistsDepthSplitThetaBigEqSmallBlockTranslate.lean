module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralTwoSidedMovedDatumEqSmallZeta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralLeftTranslatePrimitiveFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralLeftTranslatePrimitiveFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

open GlobalTheory.OneSquareZeta

theorem GlobalTheory.LeftTranslateZeta.bigF_phiA_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν ϖ n c Ψ g₀ h hϖ

  have hlat : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : (X0 k σ * (invT h).val).rank = a := by
    rw [(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ (X0 k σ * (invT h).val)).2 ⟨h, rfl⟩, Fintype.card_fin]

  obtain ⟨g₁, hg₁⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) _ hrank
  rw [← hlat] at hg₁
  have hκ : (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

  have hpt : ∀ g : GL (Fin a) k,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}.indicator
        (fun _ => fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) g := by
    intro g
    have hgX : g₀.val * (g.val * (X0 k σ * (invT h).val)) = g₀.val * g.val * (X0 k σ * (invT h).val) :=
      (Matrix.mul_assoc _ _ _).symm
    rw [hgX]
    have key := fFun_mul_left (μ := μ) (σ := σ) (ν := ν) (Ψ := Ψ) (g := g₀ * g) (h := h)
    simp only [apow_mul, map_mul, Units.val_mul] at key
    by_cases hS : g₀ * g * g₁⁻¹ ∈ KO k (Fin a)
    · have hP : IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        (isPrimFrame_mul_iff hg₁ (g₀ * g)).2 hS
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_mem (show g ∈ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_pos hP,
        eq_div_iff hκ, ← key]
      ring
    · have hP : ¬ IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        fun hP => hS ((isPrimFrame_mul_iff hg₁ (g₀ * g)).1 hP)
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_notMem (show g ∉ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_neg hP]
      ring

  have hsum : (∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in shellSet ϖ m.1,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
        ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) := by
    have hint : ∀ m : {m : Fin a → ℤ // Antitone m}, (∫ g in shellSet ϖ m.1,
        phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
          apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
        (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}) •
          (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
            ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) := by
      intro m
      rw [integral_congr_ae (ae_of_all _ hpt)]
      refine (setIntegral_indicator ?_).trans (setIntegral_const (E := ℂ)
        (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))))
      let : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
      haveI : BorelSpace (GL (Fin a) k) := borel_GL
      exact (ShellVolume.isOpen_translate g₀ g₁⁻¹).measurableSet
    rw [finsum_congr hint, ← finsum_smul,
      ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁⁻¹ hϖ, one_smul]
  unfold bigF shellSum shell
  refine (congrArg (fun s => s * (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) hsum).trans ?_
  rw [mul_assoc]
  exact div_mul_cancel₀ _ hκ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralLeftTranslatePrimitiveFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_leftTranslate_primitiveFrames : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.LeftTranslateZeta.bigF_phiA_left | exact GlobalTheory.LeftTranslateZeta.bigF_phiA_left | (intros; apply GlobalTheory.LeftTranslateZeta.bigF_phiA_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralTwoSidedMovedDatumEqSmallZeta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (N h : GL C k),
    IsUnif ϖ →
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2) *
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val)) h =
      smallP μ σ ν (ν * β) (fun Y => Ψ (Y * (invT N).val)) h := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ g₀ N h hϖ
  set h' : GL C k := h * invT N with hh'
  have hX : X0 k σ * (invT h).val * N.val = X0 k σ * (invT h').val := by
    rw [hh', map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
  have hF : bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val))
      (X0 k σ * (invT h).val) =
      bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z))
      (X0 k σ * (invT h').val) := by
    rw [← hX]; simp only [bigF, Matrix.mul_assoc]
  have hL := GlobalTheory.T.zetaIntegral_leftTranslate_primitiveFrames k a A' C μ σ ν ϖ n c Ψ g₀ h' hϖ
  rw [splitTheta_fFun_frameFirstBlock_mul] at hL
  have hS : smallF μ ν Ψ (Y0 k σ * h'.val) = smallF μ ν (fun Y => Ψ (Y * (invT N).val)) (Y0 k σ * h.val) := by
    simp only [smallF, hh', Units.val_mul, Matrix.mul_assoc]
  have hdet : gdet h' = gdet h * (gdet N)⁻¹ := by rw [hh', gdet_mul, gdet_invT]
  rw [hS, hdet, map_mul ν, apow_mul, apow_inv, map_inv ν, Units.val_mul] at hL
  rw [bigZetaIntegral_eq, hF, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  have eN : apow (gdet N) ((Fintype.card C : ℂ) / 2) * apow (gdet N) (-((Fintype.card C : ℂ) / 2)) = 1 := by
    rw [apow_neg, mul_inv_cancel₀ (apow_ne_zero _ _)]
  have eν : (ν (gdet N) : ℂ) * ((ν (gdet N))⁻¹ : ℂˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2)) * hL +
    ((β (gdet h) : ℂ) * (ν (gdet h) : ℂ) * smallF μ ν (fun Y => Ψ (Y * (invT N).val)) (Y0 k σ * h.val)) *
      (apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) * ((ν (gdet N) : ℂ) * ((ν (gdet N))⁻¹ : ℂˣ)) * eN +
        apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) * eν + e)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralTwoSidedMovedDatumEqSmallZetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (N h : GL C k),
    IsUnif ϖ →
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2) *
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val)) h =
      smallP μ σ ν (ν * β) (fun Y => Ψ (Y * (invT N).val)) h := by
  first | exact @GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta | exact GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta | (intros; apply GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PurityDepth

theorem hasDepth_scaled : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  intro k _ _ _ _ A' C _ _ _ _ ϖ P Ψ hΨ hϖ
  have hΨ' : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix A' C k) := hΨ
  have hϖ' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := fun x => by rw [hϖ, le_uniformizer_iff]
  obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k A' C Ψ hΨ'
  let f : (A' × C → k) → Matrix A' C k := fun z => Matrix.of fun i j => z (i, j)
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_apply (i, j)
  have hΛn : f ⁻¹' (Λ : Set (Matrix A' C k)) ∈ nhds (0 : A' × C → k) :=
    (hΛ.preimage hf).mem_nhds (by
      show f 0 ∈ Λ
      exact (show f 0 = 0 from rfl) ▸ Λ.zero_mem)
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ q : A' × C, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix A' C k => x q.1 q.2) '' tsupport Ψ ⊆ GlobalTheory.SplitWeil.cball (ϖ ^ e)⁻¹ := fun q =>
    GlobalTheory.AdaptedExp.eventually_subset_cball hϖ' (hc.image (by fun_prop))
  obtain ⟨M, hM1, hM2⟩ := ((Filter.eventually_all.2 h1).and (GlobalTheory.AdaptedExp.eventually_box_subset hϖ' hΛn)).exists
  refine ⟨M, fun n hn => ?_⟩

  set w := valuation k (ϖ : k) with hw
  have hw1 : w ≤ 1 := hϖ.mem
  set u := valuation k ((ϖ ^ M : kˣ) : k) with hu
  have hu0 : 0 < u := zero_lt_iff.2 (by simp [hu])
  have huw : u = w ^ M := by rw [hu, Units.val_pow_eq_pow_val, map_pow]
  have hinvu : valuation k (((ϖ ^ M)⁻¹ : kˣ) : k) = u⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn' : valuation k ((ϖ ^ n : kˣ) : k) ≤ u * u := by
    rw [Units.val_pow_eq_pow_val, map_pow, huw, ← pow_add, ← two_mul]
    exact pow_le_pow_right_of_le_one' hw1 hn
  have hd : ∀ (X : Matrix A' C k) i j, (X * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) i j = X i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)) :=
    fun X i j => mul_diagonal _ _ _ _
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · by_contra hne
    apply hY
    have hs := subset_tsupport _ hne
    have he : ∀ i j, valuation k (Y i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k))) ≤ u⁻¹ :=
      fun i j => by
        have := hM1 (i, j) ⟨_, hs, rfl⟩
        simpa only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, hd, hinvu] using this
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
    · have h := he i j
      rw [if_pos hj, map_mul, ← hu] at h
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j) ≤ u * u * valuation k (Y i j) :=
            mul_le_mul_left hn' _
        _ = u * (valuation k (Y i j) * u) := by rw [mul_assoc, mul_comm u (valuation k (Y i j))]
        _ ≤ u * u⁻¹ := mul_le_mul_right h _
        _ = 1 := mul_inv_cancel₀ hu0.ne'
    · have h := he i j
      rw [if_neg hj, map_mul, hinvu] at h
      rw [Valuation.mem_integer_iff]
      have := mul_le_mul_left h u
      rwa [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this
  · obtain ⟨h1, h2⟩ := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.1 hZ
    show Ψ ((Y + Z) * _) = Ψ (Y * _)
    rw [Matrix.add_mul]
    refine hinv _ _ ?_
    refine hM2 (fun q => (Z * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) q.1 q.2) ?_
    unfold GlobalTheory.StepData.box
    intro q
    beta_reduce
    rw [hd, map_mul, ← hu]
    by_cases hj : q.2 ∈ P
    · rw [if_pos hj, ← hu]
      calc valuation k (Z q.1 q.2) * u ≤ 1 * u := mul_le_mul_left (h1 q.1 q.2 hj) _
        _ = u := one_mul u
    · rw [if_neg hj, hinvu]
      calc valuation k (Z q.1 q.2) * u⁻¹ ≤ u * u * u⁻¹ := mul_le_mul_left ((h2 q.1 q.2 hj).trans hn') _
        _ = u := by rw [mul_assoc, mul_inv_cancel₀ hu0.ne', mul_one]

end GlobalTheory.PurityDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  first | exact @GlobalTheory.PurityDepth.hasDepth_scaled | exact GlobalTheory.PurityDepth.hasDepth_scaled | (intros; apply GlobalTheory.PurityDepth.hasDepth_scaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumber
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumber
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.ColumnRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

def permGL (π : C ≃ C) : GL C k :=
  ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixFirstColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    X0 k σ' * (invT h).val = X0 k σ * (invT (permGL (σ.symm.trans σ') * h)).val := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, invT_val, invT_val, _root_.mul_inv_rev]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul, Option.mem_def, Equiv.symm_apply_eq]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixSecondColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    Y0 k σ * (permGL (σ.symm.trans σ') * h).val = Y0 k σ' * h.val := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul]

variable [MeasurableSpace k] [BorelSpace k]

theorem fFun_renumber (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k) :
    fFun μ σ' ν Ψ X = ((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹ * fFun μ σ ν Ψ X := by
  set Q : GL C k := permGL (σ.symm.trans σ') with hQ
  by_cases hX : ∃ h : GL C k, X = X0 k σ' * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have hc : (ν (gdet Q) : ℂ) * apow (gdet Q) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    rw [splitTheta_fFun_frameFirstBlock_mul μ σ', frameMatrixFirstColumnBlock_renumber σ σ' h, splitTheta_fFun_frameFirstBlock_mul μ σ, ← hQ, frameMatrixSecondColumnBlock_renumber, gdet_mul, map_mul, apow_mul,
      Units.val_mul]
    have ha := apow_ne_zero (gdet Q) ((Fintype.card C : ℂ) / 2)
    have hn : (ν (gdet Q) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hX' : ¬ ∃ h : GL C k, X = X0 k σ * (invT h).val := fun H =>
      hX ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ' X).1 ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 H))
    rw [fFun, dite_eq_right hX, fFun, dite_eq_right hX', mul_zero]

end GlobalTheory.ColumnRenumber


open GlobalTheory.ColumnRenumber in
theorem GlobalTheory.ColumnRenumber.phiA_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  intro k _ _ _ _ _ _ A A' C _ _ _ _ _ _ μ _ σ σ' ν
  refine ⟨((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹,
    inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)), fun ϖ n Λ Ψ X => ?_⟩
  unfold phiA
  split_ifs
  · exact fFun_renumber μ σ σ' ν Ψ X
  · rw [mul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumberStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  first | exact @GlobalTheory.ColumnRenumber.phiA_renumber | exact GlobalTheory.ColumnRenumber.phiA_renumber | (intros; apply GlobalTheory.ColumnRenumber.phiA_renumber <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDepthSplitThetaBigEqSmallBlockTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PureMatch

theorem smallP_smul_measure_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) (c : NNReal) (z : ℂ) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ)
    (h : GL C k) : smallP (c • μ) σ ν α (fun Y => z * Ψ Y) h = (c : ℂ) * z * smallP μ σ ν α Ψ h := by
  simp only [smallP, smallF, mul_assoc, integral_const_mul, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  ring

theorem bigZetaIntegral_const_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {a : ℕ} {A' C : Type} [Fintype C] [DecidableEq C]
    (μ : @Measure (GL (Fin a) k) Units.instMeasurableSpace) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) C k → ℂ) (h : GL C k) :
    bigP μ ϖ σ ν β (fun Z => z * Φ Z) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, shellSum_smul]
  ring

theorem exists_depth_bigP_eq_smallP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ₀ _ σ ν β ϖ P g₀ c₀ Ψ hΨ hϖ
  have hΨ' : (fun Y : Matrix A' C k => Ψ (Y * c₀.valᵀ)) ∈ GlobalTheory.WeilM.SB (Matrix A' C k) := by
    have := comp_mul_mem_SB (1 : GL A' k) (invT c₀)⁻¹ hΨ
    simp only [invT_inv_val, Units.val_one, Matrix.one_mul] at this
    exact this
  obtain ⟨m, hm⟩ := GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth k A' C ϖ P _ hΨ' hϖ
  refine ⟨m, fun n hn μ _ σ' r hr => ?_⟩
  obtain ⟨u, hu, hphi⟩ := GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber k (Fin a) A' C μ σ σ' ν
  obtain ⟨c, hc0, hc⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ = c • μ₀ :=
    ⟨Measure.haarScalarFactor μ μ₀, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne',
      Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  set N : GL C k := c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹) with hN
  set κ : ℂ := (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) *
    apow (gdet N) ((Fintype.card C : ℂ) / 2) with hκ
  have hκ0 : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)) (Units.ne_zero _)) (apow_ne_zero _ _)
  have hc0' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hNT : ∀ Y : Matrix A' C k, Y * N.valᵀ =
      Y * diagonal (fun col => if col ∈ P then ((ϖ ^ m : kˣ) : k) else (((ϖ ^ m)⁻¹ : kˣ) : k)) * c₀.valᵀ := by
    intro Y
    rw [hN, Units.val_mul, transpose_mul, diagGL_val, diagonal_transpose, Matrix.mul_assoc]
    congr 3
    funext col
    split_ifs <;> rfl
  refine ⟨fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ), ?_, ?_⟩
  · have h1 := (depthSpace A' ϖ n (blockLat ϖ n P)).smul_mem (κ / (r * u * c)) (hm n hn)
    simp only [hNT]
    exact h1
  · funext h
    have h2 := GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta k a A' C μ σ ν β ϖ n (blockUnits ϖ n P)
      (fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ)) g₀ N h hϖ
    have h3 : ∀ Y : Matrix A' C k, Y * (invT N).val * N.valᵀ = Y := fun Y => by
      rw [Matrix.mul_assoc, ← invT_inv_val, Units.mul_inv, Matrix.mul_one]
    simp only [h3] at h2
    have h4 := smallP_smul_measure_mul μ₀ c (κ / (r * u * c)) σ ν (ν * β) Ψ h
    rw [← hc, ← h2, ← hκ] at h4
    simp only [hphi, ← mul_assoc]
    rw [bigZetaIntegral_const_mul]
    apply mul_left_cancel₀ hκ0
    rw [mul_left_comm]
    refine (congrArg (fun x => r * u * x) h4).trans ?_
    field_simp

end GlobalTheory.PureMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDepthSplitThetaBigEqSmallBlockTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_depth_splitThetaBig_eq_small_blockTranslate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  first | exact @GlobalTheory.PureMatch.exists_depth_bigP_eq_smallP | exact GlobalTheory.PureMatch.exists_depth_bigP_eq_smallP | (intros; apply GlobalTheory.PureMatch.exists_depth_bigP_eq_smallP <;> assumption)
end
