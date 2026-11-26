module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

def IsStageC (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ pp D j ∧ q ≤ qq D j ∧ A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * qq D j = rankV D i j + 2 * q ∧ NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (fun t => nuH G t i j) (locPl G)

theorem negIdx_of_isStd {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) : NegIdx V 0 := fun τ => by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]
  refine ⟨(Equiv.sumEmpty _ _).symm, 1, ?_⟩
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  all_goals first | exact a.elim0 | exact b.elim0

theorem IsBottomTri.isStageC {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) : IsStageC W i j 0 0 X := by
  have r := ranks_exact D i j
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, negIdx_of_isStd h.std, negIdx_of_isStd h.std',
    negIdx_of_isStd h.stdW, h.is⟩
  · rw [h.rank]; simpa [pp] using r.1
  · rw [h.rank']; simpa [qq] using r.2.1

end GlobalTheory.SqTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end GlobalTheory.StdCharFromIsStd

namespace GlobalTheory.StdCharFromIsStd

theorem isStdChar_of_isStd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  intro D ψ hψ
  refine ⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩
  change ψ (pairA D.host.F x 0) = _
  rw [psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]
  congr 1
  push_cast
  ring

end GlobalTheory.StdCharFromIsStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  first | exact @GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | exact GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | (intros; apply GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqSumMultMulRe
namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical

  have htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x := by
    rw [← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]
  have hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re htr
    rw [Complex.ratCast_re, Complex.re_sum] at h
    rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]
    rfl

  rw [hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

end GlobalTheory.TraceRealEmbeddingSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiNontriv

variable {F : Type} [Field F] [NumberField F]

theorem trace_re (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  first
  | exact @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | (apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re ..)

theorem trace_mixedEmbedding (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_re, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfinitePlace.sum_eq_sum_add_sum]
  simp only [Algebra.trace_complex_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, Algebra.trace_self_apply]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.embedding_of_isReal_apply w.2,
      Complex.ofReal_re]
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isComplex]
    push_cast
    rfl

end GlobalTheory.PsiNontriv

namespace GlobalTheory.PsiNontriv

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA_zero (a : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F a 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * a = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem isStd_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) :=
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ (at_pairA_zero _), hev, map_neg, map_neg,
    trace_mixedEmbedding]
  congr 1
  push_cast
  ring

theorem psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  set c := FractionalIdeal.count F v (codiff F) with hc
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (isStd_fin_rat hψ)]
    intro α hα
    have e : α * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (α v * x) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
        rfl
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    rw [e]
    have := DFunLike.congr_fun h1 (α v * x)
    rw [AddChar.one_apply] at this
    exact this
  have h2 := (mem_adelicIdeal_iff codiff_ne_zero).1 hmem v
  rw [show (GlobalTheory.AdelicU.singleFin v x) v = x from GlobalTheory.AdelicU.evalV_singleFin_self v x, hx, valued_algebraMap,
    map_zpow₀, hπ, ← WithZero.exp_zsmul, WithZero.exp_le_exp, smul_eq_mul] at h2
  omega

end GlobalTheory.PsiNontriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_adelic_character_nontrivial_at_places : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiAt_ne_one | exact GlobalTheory.PsiNontriv.psiAt_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiAt_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsTransportF (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (ψ : AddChar (AF F) ℂ) {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {κ : Type} [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (ω : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ))
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop :=
  ∀ (a : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA)) (b : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) (g : GAF σ JS) (h : GAF σ JT),
    mtF σ JT h = a.1.1 → mtF σ JS g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ schA F κ, om (a, b) Φ ∈ schA F κ ∧ thetaTr F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr F co ψ Φ)

end GlobalTheory.WeilSchrodinger

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

structure IsAdapted (C : GL (Fin n) E) : Prop where
  le : 2 * r ≤ n
  colX : ∀ (i : Fin n) (j : Fin r), i.val = j.val → ∀ k, C.1 k i = X k j
  columnBlock : ∀ (i : Fin n) (j : Fin r), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j
  perpX : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) X * J) *ᵥ (fun k => C.1 k i) = 0
  perpY : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i) = 0

def blkCols {l d : ℕ} (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin d) E :=
  Z.submatrix id fun j => ⟨l + j.val, by omega⟩

def IsBlockEmb {l d : ℕ} (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J) : Prop :=
  ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
    Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
    (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) ∧
    ∀ g : GlobalTheory.CuspRep.GA E d, (matHom _ σ J (ι g)).1 =
      1 + adMat F (blkCols h X) * (g.1.map Φ.symm - 1) * adMat F (cT (σ : E →+* E) (blkCols h Y) * J) +
        adMat F (blkCols h Y) * (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm) - 1) *
          adMat F (cT (σ : E →+* E) (blkCols h X) * J)


end GlobalTheory.BlockForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
noncomputable section

open NumberField

namespace GlobalTheory.WeilUnitaryTransport

def ratPair (F : Type) [Field F] [NumberField F] (κ : Type) :
    AddSubgroup ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
  ((AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).prodMap
    (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ)).range

theorem mem_ratPair_iff {F : Type} [Field F] [NumberField F] {κ : Type}
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    w ∈ ratPair F κ ↔ ∃ y z : κ → F,
      w = (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) := by
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    exact ⟨(y, z), rfl⟩

end GlobalTheory.WeilUnitaryTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BotFormula

def toFinE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)).toRingEquiv.trans
    (GlobalTheory.LFun.finAdEquiv ℚ D.host.E)

def IsFinPt {D : D7} (WW : HSp D) (g : Formalism.L2.Theta.GA D WW) {n : ℕ} (h : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Prop :=
  g ∈ GfC WW ∧ ∃ e : WW.rank = n, ∀ i j,
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom WW g : GL (Fin WW.rank) _) : Matrix (Fin WW.rank) (Fin WW.rank) _) i j) =
      toFinE D (((h : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Fin.cast e i) (Fin.cast e j))

def minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n) : PolF D d₁ a₁ :=
  MvPolynomial.rename (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast hd k.2.1, Fin.cast ha k.2.2))
    (GlobalTheory.NormSum.minorPol D T)

theorem IsFinPt.cast {D : D7} {WW : HSp D} {g : Formalism.L2.Theta.GA D WW} {n n' : ℕ} (e : n' = n) {h : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    (hg : IsFinPt WW g h) : IsFinPt WW g (e ▸ h : Formalism.MainNotions.StandardLatticesGL3.GA D n') := by
  subst e; exact hg

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  unfold lamC
  rw [dite_eq_left (Qbar.mul_mem hx hy), dite_eq_left hx, dite_eq_left hy, ← map_mul]
  rfl

end GlobalTheory.BotFormula
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.hTens c JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.hTens c JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.hTens GlobalTheory.WeilM.dbl
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, Matrix.neg_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.symp c ξ JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.symp
  rw [hTens_dbl, mul_sub, map_sub]

theorem toCols₁_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
theorem toCols₂_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
theorem toCols₁_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₁ = r • x.toCols₁ := rfl
theorem toCols₂_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₂ = r • x.toCols₂ := rfl

variable [Invertible (2 : R)]

def dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1, Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2))
      invFun := fun q => Matrix.fromCols (d.e.symm (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl))
        (d.e.symm (q.1 ∘ Sum.inr, -(q.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        ext (i | i) <;> simp [toCols₁_add', toCols₂_add'] <;> abel
      map_smul' := fun r x => by
        ext (i | i) <;> simp [toCols₁_smul', toCols₂_smul']
      left_inv := fun x => by
        conv_rhs => rw [← Matrix.fromCols_toCols x]
        beta_reduce
        congr 1
        · exact d.e.symm_apply_apply x.toCols₁
        · have h : (((Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1) ∘ Sum.inr,
              -((Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2)) ∘ Sum.inr)) : (κ → R) × (κ → R)) =
              d.e x.toCols₂ := Prod.ext rfl (funext fun i => neg_neg _)
          exact (congrArg d.e.symm h).trans (d.e.symm_apply_apply _)
      right_inv := fun q => by
        ext (i | i) <;> simp }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem isDblCoord_dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.IsDblCoord c ξ JA JB d (dblD c d) := by
  intro w₁ w₂
  simp [dblD]

end Gen

section Reindex

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem symp_submatrix (e : γ ≃ β) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α γ E) :
    GlobalTheory.WeilM.symp c ξ JA (JB.submatrix e e) x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix id e.symm) (y.submatrix id e.symm) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e.symm.sum_comp]
  simp

variable [Invertible (2 : R)]

def reD (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA J') κ where
  e := (Matrix.reindexLinearEquiv R E (Equiv.refl α) e).trans d.e
  form w w' := by
    rw [h, symp_submatrix, d.form]
    rfl

theorem reD_e (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α γ E) :
    (reD c e h d).e x = d.e (x.submatrix id e.symm) := rfl

end Reindex

section Group

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def reG (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' :=
  ((Units.map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom).comp (GlobalTheory.WeilM.UG c J).subtype).codRestrict
    (GlobalTheory.WeilM.UG c J') fun g => by
      have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
      show (((g : GL β E) : Matrix β β E).submatrix e e)ᵀ * J' * (((g : GL β E) : Matrix β β E).submatrix e e).map c = J'
      rw [h, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem reG_val (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) (g : GlobalTheory.WeilM.UG c J) :
    ((reG c e h g : GL γ E) : Matrix γ γ E) = ((g : GL β E) : Matrix β β E).submatrix e e := rfl

end Group

section Host

variable {D : D7}

def JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    Matrix (Fin (GlobalTheory.Doubling.dblSp S).rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E :=
  (GlobalTheory.WeilM.dbl JB).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem incM_JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    incM D.host.F (JBd S JB) =
      (GlobalTheory.WeilM.dbl (incM D.host.F JB)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [JBd, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

variable [Invertible (2 : AF D.host.F)]

def ddr {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F (JBd S JB)))
      (κ ⊕ κ) :=
  reD _ finSumFinEquiv.symm (incM_JBd S JB) (dblD _ co)

end Host

section HostGroup

variable {D : D7}

def omdOf {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (JBd S JB)) →* Module.End ℂ X) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (reG _ finSumFinEquiv.symm (incM_JBd S JB)))

end HostGroup

end GlobalTheory.DblSchr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
noncomputable section

namespace GlobalTheory.ChrWLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valuation_eq_one_iff {v : Pl F} (x : Fv F v) :
    valuation (Fv F v) x = 1 ↔ Valued.v x = 1 := by
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isUnram_chrW_iff (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t) := by
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := (SplitTie.complMap_bijective t (splitPrime_under t)).2 (y : _)
    have hv : Valued.v a = 1 := by
      rw [← SplitTie.valued_complMap t (splitPrime_under t), ha]; exact hy
    have h0 : a ≠ 0 := by rintro rfl; simp at hv
    have h1 := h (Units.mk0 a h0) ((valuation_eq_one_iff _).2 hv)
    rw [← h1]
    exact congrArg (locChar χ _) (Units.ext ha.symm)
  · intro h x hx
    exact h _ (show Valued.v (complMap (splitPrime_under t) (x : Fv F v)) = 1 by
      rw [SplitTie.valued_complMap t (splitPrime_under t)]; exact (valuation_eq_one_iff _).1 hx)

theorem chrW_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E),
    IsHecke F E χ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  intro F E _ _ _ _ _ χ hχ v t
  have hc := GlobalTheory.ChrWSmooth.continuous_chrW hχ.1 t
  refine ⟨⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ hc, GlobalTheory.ChrWSmooth.isUnitaryChar_chrW χ t⟩, ?_,
    isUnram_chrW_iff χ t⟩
  exact GlobalTheory.GaussNonvanish.exists_condLE (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec _
    (Units.continuous_val.comp hc)

end GlobalTheory.ChrWLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E), IsHecke F E χ →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  first | exact @GlobalTheory.ChrWLocal.chrW_local | exact GlobalTheory.ChrWLocal.chrW_local | (intros; apply GlobalTheory.ChrWLocal.chrW_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitUnitLift

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl (F := F)} {n : ℕ}

theorem unitary_eps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * incM F J *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (cA σ) = incM F J := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 :=
    Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F := F) (AF F))) = J.map τ :=
      Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ *
      ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F := F) (AF F))) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ *
      (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

def liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (oneAdd (liftMat h τ)).comp (pairHom (J.map τ) hJ)

def liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨⟨liftN h τ J hJ g, liftN h τ J hJ g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
    by rw [← map_mul, inv_mul_cancel, map_one]⟩, unitary_eps h τ J ε herm hJ g⟩
  map_one' := Subtype.ext (Units.ext (map_one (liftN h τ J hJ)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (liftN h τ J hJ) g g'))

theorem mat_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    mat (liftU h τ J ε herm hJ g) = 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1) := rfl

theorem liftU_mem_UAt (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Spc F E n) (ε : F)
    (herm : ∀ i j, σ (X.J j i) = algebraMap F E ε * X.J i j) (hJ : IsUnit (X.J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    liftU h τ X.J ε herm hJ g ∈ UAt σ X (evFin F v) := by
  show At (evFin F v) (mat _ - 1)
  rw [mat_liftU, add_sub_cancel_left]
  exact at_liftMat h τ _

theorem liftU_piW (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW τ) = g.val := by
  rw [mat_liftU, map_one_add_piW]
  exact add_sub_cancel _ _

theorem liftU_piW_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW (τ.comp σ)) = (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * J.map τ := by
  rw [mat_liftU, map_one_add_piW_comp]
  exact add_sub_cancel _ _

theorem isUnit_det_of_cartan (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (e : E →+* ℂ) (c : ℂ) (hc : c ≠ 0)
    (θ : Matrix (Fin n) (Fin n) ℂ) (hθ : IsCartan (c • J.map e) θ) : IsUnit (J.map τ).det := by
  have h1 : (c • J.map e).det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hx : star y ≠ 0 := fun h => hy (by simpa using congrArg star h)
    have := hθ.2.2 (star y) hx
    rw [star_star, hMy, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h2 : J.det ≠ 0 := by
    intro h0
    apply h1
    have hd : (J.map e).det = e J.det := (RingHom.map_det e J).symm
    rw [Matrix.det_smul, hd, h0, map_zero, mul_zero]
  have hd : (J.map τ).det = τ J.det := (AlgHom.map_det τ J).symm
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 h2

end GlobalTheory.SplitUnitLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvgDual

section Local

variable {F : Type} [Field F] [NumberField F]

theorem eq_of_tens_eq {κ : Type} [Fintype κ] (v : Pl (F := F)) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hRv : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hR : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by simpa using hRv 0 _ hat
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_one {κ : Type} [Fintype κ] (v : Pl (F := F)) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (1 : Module.End ℂ ((κ → AF F) → ℂ)) φ φ := fun _ _ => rfl

theorem acts_comp {κ : Type} [Fintype κ] (v : Pl (F := F)) (T S : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) : Acts (evFin F v) (S * T) φ φ₂ := by
  intro r hr
  have e := h₁ r hr
  have hr' : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT _ hr.2⟩
  rw [Module.End.mul_apply, e]
  exact h₂ r hr'

end Local

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Stab

end GlobalTheory.InertAvgDual
end
end
