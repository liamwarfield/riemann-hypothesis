module

public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaProjectionAdjointBasisRowEigenvalue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KappaConstantSharpLevelEqDataKappaConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LambdaPrimeBasisRowTypePosAtReference
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.LamPos

theorem lambdaPrime_basis_row_type_pos_at_reference : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, ∀ j ∈ Finset.Icc 1 D.R.m, 0 < D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH hL hI σ j hj
  obtain ⟨cOf, -, h2, -⟩ := hL
  obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
  have hi : j - 1 < D.R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin D.R.m) : ℕ) + 1 = j := by simp only; omega
  have key := h2 ⟨j - 1, hi⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hI σ ⟨j - 1, hi⟩)
  rw [Y.tup0, hj'] at key
  rw [key]
  exact hH.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.R3.LamPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DrowsPos
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem drows_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → 0 < D.what₂.Drows := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH _
  have e1 : Module.finrank D.what₂.LL D.div.RR.V = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis D.div.RR.b
  have e2 : Module.finrank ℂ D.what₂.EE = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm))
  have e3 : Module.finrank ℂ D.what₂.EE = D.what₂.Drows := by
    simpa using Module.finrank_eq_card_basis D.what₂.onb.toBasis
  have h2 : Module.finrank D.what₂.LL D.div.RR.V = ((R.toCx3 F).data F.cr true).D := by
    rw [← Z.eRR.finrank_eq, Module.finrank_fin_fun]
  have h3 : 0 < ((R.toCx3 F).data F.cr true).D := hH.prim.pos true
  omega

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KappaConstantSharpLevelEqDataKappaConstant
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec

theorem kapOf_of_eigen {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) {κ : ℝ} (hk : 0 < κ) (hn : 0 < n)
    (hP : ∀ σ, 0 < ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ))
    (hT : ∀ σ, S.iiStar (b σ) = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) : ℝ) : ℂ) • b σ) :
    S.kapOf ty = κ := by
  set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef
  have hdet : LinearMap.det S.iiStar = ((κ ^ n * ∏ σ, P σ : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar =
        Matrix.diagonal (fun σ => ((κ * P σ : ℝ) : ℂ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply,
        ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : j = i
      · subst hij; simp [P]
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]; simp
    rw [hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hr : S.kapRatio ty = κ ^ n := by
    unfold RowSide.kapRatio DV.lamProd
    rw [hdet, Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ (Finset.prod_pos fun σ _ => hP σ).ne'
  unfold RowSide.kapOf
  rw [hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (y : EE) :
    S.iiStar y = S.iota D.what₂.mu0 (S.eOp D.what₂.mu0 (LinearMap.adjoint (S.iota D.what₂.mu0) y)) := by
  set μ := D.what₂.mu0
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem kapSharp_eq_kap : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → kapSharp D = R.kap := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI
  exact kapOf_of_eigen (RowSide.sharp D) D.what₂.onb D.what₂.ft hH.prim.posScal.1
    (GlobalTheory.Mem.R3.drows_pos D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL)
    (fun σ => Finset.prod_pos (GlobalTheory.Mem.R3.LamPos.lambdaPrime_basis_row_type_pos_at_reference D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))
    (fun σ => (iiStar_apply_eq (RowSide.sharp D) (D.what₂.onb σ)).trans
      (GlobalTheory.T.iotaProjectionAdjoint_basisRow_eigenvalue hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI σ))

end GlobalTheory.KapRec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KappaConstantSharpLevelEqDataKappaConstantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaConstant_sharpLevel_eq_dataKappaConstant : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → kapSharp D = R.kap := by
  first | exact @GlobalTheory.KapRec.kapSharp_eq_kap | exact GlobalTheory.KapRec.kapSharp_eq_kap | (intros; apply GlobalTheory.KapRec.kapSharp_eq_kap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.KapRow

theorem kapR_eq_rows_kappa : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → (∀ σ, Xd.kapR σ = kapSharp D) → ∀ e : D.what₂.LL →+* ℂ, Xd.kapR e = (s1Of R F).κ (InfinitePlace.mk e) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hL hne hk e
  rw [hk e]
  exact GlobalTheory.T.kappaConstant_sharpLevel_eq_dataKappaConstant hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hne

end GlobalTheory.KapRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → (∀ σ, Xd.kapR σ = kapSharp D) → ∀ e : D.what₂.LL →+* ℂ, Xd.kapR e = (s1Of R F).κ (InfinitePlace.mk e) := by
  first | exact @GlobalTheory.KapRow.kapR_eq_rows_kappa | exact GlobalTheory.KapRow.kapR_eq_rows_kappa | (intros; apply GlobalTheory.KapRow.kapR_eq_rows_kappa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem.R3

namespace GlobalTheory.KapIsotRead


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isot_ne_bot_read : GlobalTheory.Published.HarishChandraFinite → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.L2.DIV.GoodStable A3.A.X → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥ := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPin hH hME hGS hgen σ i
  have hL := Y.tied.lift
  obtain ⟨w, hw, hw0⟩ := GlobalTheory.KapIsot.exists_mem_isotL hP R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hPin.char hH.aux.ex).1 hME hGS hgen Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ))) (principalLevelFrame.rowRepR_occ _ _)
  intro hbot
  let L := RecTie.toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj
  let lw : L.AmbW i := (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i) w
  have hgood : lw ∈ L.Wc i := Submodule.mem_map_of_mem hw.1
  let y : D.what₂.Mj ((i : ℕ) + 1) := (Y.IL.jMj i).symm ⟨lw, hgood⟩
  have hjy : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) = lw := by
    simp only [y, LinearEquiv.apply_symm_apply]
  have hmem : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) ∈ Y.IL.prtW i (D.what₂.ft σ) := by
    rw [hjy, Y.prtWE]
    exact ⟨w, hw, rfl⟩
  have hy0 : y ∈ D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) := (hL.isot i _ y).2 hmem
  rw [hbot, Submodule.mem_bot] at hy0
  apply hw0
  have h1 : lw = 0 := by rw [← hjy, hy0, map_zero]; rfl
  exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i).injective (h1.trans (map_zero _).symm)

end GlobalTheory.KapIsotRead
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}


set_option maxHeartbeats 2000000 in
theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i


set_option maxHeartbeats 2000000 in
theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows


end GlobalTheory.Fc.KapLinked

end
