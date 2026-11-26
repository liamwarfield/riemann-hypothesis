module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

open scoped ComplexOrder


open Formalism.IndefR.Cx.GroupActionMatrices Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition Formalism.L2.DIV.CyclotomicLifting in
theorem csum_eigSum_orth {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v : InfinitePlace K} {s : ℕ} {op : I → Module.End K B.S.Forms}
    (h : BlockHyp B ℓ v s) (hO : OkOp B op) {C C' : (I → K) → Prop} (hCC : ∀ x, C' x → ¬ C x) {f g : B.S.Forms}
    (hf : f ∈ Formalism.L2.Col.eigSum op C) (hg : g ∈ Formalism.L2.Col.eigSum op C') :
    B.S.csum (f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = 0 := by
  classical
  have hA : (B.S.H.map v.embedding).PosDef := h.ok.hpos v
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v)
  have hadj : ∀ i, ∃ i', B.S.H.map v.embedding * (oM B op i).map v.embedding =
      ((oM B op i').map v.embedding)ᴴ * B.S.H.map v.embedding := by
    intro i
    obtain ⟨i', hi'⟩ := oM_adj hO i
    have h2 : B.S.H * oM B op i = (oM B op i')ᴴ * B.S.H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    refine ⟨i', ?_⟩
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax v.embedding _ (hO.rat i')]
  have hc : Formalism.L2.Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, oM_comm hO.comm])
  have hs : Formalism.L2.Col.SplitOver (linF fun i => (oM B op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hmem : ∀ {S : (I → K) → Prop} {z : B.S.Forms}, z ∈ Formalism.L2.Col.eigSum op S →
      (fun a => v.embedding (B.S.basis.equivFun z a)) ∈ Formalism.L2.Col.eigSum (linF fun i => (oM B op i).map v.embedding)
        (fun w => ∃ x, S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h1 : B.S.basis.equivFun z ∈ Formalism.L2.Col.eigSum (fun i => Matrix.toLin' (oM B op i)) S := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_oM i f) _ hz
      simpa [Submodule.mem_comap] using this
    exact emb_mem_eigSum v.embedding (oM B op) S h1
  have hCC' : ∀ w, (fun w => ∃ x, C' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, C x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hCC x' hx' hx
  have key := cx_eig_orth (fun i => (oM B op i).map v.embedding) (B.S.H.map v.embedding) hA hadj hc hs hCC' (hmem hf) (hmem hg)
  have hform0 : hform B.S.H (B.S.basis.equivFun f) (B.S.basis.equivFun g) = 0 := by
    apply v.embedding.injective
    rw [map_zero, ← key, RationalHermitianForm.hform_eq_dot, ← emb_mulVec v.embedding B.S.H]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.conj]
    rfl
  rw [hform_eq_csum, CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hform0
  exact hform0

end GlobalTheory.Div

namespace GlobalTheory.Div


set_option maxHeartbeats 1000000 in
theorem inner_jX_csum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms) :
    Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
  rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
  congr 1
  exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y

theorem inner_jX_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : A.fam.base.Tup)
    (x y : (A.fam.R t).S.Forms)
    (h : (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)
        ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) = 0) :
    inner ℂ (R.jX t x) (R.jX t y) = 0 := by
  have key := inner_jX_csum R hM t x y
  have h1 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) = 0 :=
    key.trans ((congrArg (⇑A.v0.embedding) h).trans (map_zero A.v0.embedding))
  exact (map_eq_zero (Formalism.IndefR.Links.cj (twAt D.what₂.embLL A.v0))).1 h1

end GlobalTheory.Div

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.parts_orth_complex : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH p q hpq x hx y hy
  have hok := hOk.ok2.what₂ A3.A.μ0
  have hO := okOp_opAll hok (hOk.what₂ A3.A.μ0) (hH A3.A.μ0).1 (hH A3.A.μ0).2
  have hSS : ∀ z, (A3.rowI A3.A.μ0).HasRes3 q.1 z → ¬ (A3.rowI A3.A.μ0).HasRes3 p.1 z := fun z hq =>
    (A3.rowI A3.A.μ0).excl3 ((A3.rowI A3.A.μ0).diffAt_of_mem_ixFin3 q.2 p.2 fun e => hpq (Subtype.ext e).symm) z hq
  have hblk : BlockHyp (A3.A.fam.R A3.A.μ0) (A3.A.fam.lvl F.P0 F.ψ0) A3.A.fam.v0 s := ⟨hOk.ok2.conj, hOk.ok2.irr, hok⟩
  have hgen : ∀ f ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1, ∀ g ∈ (A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1,
      ⟪R.jX A3.A.μ0 f, R.jX A3.A.μ0 g⟫_ℂ = 0 := by
    intro f hf g hg
    have h0 := GlobalTheory.Div.csum_eigSum_orth hblk hO hSS hf hg
    exact GlobalTheory.Div.inner_jX_zero R.toRealDat hC.base.models A3.A.μ0 f g h0
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, hf, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, hg, rfl⟩ := hb
      exact hgen f hf g hg
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [inner_smul_right, hu, mul_zero]
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_parts_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → ∀ p q : A3.fam3.base3.Ix, p ≠ q → ∀ x ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ∀ y ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)), ⟪x, y⟫_ℂ = 0 := by
  first | exact @GlobalTheory.Div.parts_orth_complex | exact GlobalTheory.Div.parts_orth_complex | (intros; apply GlobalTheory.Div.parts_orth_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.inner_EEp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH hPos hB p q hpq e he e' he'

  have hmap : ∀ r, (R.EEp3 r).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
      Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum r.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) := by
    intro r
    rw [Submodule.map_le_iff_le_comap]
    exact iSup₂_le fun c hc => Submodule.map_le_iff_le_comap.1 hc.2
  have hx : LinearMap.adjoint (R.Th A3.A.μ0) e ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap p (Submodule.mem_map_of_mem he)
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) e' ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap q (Submodule.mem_map_of_mem he')
  have h0 := GlobalTheory.T.complex_points_parts_distinct_types_orthogonal R F hOk hC hH p q hpq _ hx _ hy
  have hk := hB A3.A.μ0 p e he
  rw [LinearMap.comp_apply] at hk
  have hin : ⟪R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) e), e'⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right]; exact h0
  rw [hk, inner_smul_left] at hin
  have ha : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    rw [RealDat3.prod_lamN]
    exact mul_pos hPos.1 (Finset.prod_pos fun j _ => hPos.2 j _ _)
  rcases mul_eq_zero.1 hin with h | h
  · exfalso
    rw [Complex.conj_ofReal] at h
    exact ha.ne' (by exact_mod_cast h)
  · exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_rowParts_of_distinct_types : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.Div.inner_EEp3_eq_zero_of_ne | exact GlobalTheory.Div.inner_EEp3_eq_zero_of_ne | (intros; apply GlobalTheory.Div.inner_EEp3_eq_zero_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulVecOfMemTD
noncomputable section

open scoped Matrix

namespace GlobalTheory.HaarLin

def TD (R : Type) [CommRing R] (κ : Type) [Fintype κ] [DecidableEq κ] : Submonoid (Matrix κ κ R) :=
  Submonoid.closure ({M | ∃ i j : κ, ∃ c : R, i ≠ j ∧ M = Matrix.transvection i j c} ∪
    {M | ∃ d : κ → Rˣ, M = Matrix.diagonal fun i => (d i : R)})

def HasStableRangeOne (R : Type) [CommRing R] : Prop := ∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)

end GlobalTheory.HaarLin

open NumberField MeasureTheory Matrix
open scoped NNReal ENNReal
namespace GlobalTheory.HaarLin

private lemma nnreal_eq_of_smul_addHaar_eq {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : X)
  have h1 : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hK0).ne'
  have h2 : μ K ≠ ∞ := hK.measure_lt_top.ne
  have h3 : (a • μ) K = (b • μ) K := by rw [h]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3
  exact_mod_cast (ENNReal.mul_left_inj h1 h2).1 h3

private lemma map_mul_lemma_2 {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (A B : Matrix κ κ R) (μ : Measure (κ → R)) :
    μ.map (fun x => (A * B) *ᵥ x) = (μ.map (fun x => B *ᵥ x)).map (fun x => A *ᵥ x) := by
  have hA : Measurable (fun x : κ → R => A *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun x : κ → R => B *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [Measure.map_map hA hB]
  congr 1
  funext x
  simp [Function.comp, Matrix.mulVec_mulVec]

private lemma exists_map_mulVec_eq_smul_of_invertible {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (P Q : Matrix κ κ R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∃ c : ℝ≥0, ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → μ.map (fun x => P *ᵥ x) = c • μ := by
  let e : (κ → R) ≃+ (κ → R) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => Q *ᵥ x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ]
      map_add' := fun x y => Matrix.mulVec_add P x y }
  have he : Continuous (fun x : κ → R => P *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have he' : Continuous (fun x : κ → R => Q *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure :=
    fun μ _ => e.isAddHaarMeasure_map μ he he'
  let μ₀ : Measure (κ → R) := Measure.addHaar
  haveI := key μ₀ inferInstance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun μ hμ => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hc, smul_comm]
  exact he.measurable.aemeasurable

private lemma map_transvection_mulVec_addHaar_eq_self {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (i j : κ) (hij : i ≠ j) (c : R)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => transvection i j c *ᵥ x) = μ := by
  set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0
  have hD : D * D = 1 := by
    rw [hD0, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [Function.update_apply, hk]
  have hT : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]
  have hT' : transvection i j (-c) * transvection i j c = 1 := by
    rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]
  have hconj : D * transvection i j c * D = transvection i j (-c) := by
    have hji : j ≠ i := Ne.symm hij
    clear hD hT hT'
    ext a b
    simp only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
    clear hD0
    split_ifs <;> grind
  have hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ := by
    simp only [Matrix.one_mulVec, Measure.map_id']
  obtain ⟨a, ha⟩ := exists_map_mulVec_eq_smul_of_invertible D D hD hD
  obtain ⟨t, ht⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'
  obtain ⟨t', ht'⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT
  have haa : a * a = 1 := by
    have h := map_mul_lemma_2 D D μ
    rw [hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have htt : t' * t = 1 := by
    have h := map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ
    rw [hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have hcj : t' = a * t * a := by
    have h := map_mul_lemma_2 (D * transvection i j c) D μ
    rw [hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2,
      ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ h
  have h2 : t * t = 1 := by
    rw [hcj] at htt
    calc t * t = t * t * (a * a) := by rw [haa, mul_one]
      _ = a * t * a * t := by ring
      _ = 1 := htt
  have h3 : t = 1 := by
    have h4 : (t : ℝ) * t = 1 := by exact_mod_cast h2
    apply NNReal.eq
    have h5 := t.coe_nonneg
    push_cast
    nlinarith
  rw [ht μ inferInstance, h3, one_smul]

private lemma map_diagonal_mulVec_eq_inv_prod_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [inst : MeasurableSpace (κ → R)] [hb : BorelSpace (κ → R)] (d : κ → Rˣ)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • μ := by
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩
  have e : inst = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq (κ → R) _ inst hb).trans
      (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) =
      (distribHaarChar R u)⁻¹ • Measure.addHaar := by
    intro u
    have hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y := by
      funext y
      simp [Units.smul_def]
    rw [hu]
    change DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0
  have hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν := by
    have hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i := by
      funext x i
      exact mulVec_diagonal _ _ _
    haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by
      rw [h1]; infer_instance
    rw [hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y)
      (fun i => (continuous_const_mul (d i : R)).measurable.aemeasurable)]
    simp_rw [h1]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib,
      Finset.prod_mul_distrib]
    norm_cast
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hν, smul_comm]
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable

private lemma exists_unit_det_map_mulVec_haar_eq_inv_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (M : Matrix κ κ R) (hM : M ∈ TD R κ) :
    ∃ v : Rˣ, (v : R) = M.det ∧ ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      μ.map (fun x => M *ᵥ x) = (distribHaarChar R v)⁻¹ • μ := by
  induction hM using Submonoid.closure_induction with
  | mem M hM =>
    simp only [Set.mem_union, Set.mem_setOf_eq] at hM
    rcases hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩
      rw [map_one, inv_one, one_smul]
      exact map_transvection_mulVec_addHaar_eq_self i j hij c μ
    · refine ⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩
      rw [map_prod]
      exact map_diagonal_mulVec_eq_inv_prod_smul d μ
  | one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩
  | mul M N _ _ hM hN =>
    obtain ⟨v, hv, hvμ⟩ := hM
    obtain ⟨w, hw, hwμ⟩ := hN
    refine ⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩
    rw [map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]
    exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable

theorem map_mulVec_of_mem_TD : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), M ∈ TD R κ → ∀ u : Rˣ, u.1 = M.det → ∀ μ : @Measure (κ → R) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    @Measure.map _ _ (borel _) (borel _) (fun x : κ → R => M *ᵥ x) μ = ((distribHaarChar R u)⁻¹ : ℝ≥0) • μ := by
  intro R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ
  letI : MeasurableSpace (κ → R) := borel (κ → R)
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  obtain ⟨v, hv, hvμ⟩ := exists_unit_det_map_mulVec_haar_eq_inv_smul M hM
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst huv
  exact hvμ μ hμ

end GlobalTheory.HaarLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Generic

variable {B Hf W : Type} [Group B] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : B →* Hf) (Γ : Subgroup B)
  (ρ : B →* Module.End ℂ W) {J : Subgroup Hf} {χ : J →* ℂˣ}

theorem rho_mul (a b : B) (w : W) : ρ (a * b) w = ρ a (ρ b w) := by rw [map_mul]; rfl

theorem rho_rho_inv (a : B) (w : W) : ρ a (ρ a⁻¹ w) = w := by rw [← rho_mul, mul_inv_cancel, map_one]; rfl

theorem mem_adForms (s : Hf → B) (hs : ∀ u, π (s u) = u) (hρ : ∀ u, ρ (s u) = 1) (Ψ : B → W)
    (h : ∀ γ ∈ Γ, ∀ k (hk : π k ∈ J), ∀ x, Ψ (γ * x * k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (Ψ x)) :
    (fun u => Ψ (s u)) ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ := by
  intro γ u k
  have e : π (((γ : B) * s u)⁻¹ * s (π γ * u * k)) = k := by
    rw [map_mul, map_inv, map_mul, hs, hs, inv_mul_cancel_left]
  have h1 := h γ γ.2 _ (e ▸ k.2) (s u)
  rw [mul_inv_cancel_left] at h1
  have h2 : ∀ u, ρ (s u)⁻¹ = 1 := fun u => by
    have := map_mul ρ (s u)⁻¹ (s u)
    rwa [inv_mul_cancel, map_one, hρ, mul_one, eq_comm] at this
  refine h1.trans ?_
  have h3 : ρ (((γ : B) * s u)⁻¹ * s (π γ * u * k))⁻¹ = ρ γ := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, map_mul, h2, hρ, one_mul, mul_one]
  rw [h3]
  congr 3
  exact Subtype.ext e

theorem form_law {f : Hf → W} (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : B} (hγ : γ ∈ Γ) (k : B)
    (hk : π k ∈ J) (x : B) :
    ρ (γ * x * k)⁻¹ (f (π (γ * x * k))) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (ρ x⁻¹ (f (π x))) := by
  have h : f (π γ * π x * π k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ γ (f (π x)) := hf ⟨γ, hγ⟩ (π x) ⟨π k, hk⟩
  rw [map_mul π, map_mul π, h, map_smul, ← rho_mul, ← rho_mul]
  congr 3
  group

theorem vec_law (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {a b : W} {z : ℂ} (hz : ‖z‖ = 1) (k : B)
    (h : ∀ w, inner ℂ a w = z⁻¹ * inner ℂ b (ρ k w)) : a = z • ρ k⁻¹ b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [h, inner_smul_left, ← hρ k (ρ k⁻¹ b), ← rho_mul, mul_inv_cancel, map_one, Complex.inv_eq_conj hz]
  rfl

theorem exists_dual [FiniteDimensional ℂ W] (u : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, inner ℂ a w = u w :=
  haveI := FiniteDimensional.complete ℂ W
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap u), fun _ => InnerProductSpace.toDual_symm_apply⟩

theorem exists_linear_section {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X → Y → Prop)
    (h0 : p 0 0) (hadd : ∀ x x' y y', p x y → p x' y' → p (x + x') (y + y')) (hsm : ∀ (a : ℂ) x y, p x y → p (a • x) (a • y))
    (hex : ∀ x, ∃ y, p x y) : ∃ th : X →ₗ[ℂ] Y, ∀ x, p x (th x) := by
  let S : Submodule ℂ (X × Y) :=
    { carrier := {z | p z.1 z.2}
      add_mem' := fun h h' => hadd _ _ _ _ h h'
      zero_mem' := h0
      smul_mem' := fun a _ h => hsm a _ _ h }
  obtain ⟨g, hg⟩ := (LinearMap.fst ℂ X Y ∘ₗ S.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => (hex x).elim fun y hy => ⟨⟨(x, y), hy⟩, rfl⟩)
  refine ⟨LinearMap.snd ℂ X Y ∘ₗ S.subtype ∘ₗ g, fun x => ?_⟩
  have h1 : p (g x).1.1 (g x).1.2 := (g x).2
  have h2 : (g x).1.1 = x := LinearMap.congr_fun hg x
  rwa [h2] at h1

theorem scalar_of_form {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥)
    (Λ : ℂ) (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') = Λ * inner ℂ y y') :
    ∀ y ∈ U, th (LinearMap.adjoint th y) = ((‖Λ‖ : ℝ) : ℂ) • y := by
  obtain ⟨y₀, hy₀, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have e := h y₀ hy₀ y₀
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have hn : ((‖y₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have e1 : Λ = ((‖LinearMap.adjoint th y₀‖ ^ 2 / ‖y₀‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hn)]
    exact e.symm
  have e2 : Λ = ((‖Λ‖ : ℝ) : ℂ) := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  intro y hy
  refine ext_inner_right ℂ fun y' => ?_
  rw [← LinearMap.adjoint_inner_right, h y hy, inner_smul_left, Complex.conj_ofReal, ← e2]

end Generic

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)


include hω hc hφ hinf hlev in
theorem kernel_law {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V) (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (x : GA D V)
    (g : GA D W) (w : c.W) :
    Datum.thetaKO ω (γ * x * k) g (φ w) = (Lev.levChi V β L k)⁻¹ * Datum.thetaKO ω x g (φ (c.ρ k w)) := by
  obtain ⟨κ, h1, h2⟩ := exists_finLift V ((finHom V).rangeRestrict k)
  have h3 : finHom V κ = finHom V k := congrArg Subtype.val h2
  have h4 : Lev.finE V κ = Lev.finE V k := by rw [Lev.finE_eq, Lev.finE_eq, h3]
  have h5 : κ⁻¹ * k ∈ GinfC V := by
    change finHom V (κ⁻¹ * k) = 1
    rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h6 : c.ρ (κ⁻¹ * k) = c.ρ k := by rw [map_mul, hc.1 _ (inv_mem h1), one_mul]
  have h7 : Lev.levChi V β L κ = Lev.levChi V β L k := by unfold Lev.levChi; rw [h4]
  have e : ((γ * x * k, g) : GA D V × GA D W) = (γ, 1) * ((x, g) * ((κ, 1) * (κ⁻¹ * k, 1))) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul, mul_inv_cancel_left, mul_assoc]
  unfold Datum.thetaKO
  rw [e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinf _ h5, h6,
    hlev κ ⟨h1, show Lev.finE V κ ∈ _ from h4 ▸ hk⟩, map_smul, map_smul, Pi.smul_apply, smul_eq_mul,
    hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ (hφ _)), h7]

theorem thetaKO_smul (h : GA D V) (g : GA D W) (a : ℂ) (f : Datum.WO V W → ℂ) :
    Datum.thetaKO ω h g (a • f) = a * Datum.thetaKO ω h g f := by
  unfold Datum.thetaKO
  rw [map_smul]
  rfl

theorem norm_levChi (k : GA D V) : ‖Lev.levChi V β L k‖ = 1 := norm_levFn _ _ _

theorem ext_law {x : Bridge.Gf V → c.W}
    (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V)
    (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (h : GA D V) :
    c.ext x (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (c.ext x h) :=
  form_law (finHom V).rangeRestrict (GQ V) c.ρ hx hγ k ((mem_grpOf V β L k).2 hk) h

theorem ext_finLift (hc : c.Is) (x : Bridge.Gf V → c.W) (u : Bridge.Gf V) : c.ext x (finLift V u) = x u := by
  change c.ρ (finLift V u)⁻¹ (x ((finHom V).rangeRestrict (finLift V u))) = x u
  rw [hc.1 _ (inv_mem (finLift_mem V u)), finLift_spec]
  rfl


include hω hc hφ hinf hlev in
theorem theta_classSum {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) (g : GA D W) :
    ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext x h)) ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (finLift V (y j)) g (φ (x (y j))) := by
  rw [integral_eq_classSum V β L hν hy]
  · simp only [ext_finLift c hc]
  · intro γ hγ k hk h
    rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, ext_law c β L hx hγ k hk, (c.ρ k).map_smul,
      rho_rho_inv c.ρ k, φ.map_smul, thetaKO_smul]
    exact inv_mul_cancel_left₀ (Lev.levChi_ne_zero L k) _


include hω hc hφ hinf hlev in
theorem exists_upVec (μ : Measure (GA D W)) (𝓖 : Set (GA D W)) (F : GA D W → ℂ)
    (hint : ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (F g)) 𝓖 μ) :
    ∃ Ψ : GA D V → c.W, (∀ h w, inner ℂ (Ψ h) w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F) ∧
      ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
        Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h) := by
  have h1 : ∀ h, ∃ a : c.W, ∀ w, inner ℂ a w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F := fun h =>
    exists_dual
      { toFun := fun w => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F
        map_add' := fun w w' => by
          unfold l2 Lift.pet
          rw [← integral_add (hint w h) (hint w' h)]
          simp only [Datum.thetaKO, map_add (f := _), Pi.add_apply, add_mul]
        map_smul' := fun a w => by
          unfold l2 Lift.pet
          simp only [Datum.thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
          exact integral_const_mul _ _ }
  choose Ψ hΨ using h1
  refine ⟨Ψ, hΨ, fun γ hγ k hk h => vec_law c.ρ hc.2.1 (norm_levChi β L k) k fun w => ?_⟩
  rw [hΨ, hΨ]
  unfold l2 Lift.pet
  rw [← integral_const_mul]
  congr 1
  funext g
  beta_reduce
  rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, mul_assoc]

end Kernel

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {X I : Type} [MeasurableSpace X] [Fintype I] (μ : Measure X) (𝓖 : Set X) (w : I → ℂ) (k : I → X → ℂ) (F T : X → ℂ)
    (hT : ∀ g, T g = ∑ j, w j * k j g) (hi : ∀ j, IntegrableOn (fun g => k j g * starRingEnd ℂ (F g)) 𝓖 μ) :
    l2 μ 𝓖 T F = ∑ j, w j * l2 μ 𝓖 (k j) F := by
  unfold l2 Lift.pet
  simp only [hT, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun j _ => (hi j).const_mul _]
  simp only [integral_const_mul]

theorem l2_eq_star {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓖 : Set X) (F T : X → ℂ) :
    l2 μ 𝓖 T F = ∫ g in 𝓖, star (F g) * T g ∂μ := by
  unfold l2 Lift.pet
  simp only [mul_comm]
  rfl

end GlobalTheory.AdelicScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
open MvPolynomial Filter

namespace GlobalTheory

namespace SatHilb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι K : Type*} [Field K]

end SatHilb

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_add_X_pow_mul {K : Type} [Field K] {N : ℕ} (j : Fin N) (m n : ℕ)
    (g : MvPolynomial (Fin N) K) :
    homogeneousComponent (n + m) (X j ^ m * g) = X j ^ m * homogeneousComponent n g := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]
  have hterm : ∀ i, homogeneousComponent (n + m) (X j ^ m * homogeneousComponent i g) =
      if n + m = m + i then X j ^ m * homogeneousComponent i g else 0 := fun i =>
    homogeneousComponent_of_mem
      (((isHomogeneous_X_pow j m).mul (homogeneousComponent_isHomogeneous i g)))
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp [add_comm]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [homogeneousComponent_eq_zero n g (by omega), mul_zero, ite_self]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma homogeneousComponent_mem_of_isPrime_of_X_pow_saturation {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q := by
  by_cases hX : ∀ j, X j ∈ Q
  · have hspan : Ideal.span (X '' Set.univ) ≤ Q := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact hX j
    intro g hg n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hsub : g - C (AddMonoidAlgebra.coeff g 0) ∈ Q := by
        apply hspan
        rw [mem_ideal_span_X_image]
        intro e he
        have he0 : e ≠ 0 := by
          rintro rfl
          simp at he
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
        exact ⟨i, Set.mem_univ _, hi⟩
      rw [homogeneousComponent_zero]
      have := Q.sub_mem hg hsub
      simpa using this
    · apply hspan
      rw [mem_ideal_span_X_image]
      intro e he
      rw [mem_support_iff, coeff_homogeneousComponent] at he
      have hdeg : e.degree = n := by
        by_contra hne
        exact he (if_neg hne)
      have he0 : e ≠ 0 := by
        rintro rfl
        simp at hdeg
        omega
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
  · push_neg at hX
    obtain ⟨j, hj⟩ := hX
    intro g hg n
    obtain ⟨m, hm⟩ := hs g hg j
    have hmem := hIQ (hI _ hm (n + m))
    rw [homogeneousComponent_add_X_pow_mul] at hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact absurd (hQ.mem_of_pow_mem m h) hj
    · exact h

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∃ L : ℕ, ∀ n ≥ L, ∀ h ∈ Q, h ∈ homogeneousSubmodule (Fin N) K n → h ∈ I := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian Q : Q.FG)
  choose! mexp hmexp using hs
  set M := G.sup fun g => Finset.univ.sup (mexp g)
  set D := G.sup totalDegree
  set B := N * M + 1
  have hkey : ∀ g ∈ G, ∀ e : Fin N →₀ ℕ, B ≤ (e.sum fun _ k => k) → ∀ a : K,
      monomial e a * g ∈ I := by
    intro g hgG e he a
    have hgQ : g ∈ Q := hG ▸ Submodule.subset_span hgG
    have hj : ∃ j, M ≤ e j := by
      by_contra hne
      push_neg at hne
      have hsum : (e.sum fun _ k => k) ≤ N * M := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        calc ∑ j, e j ≤ ∑ _j : Fin N, M := Finset.sum_le_sum fun j _ => (hne j).le
          _ = N * M := by simp
      omega
    obtain ⟨j, hjM⟩ := hj
    have hle : mexp g j ≤ e j :=
      le_trans (le_trans (Finset.le_sup (f := mexp g) (Finset.mem_univ j))
        (Finset.le_sup (f := fun g => Finset.univ.sup (mexp g)) hgG)) hjM
    have hsingle : Finsupp.single j (mexp g j) ≤ e := by
      rw [Finsupp.single_le_iff]
      exact hle
    have hsplit : monomial e a =
        monomial (e - Finsupp.single j (mexp g j)) a * X j ^ mexp g j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hsingle]
    rw [hsplit, mul_assoc]
    exact I.mul_mem_left _ (hmexp g hgQ j)
  refine ⟨B + D, fun n hn h hQ hh => ?_⟩
  have hhn : h = homogeneousComponent n h := by
    rw [homogeneousComponent_of_mem hh, if_pos rfl]
  rw [← hG] at hQ
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hQ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hhn, ← hf, map_sum]
  refine I.sum_mem fun g hgG => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smul_eq_mul, as_sum (f g), Finset.sum_mul, map_sum]
  refine I.sum_mem fun e _ => ?_
  by_cases hdeg : B ≤ (e.sum fun _ k => k)
  · exact hI _ (hkey g hgG e hdeg _) n
  · rw [homogeneousComponent_eq_zero]
    · exact I.zero_mem
    · have h1 := totalDegree_mul (monomial e (AddMonoidAlgebra.coeff (f g) e)) g
      have h2 := totalDegree_monomial_le e (AddMonoidAlgebra.coeff (f g) e)
      have h3 : g.totalDegree ≤ D := Finset.le_sup (f := totalDegree) hgG
      have h4 : (e.sum fun _ => id) = (e.sum fun _ k => k) := rfl
      omega

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma coe_decompose_homogeneousSubmodule_eq_homogeneousComponent {K : Type} [Field K] {N : ℕ}
    (g : MvPolynomial (Fin N) K) (n : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K)) =
      homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single n]
  · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
  · intro i _ hi
    exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g),
      homogeneousComponent_eq_zero n g (by omega)]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma isHomogeneous_of_forall_homogeneousComponent_mem {K : Type} [Field K] {N : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) I := by
  intro n g hg
  rw [coe_decompose_homogeneousSubmodule_eq_homogeneousComponent]
  exact hI g hg n


open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq (K : Type) [Field K] (N : ℕ)
    (I Q : Ideal (MvPolynomial (Fin N) K))
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧
      _root_.GlobalTheory.idealHilbertPoly Q = _root_.GlobalTheory.idealHilbertPoly I := by
  have hQh := homogeneousComponent_mem_of_isPrime_of_X_pow_saturation hI hQ hIQ hs
  refine ⟨hQh, ?_⟩
  obtain ⟨L, hL⟩ := exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous hI hs
  have hIh := isHomogeneous_of_forall_homogeneousComponent_mem hI
  have hQh' := isHomogeneous_of_forall_homogeneousComponent_mem hQh
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (((_root_.GlobalTheory.eventually_finrank_quotPiece hQh').and
      (_root_.GlobalTheory.eventually_finrank_quotPiece hIh)).and (eventually_ge_atTop L))
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n0 + n : ℕ) : ℚ))
    (fun a b hab => by simpa using hab) fun n => ?_
  obtain ⟨⟨hq, hi⟩, hLn⟩ := hn0 (n0 + n) (by omega)
  show Polynomial.eval _ _ = Polynomial.eval _ _
  rw [← hq, ← hi]
  have hint : Submodule.restrictScalars K Q ⊓ homogeneousSubmodule (Fin N) K (n0 + n) =
      Submodule.restrictScalars K I ⊓ homogeneousSubmodule (Fin N) K (n0 + n) := by
    apply le_antisymm
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hL (n0 + n) hLn h hh.1 hh.2, hh.2⟩
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hIQ hh.1, hh.2⟩
  have e1 := _root_.GlobalTheory.finrank_quotPiece_add Q (n0 + n)
  have e2 := _root_.GlobalTheory.finrank_quotPiece_add I (n0 + n)
  rw [hint] at e1
  congr 1
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturationStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation : ∀ (K : Type) [Field K] (N : ℕ) (I Q : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → Q.IsPrime → I ≤ Q → (∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) → (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧ GlobalTheory.idealHilbertPoly Q = GlobalTheory.idealHilbertPoly I := by
  first | exact @GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | exact GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | (intros; apply GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq <;> assumption)
end
end
