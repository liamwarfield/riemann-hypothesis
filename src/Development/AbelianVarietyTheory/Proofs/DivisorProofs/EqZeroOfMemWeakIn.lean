module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspQuot

section Test

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set V} {α : V → ℂ}

def IsTest (U : Set V) (α : V → ℂ) : Prop := ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U

theorem IsTest.continuous_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Continuous fun x => α x * G x :=
  continuous_of_tsupport fun x hx => h.1.continuous.continuousAt.mul
    (hG.continuousAt (hU.mem_nhds (h.2.2 (tsupport_mul_subset_left hx))))

theorem IsTest.add {β : V → ℂ} (h : IsTest U α) (h' : IsTest U β) : IsTest U (α + β) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, (tsupport_add α β).trans (Set.union_subset h.2.2 h'.2.2)⟩

theorem IsTest.mul (h : IsTest U α) {β : V → ℂ} (hβ : ContDiff ℝ ∞ β) : IsTest U fun x => α x * β x :=
  ⟨h.1.mul hβ, h.2.1.mul_right, tsupport_mul_subset_left.trans h.2.2⟩

theorem IsTest.fderiv (h : IsTest U α) (v : V) : IsTest U fun x => fderiv ℝ α x v :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem isTest_zero : IsTest U (0 : V → ℂ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

theorem IsTest.integrable_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Integrable (fun x => α x * G x) ν :=
  (h.continuous_mul hU hG).integrable_of_hasCompactSupport h.2.1.mul_right

end Test

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (φ : GA E a → ℂ) (x : GA E a) : ℂ :=
  ∫ y, α y * chart φ x y ∂ν

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]


variable {μ} [μ.IsMulRightInvariant] {S : Submodule ℂ (L2 (latticeGL E a) μ)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin a) (Cinf E) → Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact Units.isOpenEmbedding_val
end

theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Continuous fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 := by
  refine continuous_of_tsupport fun p hp => (hα.1.continuous.comp continuous_snd).continuousAt.mul ?_
  have h1 : p.2 ∈ tsupport α := by
    refine (closure_minimal (fun q hq => ?_) ((isClosed_tsupport α).preimage continuous_snd) :
      _ ⊆ Prod.snd ⁻¹' tsupport α) hp
    exact subset_tsupport _ (left_ne_zero_of_mul hq)
  obtain ⟨x, y⟩ := p
  obtain ⟨u, hu⟩ := hα.2.2 h1
  obtain rfl : y = toL u.val := hu.symm
  have he : IsOpenEmbedding (Prod.map id fun u : GL (Fin a) (Cinf E) => toL u.val : GA E a × _ → GA E a × Lie E a) :=
    IsOpenEmbedding.id.prodMap isOpenEmbedding_val
  refine (he.continuousAt_iff (x := (x, u))).1 (Continuous.continuousAt ?_)
  exact (hφ.comp (continuous_fst.mul (continuous_infGL.comp continuous_snd))).congr fun q => (chart_val φ q.1 q.2).symm

theorem norm_chart_le {φ : GA E a → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (x : GA E a) (y : Lie E a) : ‖chart φ x y‖ ≤ C := by
  unfold chart
  split_ifs
  · exact hC _
  · exact norm_zero.trans_le ((norm_nonneg _).trans (hC 1))

theorem continuous_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    Continuous (smoothing ν α φ) :=
  continuous_of_dominated (bound := fun y => ‖α y‖ * C)
    (fun x => ((continuous_integrand hα hφ).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun x => .of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC x y) (norm_nonneg _)))
    ((hα.1.continuous.integrable_of_hasCompactSupport hα.2.1).norm.mul_const C)
    (.of_forall fun y => (continuous_integrand hα hφ).comp (Continuous.prodMk_left y))

variable [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)]


omit [μ.IsMulRightInvariant] in
theorem memL2_of_bound {φ : GA E a → ℂ} (hφ : Continuous φ) (hl : LeftInv (latticeGL E a) φ) {C : ℝ}
    (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ :=
  ⟨hl, MemLp.of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (by
    rw [hl.lift_descend]; exact hφ.aestronglyMeasurable)) C (.of_forall fun q => hC _)⟩


end GlobalTheory.CuspQuot

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {B N P : LB X}

theorem IsNef.topSelf_le_of_cls_eq_add (h : Published.NefProductNonneg)
    (hp : IsProjOver (strHom k (X := X))) {D : ℕ} (hD : topologicalKrullDim X = D)
    (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : topSelfIntersection k B D ≤ topSelfIntersection k P D := by
  classical
  have hf := algebraMap_eq_strHom k X
  have hS : QCoh.suppDim (structureModule X) ≤ D := by
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le X _).trans hD.le
  have hV := diffVanish_chiPic_of_isProjOver hf (structureModule X) hp hS
  have hL : ∀ j : Fin 2, ((![B, N] : Fin 2 → LB X) j).IsLB := by
    intro j; fin_cases j
    · exact hB.isLB
    · exact hN.isLB
  have hQ : ∀ _ : Fin D, P.IsLB := fun _ => hP
  have hexp := hV.interNum_of_cls_eq_sum hL hQ (fun _ _ => (1 : ℤ)) (by
    intro _
    simp [Fin.sum_univ_two, e])
  have hnn : ∀ a : Fin D → Fin 2, 0 ≤ interNum k (structureModule X) ((![B, N] : Fin 2 → LB X) ∘ a) := by
    intro a
    refine h.interNum_nonneg hp hD ?_
    intro i
    show IsNef k (![B, N] (a i))
    generalize a i = j
    fin_cases j
    · exact hB
    · exact hN
  rw [topSelf_def, topSelf_def, hexp]
  simp only [Finset.prod_const_one, one_mul]
  have h0 := Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_univ (fun _ : Fin D => (0 : Fin 2)))
  exact h0

theorem IsBig.of_cls_eq_add_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : IsBig k P := by
  obtain ⟨D, hD, -⟩ := hb.growth
  have hf := algebraMap_eq_strHom k X
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  have hTn : IsNef k (CechPic.tens B N) := IsNef.tens_of_isProjOver hB hN hp
  have hPn : IsNef k P := hTn.of_cls_eq hP (by rw [e, CechPic.cls_tens hB.isLB hN.isLB])
  have hle := IsNef.topSelf_le_of_cls_eq_add h.1 hp hD hB hN hP e
  have hpos : 0 < topSelfIntersection k B D := (h.2.2.isBig_iff hp hD hB).1 hb
  exact (h.2.2.isBig_iff hp hD hPn).2 (lt_of_lt_of_le hpos hle)

theorem IsBig.tens_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) : IsBig k (CechPic.tens B N) := by
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  exact IsBig.of_cls_eq_add_nef h hp hb hB hN hT (CechPic.cls_tens hB.isLB hN.isLB hT)

theorem IsNef.isBig_tens_ample [IsIntegral X] (h : Published.NefNumerics)
    (hp : IsProjOver (strHom k (X := X))) (hN : IsNef k N) (hB : IsAmpleLB B) :
    IsBig k (CechPic.tens N B) := by
  have hT : (CechPic.tens N B).IsLB := CechPic.isLB_tens hN.isLB hB.isLB
  have hbig : IsBig k B := IsAmpleLB.isBig k X hp B hB
  exact IsBig.of_cls_eq_add_nef h hp hbig hB.isNef hN hT
    (by rw [CechPic.cls_tens hN.isLB hB.isLB hT, add_comm])

theorem IsNef.isPsEff : Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ N : LB X, IsNef k N → IsPsEff N := by
  intro h k _ X _ _ hp N hN
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  refine ⟨hN.isLB, A, hA, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow N m) := hN.pow hA m
  have hbig : IsBig k (CechPic.tens (lbPow N m) A) := IsNef.isBig_tens_ample h hp hNm hA
  obtain ⟨r, hr, hs⟩ := (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
  exact ⟨r, hs, hr⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRelDim

theorem exists_relDim : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro K _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim K A hA

end GlobalTheory.AbVarRelDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relativeDimension_abelianVariety_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.AbVarRelDim.exists_relDim | exact GlobalTheory.AbVarRelDim.exists_relDim | (intros; apply GlobalTheory.AbVarRelDim.exists_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
namespace GlobalTheory

theorem bernsteinZelevinskyFiniteness_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

namespace Pair

theorem unitAt_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    {x : X} {c i : M.B.ι} (hc : x ∈ M.B.U c) (hi : x ∈ M.B.U i) :
    UnitAt x ((ρ c : X.functionField) / (ρ i : X.functionField)) := by
  have hx : x ∈ M.B.U c ⊓ M.B.U i := ⟨hc, hi⟩
  rw [hρ c i (gen_mem hx), mul_div_cancel_right₀ _ (ρ i).ne_zero]
  exact unitAt_fnOf hx _ _

theorem log_norm_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    (σ : k →+* ℂ) {y : CxPts p σ} {c i : M.B.ι} (hc : y ∈ ptsIn p σ (M.B.U c))
    (hi : y ∈ ptsIn p σ (M.B.U i)) :
    Real.log ‖ratVal ((ρ c : X.functionField) / (ρ i : X.functionField)) y‖ - (M.φ σ).φ c y / 2 = -((M.φ σ).φ i y) / 2 := by
  have hy := mem_ptsIn_inf.2 ⟨hc, hi⟩
  rw [hρ c i (gen_mem (mem_ptsIn.1 hy)), mul_div_cancel_right₀ _ (ρ i).ne_zero, ratVal_fnOf hy,
    (M.φ σ).trans c i y hc hi, Real.log_pow]
  simp only [GlobalTheory.CxPts.gv]
  push_cast
  ring

end Pair

theorem Pair.rep_base (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (P : Pair p) : P.Rep 1 0 P.L ∧ P.Rep 0 1 P.A ∧ P.Rep 0 0 (HermLB.triv p) := by
  refine ⟨⟨P.r, P.hr, fun x c i j hc hi _ => ?_, fun σ y c i j hc hi _ => ?_⟩,
    ⟨P.r', P.hr', fun x c i j hc _ hj => ?_, fun σ y c i j hc _ hj => ?_⟩,
    ⟨fun _ => 1, presents_zero.isRatSec, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩⟩
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.L P.hr hc hi
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.L P.hr σ hc hi]
    push_cast
    ring
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.A P.hr' hc hj
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.A P.hr' σ hc hj]
    push_cast
    ring
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    rw [e, Units.val_one, div_one]
    exact unitAt_one x
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    have hv := ratVal_fnOf (y := y) mem_ptsIn_top trivial (1 : Γ(X, ⊤))
    rw [map_one, ev_one mem_ptsIn_top] at hv
    rw [e, Units.val_one, div_one, hv]
    simp [HermLB.triv, Weight.ofFun]

end GlobalTheory.VolBr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.represents_base_bundles_and_trivial : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), P.Rep 1 0 P.L ∧ P.Rep 0 1 P.A ∧ P.Rep 0 0 (HermLB.triv p) := by
  first | exact @GlobalTheory.VolBr.Pair.rep_base | exact GlobalTheory.VolBr.Pair.rep_base | (intros; apply GlobalTheory.VolBr.Pair.rep_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagTan GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

private theorem evR_eq_zero_of_genVal_eq_zero {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) {L : Type} [Field L] [Algebra c.F L] (z : FrPt Xo c L) :
    evR Xo c g z = 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    obtain ⟨C, ψ, z0, t', hψ, hb⟩ := hA hG L z
    rw [evR_frBor hg hb]
    have hnat := (mem_secZ.mp hg).1
    obtain ⟨p, φ0, u, hu⟩ := hL.test C.R C.y
    have e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))
    have e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))
    have e3 := evR_frBor hg C.bor
    have e4 : evR Xo c g (genFr hG C.Z) = 0 := by
      have h1 := h0 C.Z
      rw [genVal_apply hG] at h1
      exact h1
    rw [e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val] at e3
    have e5 : φ0 (g p u) = 0 := Subtype.ext e3
    rw [e1, AlgHom.comp_apply, e5, map_zero, mul_zero]

theorem secZ_eq_zero_of_genVal {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) : g = 0 :=by
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u := Ideal.Quotient.mk_surjective _
  show g p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := by
    first
    | exact IsJacobsonRing.out' _ p.rad
    | exact IsJacobsonRing.out inferInstance p.rad
    | exact Ideal.IsJacobson.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m := Ideal.Quotient.factorₐ c.F hIm
  obtain ⟨z, hz⟩ := exists_frMap φ u
  have h1 := evR_eq (mem_secZ.mp hg).1 hz
  rw [evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha] at h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h1.symm

theorem genVal_eq_zero_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Z : Comp Xo c) (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, genVal Z f = 0 ↔ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c f y = 0 :=by
  intro E _ _ _ H Dw l Xo c Z e f hf
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  constructor
  · intro h0 S _ _ y hy
    by_cases ht : Tested y
    · have hz : idem Z * f = 0 := by
        refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)
        by_cases hZ : Z' = Z
        · subst hZ
          rw [map_mul, h0, mul_zero]
        · rw [genVal_apply hG]
          exact evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))
      have h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y := evalAt_mul _ _ _ _ y
      rw [hz, evR_idem hy ht, one_mul] at h1
      rw [← h1]
      exact evalAt_zero _ _ y
    · unfold evR evalAt
      rw [dite_eq_right ht]
  · intro hall
    rw [genVal_apply hG]
    exact hall _ _ (liesOn_genFr hG Z)

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_one' {σ : k →+* ℂ} (y : CxPts p σ) : ratVal (1 : X.functionField) y = 1 := by
  have h1 := (unitAt_one (under y)).regAt
  have e := ratVal_mul (y := y) h1 h1
  rw [mul_one] at e
  have h0 := ratVal_ne_zero (y := y) (unitAt_one (under y))
  exact (mul_eq_left₀ h0).1 e.symm

theorem unitAt_pow' {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => simpa using unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem ratVal_pow' {σ : k →+* ℂ} {y : CxPts p σ} {f : X.functionField} (h : UnitAt (under y) f)
    (n : ℕ) : ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero => simpa using ratVal_one' y
  | succ n ih =>
    rw [pow_succ, ratVal_mul (unitAt_pow' h n).regAt h.regAt, ih, pow_succ]

theorem loc_mul (P : Pair p) (a b : ℤ) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc ((n : ℤ) * a) ((n : ℤ) * b) 1 i j = P.loc a b 1 i j ^ n := by
  simp only [loc, one_mul, mul_pow, mul_comm (n : ℤ), zpow_mul, zpow_natCast]

end GlobalTheory.VolBr.Pair

theorem GlobalTheory.VolBr.Pair.rep_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (n : ℕ), P.Rep a b M → P.Rep (n * a) (n * b) (M.pow n) := by
  intro k _ X _ p P a b M n ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => ρ (c PUnit.unit) ^ n, ?_, ?_, ?_⟩
  · intro j j' h
    have h' : genericPoint X ∈ M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit) :=
      ⟨Set.mem_iInter.1 h.1 PUnit.unit, Set.mem_iInter.1 h.2 PUnit.unit⟩
    have e : (M.pow n).B.g j j' = res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) := by
      change ∏ _k : PUnit, _ = _
      exact Fintype.prod_unique _
    rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hρ _ _ h', mul_pow]
    congr 1
    rw [show ((res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) : (Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j'))ˣ) :
          Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j')) =
        ((res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) : (Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j'))ˣ) :
          Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j')) ^ n by
        rw [zpow_natCast, Units.val_pow_eq_pow_val], map_pow]
    congr 1
    exact (fnOf_resG (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩ :
      (M.pow n).B.U j ⊓ (M.pow n).B.U j' ≤ M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit)) h _).symm
  · intro x c i j hc hi hj
    rw [Pair.loc_mul, Units.val_pow_eq_pow_val, ← div_pow]
    exact Pair.unitAt_pow' (hu x (c PUnit.unit) i j (Set.mem_iInter.1 hc PUnit.unit) hi hj) n
  · intro σ y c i j hc hi hj
    have hc' := mem_pow_iff.1 hc
    have hU := hu _ (c PUnit.unit) i j (mem_ptsIn.1 hc') (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y (c PUnit.unit) i j hc' hi hj
    rw [Pair.loc_mul, Units.val_pow_eq_pow_val, ← div_pow, Pair.ratVal_pow' hU, norm_pow,
      Real.log_pow]
    change _ - ((M.φ σ).zpow n).φ c y / 2 = _
    rw [show ((M.φ σ).zpow n).φ c y = (n : ℤ) * (M.φ σ).φ (c PUnit.unit) y from Weight.zpow_φ _ _ _ _]
    push_cast
    linear_combination (n : ℝ) * e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.represents_hermitianLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (n : ℕ), P.Rep a b M → P.Rep (n * a) (n * b) (M.pow n) := by
  first | exact @GlobalTheory.VolBr.Pair.rep_pow | exact GlobalTheory.VolBr.Pair.rep_pow | (intros; apply GlobalTheory.VolBr.Pair.rep_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inv_neg_mat {k : Type} [Fintype k] [DecidableEq k] {R : Type} [CommRing R] (A : Matrix k k R) :
    (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · have e : ((-1 : Rˣ) • A) = -A := by simp
    rw [← e, Matrix.inv_smul' (A := A) (k := (-1 : Rˣ)) h]
    simp
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      apply h
      have : IsUnit ((-1 : R) ^ Fintype.card k) := (isUnit_neg_one (α := R)).pow _
      exact (IsUnit.mul_iff.1 hu).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplOH_negSp (S T : HSp D) (x y : WO S T) :
    symplOH (negSp S) T x y = -symplOH S T x y := by
  have h : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplOH symplO
  rw [h, mul_neg, map_neg, mul_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp [Complex.star_def]

theorem heisO_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w₀ : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ (negSp S) T w₀ (fun w => star (g w)) = fun w => star (heisO ψ S T w₀ g w) := by
  funext w
  unfold heisO
  rw [star_mul, symplOH_negSp, ← star_psi hψ]
  ring

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-y) = -(lineAt θ τ y) := by
  have h := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ y
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-y) _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (-y)) ?_
  refine ⟨h.1.neg, fun t => ?_, fun t τ' => ?_⟩
  · have h2 := h.2.1 t
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.zero_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg, this,
      neg_zero]
  · have h3 := h.2.2 t τ'
    have e : compAt θ τ' ((-(lineAt θ τ y)) t) = -compAt θ τ' (lineAt θ τ y t) := by
      ext i j
      simp only [compAt, Matrix.map_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg]
    rw [e, h3]
    split_ifs <;> simp

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) (h : Mx D m n → ℂ) :
    Formalism.IndefR.Datum.dRho hs θ τ (-y) h = -Formalism.IndefR.Datum.dRho hs θ τ y h := by
  funext x
  have e : (fun t : ℝ => hs (lineAt θ τ (-y) t) h x) = fun t => (fun s : ℝ => hs (lineAt θ τ y s) h x) (-t) := by
    funext t
    rw [lineAt_neg hθ, AddMonoidHom.neg_apply, ← map_neg]
  simp only [Formalism.IndefR.Datum.dRho, Pi.neg_apply]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => hs (lineAt θ τ y s) h x) (x := 0)).trans (by rw [neg_zero])

theorem dRho_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z (fun w => star (g w)) = fun w => star (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g w) := by
  funext x
  simp only [Formalism.IndefR.Datum.dRho]
  have e : (fun t : ℝ => heisO ψ (negSp S) T (lineAt θ τ z t) (fun w => star (g w)) x) =
      fun t => star (heisO ψ S T (lineAt θ τ z t) g x) := by
    funext t
    rw [heisO_negSp_star hψ]
  rw [e, deriv.star]

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem aPlus_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    aPlus (heisO ψ (negSp S) T) θ τ (cplxO (-sS) sT) u (fun w => star (g w)) =
      fun w => star (aPlus (heisO ψ S T) θ τ (cplxO sS sT) u g w) := by
  funext w
  simp only [aPlus, crea, cplxO_neg, dRho_neg hθ, dRho_negSp_star hψ]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul, star_mul, star_sub, Complex.star_def, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  ring

theorem foldr_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (L : List (FVar D T.rank S.rank)) (g : WO S T → ℂ) :
    L.foldr (fun i h => aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT i h)
        (fun w => star (g w)) =
      fun w => star (L.foldr (fun i h => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i h) g w) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact aPlus_negSp_star hψ hθ S T a.1 (sS a.1) (sT a.1) _ _

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  intro D ψ θ S T sS sT BS BT f hψ hθ k x
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have h1 : pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h2 : pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k (fun w => starRingEnd ℂ (f w)) := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k
        (fun w => starRingEnd ℂ (f w))) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  rw [h1, h2, opPow, opPow]
  have hf : f = fun w => star (starRingEnd ℂ (f w)) := by
    funext w
    simp
  conv_lhs => rw [hf]
  rw [foldr_negSp_star hn hθ S T sS sT BS BT]
  rfl

end GlobalTheory.FockConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  first | exact @GlobalTheory.FockConj.pureTensorO_negSp_monomial | exact GlobalTheory.FockConj.pureTensorO_negSp_monomial | (intros; apply GlobalTheory.FockConj.pureTensorO_negSp_monomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuMul

theorem loc_mul {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b a' b' : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') (f * g) i j = P.loc a b f i j * P.loc a' b' g i j := by
  have h1 : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h2 : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [Pair.loc, zpow_add₀ h1, zpow_add₀ h2]
  ring

theorem mul_mem_H_and_nu_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  intro k _ X _ p P a b a' b' f g hf hg
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_mul]
    exact (hf x i j hi hj).mul (hg x i j hi hj)
  · have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    simp only [Pair.nu]
    rw [loc_mul, ratVal_mul (hf _ _ _ hi hj) (hg _ _ _ hi hj), norm_mul]
    have e : -(((a + a' : ℤ) : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + ((b + b' : ℤ) : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
      = -((a : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
        + -((a' : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b' : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 := by
      push_cast; ring
    rw [e, Real.exp_add]
    ring

end GlobalTheory.VolBr.NuMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  first | exact @GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | exact GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul | (intros; apply GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
noncomputable section

open MeasureTheory Formalism.UG

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cornerU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : L :=
  ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev

def depthU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : ℕ :=
  (-ordL (cornerU k u)).toNat

def shellU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℤ) : Set (cellU y) :=
  {u | Valued.v (cornerU k (u : GU σ n)) ≤ WithZero.exp j}

theorem mem_shellU_iff_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℕ) (u : cellU y) :
    u ∈ shellU k y j ↔ depthU k (u : GU σ n) ≤ j := by
  unfold shellU depthU
  simp only [Set.mem_setOf_eq]
  by_cases h0 : cornerU k (u : GU σ n) = 0
  · rw [h0]; simp [ordL]
  · rw [GlobalTheory.BorelUMod.v_eq_exp h0, WithZero.exp_le_exp]
    omega

theorem mem_shellU_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (u : cellU y) :
    u ∈ shellU k y (depthU k (u : GU σ n)) :=
  (mem_shellU_iff_depth k y _ u).2 le_rfl

theorem shellU_mono {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) {j j' : ℤ} (h : j ≤ j') :
    shellU k y j ⊆ shellU k y j' :=
  fun _ hu => le_trans hu (WithZero.exp_le_exp.2 h)

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockPos

variable {D : D7}

def frAt {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  fr.1.map (tauE D τ)

def zCo (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ

def gaussO (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ))

theorem cartan_eq_one {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) (hG : G.PosDef) : s = 1 := by
  obtain ⟨hss, -, hP⟩ := h
  have key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hx
    set x := (s - 1) *ᵥ v with hxdef
    have hsx : s *ᵥ x = -x := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]
    have h1 := hP.dotProduct_mulVec_pos hx
    have h2 := hG.dotProduct_mulVec_pos hx
    rw [← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg] at h1
    have := add_pos h1 h2
    simp at this
  have : s - 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

theorem frAt_det_ne {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : (frAt fr τ).det ≠ 0 := by
  have e : (frAt fr τ).det = tauE D τ fr.1.det := (RingHom.map_det (tauE D τ) fr.1).symm
  rw [e, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero

theorem frAt_on {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ = 1 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h2 := congrArg (fun M => M.map (tauE D τ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2, frAt, gramAt]
  congr 2
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  exact (hs _).symm

theorem gramAt_posDef {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (gramAt D S τ).PosDef := by
  have hMd : IsUnit (frAt fr τ).det := isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hM : IsUnit (frAt fr τ) := (Matrix.isUnit_iff_isUnit_det _).2 hMd
  have hMHd : IsUnit (frAt fr τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hMd.star
  have h1 := frAt_on fr h τ
  have e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ := by
    calc ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹
        = ((frAt fr τ)ᴴ)⁻¹ * ((frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ) * (frAt fr τ)⁻¹ := by
          rw [h1, Matrix.conjTranspose_nonsing_inv]
      _ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramAt D S τ := by
          rw [Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]
  rw [← e]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)

theorem cart_one {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1)
    {s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) : s = fun _ => 1 := by
  funext τ
  have h1 : (gramAt D S τ).PosDef := gramAt_posDef fr h τ
  exact cartan_eq_one (hs τ) h1

end GlobalTheory.FockPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleGL
theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end
