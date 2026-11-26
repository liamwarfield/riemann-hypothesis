module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySeventh
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
public import Development.DiscreteGroups.GlobalIrreducibility.LConvFinal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem laHyp_eSmooth_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
      I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  intro B X I h _ l Z a u i _
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hs := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hL := Formalism.L2.Ker.laHyp_ambOf_top (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
    hs hδ (he i) (he (i + 1)) ∅ (fun P hP => absurd hP (Finset.notMem_empty P)) (fun P hP => absurd hP (Finset.notMem_empty P))
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hE := Formalism.L2.Ker.Cd.ambOf_eSmooth (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar
    I.chi I.J.cD hs hcc hδ I.J.δ_ne_zero (he i) (he (i + 1))
  rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  exact ⟨⟨hL.1, hL.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
    (bad P hP).2.2.1 (by simp), hL.2.2.2.2⟩, hE⟩

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmoothStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | exact GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | (intros; apply GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypic
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.IsotSum


set_option maxHeartbeats 2000000 in
theorem span_all : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m), (⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) = ⊤ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    have hn : (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) *
        (((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) false)).ne', Complex.ofReal_one]
    have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.toRealDat.hv0
    have h1 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        ∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
      rfl
    apply_fun (Tw.out (s := twAt D.what₂.embLL A3.A.v0))
    case inj =>
      intro a b h
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) h
    rw [h1]
    change Tw.out (∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k)) = _
    change (∑ k, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) (A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k))) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding (y k)) •
      ((((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) •
        (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k))) = _
    rw [smul_smul (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)), hn, one_smul, R.toRealDat.emb0, cj_cj]
    congr 1
    exact (DFunLike.congr_fun hs (y k)).symm
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i

  have hUT : ∀ p, Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) =
      (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
    intro p
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy, LinearMap.mem_range_self _ _⟩
    · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
        hR.liftHyp0.h3W hR.partsW i p]
      exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw (Submodule.span ℂ
        ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))) ((R.toCx3 F).WpK false i p)
        (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
  let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
    { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
      map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
      map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
  set S : Submodule ℂ (D.what₂.Mj ((i : ℕ) + 1)) :=
    ⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) with hS

  have h5 : ∀ p, (Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))).map outL ≤
      S.map (Y.mj.eW i) := by
    intro p
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_map.2 ⟨Z.jW i y, ?_, ?_⟩
    · exact (le_iSup (fun p => Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) p)
        (Submodule.subset_span ⟨y, hy, rfl⟩)
    · show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
  rw [eq_top_iff]
  intro x _
  have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hR.partsW i).2] at h1
  have h4 : Y.mj.eW i x ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL :=
    Submodule.mem_map_of_mem (f := outL) h1
  rw [Submodule.map_iSup] at h4
  have h6 : (⨆ p, ((R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL) ≤ S.map (Y.mj.eW i) :=
    iSup_le fun p => (hUT p) ▸ h5 p
  obtain ⟨x', hx', hxx⟩ := h6 h4
  rw [← hinj hxx]
  exact hx'

end GlobalTheory.IsotSum

namespace GlobalTheory.IsotSum


set_option maxHeartbeats 1000000 in
theorem isotInternal_of_read : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hRk
  obtain ⟨cOf, h1, -, -⟩ := GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost hRk
  show Rows.IsotInternal D.what₂
  intro j hj1 hjm
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i
  · rw [eq_top_iff, ← span_all hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i]
    refine iSup_le fun c => ?_
    rw [← (h1 i c).2]
    exact iSup_le fun σ => le_iSup (fun σ => D.what₂.isot ((i : ℕ) + 1) σ) σ.1

end GlobalTheory.IsotSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypicStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_forms_internal_direct_sum_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  first | exact @GlobalTheory.IsotSum.isotInternal_of_read | exact GlobalTheory.IsotSum.isotInternal_of_read | (intros; apply GlobalTheory.IsotSum.isotInternal_of_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckePowOne
noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

end GlobalTheory.WeightTwoHeckePower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwist
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedFirst

theorem single_linked_single_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (he : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst he
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem unlinked_first_of_len_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc c Δ hlen hun
  obtain ⟨a, ha, L⟩ := hrc
  intro y hy z hz hyz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  have hne : (Δ j).first ≠ (Δ j).first.nu 1 := by
    intro e0
    refine GlobalTheory.UnlinkedMono.lpTw_one_ne (rc (Δ j).first) (by rw [L.dim]; exact (Δ j).isCusp_first.1) ?_
    calc (rc (Δ j).first).lpTw 1 = rc ((Δ j).first.nu ((1 : ℝ) : ℂ)) := (L.nu _ 1).symm
      _ = rc (Δ j).first := by rw [Complex.ofReal_one, ← e0]
  have eΔ : ∀ k, Δ k = Segment.single (Δ k).first (Δ k).isCusp_first := fun k =>
    Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, hlen k])
  by_cases hij : j = i
  · subst hij; exact hne hyz
  exact hun j i hij (by
    rw [eΔ j, eΔ i]
    exact single_linked_single_nu (Δ j).isCusp_first (Δ i).isCusp_first hne hyz)

end GlobalTheory.UnlinkedFirst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwistStatement
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinkedLengthOneSegments_firstTerms_not_nuTwist : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  first | (exact @GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (exact GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (intros; apply GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Holds7SizeAway
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut7.SizeAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}


open GlobalTheory.ResW in
theorem isUnitarisable (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ha : 1 ≤ a)
    (π : CuspSub E a) (wt : ℤ) (hw : IsWeight π wt) (w : HeightOneSpectrum (𝓞 E)) (σ) (hσ : π.IsLocComp w σ) :
    GlobalTheory.SmGL.IsUnitarisable ((algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ)).rep := by
  set t : ℝ := ((a : ℝ) - 1 - wt) / 2 with ht
  have hr := GlobalTheory.UnitLocWeight.rexp_eq ha hw
  have hu : (π.twist (nu E (-t))).IsUnitary := by
    have e := (letter_centralExponent E ⟨a, π⟩).2.2.1 ha (-t)
    refine ((rexp_eq_zero_iff_isUnitary E (tw ⟨a, π⟩ (-t)) ha).1.1 ?_)
    rw [e, hr]; ring
  have hU := isUnitarisable_of_isLocComp_cusp E a _ ha hu w _ (hσ.twist (nu E (-t)))
  have hloc : (nu E (-t)).loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ) :=
    GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-t)) w
  set σ' := σ.twist (CuspSub.locDet a (nu E (-t)) w) (CuspSub.isOpen_ker_locDet (nu E (-t)) w) with hσ'
  have key : (algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ) = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
    have e1 : (((1 - (a : ℝ)) / 2 : ℝ) : ℂ) + (((wt : ℝ) / 2 : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    unfold algNorm
    rw [IrrGL.nu_nu, e1]
    unfold IrrGL.nu
    rw [IrrGL.tw_of]
    refine IrrGL.of_eq_of.2 ⟨?_⟩
    have e2 : GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ))) =
        σ'.ρ := by
      ext g v
      change ((GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ)) g : ℂˣ) : ℂ) • σ.ρ g v =
        ((CuspSub.locDet a (nu E (-t)) w g : ℂˣ) : ℂ) • σ.ρ g v
      congr 2
      simp [CuspSub.locDet, hloc, GlobalTheory.SmGL.detChar]
    rw [e2]
    exact .refl _
  rw [key]
  exact GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred) hU

end GlobalTheory.GalCut7.SizeAway

end
end
