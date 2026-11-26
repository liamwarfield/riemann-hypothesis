module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.Columns.TiedUpDnA
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCombOfMemClosureFinset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
noncomputable section

namespace GlobalTheory.HaarMat

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD Topology

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem intMat_eq_pi (n m : ℕ) : intMat (OP P) n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
      fun _ : Fin m => ((P.adicCompletionIntegers L : Set (P.adicCompletion L)))) := by
  ext y
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩

theorem isCompact_intMat (n m : ℕ) : IsCompact (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P

theorem isOpen_intMat (n m : ℕ) : IsOpen (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

def intMatK (n m : ℕ) : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) (P.adicCompletion L)) where
  carrier := intMat (OP P) n m
  isCompact' := isCompact_intMat P n m
  interior_nonempty' := by
    rw [(isOpen_intMat P n m).interior_eq]
    exact ⟨0, fun i j => (OP P).zero_mem⟩

theorem exists_haar_intMat : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ),
    letI : MeasurableSpace (P.adicCompletion L) := borel _;
    ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)),
      ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  intro L _ _ P n m
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  haveI : BorelSpace (P.adicCompletion L) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin m → P.adicCompletion L))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    (isCompact_intMat P n m).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((isOpen_intMat P n m).mem_nhds fun i j => (OP P).zero_mem)
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin m → P.adicCompletion L))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) := inferInstance
  haveI : SigmaFinite (Measure.addHaarMeasure (intMatK P n m)) := inferInstance
  refine ⟨Measure.addHaarMeasure (intMatK P n m), inferInstance, inferInstance,
    Measure.addHaarMeasure_self⟩

end GlobalTheory.HaarMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOneStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ), letI : MeasurableSpace (P.adicCompletion L) := borel _; ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)), ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  first | exact @GlobalTheory.HaarMat.exists_haar_intMat | exact GlobalTheory.HaarMat.exists_haar_intMat | (intros; apply GlobalTheory.HaarMat.exists_haar_intMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem pr_lvC_eq_lv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  intro B X I hI hP l Z H F hS hC u i h1 h2 v c
  have hi := le_of_succ_m h2
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hL⟩ := hsp i hi
  have hlat := (hL u I.mu0).1 c
  obtain ⟨hF, hFC⟩ := hS u
  have hcl : clsCrd (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hlat
  have hres := hF.res
  have hsep := sepElt_of_ok l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hLd : Ld (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.Lsh := by
    show dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (clsCrd (I.rec7 l Z) u i hi c) = _
    rw [hg, hcl]
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ _
  have hPv : (F u).atT.Pv v = (show (B.primes X).vT u from v).1.asIdeal := by
    ext x
    show (F u).atT.res v x = 0 ↔ _
    rw [hres]
    exact Ideal.Quotient.eq_zero_iff_mem (I := (show HeightOneSpectrum (𝓞 B.fields.E) from v.1).asIdeal)
  have hLk : Formalism.L2.Forms.Lk (F u).atT i hi v c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.LshKer v := by
    rw [lv_LshKer_eq _ hsep v]
    show clsCrd (I.rec7 l Z) u i hi c ⊔ (F u).atT.Pv v • Ld (I.rec7 l Z) u i hi c = _
    rw [hLd, hcl, hPv]
    rfl
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 (I.rec7 l Z).host.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hu : (F u).atT.res v s ≠ 0 := by
    rw [hres, hs]
    exact fun h => hsep.off v (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hd : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Ld (I.rec7 l Z) u i hi c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.N := fun x hx => by
    rw [hs]
    exact (((I.stp u I.mu0 i).rep c).1.1.deco).2.smul_Lsh_mem_N hsep.conj (hLd ▸ hx)
  have hk : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v := fun x hx => by
    rw [hs]
    exact (le_sup_left : _ ≤ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v) (lv_smul_LshKer_mem _ hsep v (hLk ▸ hx))
  refine ⟨fun z z' e => ?_, fun z z' e => ?_⟩
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.pr i hi v c (s • ⟨x', hx⟩) (hd x' hx)
    have e2 := (hFC.1 i h1 h2).1 v c (s • ⟨x', hx'⟩) (hd x' hx)
    rw [((F u).lv i hi).pr_smul] at e1
    rw [((F u).lvC i h1 h2).pr_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.prk i hi v c (s • ⟨x', hx⟩) (hk x' hx)
    have e2 := (hFC.1 i h1 h2).2 v c (s • ⟨x', hx'⟩) (hk x' hx)
    rw [((F u).lv i hi).prk_smul] at e1
    rw [((F u).lvC i h1 h2).prk_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)

end GlobalTheory.Mem.Col2.HAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  first | exact @GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | exact GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | (intros; apply GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df.RowsEx

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

end GlobalTheory.Mem.Df.RowsEx

open GlobalTheory.Mem.Df.RowsEx in
theorem GlobalTheory.Mem.Df.rowsDef_nonempty : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme := GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms I hI hP l hX
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

noncomputable def pvPlace {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := A.Pv v
  isPrime := inferInstance
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (A.eV v).1.ne_bot
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ A.Pv v := (A.res_v v x).1 hx
    rw [h, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E) (by simpa using h1))

theorem pvPlace_isOver {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    IsOver (A.eV v).1 (pvPlace A v) := by
  ext x
  exact A.res_v v x

theorem eq_Pv_or_conj {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT)
    (q : HeightOneSpectrum (𝓞 D.host.E)) (hq : q.under (𝓞 D.host.F) = (A.eV v).1) :
    q.asIdeal = A.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) := by
  have hov : IsOver (A.eV v).1 q := by
    rw [← hq]
    rfl
  rcases rll_over_cases D.sp.cm (pvPlace_isOver A v) hov with e | e
  · exact Or.inl (congrArg HeightOneSpectrum.asIdeal e)
  · refine Or.inr ?_
    have h1 := conjIdeal_asIdeal (pvPlace A v)
    rw [e, ← h1]
    rfl

theorem primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) :=
  fun _ _ _ _ _ _ F _ _ u v q hq => eq_Pv_or_conj (F u).atT v q hq

end GlobalTheory.Mem.Col2.HAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.primes_over_level_place | exact GlobalTheory.Mem.Col2.HAt.primes_over_level_place | (intros; apply GlobalTheory.Mem.Col2.HAt.primes_over_level_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.EigEx

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (h : StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h

theorem isSF_ssetF {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : R.WeakCharacterisation F) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  classical
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 h.base.lev).1
  have hS : R.Sb = R.Pg := h.allPl
  intro v
  unfold SsetF
  rw [hQ, hS, Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  rw [HeightOneSpectrum.ext_iff]
  rfl

theorem exists_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ hgen π
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig
  rw [hμ]
  exact GlobalTheory.T.row_type_has_spherical_hecke_eigensystem R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex).1 hgen _
    (isSF_ssetF hP.char) Y.hF Y.PY Y.PW (stdPsi_of_stdFrame Y.stdPsi.1) (fun i => stdPsi_of_stdFrame (Y.stdPsi.2 i)) _
    (principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)) ⟨0, Y.hm⟩

end GlobalTheory.Mem.R3.EigEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  first | exact @GlobalTheory.Mem.R3.EigEx.exists_hasEig | exact GlobalTheory.Mem.R3.EigEx.exists_hasEig | (intros; apply GlobalTheory.Mem.R3.EigEx.exists_hasEig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
namespace GlobalTheory.TameTau

theorem char_eq_of_apply_root_eq : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ A P hP O _ _ _ _ _ hO χ hχ m hm hmP hχm ϖ hϖP hϖ2 π hπ σ hσ σ' hσ' heq
  have hm0 : m ≠ 0 := hm.ne'
  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hP]
    simpa using h
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨σ₀, hσ₀, hσ₀π⟩ := GlobalTheory.T.inertia_acts_on_tame_root A P hP m hm hmP ϖ hϖP hϖ2 π hπ ζ hζ.pow_eq_one
  have J := fun τ hτ => GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator A γ hγ hO χ hχ m hm hvm hχm (ϖ : E) π hπ0 hπ τ hτ
  obtain ⟨k, -, hk⟩ := J σ₀ hσ₀
  obtain ⟨n, hn1, hn2⟩ := J σ hσ
  obtain ⟨n', hn1', hn2'⟩ := J σ' hσ'
  set θ := γ π / π with hθ
  rw [hσ₀π, mul_div_cancel_right₀ _ hπ0] at hk
  have hθn : θ ^ n = θ ^ n' := by rw [← hn2, ← hn2', heq]
  have hζn : ζ ^ n = ζ ^ n' := by rw [hk, ← pow_mul, ← pow_mul, mul_comm k n, mul_comm k n', pow_mul, pow_mul, hθn]
  have hmod : n ≡ n' [MOD m] := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
    have hu : (Units.mk0 ζ hζ0) ^ n = (Units.mk0 ζ hζ0) ^ n' := Units.ext (by simpa using hζn)
    rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hζ.eq_orderOf] at hu
    exact hu
  have hγI : γ ∈ Ine (F := E) A := hγ.1
  have hord : orderOf (χ γ) ∣ m := orderOf_dvd_of_pow_eq_one (hχm γ hγI)
  rw [hn1, hn1', pow_eq_pow_iff_modEq]
  exact Nat.ModEq.of_dvd hord hmod

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_char_eq_of_inertia_condition : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_apply_root_eq | exact GlobalTheory.TameTau.char_eq_of_apply_root_eq | (intros; apply GlobalTheory.TameTau.char_eq_of_apply_root_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem

theorem card_GL_eq_pow_mul_qE (k : Type) [Field k] [Fintype k] (r : ℕ) :
    (Nat.card (GL (Fin r) k) : ℝ)
      = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card k := by omega
    exact_mod_cast this.ne'
  have hconst : (Fintype.card k : ℝ) ^ (r * r)
      = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range
      (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r,
    hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    show r - (r - i) = i
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    show r - (r - j) = j
    omega
  · intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hle : Fintype.card k ^ i ≤ Fintype.card k ^ r :=
      Nat.pow_le_pow_right (by omega) hir.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hir.le]; ring
    rw [hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProdStatement
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod : ∀ (k : Type) [Field k] [Fintype k] (r : ℕ), (Nat.card (GL (Fin r) k) : ℝ) = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  first | exact @GlobalTheory.Mem.card_GL_eq_pow_mul_qE | exact GlobalTheory.Mem.card_GL_eq_pow_mul_qE | (intros; apply GlobalTheory.Mem.card_GL_eq_pow_mul_qE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.EtaUnitArg

theorem denseRange_atInf_single {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) :
    DenseRange (atInf w : Lˣ → (w.Completion)ˣ) := by
  classical
  have hs : Function.Surjective (fun u : ∀ v : InfinitePlace L, (v.Completion)ˣ => u w) := fun z =>
    ⟨Function.update (1 : ∀ v : InfinitePlace L, (v.Completion)ˣ) w z, by simp⟩
  exact hs.denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf L) (continuous_apply w)

open Classical in
theorem locInf_eq {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) (z : (w.Completion)ˣ) :
    Units.map (Formalism.L2.NC.locInf w) z = infIdele L w z := by
  apply Units.ext
  rfl

theorem etaT_isUnitArg : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  intro R H χ hχ h hh g f hf hfE z
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hloc := (GlobalTheory.InfTypeLocal.infType_iff_local H.E (R.Psi) (embPsi H) hcm.bij χ.1 χ.2.1
    (fun _ => 1)).1 (fun k => hχ.inf k) g
  have key : (fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
      ((χ.1 (infIdele H.E _ z) : ℂˣ) : ℂ)) =
      fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
        f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) /
          ((‖f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion)‖ : ℝ) : ℂ) := by
    refine (denseRange_atInf_single _).equalizer ?_ ?_ ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (GlobalTheory.InfTypeLocal.continuous_infIdele _ _))
    · have h1 := hf.comp Units.continuous_val
      have h2 : ∀ u : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ,
          f (u : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) ≠ 0 := fun u =>
        (_root_.map_ne_zero _).2 u.ne_zero
      exact h1.div (Complex.continuous_ofReal.comp h1.norm) fun u => by exact_mod_cast norm_ne_zero_iff.2 (h2 u)
    · funext k
      have e : f ((atInf _ k : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ) :
          (InfinitePlace.mk (H.emb (g : R.GG))).Completion) = H.emb (g : R.GG) k := by
        change f (algebraMap H.E _ (k : H.E)) = H.emb (g : R.GG) k
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
          Algebra.algebraMap_self_apply]
        exact hfE k
      simp only [Function.comp_apply]
      rw [e]
      have := hloc k
      exact this.trans (zpow_one _)
  rw [locInf_eq, hh]
  exact congrFun key z

end GlobalTheory.EtaUnitArg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaTilde_isUnitArg_at_cmType_places : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  first | exact @GlobalTheory.EtaUnitArg.etaT_isUnitArg | exact GlobalTheory.EtaUnitArg.etaT_isUnitArg | (intros; apply GlobalTheory.EtaUnitArg.etaT_isUnitArg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReduction
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

theorem inv_smul_mem_of_be_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.at w.1) (h0 : d.be w x = 0) :
    ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • x ∈ d.at w.1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TopStep.liftFr_spec hd w
  set fr := d.liftFr w with hfr
  have e : fr (fr.symm x) = x := fr.apply_symm_apply x
  have hs : fr.symm x ∈ stdAt E n w.1 := (h1 _).1 (by rwa [e])
  have hr := h2 _ hs
  rw [e, h0] at hr
  have hi := GlobalTheory.TopStep.mem_stdAt.1 hs
  have hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1 := GlobalTheory.TopStep.mem_stdAt.2 fun i => by
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm
    rwa [div_eq_inv_mul] at this
  have := (h1 _).2 hs'
  rwa [map_smul, e] at this

theorem sub_mem_of_be_eq {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {y y' z : Sp E n}
    (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.at w.1) (hy' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y' ∈ d.at w.1)
    (hz : z - y' ∈ d.at w.1)
    (e : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)) :
    y - y' ∈ d.at w.1 := by
  have hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1 :=
    GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz
  have e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0 := by
    rw [GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]
  have e2 := hd.be_add w _ hqz _ hy'
  rw [← smul_add, sub_add_cancel, e1, zero_add, ← e] at e2
  have hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1 := by
    rw [smul_sub]
    exact sub_mem hy hy'
  have e3 := hd.be_add w _ hx _ hy'
  rw [← smul_add, sub_add_cancel, e2, right_eq_add] at e3
  have := inv_smul_mem_of_be_eq_zero hd w hq hx e3
  rwa [smul_smul, inv_mul_cancel₀ hq0, one_smul] at this

theorem mem_coset {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] {L : Submodule A M} {y z : M} :
    z ∈ {z | z - y ∈ L} ↔ z - y ∈ L := Iff.rfl

theorem coset_eq {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] (L : Submodule A M) {y y' : M} (h : y - y' ∈ L) :
    {z | z - y ∈ L} = {z | z - y' ∈ L} := by
  refine Set.ext fun z => ?_
  rw [mem_coset, mem_coset]
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have := add_mem h' h
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h' h
    rwa [sub_sub_sub_cancel_right] at this

theorem eq_of_deco_bar : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  intro X Pr R sel S mu cst u j hQ hq q q' hd hb
  have hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P => by
    have := P.2
    simpa [rowSG, uSG, hQ] using this
  have hfr : q.1.1 = q'.1.1 := by
    apply Subtype.ext
    have hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False := fun a ha => by
      rw [hQ] at ha
      simp at ha
    exact Prod.ext hd (funext fun P => (hE _ P.2).elim)
  suffices h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := q.mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := q'.mem_ybSet hj
    have eN : q'.1.1.deco.1.N = q.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e := by
      intro e he
      refine (mem_locLat _ _ _ _).2 fun P => ?_
      rw [he P, zpow_zero, inv_one, one_smul]
      have hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩ :=
        ⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩
      rw [congrFun hb ⟨P.1, hP P⟩] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos (hP P), zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos (hP P), _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez
    rw [eY, eY']
    exact coset_eq _ (key _ fun P => if_pos (hP P))
  · have h1 := q.2
    have h1' := q'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.MemChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnPointEqOfDecoAndCosetReductionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPoint_eq_of_deco_and_cosetReduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | exact GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | (intros; apply GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubOneLtOfRed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameCoupledEx

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_g_lt (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver (F := E) A v) {g : ℕ}
    (hg : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal) : A.valuation ((g : ℕ) : Ω) < 1 := by
  have := (hA ((g : ℕ) : 𝓞 E)).2 hg
  simpa using this


omit [NumberField E] in
theorem val_nat_not_lt (A : ValuationSubring Ω) {g m : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    (hm : ¬ g ∣ m) : ¬ A.valuation ((m : ℕ) : Ω) < 1 := by
  intro hm1
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hgp).2 hm))
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have e : (a : Ω) * m + (b : Ω) * g = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * m + (b : Ω) * g) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle a) zero_le hm1
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle b) zero_le hg
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem fix_rou {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {m : ℕ} (hm : 0 < m) (hgm : ¬ g ∣ m) {μ : Ω} (hμ : μ ^ m = 1) :
    σ μ = μ := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (val_nat_not_lt A hgp hg hgm) (by rw [← map_pow, hμ, map_one]) hμ ?_
  exact hσ.2 μ ((A.valuation_le_one_iff _).2 (Formalism.L2.NT.mem_of_pow_eq_one A hm hμ))

theorem not_dvd_pow_sub_one {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : ¬ g ∣ g ^ d - 1 := by
  intro h
  have h1 : g ∣ g ^ d := dvd_pow_self g hd.ne'
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  have h3 : g ∣ g ^ d - (g ^ d - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2.le] at h3
  exact hgp.not_dvd_one h3

theorem pow_sub_one_pos {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : 0 < g ^ d - 1 := by
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  omega

variable [CharZero Ω]

omit [NumberField E] in
theorem ne_zero_of_pow_eq {g N : ℕ} (hgp : g.Prime) (hN : 0 < N) {y : Ω} (hy : y ^ N = ((g : ℕ) : Ω)) : y ≠ 0 := by
  rintro rfl
  rw [zero_pow hN.ne'] at hy
  exact (Nat.cast_ne_zero.2 hgp.ne_zero : ((g : ℕ) : Ω) ≠ 0) hy.symm

theorem ratio_indep {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y y' : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (hy' : y' ^ N = ((g : ℕ) : Ω)) : σ y' / y' = σ y / y := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  obtain ⟨μ, rfl⟩ : ∃ μ, y' = μ * y := ⟨y' / y, by field_simp⟩
  have hμ : μ ^ N = 1 := by
    rw [mul_pow, hy] at hy'
    exact (mul_eq_right₀ hg0).1 hy'
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hμ; exact zero_ne_one hμ
  rw [map_mul, fix_rou hgp hg hσ hN hgN hμ]
  field_simp

theorem ratio_mul {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (τ : G E Ω) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) : (σ * τ) y / y = (σ y / y) * (τ y / y) := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  have hc : (τ y / y) ^ N = 1 := tameQuot_pow τ hg0 hy
  set c := τ y / y with hcdef
  have e : τ y = c * y := by rw [hcdef]; field_simp
  rw [AlgEquiv.mul_apply, e, map_mul, fix_rou hgp hg hσ hN hgN hc]
  field_simp

theorem ratio_pow {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (j : ℕ) : (σ ^ j) y / y = (σ y / y) ^ j := by
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  induction j with
  | zero => simp [hy0]
  | succ j ih =>
    rw [pow_succ, ratio_mul hgp hg (pow_mem hσ j) σ hN hgN hy, ih, pow_succ]

theorem root_down {g d D : ℕ} (hdD : d ∣ D) {r : Ω} (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    (r ^ ((g ^ D - 1) / (g ^ d - 1))) ^ (g ^ d - 1) = ((g : ℕ) : Ω) := by
  rw [← pow_mul, Nat.div_mul_cancel (Nat.pow_sub_one_dvd_pow_sub_one g hdD), hr]

theorem ratio_descent {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {d D : ℕ} (hd : 0 < d) (hdD : d ∣ D) {y r : Ω}
    (hy : y ^ (g ^ d - 1) = ((g : ℕ) : Ω)) (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    σ y / y = (σ r / r) ^ ((g ^ D - 1) / (g ^ d - 1)) := by
  rw [ratio_indep hgp hg hσ (pow_sub_one_pos hgp hd) (not_dvd_pow_sub_one hgp hd) (root_down hdD hr) hy,
    map_pow, div_pow]

end

theorem val_sub_one_lt_of_red {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {x : Ω} (hx : x ∈ A) (h : redThrough A κ x = 1) :
    A.valuation (x - 1) < 1 := by
  unfold redThrough at h
  rw [dite_eq_left hx] at h
  have h1 : IsLocalRing.residue A ⟨x, hx⟩ = IsLocalRing.residue A 1 := κ.injective (by rw [h, map_one, map_one])
  have h2 : (⟨x, hx⟩ : A) - 1 ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 h1
  have h3 := (A.valuation_lt_one_iff _).1 h2
  simpa using h3

end GlobalTheory.TameCoupledEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
open scoped Matrix ComplexOrder

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_conj_bVV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (i : VVIdx lam) :
    MvPolynomial.map ((starRingEnd ℂ).comp φ) (bVV K lam i : VV K lam).1 = MvPolynomial.map φ (bVV K lam i : VV K lam).1 := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [bVV_coe, hQ, MvPolynomial.map_map, MvPolynomial.map_map]
  rw [RingHom.ext_int (((starRingEnd ℂ).comp φ).comp (Int.castRingHom K)) (φ.comp (Int.castRingHom K))]

theorem map_smul_pol {K : Type} [Field K] {σ : Type} (φ : K →+* ℂ) (r : K) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem pairB_conj_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (y : VV K lam) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map φ y.1)) (MvPolynomial.map φ y.1) =
      star (fun i => φ ((bVV K lam).repr y i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map φ *ᵥ (fun i => φ ((bVV K lam).repr y i)) := by
  have hy : y.1 = ∑ i, (bVV K lam).repr y i • (bVV K lam i : VV K lam).1 := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [Submodule.coe_sum]
    rfl
  rw [MvPolynomial.map_map, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul_pol, map_conj_bVV, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← GlobalTheory.PeriodOnStep.map_pairB, dotProduct, Matrix.mulVec, Matrix.map_apply, GlobalTheory.TestLat.Compare.gramB, Matrix.of_apply, pairBK_apply,
    Pi.star_apply, RingHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem herm_mk {K : Type} [Field K] {ι : Type} [Fintype ι] (M : Matrix ι ι K) (φ : K →+* ℂ) (hM : (M.map φ).PosDef)
    (a : ι → K) :
    star (fun i => (InfinitePlace.mk φ).embedding (a i)) ⬝ᵥ M.map (InfinitePlace.mk φ).embedding *ᵥ
        (fun i => (InfinitePlace.mk φ).embedding (a i)) =
      star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h]
    have hr := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => φ (a i))
    have hc : starRingEnd ℂ (star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i))) =
        star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hr).2.symm
    rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
      map_mul, starRingEnd_apply, star_star]

theorem normAt_sq_eq_cSum {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) =
      cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  have h0 := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH B.wts I.Ch I.sel (I.tup a) I.Ps hX).2 (InfinitePlace.mk B.embLL)
  refine (h0 (x : (MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps).V)).trans ?_
  rw [cSum_apply]
  unfold GSD.ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cTerm
  rw [GSD.wt_eq]
  congr 1
  rw [GlobalTheory.PeriodClassSum.pairAt_eq, GlobalTheory.PeriodClassSum.row_gramV]
  exact (herm_mk _ _ (GlobalTheory.PeriodClassSum.gramB_posDef _ _) _).trans (pairB_conj_map _ _ _).symm

end GlobalTheory.Mem.Df
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetricStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V), ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) = cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  first | exact @GlobalTheory.Mem.Df.normAt_sq_eq_cSum | exact GlobalTheory.Mem.Df.normAt_sq_eq_cSum | (intros; apply GlobalTheory.Mem.Df.normAt_sq_eq_cSum <;> assumption)
end
end
