module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowsSum3

theorem rowTypePart_map_finiteGroup_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (p : A3.fam3.base3.Ix) (g : G) :
    (R.EEp3 p).map (R.gE g) ≤ R.EEp3 p := by
  obtain ⟨hcore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hE
  simp only [RealDat3.EEp3, Submodule.map_iSup]
  refine iSup_le fun c => iSup_le fun hc => ?_
  refine le_trans ?_ (le_iSup₂_of_le c hc le_rfl)
  rw [hEE]
  exact GlobalTheory.RowPartStable.map_gE_le (s := 0) R.toRealDat F.lv2 hcore _ hSF c g

theorem iSup_EEp_inf_typeSp3 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (htop : (⨆ p, R.EEp3 p) = ⊤) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) :
    (⨆ p, (R.toCx3 F).EEp p ⊓ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
  have hsup : (⨆ p, (R.toCx3 F).EEp p) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x ∈ ⨆ p, R.EEp3 p := htop ▸ Submodule.mem_top
    exact Submodule.iSup_induction R.EEp3
      (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈ ⨆ p, (R.toCx3 F).EEp p) hx
      (fun p y hy => Submodule.mem_iSup_of_mem (p := (R.toCx3 F).EEp) p hy) (Submodule.zero_mem _)
      fun y z hy hz => Submodule.add_mem _ hy hz
  have hst : ∀ p g, ((R.toCx3 F).EEp p).map (R.gEx F g) ≤ (R.toCx3 F).EEp p := by
    rintro p g _ ⟨x, hx, rfl⟩
    exact rowTypePart_map_finiteGroup_le R F hC hE p g ⟨_, hx, rfl⟩
  have h := GlobalTheory.iSup_stable_inf_typeSpace (R.gEx F) P ((Units.map (A3.A.fam.v0.embedding : D.what₂.LL →+* ℂ).toMonoidHom).comp ψ)
    (R.toCx3 F).EEp (fun _ => True) hst
  simp only [iSup_pos, hsup, top_inf_eq] at h
  exact h.symm

theorem partsE : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ b, (R.toCx3 F).PartsE b := by
  intro hCR hHU D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hE hJ hOkH hPG hPos hkl hB b
  have hcar := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCR hHU R F hLI hOk hC hE hJ hPG hPos
  have htop := GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hE (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R.toRealDat) hcar
  have hor := GlobalTheory.T.orthogonal_rowParts_of_distinct_types R F hOk hC hOkH hkl hB
  refine ⟨fun p q hpq e he e' he' => ?_, ?_⟩
  · exact (congrArg (cj _) (hor p q hpq _ he.1 _ he'.1)).trans (map_zero _)
  · obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
    cases b
    · rw [h0]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _
    · rw [h1]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _

end GlobalTheory.RowsSum3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelRows_orthogonalSum_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ b, (R.toCx3 F).PartsE b := by
  first | exact @GlobalTheory.RowsSum3.partsE | exact GlobalTheory.RowsSum3.partsE | (intros; apply GlobalTheory.RowsSum3.partsE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.SWLit.tamagawa_eq_map_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  intro F _ _ κ _ N e ν hν μ ⟨hμ, 𝓕, h𝓕1, h𝓕⟩
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨hHaar, hmem, -, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  haveI := hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  let L := (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range
  let L' := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
  have hmap : ∀ g : L', T g.1 ∈ L := by
    intro g
    obtain ⟨ξ, hξ⟩ := (hmem g.1).1 g.2
    exact ⟨fun i => ξ (e i), by rw [hξ]; rfl⟩
  let φ : L' → L := fun g => ⟨T g.1, hmap g⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, η, rfl⟩
    refine ⟨⟨rat fun j => η (e.symm j), (hmem _).2 ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    funext i
    show algebraMap F (AF F) (η (e.symm (e i))) = algebraMap F (AF F) (η i)
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Tm.symm (Measure.map Tm (muV N ν)) (muV N ν) :=
    MeasurePreserving.symm Tm ⟨Tm.measurable, rfl⟩
  have hD' : IsAddFundamentalDomain L (Tm.symm ⁻¹' D) (Measure.map Tm (muV N ν)) := by
    refine hD.preimage_of_equiv hmp.quasiMeasurePreserving hφ fun g x => ?_
    show T.symm (T g.1 + x) = g.1 + T.symm x
    rw [map_add (f := _), T.symm_apply_apply]
  have hD'1 : Measure.map Tm (muV N ν) (Tm.symm ⁻¹' D) = 1 := by
    rw [hmp.measure_preimage hDm.nullMeasurableSet, hD1]
  have hac : μ ≪ Measure.map Tm (muV N ν) := by
    rw [hr]
    exact Measure.smul_absolutelyContinuous
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable L := by
    have : Countable (Set.range (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ)) :=
      (Set.countable_range _).to_subtype
    exact this
  have h1 : μ (Tm.symm ⁻¹' D) = 1 := by
    rw [← h𝓕1]
    exact (hD'.mono hac).measure_eq h𝓕
  have hr1 : r = 1 := by
    rw [hr, Measure.smul_apply, hD'1] at h1
    simpa using h1
  rw [hr1, one_smul] at hr
  exact hr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasureStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  first | exact @GlobalTheory.SWLit.tamagawa_eq_map_pi | exact GlobalTheory.SWLit.tamagawa_eq_map_pi | (intros; apply GlobalTheory.SWLit.tamagawa_eq_map_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine.RightUnfold

theorem isMulRightInvariant_of_lattice {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Λ : Subgroup G)
    [Countable Λ] (𝓑 : Set G) (h𝓑 : IsFundamentalDomain Λ 𝓑 ν) (hfin : ν 𝓑 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  haveI : (ν.map (· * x)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν x
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map (· * x)) ν
  set c := Measure.haarScalarFactor (ν.map (· * x)) ν
  have h𝓑' : IsFundamentalDomain Λ ((· * x) ⁻¹' 𝓑) ν := by
    refine h𝓑.preimage_of_equiv (quasiMeasurePreserving_mul_right ν x) (e := id)
      Function.bijective_id ?_
    intro g y
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ν ((· * x) ⁻¹' 𝓑) = ν 𝓑 := h𝓑'.measure_eq h𝓑
  have h0 : ν 𝓑 ≠ 0 := h𝓑.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map (· * x)) 𝓑 = ν ((· * x) ⁻¹' 𝓑) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x) 𝓑
  have h1 : (c : ENNReal) * ν 𝓑 = 1 * ν 𝓑 := by
    calc (c : ENNReal) * ν 𝓑 = (c • ν) 𝓑 := by simp [Measure.smul_apply]
      _ = (ν.map (· * x)) 𝓑 := by rw [hc]
      _ = 1 * ν 𝓑 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem unimodular_and_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  intro G _ _ _ _ _ _ _ _ ν Λ _ 𝓑 hν h𝓑 hfin
  haveI hR := isMulRightInvariant_of_lattice ν Λ 𝓑 h𝓑 hfin
  haveI := isInvInvariant_of_right ν
  refine ⟨hR, fun f hf => ?_⟩
  rw [← lintegral_inv_eq_self f, h𝓑.lintegral_eq_tsum' (fun x => f x⁻¹), lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    refine lintegral_congr fun b => ?_
    simp [Subgroup.smul_def]
  · intro γ
    exact (hf.comp (measurable_inv.mul_const _)).aemeasurable

end GlobalTheory.ResLine.RightUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLatticeStatement
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  first | exact @GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold | exact GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold | (intros; apply GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem gcd_nsmul_mem_of {A S : Type*} [AddCommGroup A] [SetLike S A] [AddSubgroupClass S A] (Λ : S) {x : A}
    {k k' : ℕ} (h : k • x ∈ Λ) (h' : k' • x ∈ Λ) : Nat.gcd k k' • x ∈ Λ := by
  have e : Nat.gcd k k' • x = Nat.gcdA k k' • (k • x) + Nat.gcdB k k' • (k' • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, Nat.gcd_eq_gcd_ab]
    congr 1; ring
  rw [e]
  exact add_mem (zsmul_mem h _) (zsmul_mem h' _)

theorem add_mul_succ_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    z + ((k : ℤ) * (n + 1)) • w = (z + ((k : ℤ) * n) • w) + k • w := by
  rw [mul_add, mul_one, add_smul, natCast_zsmul, add_assoc]

theorem add_mul_pred_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    (z + ((k : ℤ) * (n - 1)) • w) + k • w = z + ((k : ℤ) * n) • w := by
  rw [add_assoc, ← natCast_zsmul, ← add_smul]; congr 2; ring

theorem add_gcd_nsmul_eq {A : Type*} [AddCommGroup A] (k k' : ℕ) (z w : A) :
    z + Nat.gcd k k' • w = (z + ((k : ℤ) * Nat.gcdA k k') • w) + ((k' : ℤ) * Nat.gcdB k k') • w := by
  rw [add_assoc, ← add_smul, ← Nat.gcd_eq_gcd_ab, natCast_zsmul]

theorem isHalf_add_zsmul {e : AE D} {m n : ℕ} {a b : Mx D m n} (ha : IsHalf e a) (hb : IsHalf e b) (c : ℤ) :
    IsHalf e (a + c • b) := fun i j => by
  have h1 := ha i j
  have h2 := hb i j
  show e * (a i j + c • b i j) = a i j + c • b i j
  rw [zsmul_eq_mul, mul_add, mul_left_comm, h1, h2]

theorem DepthOK.flatProd_add_zsmul {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t} {e : AE D} {k : ℕ}
    (hK : DepthOK S t Φ β e k) (c : ℤ)
    (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))
    (hx : ∀ j, IsHalf e (x j)) (hy : ∀ i, IsHalf e (y i))
    (hu : ∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j))
    (hv : ∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) :
    flatProd S t Φ β (x + ((k : ℤ) * c) • u) (y + ((k : ℤ) * c) • v) = flatProd S t Φ β x y := by
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_mul_succ_zsmul, add_mul_succ_zsmul,
      hK.2 (x + ((k : ℤ) * n) • u) u (y + ((k : ℤ) * n) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv, ih]
  | pred n ih =>
    rw [← hK.2 (x + ((k : ℤ) * (-n - 1)) • u) u (y + ((k : ℤ) * (-n - 1)) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
      add_mul_pred_zsmul, add_mul_pred_zsmul, ih]

theorem depthOK_gcd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ)
    (h : DepthOK S t Φ β e k) (h' : DepthOK S t Φ β e k') : DepthOK S t Φ β e (Nat.gcd k k') := by
  refine ⟨fun x y hx hy hF => ⟨fun j => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).1 j) ((h'.1 x y hx hy hF).1 j),
    fun i => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).2 i) ((h'.1 x y hx hy hF).2 i)⟩, ?_⟩
  intro x u y v hx hy hu hv
  rw [add_gcd_nsmul_eq k k' x u, add_gcd_nsmul_eq k k' y v,
    h'.flatProd_add_zsmul _ (x + ((k : ℤ) * Nat.gcdA k k') • u) u (y + ((k : ℤ) * Nat.gcdA k k') • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _)
      (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
    h.flatProd_add_zsmul _ x u y v hx hy hu hv]

end GlobalTheory.DepthUnf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatProductDepthPeriodic_gcd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ), DepthOK S t Φ β e k → DepthOK S t Φ β e k' → DepthOK S t Φ β e (Nat.gcd k k') := by
  first | exact @GlobalTheory.DepthUnf.depthOK_gcd | exact GlobalTheory.DepthUnf.depthOK_gcd | (intros; apply GlobalTheory.DepthUnf.depthOK_gcd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHom
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem path_bc_ring {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] {R' : Type} [CommRing R']
    (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) (h : IsPath G c b ξ) :
    IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) := by
  have hC : ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.C (R := R)) =
      (PowerSeries.C (R := R')).comp φ := by
    ext a n
    simp [PowerSeries.coeff_C]
    split_ifs <;> simp_all
  have h0 : (PowerSeries.constantCoeff (R := R')).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      φ.comp (PowerSeries.constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp
  have hs : (PowerSeries.rescale (φ c)).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.rescale c) := by
    ext p n
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, h.base, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hC,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.zero, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.scale, Category.assoc]

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := by
  show (η[G]).left ≫ q.left = (η[H]).left
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem sqr_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    sqr G ≫ q.left = q.left ≫ sqr H := by
  unfold sqr
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]

end GlobalTheory.Nef

theorem GlobalTheory.Nef.paths_bc : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  refine ⟨?_, ?_⟩
  · intro S G _ R _ R' _ φ c u b ξ h
    refine ⟨path_bc_ring G φ c u b ξ h, ?_⟩
    intro _ n V τ w _ U hU ht hU' V' hV he hb f
    rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 (PowerSeries R) (PowerSeries R') G.left ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ξ U hU hU' f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ht U hU V' hV he hb f, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pow_one, ← _root_.mul_assoc]
  · intro S G H _ _ q _ R _ c b ξ
    refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_, sqr_comp q⟩
    · rw [Category.assoc, Over.w q, h.base]
    · rw [← Category.assoc, h.zero, Category.assoc, unitSec_comp]
    · rw [← Category.assoc, h.scale, Category.assoc, Category.assoc, sqr_comp]
    · rw [triv, Category.assoc, Category.assoc, unitSec_comp, triv]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHomStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSquaringPaths_baseChange_and_hom : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  first | exact @GlobalTheory.Nef.paths_bc | exact GlobalTheory.Nef.paths_bc | (intros; apply GlobalTheory.Nef.paths_bc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

namespace GlobalTheory.CondLESplit

open ValuativeRel

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))

theorem valued_unifAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have he := isEquiv_Fv v
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ' : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    he.lt_one_iff_lt_one.1 (hϖ ▸ uniformizer_lt_one)
  apply le_antisymm
  · have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · rw [← hπ']
    have hπ1 : valuation (Fv F v) ((π : F) : Fv F v) < 1 := by
      refine he.lt_one_iff_lt_one.2 ?_
      rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    exact (he _ _).1 (hϖ ▸ le_uniformizer_iff.2 hπ1)

end GlobalTheory.CondLESplit

open GlobalTheory.CondLESplit in
theorem GlobalTheory.CondLESplit.condLE_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (ρ : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ →* ℂˣ) (n : ℕ),
    GlobalTheory.SplitFlip.CondLE (unifAt v) n (ρ.comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔
      ∀ x : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ, Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) x →
        Valued.v ((x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρ x = 1 := by
  intro F E _ _ _ _ _ v τ ρ n
  set hw := GlobalTheory.AdelicU.splitPrime_under τ
  set f := GlobalTheory.LFun.complMap hw
  have he := isEquiv_Fv v
  have hval : ∀ a : Fv F v, Valued.v (f a) = Valued.v a := GlobalTheory.LFun.SplitTie.valued_complMap τ hw
  have hbij : Function.Bijective f := GlobalTheory.LFun.SplitTie.complMap_bijective τ hw
  have key : ∀ y : (Fv F v)ˣ, y ∈ GlobalTheory.SplitFlip.unitCong (unifAt v ^ n) ↔
      (Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map f.toMonoidHom y) ∧
        Valued.v (((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
          (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) := by
    intro y
    have h1 : ((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
        (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) = f y := rfl
    have hp : Valued.v (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v) = WithZero.exp (-(n : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, map_pow, valued_unifAt, ← WithZero.exp_nsmul]
      congr 1; simp
    show (ValuativeRel.valuation (Fv F v) (y : Fv F v) = 1 ∧ ValuativeRel.valuation (Fv F v) ((y : Fv F v) - 1) ≤
        ValuativeRel.valuation (Fv F v) (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v)) ↔ _
    unfold Formalism.L2.Host.IsUnitAt
    rw [h1, he.eq_one_iff_eq_one, he, hp, ← map_one f, ← map_sub, hval, hval]
  constructor
  · intro h x hx1 hx2
    obtain ⟨a, ha⟩ := hbij.2 (x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero] at ha; exact x.ne_zero ha.symm
    set y := Units.mk0 a ha0
    have hy : Units.map f.toMonoidHom y = x := Units.ext ha
    have := h y ((key y).2 (hy ▸ ⟨hx1, hx2⟩))
    rw [← hy]; exact this
  · intro h y hy
    exact h _ ((key y).1 hy).1 ((key y).1 hy).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwo
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem eta_comp_mul_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id]
  simpa using lift_comp_one_left (𝟙 _) η[G]

private theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G :=
  congrArg (·.left) (eta_comp_mul_self G)

theorem sqr_sub_two_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  intro S G _ hqs s π ε m hd f hf
  haveI := hqs
  obtain ⟨hπ, hε, hm⟩ := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hd
  have he : unitSec G ≫ G.hom = 𝟙 S := sec_hom η[G]
  obtain ⟨U₀, hU₀, g, rfl⟩ := G.left.presheaf.germ_exist f
  have hsq : sqr G (unitSec G s) = unitSec G s := by rw [← Scheme.Hom.comp_apply, unitSec_comp_sqr]
  have hb : G.hom (unitSec G s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨U₁, hU₁, hs₁, -⟩ := QCoh.exists_affine_mem_le (U := (⊤ : S.Opens)) s trivial
  obtain ⟨W₁, hW₁, hx₁, k₁⟩ := QCoh.exists_affine_mem_le
    (U := U₀ ⊓ sqr G ⁻¹ᵁ U₀ ⊓ G.hom ⁻¹ᵁ U₁) (unitSec G s)
    ⟨⟨hU₀, show sqr G (unitSec G s) ∈ U₀ by rw [hsq]; exact hU₀⟩,
      show G.hom (unitSec G s) ∈ U₁ by rw [hb]; exact hs₁⟩
  obtain ⟨U, hsU, -, -, c⟩ := GlobalTheory.Conormal.exists_isChart_inf he hU₁ hW₁ (k₁.trans inf_le_right) hx₁
    (show s ∈ (⊤ : S.Opens) from trivial)
  have kW : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ U₀ := inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_left))
  have kS : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ sqr G ⁻¹ᵁ U₀ :=
    inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_right))
  have hxW : unitSec G s ∈ W₁ ⊓ G.hom ⁻¹ᵁ U := c.le hsU
  have hU0 : U ≤ unitSec G ⁻¹ᵁ U₀ := c.le.trans ((unitSec G).preimage_mono kW)

  have a1 := cotMap_d (𝟙 G * 𝟙 G) (eta_comp_mul_self G) hU0 c.le kS g
  have a2 := cotMap_d (𝟙 G) (Category.comp_id _) hU0 c.le kW g
  have hmul := cotMap_mul (x := 𝟙 G) (y := 𝟙 G) (Category.comp_id η[G]) (Category.comp_id η[G]) (eta_comp_mul_self G)
  have key : GlobalTheory.Conormal.d he c.le ((sqr G).appLE U₀ _ kS g) =
      GlobalTheory.Conormal.d he c.le (resG G.left kW g) + GlobalTheory.Conormal.d he c.le (resG G.left kW g) := by
    have := congrArg (fun φ => φ.app U (GlobalTheory.Conormal.d he hU0 g)) hmul
    simp only at this
    exact (a1.symm.trans this).trans (congrArg₂ (· + ·) a2 a2)
  letI := c.algebra
  let h : Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) := (sqr G).appLE U₀ _ kS g - (resG G.left kW g + resG G.left kW g)
  have hz : AugCot.d (c.aug he) h = 0 := (c.augCotEquiv he).injective (by
    rw [c.augCotEquiv_d he, map_zero, map_sub, map_add (f := _), key, sub_self])
  rw [AugCot.d_eq_zero_iff] at hz
  let gW := G.left.presheaf.germ (W₁ ⊓ G.hom ⁻¹ᵁ U) (unitSec G s) hxW
  have g1 : gW ((sqr G).appLE U₀ _ kS g) = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) :=
    (hm U₀ hU₀ _ hxW kS g).symm
  have g2 : gW (resG G.left kW g) = G.left.presheaf.germ U₀ (unitSec G s) hU₀ g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gh : gW h = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) -
      2 * G.left.presheaf.germ U₀ (unitSec G s) hU₀ g := by
    simp only [h, map_sub, map_add (f := _), g1, g2, two_mul]
  have hf0 : ε (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) = 0 := hf
  have hker : ∀ x, c.aug he x = 0 → ε (gW x) = 0 := by
    intro x hx
    have hx' : (unitSec G).appLE _ U c.le x = 0 := hx
    rw [hε _ hxW U hsU c.le x, hx', map_zero]
  have hmap : ∀ y ∈ RingHom.ker (c.aug he) ^ 2, gW y ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    have := Ideal.mem_map_of_mem (ConcreteCategory.hom gW) hy
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (RingHom.mem_ker.2 (hker x (RingHom.mem_ker.1 hx)))) 2 this
  have hεm : ε (m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g)) = 0 := by
    rw [← g1, hε _ hxW U hsU c.le, GlobalTheory.Conormal.appLE_appLE (unitSec_comp_sqr G) kS c.le hU0,
      ← hε U₀ hU₀ U hsU hU0 g, hf0]
  have hεh : ε (gW h) = 0 := by rw [gh, map_sub, map_mul, hεm, hf0, mul_zero, sub_zero]
  have halg : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) = 0 := by
    have e1 : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) =
        π (S.presheaf.germ U s hsU (c.aug he h)) := (hπ U hsU _ hxW c.le_base _).symm
    have e2 : S.presheaf.germ U s hsU (c.aug he h) = ε (gW h) := (hε _ hxW U hsU c.le h).symm
    rw [e1, e2, hεh, map_zero]
  rw [← gh, show gW h = gW (h - algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) +
      gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) by rw [← map_add (f := _), sub_add_cancel],
    halg, add_zero]
  exact hmap _ hz
end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  first | exact @GlobalTheory.Nef.sqr_sub_two_mem | exact GlobalTheory.Nef.sqr_sub_two_mem | (intros; apply GlobalTheory.Nef.sqr_sub_two_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem evAt_congr' {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt ξ h f = evAt ξ' h' f := by
  subst e; rfl

theorem top_le_preimage_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro z _
  exact h (Set.mem_univ (f z))

theorem finite_centre_not_mem (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E]
    [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) (hx : IsGenOver k x) (V : C.Opens) (hV : (V : Set C).Nonempty) :
    {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  have hC := hx.1
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  obtain ⟨z, hz⟩ := hV
  obtain ⟨V', hV'a, hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens hz
  have hV'a : IsAffineOpen V' := hV'a
  obtain ⟨hxV', -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨z, hzV'⟩
  obtain ⟨ev1, ev2, -, -, ev5, ev6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  let f : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hxV')
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have eV : V' ≤ strHom k C ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let ψ := ((strHom k C).appLE ⊤ V' eV).hom
  have hft : ψ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (strHom k C) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V', hV'a⟩ eV
  letI := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out

  have hconst : ∀ (p : Place k E) (c : Γ(Sp k, ⊤)), p.1 (f (ψ c)) ≤ 1 := by
    intro p c
    have hxs : ⊤ ≤ (x ≫ strHom k C) ⁻¹ᵁ (⊤ : (Sp k).Opens) := top_le_preimage_comp' x (strHom k C) ⊤ (fun _ _ => trivial)
    have htop : ⊤ ≤ (𝟙 (Sp k)) ⁻¹ᵁ (⊤ : (Sp k).Opens) := fun _ _ => trivial
    have h1 : evAt x hxV' (ψ c) = evAt (x ≫ strHom k C) hxs c :=
      (ev2 K C (Sp k) x (strHom k C) V' ⊤ hxV' _ eV c).symm
    have h2 : evAt (x ≫ strHom k C) hxs c =
        evAt (spMap (algebraMap k K) ≫ 𝟙 (Sp k)) (top_le_preimage_comp' _ _ _ htop) c :=
      evAt_congr' (by rw [Category.comp_id]; exact hx.2.2) _ _ c
    have h3 := ev1 k K (Sp k) (algebraMap k K) (𝟙 (Sp k)) ⊤ htop (top_le_preimage_comp' _ _ _ htop) c
    have hf : f (ψ c) = algebraMap k E (evAt (𝟙 (Sp k)) htop c) := by
      simp only [f, RingHom.comp_apply]
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply]
    rw [hf]
    by_cases hd : evAt (𝟙 (Sp k)) htop c = 0
    · rw [hd, map_zero, map_zero]; exact zero_le'
    · exact (p.2.2 _ hd).le
  have key : ∀ p : Place k E, (∀ a ∈ s, p.1 (f a) ≤ 1) → ∀ g, p.1 (f g) ≤ 1 := by
    intro p hp g
    have hg : g ∈ Algebra.adjoin Γ(Sp k, ⊤) (s : Set Γ(C, V')) := by rw [hs]; trivial
    induction hg using Algebra.adjoin_induction with
    | mem a ha => exact hp a ha
    | algebraMap c => exact hconst p c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact (p.1.map_add _ _).trans (max_le ha hb)
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_le_one' ha hb
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  refine ((s.finite_toSet.biUnion fun a _ => (?_ : {p : Place k E | ¬ p.1 (f a) ≤ 1}.Finite))).subset ?_
  · by_cases h0 : f a = 0
    · simpa [h0] using (Set.finite_empty : (∅ : Set (Place k E)).Finite)
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (f a) h0).1.subset fun p hp h1 => hp h1.le
  · rintro p ⟨b, hb1, hb2⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hno
    push_neg at hno
    have hall := key p fun a ha => hno a ha
    have hmem : ∀ g, f g ∈ p.O := fun g => (Valuation.mem_valuationSubring_iff _ _).2 (hall g)
    let φ : Γ(C, V') →+* p.O := f.codRestrict p.O hmem
    obtain ⟨b', hb', hev⟩ := ev6 p.O C V' hV'a φ
    have hc := top_le_preimage_comp' (spMap p.O.subtype) b' V' hb'
    have hd := top_le_preimage_comp' (spMap (algebraMap K E)) x V' hxV'
    have hcd : spMap p.O.subtype ≫ b' = spMap (algebraMap K E) ≫ x := by
      refine ev5 E C _ _ V' hV'a hc hd ?_
      ext g
      rw [ev1 p.O E C p.O.subtype b' V' hb' hc g, ev1 K E C (algebraMap K E) x V' hxV' hd g, hev]
      rfl
    have hbb := (GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K E C x hx p).unique hb1 hcd
    subst hbb
    exact hb2 fun w hw => hV'V (hb' hw)

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_centre_outside_open : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ V : C.Opens, (V : Set C).Nonempty → {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  first | exact @GlobalTheory.Nef.finite_centre_not_mem | exact GlobalTheory.Nef.finite_centre_not_mem | (intros; apply GlobalTheory.Nef.finite_centre_not_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevel
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaOfSmF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_theta_infPartF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) :
    Continuous fun z : AEF F E => θ (infPartF F E z) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AEF F E, θ (infPartF F E z) = ∑ i, θ (fstA F (bb.repr z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← bb.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    show θ (fstA F (bb.repr z i) ⊗ₜ[F] b i) = _
    rw [← hθ.1 (b i), ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc : ∀ i, Continuous fun z : AEF F E => bb.repr z i := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  refine (continuous_finsetSum _ fun i _ => ?_).congr fun z => (hz z).symm
  exact (hθ.2.comp (continuous_fst.comp (hc i))).mul continuous_const

end GlobalTheory.ThetaOfSmF


open GlobalTheory.ThetaOfSmF in
theorem GlobalTheory.ThetaOfSmF.theta_of_smF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)

  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add (f := _), Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _

  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _), neg_add] }
  have hφ : Continuous φ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) := by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevelStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFun_of_smooth_real_heisenberg_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  first | exact @GlobalTheory.ThetaOfSmF.theta_of_smF | exact GlobalTheory.ThetaOfSmF.theta_of_smF | (intros; apply GlobalTheory.ThetaOfSmF.theta_of_smF <;> assumption)
end
end
