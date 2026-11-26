module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdelicHaarProd

theorem haar_prod : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  intro D V μf hμf
  obtain ⟨hLC, hSC, hT2, hB, hTG, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hi := GlobalTheory.AdelicSplit.isClosed_GinfC' V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  let e := GlobalTheory.AdelicSplit.splitEquiv V
  let μi : Measure (GinfC V) := Measure.haar
  haveI : SFinite μf := inferInstance
  refine ⟨Measure.map e (μi.prod μf), μi, ContinuousMulEquiv.isHaarMeasure_map _ e, fun S E => ?_⟩
  have hset : {h : GA D V | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = e '' (S ×ˢ E) := by
    ext h
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨(a, k), ⟨ha, hk⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hk⟩, rfl⟩
      exact ⟨p.1, ha, p.2, hk, rfl⟩
  rw [hset]
  rw [show (Measure.map e (μi.prod μf)) = Measure.map (e.toHomeomorph.toMeasurableEquiv) (μi.prod μf) from rfl]
  rw [MeasurableEquiv.map_apply]
  rw [show (e.toHomeomorph.toMeasurableEquiv) ⁻¹' (e '' (S ×ˢ E)) = S ×ˢ E from e.toEquiv.preimage_image _]
  exact Measure.prod_prod S E

end GlobalTheory.AdelicHaarProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  first | exact @GlobalTheory.AdelicHaarProd.haar_prod | exact GlobalTheory.AdelicHaarProd.haar_prod | (intros; apply GlobalTheory.AdelicHaarProd.haar_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HaarEmb

theorem map_wittEmbedding_zero_rank_isHaarMeasure : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)), μ.IsHaarMeasure → (Measure.map d.emb0 μ).IsHaarMeasure := by
  intro D S S₀ d μ hμ
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S₀) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D S₀) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hbkc : Continuous (GlobalTheory.WeilSrc.Zero.back d) := continuous_of_mt S₀ (by
    simp only [GlobalTheory.WeilSrc.Zero.back, mt_ofMat]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)
  have hli : ∀ g, GlobalTheory.WeilSrc.Zero.back d (d.emb0 g) = g := fun g =>
    d.wittDecomp_anisotropicEmbedding_injective (GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d _)
  let e : GA D S₀ ≃* GA D S :=
    { toFun := d.emb0, invFun := GlobalTheory.WeilSrc.Zero.back d, left_inv := hli,
      right_inv := GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d, map_mul' := fun x y => map_mul d.emb0 x y }
  exact MulEquiv.isHaarMeasure_map μ e d.continuous_embed hbkc

end GlobalTheory.HaarEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)), μ.IsHaarMeasure → (Measure.map d.emb0 μ).IsHaarMeasure := by
  first | exact @GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure | exact GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure | (intros; apply GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBessel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBessel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarExist

theorem haar_exists : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  intro D V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨⟨Measure.haar, inferInstance⟩, fun V₀ ρ d => ⟨?_, fun A L o => ?_⟩⟩
  · have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
    have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩
  · have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
    have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩

end GlobalTheory.HaarExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBesselStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  first | exact @GlobalTheory.HaarExist.haar_exists | exact GlobalTheory.HaarExist.haar_exists | (intros; apply GlobalTheory.HaarExist.haar_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroups
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem haar_box_prod_finite_pos : ∀ (ι : Type) [Fintype ι] (p q : ι → ℕ) (m : ∀ i, Measure (UpqT (p i) (q i))), (∀ i, (m i).IsHaarMeasure) → ∃ B : ∀ i, Set (UpqT (p i) (q i)), (∀ i, MeasurableSet (B i)) ∧ ∏ i, m i (B i) ≠ 0 ∧ ∏ i, m i (B i) ≠ ⊤ := by
  intro ι _ p q m hm
  have hK : ∀ i, ∃ K : Set (UpqT (p i) (q i)), IsCompact K ∧ K ∈ nhds (1 : UpqT (p i) (q i)) :=
    fun i => exists_compact_mem_nhds 1
  choose K hKc hKn using hK
  refine ⟨fun i => interior (K i), fun i => isOpen_interior.measurableSet, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (isOpen_interior.measure_pos (m i) ⟨1, mem_interior_iff_mem_nhds.mpr (hKn i)⟩).ne'
  · apply ENNReal.prod_ne_top
    intro i _
    exact (lt_of_le_of_lt (measure_mono interior_subset) (hKc i).measure_lt_top).ne

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroupsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_box_finite_pos_product_haar_unitaryGroups : ∀ (ι : Type) [Fintype ι] (p q : ι → ℕ) (m : ∀ i, Measure (UpqT (p i) (q i))), (∀ i, (m i).IsHaarMeasure) → ∃ B : ∀ i, Set (UpqT (p i) (q i)), (∀ i, MeasurableSet (B i)) ∧ ∏ i, m i (B i) ≠ 0 ∧ ∏ i, m i (B i) ≠ ⊤ := by
  first | exact @GlobalTheory.haar_box_prod_finite_pos | exact GlobalTheory.haar_box_prod_finite_pos | (intros; apply GlobalTheory.haar_box_prod_finite_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGeometricMeasureVolume
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MeasCommon

open scoped ENNReal NNReal

theorem common_measure : ∀ (D : D7) (V : HSp D) (T : Type) (K : T → Subgroup (GL (Fin V.rank) (Lev.EAf D))) (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop), (∀ ρ m, good ρ m → m.IsHaarMeasure) → ∀ (μf : Measure (GfC V)), μf.IsHaarMeasure → ∀ (ν : T → Measure (GA D V)), (∀ t, Lev.IsMeasLevW V (K t) good (ν t)) → ∃ ν₀ : Measure (GA D V), ν₀.IsHaarMeasure ∧ ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 ∧ μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ ∧ μf {k | Lev.finE V k.1 ∈ K t} • ν t = ν₀ := by
  intro D V T K good hgood μf hμf ν hν
  haveI : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  obtain ⟨μR, μi, hR, hprod⟩ := GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite D V μf hμf
  obtain ⟨hdec, hfin⟩ := GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D V
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨μR, hR, fun t => isEmptyElim t⟩
  obtain ⟨⟨θ, hθ⟩, hθall⟩ := (hν t₀).2
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := hAall A hA
  obtain ⟨B, hBm, hB0, hBT⟩ := GlobalTheory.T.exists_box_finite_pos_product_haar_unitaryGroups D.what₂.Tau (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) m
    (fun ρ => hgood ρ _ (hm ρ))
  haveI hνH : ∀ t, (ν t).IsHaarMeasure := fun t => (hν t).1
  let S : Set (GinfC V) := {a | ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) (a : GA D V)}
  have key : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) * (μi S * μf {k | Lev.finE V k.1 ∈ K t}) = ∏ ρ, m ρ (B ρ) := by
    intro t
    haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hbox := (((hν t).2.2 θ hθ).2 A hA).2 m hm B hBm
    have hset : {h : GA D V | Lev.finE V h ∈ K t ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} =
        {h | ∃ a ∈ S, ∃ k ∈ {k : GfC V | Lev.finE V k.1 ∈ K t}, h = (a : GA D V) * k} := by
      ext h
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, k, hk, rfl⟩ := hdec h
        obtain ⟨e1, e2⟩ := hfin a ha k hk
        refine ⟨⟨a, ha⟩, fun ρ => ?_, ⟨k, hk⟩, ?_, rfl⟩
        · obtain ⟨b, hb, hb'⟩ := h2 ρ
          exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
        · show Lev.finE V k ∈ K t
          rw [← e1]; exact h1
      · rintro ⟨a, ha, k, hk, rfl⟩
        obtain ⟨e1, e2⟩ := hfin a.1 a.2 k.1 k.2
        refine ⟨by rw [e1]; exact hk, fun ρ => ?_⟩
        obtain ⟨b, hb, hb'⟩ := ha ρ
        exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
    rw [e, hset, Measure.smul_apply, hprod] at hbox
    rw [← hbox, ENNReal.smul_def, smul_eq_mul]
  have hc0 : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ 0 := fun t => by
    haveI : (ν t).IsHaarMeasure := (hν t).1
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure (ν t) μR).ne'
  have hcT : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ ⊤ := fun t => ENNReal.coe_ne_top
  have hX0 : μi S ≠ 0 := fun h0 => hB0 (by rw [← key t₀, h0, zero_mul, mul_zero])
  have hY0 : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 := fun t h0 => hB0 (by rw [← key t, h0, mul_zero, mul_zero])
  have hXT : μi S ≠ ⊤ := fun h0 => hBT (by rw [← key t₀, h0, ENNReal.top_mul (hY0 t₀), ENNReal.mul_top (hc0 t₀)])
  have hYT : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ := fun t h0 =>
    hBT (by rw [← key t, h0, ENNReal.mul_top hX0, ENNReal.mul_top (hc0 t)])
  refine ⟨((∏ ρ, m ρ (B ρ)) / μi S) • μR, ?_, fun t => ⟨hY0 t, hYT t, ?_⟩⟩
  · exact Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.2 ⟨hB0, hXT⟩).ne' (ENNReal.div_ne_top hBT hX0)
  · haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hv : μf {k | Lev.finE V k.1 ∈ K t} * ((ν t).haarScalarFactor μR : ℝ≥0∞) = (∏ ρ, m ρ (B ρ)) / μi S := by
      rw [ENNReal.eq_div_iff hX0 hXT, ← key t]
      ring
    rw [← hv]
    conv_lhs => rw [e]
    ext s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_assoc]

noncomputable def volOf {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : Vol V :=
  ⟨μ, (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose, h,
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose_spec⟩

@[simp] theorem volOf_μ {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : (volOf μ h).μ = μ := rfl

theorem measures_common : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (b : ∀ j, GA D (Yc D j)), (∀ j, j ≤ D.R.m → (a.x j).Is) → ∃ m : YMeas y, GeoMeas (pk W) (mkGeo m b) ∧ (commOf (pk W) u (mkGeo m b)).VolLast := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y b _
  have hM : (pk W).IsModels := hP.bot.hyp.2.2.2.1.models
  have hm2 := D.R.two_le_m
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V =>
    (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have hf : ∀ j, ∃ μ : Measure (GfC (Yc D j)), μ.IsHaarMeasure := fun j =>
    (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).1
  choose μf hμf using hf
  obtain ⟨μT, hμT⟩ := (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D D.sp.X').1
  choose ρJ hρJ using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D (j + 1))).2 _ _ (y.jac j ρ h).d).1
  choose ρB hρB using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).2 _ _ (y.bes j ρ h).d).2 _ _ (y.bes j ρ h).o
  have hc : ∀ k, ∃ ν₀ : Measure (GA D (Yc D k)), ν₀.IsHaarMeasure ∧ (k < D.R.m → ∀ t,
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ 0 ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ ⊤ ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} •
        (pk W).νY t k = ν₀) := by
    intro k
    by_cases hk : k < D.R.m
    · have hw : ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D k).sig (tauE D ρ)).1 ((Yc D k).sig (tauE D ρ)).2) → Prop,
          (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧ ∀ t, Lev.IsMeasLevW (Yc D k)
            (Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)) good ((pk W).νY t k) := by
        by_cases hk' : k + 1 < D.R.m
        · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ h => h.1, fun t => (hM.νY t k hk').1⟩
        · obtain rfl : k = D.R.m - 1 := by omega
          exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ h => h.1, fun t => (hM.νY' t).1⟩
      obtain ⟨good, hg, hw⟩ := hw
      obtain ⟨ν₀, h1, h2⟩ := common_measure D (Yc D k) _ _ good hg (μf k) (hμf k) _ hw
      exact ⟨ν₀, h1, fun _ => h2⟩
    · exact ⟨_, (Classical.choice (GlobalTheory.Unf.VolExist.nonempty_vol (Yc D k))).haar, fun h => absurd h hk⟩
  choose ν₀ hν₀H hν₀ using hc
  obtain ⟨ν₀T, hν₀TH, hν₀T⟩ := common_measure D D.sp.X' _
    (fun t => Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t))
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1) μT hμT (fun t => (pk W).νX t)
    (fun t => (hM.νX t).1)
  have hLH : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).IsHaarMeasure :=
    fun j h => GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition D _ _ _ _ (a.x (j + 1)).vol.haar
  let vS : ∀ j, Vol (Yc D (j + 1)) := fun j => if h : j + 2 * 0 + 2 = D.R.m then volOf _ (hLH j h)
    else volOf (ν₀ (j + 1)) (hν₀H (j + 1))
  have hvS1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (vS j).μ = Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ := by
    intro j h; simp only [vS, dif_pos h, volOf_μ]
  have hvS2 : ∀ j, ¬ (j + 2 * 0 + 2 = D.R.m) → (vS j).μ = ν₀ (j + 1) := by
    intro j h; simp only [vS, dif_neg h, volOf_μ]
  let vol : ∀ k, Vol (Yc D k) := fun k => Nat.casesOn (motive := fun k => Vol (Yc D k)) k (volOf (ν₀ 0) (hν₀H 0)) vS
  let κ : ℕ → ℝ := fun k => Nat.casesOn (motive := fun _ => ℝ) k 1 fun j => if h : j + 2 * 0 + 2 = D.R.m then
    ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) else 1
  have hκ1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), κ (j + 1) =
      ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) := by
    intro j h; simp only [κ, dif_pos h]
  have hκ2 : ∀ k, k + 1 ≠ D.R.m → κ k = 1 := by
    intro k hk
    cases k with
    | zero => rfl
    | succ j => simp only [κ, dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)]
  have hκpos : ∀ k, 0 < κ k := by
    intro k
    by_cases hk : k + 1 = D.R.m
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h : j + 2 * 0 + 2 = D.R.m := by omega
      rw [hκ1 j h]
      haveI := hLH j h
      haveI := hν₀H (j + 1)
      exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
    · rw [hκ2 k hk]; exact one_pos
  have hset : ∀ k (β : GL (Fin (Yc D k).rank) (Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D k).rank),
      ({g : GfC (Yc D k) | g.1 ∈ levS _ β Ld} : Set (GfC (Yc D k))) =
        {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram β Ld} := by
    intro k β Ld; ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  refine ⟨⟨vol, volOf ν₀T hν₀TH, μf, μT, ρJ, ρB, κ⟩, ⟨hμf, hμT, hρJ, hρB, hκpos, ?_, ?_⟩, ?_⟩
  · intro t j hj
    have hX := hν₀ (j + 1) hj t
    show (vS j).μ = _
    rw [GlobalTheory.Fam.volLev, if_pos hj]
    change (vS j).μ = ENNReal.ofReal (κ (j + 1) * (μf (j + 1) {g | g.1 ∈ levS _ ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)}).toReal) • (pk W).νY t (j + 1)
    rw [hset]
    obtain ⟨hX0, hXT, hXe⟩ := hX
    generalize μf (j + 1) {g | Lev.finE (Yc D (j + 1)) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)} = X at hX0 hXT hXe ⊢
    by_cases hL : j + 2 * 0 + 2 = D.R.m
    · rw [hvS1 j hL, hκ1 j hL]
      haveI := hLH j hL
      haveI := hν₀H (j + 1)
      have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ) (ν₀ (j + 1))
      generalize (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) = c at e ⊢
      rw [e, ← hXe, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXT, mul_smul]
      ext s _
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    · rw [hvS2 j hL, hκ2 (j + 1) (by omega), one_mul, ENNReal.ofReal_toReal hXT, hXe]
  · intro t
    obtain ⟨hX0, hXT, hXe⟩ := hν₀T t
    show ν₀T = _
    rw [GlobalTheory.Fam.volLev, if_neg (by omega)]
    change ν₀T = ENNReal.ofReal (κ D.R.m * (μT {k | k.1 ∈ levS _ (pk W).βX ((pk W).datXt t)}).toReal) • (pk W).νX t
    rw [hκ2 D.R.m (by omega), one_mul]
    have hs : {g : GfC D.sp.X' | g.1 ∈ levS _ (pk W).βX ((pk W).datXt t)} =
        {g | Lev.finE D.sp.X' g.1 ∈ Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)} := by
      ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [hs, ENNReal.ofReal_toReal hXT, hXe]
  · intro j h
    exact hvS1 j h

end GlobalTheory.MeasCommon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGeometricMeasureVolumeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_measure_volume : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (b : ∀ j, GA D (Yc D j)), (∀ j, j ≤ D.R.m → (a.x j).Is) → ∃ m : YMeas y, GeoMeas (pk W) (mkGeo m b) ∧ (commOf (pk W) u (mkGeo m b)).VolLast := by
  first | exact @GlobalTheory.MeasCommon.measures_common | exact GlobalTheory.MeasCommon.measures_common | (intros; apply GlobalTheory.MeasCommon.measures_common <;> assumption)
end
