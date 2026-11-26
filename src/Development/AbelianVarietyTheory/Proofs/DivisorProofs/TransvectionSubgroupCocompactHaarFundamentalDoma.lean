module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMeasure

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G}
    (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  refine ⟨S, Set.inter_subset_left, IsFundamentalDomain.mk' (MeasurableSet.nullMeasurableSet ?_) fun x => ?_⟩
  · exact hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  · obtain ⟨d, hd, hdu⟩ := hu x
    have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
      obtain ⟨γ, hγ, h⟩ := hcov x
      refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
      exact h
    obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
    refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
    · rw [smul_smul, mul_inv_cancel_left]; exact hd
    · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
      rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
    · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
      rw [smul_smul] at h1
      have e : g' * k = d := hdu _ h1
      have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
      have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
      rcases hle.eq_or_lt with h | h
      · rw [ek, hc (hg.trans h)]
      · refine (h2 g (hg ▸ h) ?_).elim
        rw [smul_smul, mul_assoc, e]
        exact hgK


open Pointwise in
theorem measure_ne_top_of_cocompact (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F ≠ ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  refine ne_of_lt ?_
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

end General

theorem exists_sub_mem_of_isOpen (F : Type) [Field F] [NumberField F] (W : AddSubgroup (AF F))
    (hW : IsOpen (W : Set (AF F))) (a : AF F) : ∃ x : F, a - algebraMap F (AF F) x ∈ W := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let H : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range ⊔ W
  have hH : IsOpen (H : Set (AF F)) := AddSubgroup.isOpen_mono le_sup_right hW
  have hd : DiscreteTopology (AF F ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hf : Finite (AF F ⧸ H) := by
    have h1 : (QuotientAddGroup.mk '' K : Set (AF F ⧸ H)).Finite :=
      (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
    refine Set.finite_univ_iff.1 (h1.subset fun q _ => ?_)
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, h⟩ := hx b
    refine ⟨_, h, QuotientAddGroup.eq.2 ?_⟩
    have : -(b - algebraMap F (AF F) x) + b = algebraMap F (AF F) x := by ring
    rw [this]
    exact AddSubgroup.mem_sup_left ⟨x, rfl⟩
  have hn : (H.index : F) ≠ 0 := Nat.cast_ne_zero.2 H.index_ne_zero_of_finite
  have hm := H.nsmul_index_mem ((H.index : F)⁻¹ • a)
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hn, one_smul] at hm
  obtain ⟨_, ⟨x, rfl⟩, w, hw, e⟩ := AddSubgroup.mem_sup.1 hm
  refine ⟨x, ?_⟩
  rw [← e]
  simpa using hw

theorem map_proj {R A n : Type} [CommRing R] [CommRing A] [DecidableEq n] (f : R →+* A) (ε : R) (M : Matrix n n R) :
    (f ε = 0 → (1 + ε • (M - 1)).map f = 1) ∧ (f ε = 1 → (1 + ε • (M - 1)).map f = M.map f) := by
  constructor <;> intro h <;> ext i j <;> by_cases hij : i = j <;> simp [h, Matrix.one_apply, hij]

theorem continuous_proj {X R n : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DecidableEq n] (ε : R) {M : X → Matrix n n R} (h : Continuous M) : Continuous fun x => 1 + ε • (M x - 1) :=
  continuous_const.add ((h.sub continuous_const).const_smul ε)

theorem proj_smul {R n : Type} [CommRing R] [DecidableEq n] (ε a : R) {M M' N : Matrix n n R}
    (h : M' = 1 + ε • (M - 1)) (ha : M - 1 = a • N) : M' - 1 = (ε * a) • N := by
  rw [h, ha, add_sub_cancel_left, smul_smul]

variable {D : D7}

theorem exists_finite_projection_mat (V : HSp D) : ∃ (p : GA D V →* GA D V) (ε : AE D), (∀ g, infHom V (p g) = 1) ∧
    (∀ g, finHom V (p g) = finHom V g) ∧ ∀ g, (matHom V (p g)).1 = 1 + ε • ((matHom V g).1 - 1) := by
  choose q h1 h2 using fun g : GA D V =>
    GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  obtain ⟨ε, e1, e2⟩ := GlobalTheory.UnitarySplit.parts_surj D 0 1
  refine ⟨MonoidHom.mk' q fun a b => GlobalTheory.UnitarySplit.ga_ext V
    (by rw [map_mul, h1, h1, h1, mul_one]) (by rw [h2, map_mul, map_mul, h2, h2]), ε, h1, h2, fun g => ?_⟩
  refine GlobalTheory.UnitarySplit.mat_ext (infPart D) (finPart D) (GlobalTheory.UnitarySplit.parts_inj D) ?_ ?_
  · exact (congrArg Units.val (h1 g)).trans ((map_proj (infPart D) ε _).1 e1).symm
  · exact (congrArg Units.val (h2 g)).trans ((map_proj (finPart D) ε _).2 e2).symm

theorem exists_finite_projection (V : HSp D) : ∃ p : GA D V →* GA D V, Continuous p ∧ (∀ g, p g ∈ GfC V) ∧
    (∀ g, g * (p g)⁻¹ ∈ GinfC V) ∧ ∀ ξ, ∀ g ∈ ZI V ξ, p g ∈ ZI V ξ := by
  obtain ⟨p, ε, h1, h2, hm⟩ := exists_finite_projection_mat V
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hc : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  have hc' : Continuous fun g : GA D V => (matHom V (p g)).1 :=
    (continuous_proj (R := AE D) ε hc).congr fun g => (hm g).symm
  refine ⟨p, ?_, h1, fun g => ?_, fun ξ g hg => ?_⟩
  · have h3 : Continuous fun g : GA D V => matHom V (p g) := by
      refine Units.continuous_iff.2 ⟨hc', (hc'.comp (continuous_inv (G := GA D V))).congr fun g => ?_⟩
      rw [Function.comp_apply, map_inv, map_inv]
    exact continuous_induced_rng.2 h3
  · change finHom V (g * (p g)⁻¹) = 1
    rw [map_mul, map_inv, h2 g, mul_inv_cancel]
  · have : ZI V ξ ≤ (ZI V ξ).comap p := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨a, ha⟩
      exact Subgroup.subset_closure ⟨ε * a, proj_smul ε a (hm g) ha⟩
    exact this hg

theorem transvection_measure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  intro D θ V hθ ξ hξ
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have i4 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  obtain ⟨-, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have : LocallyCompactSpace (Multiplicative (AF D.host.F)) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : LocallyCompactSpace (ZI V ξ) := e.toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hd : DiscreteTopology ((GQ V).subgroupOf (ZI V ξ)) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F
    refine discreteTopology_of_isOpen_singleton_one ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : (GQ V).subgroupOf (ZI V ξ) => Multiplicative.toAdd (e.symm x)) 1 :=
      (continuous_toAdd.comp (e.symm.continuous.comp continuous_subtype_val)).continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds (by simpa using hU)) ?_
    rintro ⟨z, hz⟩ hy
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hxa⟩ := (he a).1 hz
    have hy' : Multiplicative.toAdd a ∈ U := by simpa using hy
    have h0 : x = 0 := hx x (hxa ▸ hy')
    have : a = 1 := by
      rw [h0, map_zero] at hxa
      exact Multiplicative.toAdd.injective hxa.symm
    subst this
    exact Subtype.ext (map_one e)
  have := GlobalTheory.countable_of_discrete_subgroup ((GQ V).subgroupOf (ZI V ξ))
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  have hK' : IsCompact ((fun a => e (Multiplicative.ofAdd a)) '' K) :=
    hK.image (e.continuous.comp continuous_ofAdd)
  have hcov : ∀ z : ZI V ξ, ∃ γ ∈ (GQ V).subgroupOf (ZI V ξ), γ * z ∈ (fun a => e (Multiplicative.ofAdd a)) '' K := by
    intro z
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hx⟩ := hKx a.toAdd
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ (-x))), (he _).2 ⟨-x, rfl⟩, _, hx, ?_⟩
    beta_reduce
    rw [← map_mul, map_neg, sub_eq_neg_add]
    rfl
  refine ⟨?_, fun μ 𝓕 hμ h𝓕 => ⟨h𝓕.measure_ne_zero (NeZero.ne μ), measure_ne_top_of_cocompact _ hK' hcov μ h𝓕⟩,
    fun U hU z hz => ?_⟩
  · obtain ⟨S, hS, h⟩ := exists_fundamentalDomain_subset _ hK'.isClosed hcov Measure.haar
    exact ⟨Measure.haar, S, inferInstance, h, hK'.closure_of_subset hS⟩
  · obtain ⟨p, hp, h1, h2, h3⟩ := exists_finite_projection V
    let f : Multiplicative (AF D.host.F) →* GA D V := p.comp ((ZI V ξ).subtype.comp e.toMulEquiv.toMonoidHom)
    have hf : Continuous f := hp.comp (continuous_subtype_val.comp e.continuous)
    obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_sub_mem_of_isOpen D.host.F (Subgroup.toAddSubgroup' (U.comap f))
      (hU.preimage (hf.comp continuous_ofAdd)) a.toAdd
    set k : ZI V ξ := e (Multiplicative.ofAdd (a.toAdd - algebraMap _ _ x)) with hk
    have hkU : p k ∈ U := hx
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ x)), SetLike.coe_mem _, (he _).2 ⟨x, rfl⟩,
      k * (p k)⁻¹, mul_mem k.2 (inv_mem (h3 ξ _ k.2)), h2 _, p k, h3 ξ _ k.2, h1 _, hkU, ?_⟩
    rw [mul_assoc, inv_mul_cancel_right, hk, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, add_sub_cancel,
      ofAdd_toAdd, ha]

end GlobalTheory.TransvMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  first | exact @GlobalTheory.TransvMeasure.transvection_measure | exact GlobalTheory.TransvMeasure.transvection_measure | (intros; apply GlobalTheory.TransvMeasure.transvection_measure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.Transl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem lifts (hL : R.toLevCh.Is A.μ0) : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  have h := hL.βW i
  obtain ⟨c, hc⟩ := h
  exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ _ _ _ hc rfl
    (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)

theorem levChi_flag (k : GA D (Wc D i)) : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := Lev.subgroupCharExtension_one_apply _ _
  unfold Lev.levChi levFn
  rw [h2, show (Lev.flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (Lev.flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem hasType (hW : R.models_HW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    Lev.HasType (Wc D i) (R.βW i) (Lev.flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := (hW i σ).2.1.le (LinearMap.mem_range_self _ y)
  exact fun κ hκ h => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hm).lev v κ hκ h

theorem transl (hW : R.models_HW) (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (g : G) (k : GA D (Wc D i))
    (hk : IsLiftW R i g k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) (h : GA D (Wc D i)) :
    (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k) := by
  have h1 := Lev.level_action_spec (hasType R i hW σ y v) ⟨k, hk⟩ k hk h
  have h2 : (R.HW i σ).e (R.gW i σ g y) v h =
      Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e y v) h :=
    congrArg (fun U : MMap (R.MW i σ) => U v h) (hg i σ g y)
  refine h2.trans (h1.trans ?_)
  rw [levChi_flag, inv_one, one_mul]

theorem sum_apply_eq {G X Y : Type} [Fintype G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ev : X →ₗ[ℂ] Y) (c : G → ℂ) (a : G → Y →ₗ[ℂ] Y) (b : G → X) (y : Y) (h : ∀ g, ev (b g) = a g y) :
    (∑ g, c g • a g) y = ev (∑ g, c g • b g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]

theorem proj (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v :=
  sum_apply_eq
    (({ toFun := fun U => U v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      MMap (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)) ∘ₗ (R.HW i σ).e)
    (RealDat.eC (A := A) σ) (fun g => actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (fun g => R.gW i σ g y)
    ((R.HW i σ).e y v) fun g => congrArg (fun U : MMap (R.MW i σ) => U v) (hg i σ g y)

end GlobalTheory.GalLift.Transl

namespace GlobalTheory.GalLift

end GlobalTheory.GalLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunction
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem support_subset_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨S, hS⟩ := hf.2.2.2
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => q.1 * s * q.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => ?_
    exact (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory.FinClsLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.FinClsLoc.support_subset_compact) | (exact GlobalTheory.FinClsLoc.support_subset_compact) | (intros; apply GlobalTheory.FinClsLoc.support_subset_compact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquiv
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc

theorem localTransfer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  intro p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩
  have hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q := fun q =>
    RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q
  let e' : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) hq
  let T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C := Algebra.TensorProduct.congr e' AlgEquiv.refl
  have hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c := by
    intro c
    simp [T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x) := by
    intro x
    simp [T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
  have hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : T (r ⊗ₜ x) = e r ⊗ₜ x := by
        simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rw [this, starT_tmul, starT_tmul]
      simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]
  refine ⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩
  · have := hc.map T
    rw [hT1] at this
    exact this
  · have h' := congrArg T h
    rw [hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3] at h'
    simpa using h'

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  first | (exact @GlobalTheory.FinClsLoc.localTransfer) | (exact GlobalTheory.FinClsLoc.localTransfer) | (intros; apply GlobalTheory.FinClsLoc.localTransfer  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
  (P.valuedAdicCompletion_eq_valuation' _).symm.trans (unif_spec P)

theorem exists_unit_part (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ∃ u : Eˣ, P.valuation E (u : E) = 1 ∧ k = unif P ^ ordF P k * u := by
  refine ⟨(unif P ^ ordF P k)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
  have h0 : P.valuation E (k : E) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, val_unif,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg, ordF]
  conv_lhs => rw [← WithZero.exp_log h0, WithZero.log_exp, ← WithZero.exp_add]
  simp

theorem twVal_half (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1)
    (k : Eˣ) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal χ (1 / 2) P k =
      (((χ.locK P (unif P) : ℂˣ) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)) ^ ordF P k := by
  obtain ⟨u, hu, hk⟩ := exists_unit_part P k
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  generalize ordF P k = n at hk ⊢
  rw [hk, map_mul, h u hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  congr 1
  have hN : (0 : ℝ) ≤ (Nat.card (kP P) : ℕ) := Nat.cast_nonneg _
  rw [show Ideal.absNorm P.asIdeal = Nat.card (kP P) from Ideal.absNorm_eq_natCard _, ← Complex.ofReal_zpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hN, ← Real.rpow_intCast, ← Real.rpow_mul hN, Complex.ofReal_cpow hN]
  push_cast
  congr 1
  ring

end General

theorem locK_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ) (hu : UnramEverywhere D c)
    (P : Pl D.host.E) (u : D.host.Eˣ) (h : P.valuation D.host.E (u : D.host.E) = 1) : χ.locK P u = 1 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, hP, hQ⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have key : ∀ k : D.host.E, P.valuation D.host.E k = 1 → finPart D (locE D e k) ∈ intAE D := by
    intro k hk
    rw [h2]
    intro Q
    have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (ι (finPart D (incA D k)) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
    rw [h5, h4]
    change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
    by_cases hQP : Q = P
    · subst hQP
      rw [hP, one_mul, add_sub_cancel]
      exact ((Q.valuedAdicCompletion_eq_valuation' k).trans hk).le
    · rw [hQ Q hQP, zero_mul, add_zero, map_one]
  have hinv : (((locU he.1 u)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((u⁻¹ : D.host.Eˣ) : D.host.E) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [locU_val, locE_mul_locE he.1]
    simp [locE]
  have h6 := hu (locU he.1 u) (by
    rw [locU_val, locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf, zero_mul, add_zero])
    (key _ h) (by
      rw [hinv]
      refine key _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one])
  have h7 := hc.2 P e he u (locU he.1 u) rfl
  rw [h6] at h7
  exact Units.ext h7.symm

end GlobalTheory.EtaConjChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory

theorem twisted_norm_local_step : ∀ {A K : Type} [Ring A] [CommRing K] [Algebra K A] (σ : A →+* Aᵐᵒᵖ), (∀ x, (σ (σ x).unop).unop = x) →
    ∀ (β Y k z m : Aˣ) (a : A) (lam s : Kˣ), (σ (β : A)).unop = β →
    (Y : A) * β * (σ (Y : A)).unop = algebraMap K A s * β → Commute a Y →
    (k : A) * (a * β) * (σ (k : A)).unop = algebraMap K A lam → k⁻¹ = z * m → Commute (z : A) Y →
    (∀ m' : Aˣ, (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) → Commute (m' : A) Y →
      (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' →
      ∃ v : Aˣ, Commute (v : A) Y ∧ (m' : A) = v * ((β : A) * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A))) →
    ∃ z' : Aˣ, Commute (z' : A) Y ∧ a = algebraMap K A lam * ((z' : A) * β * (σ (z' : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
  intro A K _ _ _ σ hσ β Y k z m a lam s hβ hY haY hk hkz hzY H
  have shmul : ∀ x y : A, (σ (x * y)).unop = (σ y).unop * (σ x).unop := fun x y => by
    rw [map_mul, MulOpposite.unop_mul]
  have shinv : ∀ u : Aˣ, (σ ((u⁻¹ : Aˣ) : A)).unop * (σ (u : A)).unop = 1 := fun u => by
    rw [← shmul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have shinv' : ∀ u : Aˣ, (σ (u : A)).unop * (σ ((u⁻¹ : Aˣ) : A)).unop = 1 := fun u => by
    rw [← shmul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have shc : ∀ (u : Aˣ) (x : A), (σ (u : A)).unop * ((σ ((u⁻¹ : Aˣ) : A)).unop * x) = x := by
    intro u x; rw [← mul_assoc, shinv', one_mul]

  have hτY : (β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A) = algebraMap K A s * ((Y⁻¹ : Aˣ) : A) := by
    have h := congrArg (fun x => ((Y⁻¹ : Aˣ) : A) * x * ((β⁻¹ : Aˣ) : A)) hY
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one] at h
    rw [mul_assoc, h]
    exact (Algebra.commutes _ _).symm
  have hτ : ∀ w : A, Commute w Y → Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A)) Y := by
    intro w hw
    have hsh : Commute (σ w).unop (σ (Y : A)).unop := by
      show _ = _
      rw [← shmul, ← shmul, hw.eq]
    have hc : Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A))
        ((β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
      show _ = _
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (σ w).unop, hsh.eq, mul_assoc]
    rw [hτY] at hc
    have h2 := (Algebra.commute_algebraMap_right ((s⁻¹ : Kˣ) : K) _).mul_right hc
    rw [← mul_assoc (algebraMap K A ((s⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul, map_one,
      one_mul] at h2
    exact Commute.units_inv_right_iff.mp h2

  have e : a * (β : A) = ((k⁻¹ : Aˣ) : A) * ((k : A) * (a * β) * (σ (k : A)).unop) *
      (σ ((k⁻¹ : Aˣ) : A)).unop := by
    simp only [mul_assoc, shinv', shc, mul_one, Units.inv_mul_cancel_left]
  rw [hk, ← Algebra.commutes (lam : K), hkz, Units.val_mul, shmul] at e
  have ha : a = algebraMap K A lam * ((z : A) * ((m : A) * (σ (m : A)).unop) * (σ (z : A)).unop *
      ((β⁻¹ : Aˣ) : A)) := by
    calc a = a * β * ((β⁻¹ : Aˣ) : A) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e]; simp only [mul_assoc]

  have hbi : (σ ((β⁻¹ : Aˣ) : A)).unop = ((β⁻¹ : Aˣ) : A) := by
    have h := shinv β
    rw [hβ] at h
    calc (σ ((β⁻¹ : Aˣ) : A)).unop = (σ ((β⁻¹ : Aˣ) : A)).unop * β * ((β⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h, one_mul]
  let mu : Aˣ := ⟨(σ (m : A)).unop, (σ ((m⁻¹ : Aˣ) : A)).unop, shinv' m, shinv m⟩
  let m' : Aˣ := m * mu * β⁻¹
  have hm' : (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) := rfl
  have hm'c : (m' : A) = ((z⁻¹ : Aˣ) : A) * (algebraMap K A ((lam⁻¹ : Kˣ) : K) * a) *
      ((β : A) * (σ ((z⁻¹ : Aˣ) : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
    rw [hm', ha, ← mul_assoc (algebraMap K A ((lam⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul,
      map_one, one_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left, shc]
  have hmY : Commute (m' : A) Y := by
    rw [hm'c]
    exact ((hzY.units_inv_left).mul_left
      ((Algebra.commute_algebraMap_left _ _).mul_left haY)).mul_left (hτ _ hzY.units_inv_left)
  have hmτ : (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' := by
    rw [hm', shmul, shmul, hσ, hbi]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  obtain ⟨v, hvY, hv⟩ := H m' hm' hmY hmτ
  have h3 : (m : A) * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) =
      v * β * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A) := by
    rw [← hm', hv]; simp only [mul_assoc]
  have hmm := (Units.mul_left_inj β⁻¹).mp h3
  refine ⟨z * v, by rw [Units.val_mul]; exact hzY.mul_left hvY, ?_⟩
  rw [Units.val_mul, shmul, ha, hmm]
  simp only [mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

theorem ratInt_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

theorem glueL_evalT_inC (G : HTGroup p) (w : AwayP p) (c : G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) c) =
      inC G (w.1.adicCompletion ℚ) c := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((1 : AfP p) ⊗ₜ c) = (1 : w.1.adicCompletion ℚ) ⊗ₜ c
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem glueL_evalT_starT (G : HTGroup p) (w : AwayP p) (a : AfP p ⊗[ℚ] G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (starT G.star (AfP p) a).unop =
      (starT G.star (w.1.adicCompletion ℚ) (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) a)).unop := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem glueL_evalT_algebraMap (G : HTGroup p) (w : AwayP p) (t : AfP p) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) t) =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (AfP.eval w t) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem glueL_compL_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (w : AwayP p) :
    ((((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
        w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (x : AfP p ⊗[ℚ] G.C) *
        inC G (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
        Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x : AfP p ⊗[ℚ] G.C) *
    inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
  rw [map_mul, map_mul, glueL_evalT_inC]

theorem glueL_sh_inv_mul (G : HTGroup p) (c : G.Cˣ) : sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem glueL_main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  intro p _ G β x t hx y g c Y hy w
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom c
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * (ci * mY * ci⁻¹) * xw⁻¹ := by
    apply Units.ext
    rw [glueL_compL_toAfF_fst]
    have hy' : ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) = c * Y * c⁻¹ := Units.ext (by rw [hy]; rfl)
    rw [hy', ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have E : ((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw * ci) * mY * (u⁻¹ * xw * ci)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw * ci, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * ci * mY * (u⁻¹ * xw * ci)⁻¹)⁻¹ = (u⁻¹ * xw * ci) * mY⁻¹ * (u⁻¹ * xw * ci)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hs : ∀ z : G.C, (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) z)).unop =
        inC G (w.1.adicCompletion ℚ) (sh G z) := fun z => starT_tmul G.star _ 1 z
    have hC : (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
        sh G (c : G.C) = β := by
      calc (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
            sh G (c : G.C)
          = ((c : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) *
              (((β⁻¹ : G.Cˣ) : G.C) * β) * sh G (c : G.C) := by simp only [mul_assoc]
        _ = β * (sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C)) := by
            rw [Units.mul_inv, Units.inv_mul, one_mul, mul_one, mul_assoc]
        _ = β := by rw [glueL_sh_inv_mul, mul_one]
    have hk : (((u⁻¹ * xw * ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) *
          inC G (w.1.adicCompletion ℚ) (c : G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)),
      MulOpposite.unop_mul, MulOpposite.unop_mul, hs]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * (inC G (w.1.adicCompletion ℚ) ((c : G.C) *
            (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β * sh G (c : G.C))) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [map_mul, mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hC, hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

end GlobalTheory.FinClsLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayPStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  first | (exact @GlobalTheory.FinClsLoc.glueL_main) | (exact GlobalTheory.FinClsLoc.glueL_main) | (intros; apply GlobalTheory.FinClsLoc.glueL_main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
noncomputable section

namespace GlobalTheory.UnrEuler

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




end GlobalTheory.UnrEuler
end
end
