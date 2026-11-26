module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem isClosed_range_of_isCompact_preimage {G H : Type} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (φ : G →* H) (hφ : Continuous φ) (U : Set H)
    (hU : IsOpen U) (h1 : (1 : H) ∈ U) (hc : IsCompact (φ ⁻¹' U)) : IsClosed (Set.range φ) := by
  have hcl : IsClosed (U ∩ Set.range φ) := by
    have e : U ∩ Set.range φ = φ '' (φ ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨hy, g, rfl⟩
        exact ⟨g, hy, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨hg, g, rfl⟩
    rw [e]
    exact (hc.image hφ).isClosed
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  have hO : IsOpen ((fun s => s⁻¹ * x) ⁻¹' U) := hU.preimage (by fun_prop)
  have hxO : x ∈ (fun s => s⁻¹ * x) ⁻¹' U := by
    show x⁻¹ * x ∈ U
    rwa [inv_mul_cancel]
  obtain ⟨s, hsU, g, rfl⟩ := mem_closure_iff.mp hx _ hO hxO
  have hy : (φ g)⁻¹ * x ∈ closure (Set.range φ) :=
    map_mem_closure (f := fun s => (φ g)⁻¹ * s) (by fun_prop) hx
      (by rintro _ ⟨k, rfl⟩; exact ⟨g⁻¹ * k, by simp⟩)
  have hyU : (φ g)⁻¹ * x ∈ U ∩ Set.range φ := by
    rw [← hcl.closure_eq]
    exact hU.inter_closure ⟨hsU, hy⟩
  obtain ⟨-, k, hk⟩ := hyU
  exact ⟨g * k, by rw [map_mul, hk, mul_inv_cancel_left]⟩

theorem nhds_one_hasBasis_Kg (I : AutInst) : (nhds (1 : I.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) I.Kg := by
  refine ⟨fun t => ⟨fun ht => I.topf_basis t ht, ?_⟩⟩
  rintro ⟨N, hN, hsub⟩
  refine Filter.mem_of_superset ((I.topf_open N hN).mem_nhds ?_) hsub
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simpa using one_mem (Formalism.UG.stabGL (lamAf (F := I.F) I.L))
  · simp

theorem isClosedEmbedding_of_preimage_Kg (I I' : AutInst) (φ : I'.Gf →* I.Gf)
    (h : ∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ φ g ∈ I.Kg N) : Topology.IsClosedEmbedding φ := by
  have hpre : (fun N : ℕ => φ ⁻¹' I.Kg N) = I'.Kg := by
    funext N
    ext g
    exact (h N g).symm
  have hb : (nhds (1 : I'.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) fun N => φ ⁻¹' I.Kg N := by
    rw [hpre]
    exact nhds_one_hasBasis_Kg I'
  have hind : Topology.IsInducing φ :=
    IsTopologicalGroup.isInducing_iff_nhds_one.mpr
      (hb.eq_of_same_basis ((nhds_one_hasBasis_Kg I).comap φ))
  have hT' := GlobalTheory.CongTop.adelic_topology I'
  haveI : T2Space I'.Gf := hT'.1
  haveI : T2Space I.Gf := (GlobalTheory.CongTop.adelic_topology I).1
  obtain ⟨hopen1, ⟨K, hK⟩, -⟩ := hT'.2.2.2.2.2.2 1 le_rfl
  have hKcl : IsClosed (I'.Kg 1) := by
    rw [← hK]
    exact K.isClosed_of_isOpen (by rw [hK]; exact hopen1)
  have hcpt : IsCompact (φ ⁻¹' I.Kg 1) := by
    rw [show φ ⁻¹' I.Kg 1 = I'.Kg 1 from congrFun hpre 1]
    exact hT'.2.2.2.1.of_isClosed_subset hKcl fun x hx => hx.1
  have hU : IsOpen (I.Kg 1) := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 1 le_rfl).1
  have h1 : (1 : I.Gf) ∈ I.Kg 1 := mem_of_mem_nhds ((nhds_one_hasBasis_Kg I).mem_of_mem le_rfl)
  exact ⟨hind.isEmbedding, isClosed_range_of_isCompact_preimage φ hind.continuous (I.Kg 1) hU h1 hcpt⟩

theorem isClosedEmbedding_of_conj_Kg : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf),
    (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  intro I I' j xf hj
  let ψ : I'.Gf →* I.Gf := (MulAut.conj xf⁻¹).toMonoidHom.comp j
  have hψ : ∀ g, ψ g = xf⁻¹ * j g * xf := fun g => by simp [ψ, MulAut.conj_apply]
  have hc : Topology.IsClosedEmbedding ψ :=
    isClosedEmbedding_of_preimage_Kg I I' ψ fun N g => by rw [hψ]; exact hj N g
  have e : (j : I'.Gf → I.Gf) = ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)) ∘ ψ := by
    funext g
    simp [hψ, mul_assoc]
  rw [e]
  exact ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)).isClosedEmbedding.comp hc

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConjStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf), (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | exact GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | (intros; apply GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegral
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGlue

open IsDedekindDomain

theorem exists_pow_sat {R : Type*} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R)
    {g : R} (hg : g ≠ 0) :
    ∃ e : ℕ, ∀ x ∈ P.asIdeal ^ e, ∃ s : R, s ∉ P.asIdeal ∧ s * x ∈ Ideal.span {g} := by
  classical
  haveI := P.isPrime
  let Rp := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hI : Ideal.map (algebraMap R Rp) (Ideal.span {g}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ hinj).2 hg
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, fun x hx => ?_⟩
  have hmap : Ideal.map (algebraMap R Rp) (P.asIdeal ^ n) =
      Ideal.map (algebraMap R Rp) (Ideal.span {g}) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, hn]
  have hx' : algebraMap R Rp x ∈ Ideal.map (algebraMap R Rp) (Ideal.span {g}) :=
    hmap ▸ Ideal.mem_map_of_mem _ hx
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl Rp).1 hx'
  refine ⟨s, s.2, ?_⟩
  have h2 : s.1 * x = a.1 := hinj (by rw [map_mul, mul_comm]; exact h)
  rw [h2]; exact a.2

end GlobalTheory.FrameGlue

open IsDedekindDomain in
theorem GlobalTheory.FrameGlue.glue : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  intro E _ _ _ S r Λ g hg f f' hf hloc
  classical
  have hg0 : ((g : 𝓞 E)) ≠ 0 := by exact_mod_cast hg.ne'
  have hfin : {P : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(g : 𝓞 E)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
    · intro P hP
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hP)
  choose e he using fun P : HeightOneSpectrum (𝓞 E) => GlobalTheory.FrameGlue.exists_pow_sat P hg0
  let ξP : HeightOneSpectrum (𝓞 E) → Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun P =>
    if h : (g : 𝓞 E) ∈ P.asIdeal then Classical.choose (hloc P h) else 0
  have hξP : ∀ P (h : (g : 𝓞 E) ∈ P.asIdeal), ξP P = Classical.choose (hloc P h) := by
    intro P h; simp only [ξP, dif_pos h]
  have hcrt : ∀ a b : Fin (r + 1), ∃ y : 𝓞 E, ∀ P (hP : P ∈ hfin.toFinset),
      y - ξP P a b ∈ P.asIdeal ^ e P := by
    intro a b
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
      (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) e
      (fun P _ => P.prime) (fun P _ Q _ hPQ => fun h => hPQ (HeightOneSpectrum.ext h))
      (fun P => ξP P.1 a b)
    exact ⟨y, fun P hP => hy P hP⟩
  choose y hy using hcrt
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else y a b
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], fun b P hP => ?_⟩
  haveI := P.isPrime
  have hPs : P ∈ hfin.toFinset := by simpa using hP
  obtain ⟨hlow, hdiag, hmod⟩ := Classical.choose_spec (hloc P hP)
  rw [← hξP P hP] at hlow hdiag hmod

  have hdiff : ∀ a, ξP P a b - ξ a b ∈ P.asIdeal ^ e P := by
    intro a
    by_cases hba : b < a
    · simp [ξ, hba, hlow a b hba]
    · by_cases hab : a = b
      · subst hab; simp [ξ, hdiag]
      · have := hy a b P hPs
        simp only [ξ, hba, hab, if_false]
        rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 this
  set L := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) with hL
  have key : ∀ (x : 𝓞 E) (v : S.V), ((x : E)) • v = x • v := fun x v => algebraMap_smul E x v
  have hterm : ∀ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a ∈ L := by
    intro a
    obtain ⟨s, hsP, hs⟩ := he P _ (hdiff a)
    obtain ⟨t, ht, htf⟩ := hf P hP a
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hsP ht, ?_⟩
    have : (s * t) • (((ξP P a b - ξ a b : 𝓞 E) : E) • f a) =
        (s * (ξP P a b - ξ a b)) • (t • f a) := by
      rw [key, smul_smul, smul_smul]
      congr 1; ring
    rw [this]
    exact Submodule.smul_mem_smul hs htf
  have hsplit : f' b - frameAct f ξ b =
      (f' b - frameAct f (ξP P) b) + ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a := by
    have hs : ∑ a, ((ξP P a b - ξ a b : 𝓞 E) : E) • f a =
        frameAct f (ξP P) b - frameAct f ξ b := by
      simp only [frameAct, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; rw [sub_smul]
    rw [hs]; abel
  rw [hsplit]
  exact L.add_mem (hmod b) (L.sum_mem fun a _ => hterm a)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegralStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_frame_congruences_unitriangular_integral : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  first | exact @GlobalTheory.FrameGlue.glue | exact GlobalTheory.FrameGlue.glue | (intros; apply GlobalTheory.FrameGlue.glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUnique
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeSubHaar

open Topology

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem uMat_one_flag_measures {n : ℕ} {ε : Fin n → Bool} : _root_.Formalism.MainNotions.S.uMat (1 : _root_.Formalism.REAL.UJ ε) = 1 := by
  have h1 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul (1 : _root_.Formalism.REAL.UJ ε) 1
  have h2 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul_inv (1 : _root_.Formalism.REAL.UJ ε)
  rw [mul_one] at h1
  rw [inv_one, ← h1] at h2
  exact h2

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem comap_subtype_val_haar_properties {n : ℕ} {ε : Fin n → Bool}
    (S : Subgroup (_root_.Formalism.REAL.UJ ε)) (hS : IsClosed (S : Set (_root_.Formalism.REAL.UJ ε))) (d : ℕ)
    (μ : Measure (_root_.Formalism.REAL.UJ ε)) (h : _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ) :
    Measure.map (Subtype.val : S → _root_.Formalism.REAL.UJ ε) (μ.comap Subtype.val) = μ ∧
      (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) ∧
      μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hmap : Measure.map Subtype.val ν = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h1)
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    have key : Measure.map Subtype.val (Measure.map (s * ·) ν) = Measure.map Subtype.val ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul s)]
      have hcomp : (Subtype.val ∘ (s * ·)) =
          (fun g : _root_.Formalism.REAL.UJ ε => (s : _root_.Formalism.REAL.UJ ε) * g) ∘ Subtype.val := by
        funext x; rfl
      rw [hcomp, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact h2 s s.2
    have := congrArg (Measure.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) key
    rwa [hme.comap_map, hme.comap_map] at this
  set f : _root_.Formalism.REAL.UJ ε → ℝ := fun g => √(_root_.Formalism.REAL.hs (_root_.Formalism.MainNotions.S.uMat g - 1)) with hfdef
  have hf : Continuous f := by
    simp only [hfdef, _root_.Formalism.REAL.hs]
    have := _root_.GlobalTheory.GaugeConst.continuous_uMat ε
    fun_prop
  have hf1 : f 1 = 0 := by simp [hfdef, _root_.Formalism.REAL.hs, uMat_one_flag_measures]
  revert h3
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hev := (h3.eventually (isOpen_Ioo.mem_nhds ⟨pos_iff_ne_zero.2 hL0, lt_top_iff_ne_top.2 hLtop⟩)).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  obtain ⟨r, ⟨hpos, htop⟩, hr⟩ := hev.exists
  set B := {g | f g ≤ r} with hBdef
  have hB0 : μ B ≠ 0 := by
    intro h0
    change 0 < μ B / _ at hpos
    rw [h0, ENNReal.zero_div] at hpos
    exact lt_irrefl _ hpos
  have hBtop : μ B ≠ ⊤ := by
    intro h0
    change μ B / _ < ⊤ at htop
    rw [h0, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htop
    exact lt_irrefl _ htop
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by rw [← hme.map_apply, hmap]
  refine ⟨hmap, hinv, ?_, ?_⟩
  · refine ⟨fun K hK => ?_⟩
    have hUo : IsOpen (Subtype.val ⁻¹' {g | f g < r} : Set S) :=
      (isOpen_lt hf continuous_const).preimage continuous_subtype_val
    have hUne : (Subtype.val ⁻¹' {g | f g < r} : Set S).Nonempty :=
      ⟨1, by simp only [Set.mem_preimage, Set.mem_setOf_eq, OneMemClass.coe_one, hf1]; exact hr⟩
    have hUtop : ν (Subtype.val ⁻¹' {g | f g < r}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.preimage_mono
        (show {g | f g < r} ⊆ B from fun g (hg : f g < r) => (le_of_lt hg : f g ≤ r))))
      rw [hνB]; exact hBtop
    exact measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hUo hUne hUtop hK
  · intro h0
    apply hB0
    rw [← hνB, h0, Measure.coe_zero, Pi.zero_apply]


open MeasureTheory NumberField Matrix Finset in
open Topology in
theorem _root_.GlobalTheory.GaugeSubHaar.isGaugeSub_haar : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (_root_.Formalism.REAL.UJ ε)), IsClosed (S : Set (_root_.Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (_root_.Formalism.REAL.UJ ε)), _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  intro n ε S hS d μ hμ
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  obtain ⟨hmap, hinv, hfin, hne⟩ := comap_subtype_val_haar_properties S hS d μ hμ
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hfinμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← hmap, hme.map_apply]
    exact (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top⟩
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.Formalism.REAL.UJ ε) := inferInstance
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨inferInstance, hfinμ, fun μ' hμ' => ?_⟩
  obtain ⟨hmap', hinv', hfin', -⟩ := comap_subtype_val_haar_properties S hS d μ' hμ'
  set ν' := μ'.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν'
  have hcover : ∃ k, ν (compactCovering S k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null hcon
  obtain ⟨k, hk⟩ := hcover
  haveI : ν.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering S k) hk
  haveI : ν.IsHaarMeasure := { }
  have hsmul := Measure.isMulLeftInvariant_eq_smul ν' ν
  set c := ν'.haarScalarFactor ν with hc
  have hμc : μ' = c • μ := by
    rw [← hmap', hsmul, Measure.map_smul c hme.measurable.aemeasurable, hmap]
  obtain ⟨-, -, h3⟩ := hμ
  obtain ⟨-, -, h3'⟩ := hμ'
  rw [hμc] at h3'
  revert h3 h3'
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) →
    Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3 h3'
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr (ENNReal.coe_ne_top (r := c)))
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc] at h3'
  have heq := tendsto_nhds_unique h4 h3'
  have hc1 : (c : ENNReal) = 1 := by
    rw [← ENNReal.mul_left_inj hL0 hLtop, one_mul]
    exact heq
  rw [hμc, ENNReal.coe_eq_one.1 hc1, one_smul]

end GlobalTheory.GaugeSubHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUniqueStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_sigmaFinite_unique : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  first | exact @GlobalTheory.GaugeSubHaar.isGaugeSub_haar | exact GlobalTheory.GaugeSubHaar.isGaugeSub_haar | (intros; apply GlobalTheory.GaugeSubHaar.isGaugeSub_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.NmlCoset

variable {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

theorem X_iso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, (VS D).hT x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [map_add (f := _), h1, h2]
    | smul c y _ h => simp [map_smul, h]
  | zero => simp
  | add x x' _ _ h1 h2 => simp [map_add (f := _), h1, h2]
  | smul c x _ h => simp [h]

theorem X_le_orth : Xsp F ≤ orth (VS D) (Xsp F) := by
  intro y hy
  rw [mem_orth_iff]
  intro x hx
  exact X_iso F x hx y hy

theorem Xa_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

instance Xa_fd (j : ℕ) : FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.Finite.image _ (Set.toFinite _))

theorem maps_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n x ∈ Xflag F (j + 1) := by
  intro x hx
  have h := hn.2.1 j x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xflag F (j + 1)).add_mem (Xa_mono F j h) hx

theorem maps_X {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h := hn.2.2 x (X_le_orth F hx)
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xsp F).add_mem h hx

theorem maps_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ orth (VS D) (Xsp F), n x ∈ orth (VS D) (Xsp F) := by
  intro x hx
  have h := hn.2.2 x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (orth (VS D) (Xsp F)).add_mem (X_le_orth F h) hx

theorem symm_mem_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n.symm x ∈ Xflag F (j + 1) := by
  intro x hx
  have hle : (Xflag F (j + 1)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F (j + 1) := by
    rintro _ ⟨y, hy, rfl⟩
    exact maps_Xa F hn j y hy
  have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n _)
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : n.symm x = y := by rw [← hyx]; simp
  rw [this]; exact hy

theorem one_mem : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, ?_, ?_⟩
  · intro j x _; simp
  · intro x _; simp

theorem mul_mem {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) :
    n * m ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, ?_, ?_⟩
  · intro j x hx
    show n (m x) - x ∈ Xflag F j
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xflag F j).add_mem (hn.2.1 j (m x) (maps_Xa F hm j x hx)) (hm.2.1 j x hx)
  · intro x hx
    show n (m x) - x ∈ Xsp F
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xsp F).add_mem (hn.2.2 (m x) (maps_orth F hm x hx)) (hm.2.2 x hx)

theorem inv_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n⁻¹ ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, ?_, ?_⟩
  · intro j x hx
    show n.symm x - x ∈ Xflag F j
    have hy := symm_mem_Xa F hn j x hx
    have h := hn.2.1 j (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xflag F j).neg_mem h
  · intro x hx
    show n.symm x - x ∈ Xsp F
    have hy : n.symm x ∈ orth (VS D) (Xsp F) := by
      rw [mem_orth_iff] at hx ⊢
      intro v hv
      have hi := hn.1 v (n.symm x)
      rw [LinearEquiv.apply_symm_apply] at hi
      rw [← hi]
      exact hx _ (maps_X F hn v hv)
    have h := hn.2.2 (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xsp F).neg_mem h

end GlobalTheory.HL.NmlCoset

namespace GlobalTheory.HL


open GlobalTheory.HL.NmlCoset in
theorem nmlOf_eq_iff_lin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔
      ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧
        t.lin = n⁻¹ * t₀.lin * m := by
  intro D X Y u u' _ t₀ t
  constructor
  · intro h
    have ht : t.lin ∈ nmlOf Y u u' t := ⟨1, one_mem _, 1, one_mem _, by simp⟩
    rw [h] at ht
    obtain ⟨n, hn, n', hn', e⟩ := ht
    exact ⟨n⁻¹, n', inv_mem _ hn, hn', by simpa using e⟩
  · rintro ⟨n, m, hn, hm, e⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, mul_mem _ ha (inv_mem _ hn), m * b, mul_mem _ hm hb, ?_⟩
      rw [e]; simp only [mul_assoc]
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n, mul_mem _ ha hn, m⁻¹ * b, mul_mem _ (inv_mem _ hm) hb, ?_⟩
      rw [e]; group

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslateStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔ ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m := by
  first | exact @GlobalTheory.HL.nmlOf_eq_iff_lin | exact GlobalTheory.HL.nmlOf_eq_iff_lin | (intros; apply GlobalTheory.HL.nmlOf_eq_iff_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReading
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtMatInjective
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    have hs' : 1 ≤ s' := (h' (t', s') (by simp)).2
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    simp only [ptEntry] at k0
    rw [ite_eq_left (by omega), ite_eq_left (by omega)] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    rcases hss with ⟨rfl, rfl⟩
    apply congrArg (List.cons (t, s))
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have shifted := k (a + s) (by omega) (b + s) (by omega)
    have outside : ¬ (a + s < s ∧ b + s < s) := by omega
    have inside : s ≤ a + s ∧ s ≤ b + s := by omega
    simpa only [ptEntry, ite_eq_right outside, ite_eq_left inside, Nat.add_sub_cancel] using shifted

theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

end GlobalTheory.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReading
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinScale

open Formalism.L2.SG.RealObj

theorem ptEntry_row_zero {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (a b : ℕ), a < b → b < (bs.map Prod.snd).sum →
      blkOf bs a = blkOf bs b → ∃ c, c < b ∧ ∀ j, j ≤ c → Formalism.MainNotions.S.ptEntry bs c j = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro a b hab hb hbl
    simp at hb
  | cons block rest ih =>
    obtain ⟨t, s⟩ := block
    intro a b hab hb hbl
    by_cases ha : a < s
    · by_cases hbs : b < s
      · refine ⟨0, by omega, fun j hj => ?_⟩
        have hj0 : j = 0 := by omega
        subst hj0
        have hs : 0 < s := by omega
        simp only [Formalism.MainNotions.S.ptEntry]
        rw [if_pos ⟨hs, hs⟩, if_neg (by omega)]
      · exfalso
        simp [blkOf, ha, hbs] at hbl
    · have hbs : ¬ b < s := by omega
      simp only [blkOf, ha, hbs, if_false] at hbl
      have hbl' : blkOf rest (a - s) = blkOf rest (b - s) := by omega
      have hb' : b - s < (rest.map Prod.snd).sum := by simp at hb; omega
      obtain ⟨c, hc, hz⟩ := ih (a - s) (b - s) (by omega) hb' hbl'
      refine ⟨c + s, by omega, fun j hj => ?_⟩
      simp only [Formalism.MainNotions.S.ptEntry]
      rw [if_neg (by omega)]
      split_ifs with h
      · have hcs : c + s - s = c := by omega
        rw [hcs]
        exact hz _ (by omega)
      · rfl

theorem isEmpty_freeE_of_reg {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hreg : RegX X u u' γ) (hrep : IsPtRep X u u' w γ) :
    IsEmpty (FreeE w) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hbl⟩ := p
  have hab' : a.1 < b.1 := hab
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hb := b.2
  obtain ⟨c, hcb, hz⟩ := ptEntry_row_zero w.1 a.1 b.1 hab' (by rw [hsum]; exact b.2) hbl
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hle : c + 1 ≤ D.R.rS + 1 := by omega
  apply (hreg v).1 (c + 1) (by omega) (by omega)
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hle]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨c, by omega⟩
  intro j
  simp only [Matrix.submatrix_apply]
  have hrow := congrFun (congrFun (hrep v) (Fin.castLE hle ⟨c, by omega⟩)) (Fin.castLE hle j)
  simp only [ptC, Formalism.MainNotions.S.ptMat, Matrix.map_apply, Formalism.L2.SG.RealObj.ZhatO, Fin.val_castLE] at hrow
  rw [hz j.1 (by omega), map_zero, map_zero] at hrow
  rcases mul_eq_zero.mp hrow with h | h
  · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact h

theorem ptRep_unique {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) {w w' : Point D.host.E (D.R.rS + 1)}
    {γ : X.B.I.Ginf} (h : IsPtRep X u u' w γ) (h' : IsPtRep X u u' w' γ) : w = w' := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have e := (h v).symm.trans (h' v)
  apply GlobalTheory.IntTerm.ptMat_injective
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun e i) j
  simp only [ptC, Matrix.map_apply] at hij
  exact X.ιE.symm.injective ((X.B.I.φ v).injective hij)

theorem one_le_g {D : D7} (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem scale_pin : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X u u'
  have hg : (1 : NNReal) ≤ (X.B.g : NNReal) := by exact_mod_cast one_le_g X
  let sc : X.B.I.Ginf → NNReal := fun γ =>
    if h : ∃ w, IsPtRep X u u' w γ then ((X.B.g : NNReal) ^ (D.R.f * Fintype.card (FreeE h.choose)))⁻¹ else 1
  refine ⟨sc, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [sc]
    split_ifs with h
    · have := isEmpty_freeE_of_reg X u u' _ γ hγ h.choose_spec
      simp [Fintype.card_eq_zero]
    · rfl
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos hg) _)
    · exact one_pos
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    · exact le_rfl
  · rintro w ⟨γ0, hγ0⟩
    have hex0 : ∃ γ, IsPtRep X u u' w γ := ⟨γ0, hγ0⟩
    have hw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW
      rw [dif_pos hex0]
      exact hex0.choose_spec
    have hex : ∃ w', IsPtRep X u u' w' (gamW X u u' w) := ⟨w, hw⟩
    simp only [sc, dif_pos hex]
    rw [ptRep_unique X u u' hex.choose_spec hw]
    push_cast
    rfl

end GlobalTheory.PinScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReadingStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_normalised_localReading : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  first | exact @GlobalTheory.PinScale.scale_pin | exact GlobalTheory.PinScale.scale_pin | (intros; apply GlobalTheory.PinScale.scale_pin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulTheta
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulThetaStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  first | exact @GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | exact GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | (intros; apply GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta <;> assumption)
end
end
