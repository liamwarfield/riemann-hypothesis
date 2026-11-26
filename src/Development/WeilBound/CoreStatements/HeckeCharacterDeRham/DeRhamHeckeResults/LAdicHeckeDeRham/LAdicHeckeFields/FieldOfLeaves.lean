module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateScaledIterateTends
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesCommuteLinear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateCommutingSeriesUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateEventuallyZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFBOfNear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesDeRhamPeriod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsTer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTied
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitary
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTHodge

theorem exists_lubinTateChar : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 :=
  fun K => GlobalTheory.CompanionTheory.LTHodge.CharEx.exists_ltChar K

end GlobalTheory.CompanionTheory.LTHodge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitaryStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubin_tate_character_unitary : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | exact GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | (intros; apply GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtension
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical Topology

namespace GlobalTheory.CompanionTheory.EmbBridge

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem tendsto_pow_zero (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E)
    (hx : Valued.v x < 1) : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  have : ∃ n : ℕ, (Valued.v x) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    exact exists_pow_lt₀ hx (Units.mk0 _ hpos)
  obtain ⟨n, hn⟩ := this
  refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩)
  have e : Valued.v (x ^ m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    rw [map_pow]
    exact (pow_le_pow_of_le_one zero_le' hx.le hm).trans_lt hn
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 e

theorem norm_lt_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : Valued.v x < 1) : ‖φ x‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ x ^ n) Filter.atTop (𝓝 0) := by
    have := (hφ.tendsto 0).comp (tendsto_pow_zero w x hx)
    simpa [Function.comp_def, map_pow] using this
  by_contra hge
  have h2 : ∀ n : ℕ, 1 ≤ ‖φ x ^ n‖ := fun n => by
    rw [norm_pow]; exact one_le_pow₀ (not_lt.1 hge)
  have h3 := h1.norm
  rw [norm_zero] at h3
  have := ge_of_tendsto' h3 h2
  linarith

theorem v_le_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ < 1) : Valued.v x ≤ 1 := by
  by_contra hgt
  have hgt' := not_le.1 hgt
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt'
  have h2 := norm_lt_one w φ hφ _ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx0)
  have := (one_lt_inv₀ hpos).2 hx
  linarith

theorem exists_v_lt_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ π : w.adicCompletion E, π ≠ 0 ∧ Valued.v π < 1 := by
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine ⟨algebraMap E _ (y : E), ?_, ?_⟩
  · simpa using hy0
  · have h : w.valuation E (y : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w y).2 hyw
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (y : E)
    rw [e]
    exact h

theorem isInducing (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    Topology.IsInducing φ := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa using (hφ.tendsto 0).le_comap) ?_
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨π, hπ0, hπ⟩ := exists_v_lt_one w
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (Valued.v π) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    exists_pow_lt₀ hπ (Units.mk0 _ hpos)
  have hε : 0 < ‖φ (π ^ n)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 (pow_ne_zero n hπ0))
  refine Filter.mem_comap.2 ⟨Metric.ball 0 ‖φ (π ^ n)‖, Metric.ball_mem_nhds _ hε, fun x hx => hγ ?_⟩
  have hx' : ‖φ x‖ < ‖φ (π ^ n)‖ := by simpa using hx
  have h1 : ‖φ (x / π ^ n)‖ < 1 := by
    rw [map_div₀, norm_div]
    exact (div_lt_one hε).2 hx'
  have h2 := v_le_one w φ hφ _ h1
  have hv : 0 < Valued.v π ^ n := zero_lt_iff.2 (pow_ne_zero n ((Valuation.ne_zero_iff _).2 hπ0))
  rw [map_div₀, map_pow, div_le_one₀ hv] at h2
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 (h2.trans_lt hn)

end GlobalTheory.CompanionTheory.EmbBridge

namespace GlobalTheory.CompanionTheory.EmbBridge

theorem embeddings_of_continuous : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI LL' hLL j
  have hKL : Bw.Kw.1 ≤ LL'.1 := fun x hx => hLL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)
  obtain ⟨⟨φ, hφc⟩, hφ, -⟩ := GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced w A hA O Bw hI LL'
    (IntermediateField.inclusion hKL)
  have hφE : ∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y) := fun y => hφ y
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hKc : IsClosed (Bw.Kw.1 : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra)
  have hmem : ∀ x, φ x ∈ Bw.Kw.1 := fun x =>
    (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x
      (hKc.preimage hφc) (fun y => by
        show φ _ ∈ Bw.Kw.1
        rw [hφE]; exact Bw.j_E y)
  have hind := isInducing w φ hφc
  have hrc : IsClosed (Set.range φ) :=
    (AddMonoidHom.isUniformInducing_of_isInducing (f := φ.toAddMonoidHom) hind).isComplete_range.isClosed
  have hsurj : ∀ k : ↥Bw.Kw.1, ∃ x, φ x = k := fun k => by
    have h1 : (k : Om l) ∈ closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) := Bw.j_dense k.2
    have h2 : (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ Set.range φ := by
      rintro _ ⟨y, rfl⟩
      exact ⟨_, hφE y⟩
    exact hrc.closure_subset_iff.2 h2 h1
  let φ' : w.adicCompletion E →+* ↥Bw.Kw.1 := φ.codRestrict Bw.Kw.1 hmem
  have hbij : Function.Bijective φ' := ⟨fun a b h => φ.injective (congrArg Subtype.val h), fun k => by
    obtain ⟨x, hx⟩ := hsurj k
    exact ⟨x, Subtype.ext hx⟩⟩
  let e : w.adicCompletion E ≃+* ↥Bw.Kw.1 := RingEquiv.ofBijective φ' hbij
  have hei : Topology.IsInducing e := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val hind
    exact hφc.subtype_mk hmem
  have hes : Continuous e.symm := (e.toEquiv.toHomeomorphOfIsInducing hei).symm.continuous
  let ψ : ↥Bw.Kw.1 →+* Om l := j.1.comp (e.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hψc : Continuous ψ := j.2.comp hes
  have hlin : ∀ a : ℚ_[l], ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) = algebraMap ℚ_[l] (Om l) a := fun a => by
    have c1 : Continuous fun a : ℚ_[l] => ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) :=
      hψc.comp (continuous_algebraMap ℚ_[l] ↥Bw.Kw.1)
    have c2 : Continuous fun a : ℚ_[l] => algebraMap ℚ_[l] (Om l) a := continuous_algebraMap ℚ_[l] (Om l)
    refine congrFun ((Padic.denseRange_ratCast l).equalizer c1 c2 (funext fun q => ?_)) a
    simp
  let μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := { ψ with commutes' := hlin }
  let τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := μ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split μ x)
  have hτ : ∀ x (hx : φ x ∈ Bw.Kw.1), ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x := fun x hx => by
    have : e.symm ⟨φ x, hx⟩ = x := e.symm_apply_apply x
    show j.1 (e.symm ⟨φ x, hx⟩) = j.1 x
    rw [this]
  have key : ∀ y : E, ((τ (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y) : ↥LL'.1) : Om l) = j.1 (algebraMap E _ y) := fun y => by
    have e1 : GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y = ⟨φ (algebraMap E _ y), hmem _⟩ := Subtype.ext (hφE y).symm
    rw [e1]
    exact hτ _ _
  have hd : DenseRange (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw) := fun k => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.range_comp]
    exact Bw.j_dense k.2
  have hc : ∀ t : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, Continuous fun x => ((t x : ↥LL'.1) : Om l) := fun t => by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a h => ?_⟩
    have h' : ‖(a : Om l) - (b : Om l)‖ < ε := by rwa [← dist_eq_norm]
    rw [dist_eq_norm]
    have e2 : ((t a : ↥LL'.1) : Om l) - ((t b : ↥LL'.1) : Om l) = ((t (a - b) : ↥LL'.1) : Om l) := by
      simp
    rw [e2, GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom]
    exact h'
  refine ⟨φ, τ, hφc, hφE, fun x => ⟨hmem x, hτ x _⟩, fun τ' => ⟨fun h => ?_, ?_⟩⟩
  · refine AlgHom.ext fun x => Subtype.ext (congrFun (hd.equalizer (hc τ') (hc τ) (funext fun y => ?_)) x)
    exact (h y).symm.trans (key y).symm
  · rintro rfl y
    exact (key y).symm

end GlobalTheory.CompanionTheory.EmbBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtensionStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_galois_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  first | exact @GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | exact GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | (intros; apply GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompat
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeLocal

theorem isLAdicOf_localIdele {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ) (h : IsLAdicOf art ι χ n μ) (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) (σ : G E Ω) (hx : art (localIdele E w x) = toAb E Ω σ) :
    ((μ σ : (Qbar l)ˣ) : Qbar l) =
      ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  rw [h _ σ hx, infPow_localIdele, inv_one, mul_one, lPow_localIdele]

end GlobalTheory.CompanionTheory.HeckeLocal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompatStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_character_artin_compat : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (σ : G E Ω), art (localIdele E w x) = toAb E Ω σ →
    ((μ σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | exact GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | (intros; apply GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnits
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.InertOpen

section Local

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finiteSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

theorem continuous_localIdele' (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finiteSingle v)

theorem isOpen_valued_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen {x : w.adicCompletion L | Valued.v x < 1} := by
  have := Valued.isOpen_ball (w.adicCompletion L) 1
  simpa [Valuation.restrict_lt_one_iff] using this

theorem isCompact_setOf_isUnitAt (w : HeightOneSpectrum (𝓞 L)) :
    IsCompact {x : (w.adicCompletion L)ˣ | IsUnitAt w x} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : (w.adicCompletion L)ˣ → w.adicCompletion L) '' {x | IsUnitAt w x} =
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) \ {x | Valued.v x < 1} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, not_lt, IsUnitAt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.le, hx.ge⟩
    · rintro ⟨h1, h2⟩
      have hy : Valued.v y = 1 := le_antisymm h1 h2
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers L w).diff (isOpen_valued_lt_one w)

end Local

section Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem continuous_toAb' : Continuous (toAb E Ω) := continuous_quot_mk

theorem hausdorff_absolute_galois_abelianization : T2Space (Gab E Ω) := by
  haveI : Algebra.IsIntegral E Ω := (IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isIntegral
  haveI : T2Space (G E Ω) := krullTopology_t2
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

end Gal

end GlobalTheory.CompanionTheory.InertOpen

namespace GlobalTheory.CompanionTheory.InertOpen

theorem exists_openSubgroup_ine_art_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  intro E Ω _ _ _ _ _ l _ art hart w A hA U hUo _
  haveI := hausdorff_absolute_galois_abelianization (E := E) (Ω := Ω)
  let f : (w.adicCompletion E)ˣ →* Gab E Ω := art.comp (localIdele E w)
  have hf : Continuous f := hart.quot.continuous.comp (continuous_localIdele' w)
  let K : Set (w.adicCompletion E)ˣ := {y | ∃ u ∈ U, f u = f y}
  have hK : IsOpen K := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨u, hu, hux⟩
    refine ⟨{y | x⁻¹ * y ∈ U}, ?_, hUo.preimage (continuous_const.mul continuous_id), ?_⟩
    · intro y hy
      refine ⟨u * (x⁻¹ * y), U.mul_mem hu hy, ?_⟩
      rw [map_mul, hux, ← map_mul, mul_inv_cancel_left]
    · show x⁻¹ * x ∈ U
      rw [inv_mul_cancel]
      exact U.one_mem
  let C : Set (Gab E Ω) := f '' ({x | IsUnitAt w x} \ K)
  have hC : IsClosed C := (((isCompact_setOf_isUnitAt w).diff hK).image hf).isClosed
  have h1 : (1 : Gab E Ω) ∉ C := by
    rintro ⟨y, ⟨-, hyK⟩, hy⟩
    exact hyK ⟨1, U.one_mem, by rw [map_one, hy]⟩
  have hW : (toAb E Ω) ⁻¹' Cᶜ ∈ nhds (1 : G E Ω) :=
    (hC.isOpen_compl.preimage continuous_toAb').mem_nhds (by simpa using h1)
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 hW
  refine ⟨M.fixingSubgroup, M.fixingSubgroup_isOpen, fun σ hσV hσI => ?_⟩
  obtain ⟨x, hxu, hx⟩ := (hart.ine w A hA (toAb E Ω σ)).2 ⟨σ, hσI, rfl⟩
  have hnot : toAb E Ω σ ∉ C := hMs hσV
  by_contra hne
  apply hnot
  refine ⟨x, ⟨hxu, ?_⟩, hx⟩
  rintro ⟨u, hu, hux⟩
  exact hne ⟨u, hu, hux.trans hx⟩

end GlobalTheory.CompanionTheory.InertOpen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnitsStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_open_subgroup_local_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  first | exact @GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | exact GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | (intros; apply GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units <;> assumption)
end
end
end

section -- merged from Development.WeilBound.CoreStatements.HeckeCharacterDeRham.DeRhamHeckeResults.LAdicHeckeDeRham.LAdicHeckeFields.Reduce
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace PositivityTheory.SecR.Hladr

def LTPeriods : Prop := ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
      Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) → HasPeriods P K χ
end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr
theorem repE_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l)
    (ψ : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp (ψ.comp Bw.e.toMonoidHom)) = lineRep ψ := by
  apply MonoidHom.ext
  intro g
  simp [LocBridge.repE, lineRep]

theorem lubinTate_at_embedding (HP : LTPeriods) : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ lam : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ,
      Continuous (fun g => ((lam g : ↥LL'.1) : Qbar l)) ∧ (∀ g, ‖((lam g : ↥LL'.1) : Qbar l)‖ = 1) ∧
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' lam
        (fun τ' => if IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' then -1 else 0) ∧
      ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
        art (localIdele E w x) = toAb E Ω σ → ((lam σ : ↥LL'.1) : Qbar l) = j.1 x := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A hA O _ _ _ Bw hI art hart LL' hLL j
  obtain ⟨χ, hχ, hc, hn⟩ := GlobalTheory.T.exists_lubin_tate_character_unitary Bw.Kw
  obtain ⟨φ, τ, hφc, hφ, hτ, hu⟩ := GlobalTheory.T.local_galois_embedding_extension w A hA O Bw hI LL' hLL j
  have hper := HP P AI hT Bw.Kw χ hχ hc
  have hsplit : ∀ (μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) (x : ↥Bw.Kw.1), μ x ∈ LL'.1 :=
    fun μ x => hLL (Bw.LL_split μ x)
  obtain ⟨hd, hm⟩ := GlobalTheory.T.de_rham_rank_lubin_tate_line P AI hT Bw.Kw LL' hsplit χ hper τ
  set ψ : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ := (Units.map ((τ : ↥Bw.Kw.1 →+* ↥LL'.1) : ↥Bw.Kw.1 →* ↥LL'.1)).comp χ with hψ
  have hnorm : ∀ x : ↥Bw.Kw.1, ‖((τ x : ↥LL'.1) : Om l)‖ = ‖(x : Om l)‖ := fun x =>
    GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom τ x
  refine ⟨ψ.comp Bw.e.toMonoidHom, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · have hc' : Continuous (fun g : ↥(Dec (F := E) A) =>
        (((χ (Bw.e g) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l)) := hc.comp Bw.e_cont
    have hc'' := Metric.continuous_iff'.1 hc'
    refine Metric.continuous_iff'.2 fun b ε hε => ?_
    filter_upwards [hc'' b ε hε] with a h2
    rw [dist_eq_norm] at h2 ⊢
    have e : (((ψ.comp Bw.e.toMonoidHom) a : (↥LL'.1)ˣ) : ↥LL'.1).1 -
        (((ψ.comp Bw.e.toMonoidHom) b : (↥LL'.1)ˣ) : ↥LL'.1).1 =
        ((τ (((χ (Bw.e a) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) - ((χ (Bw.e b) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1)) : ↥LL'.1) : Om l) := by
      simp [hψ]
    refine lt_of_eq_of_lt ?_ h2
    refine (congrArg norm e).trans ?_
    rw [hnorm]
    rfl
  · intro g
    simpa [hψ] using (hnorm _).trans (hn (Bw.e g))
  · set_option synthInstance.maxHeartbeats 100000 in
    show Module.finrank _ ↥(DdR (P.PD Bw.Kw) (Bw.repE LL' _)) = _
    rw [repE_eq]; exact hd
  · intro τ' a
    show multV (P.PD Bw.Kw) (Bw.repE LL' _) τ' a = _
    rw [repE_eq, hm τ' a]
    simp only [hu τ']
  · intro x σ hx hσ hart'
    have h1 := GlobalTheory.CompanionTheory.LTLink.link w A hA O Bw hI art hart χ hχ φ hφc hφ x σ hx hσ hart'
    obtain ⟨hxk, hxj⟩ := hτ (x : w.adicCompletion E)
    rw [← hxj]
    have : (χ (Bw.e σ) : ↥Bw.Kw.1) = ⟨φ x, hxk⟩ := Subtype.ext h1
    simp [hψ, this]
end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

theorem coe_units_prod_zpow_hlc {ι' G : Type} [Fintype ι'] [Group G] {K L : Type} [Field K] [Field L]
    (f : K →+* L) (lam : ι' → G →* Kˣ) (m : ι' → ℤ) (g : G) :
    f (((∏ j, lam j ^ m j) g : Kˣ) : K) = ∏ j, f ((lam j g : Kˣ) : K) ^ m j := by
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]

end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

open PositivityTheory.HodgeLocalCharacter.HLC

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
  (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied6 l P AI))
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A w)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
  (hI : GlobalTheory.Pst.Induces Bw) (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1)

include hT hA hI hLL

theorem isdRJ_one_hlc : IsdRJ Bw P LL' 1 0 := by
  refine GlobalTheory.T.local_character_induced_agree P AI (UpperTheory.Lit.Cmp.locTied_of6 l P AI hT) w A hA O Bw hI LL' hLL 1 ?_ ?_ ⊤ ?_ ?_
  · simp only [MonoidHom.one_apply, Units.val_one]
    exact continuous_const
  · intro g
    simp
  · rw [Subgroup.coe_top]
    exact isOpen_univ
  · intro σ _ _
    rfl

theorem isdRJ_zpow_hlc {ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ} {J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ}
    (h : IsdRJ Bw P LL' ψ J) (k : ℤ) : IsdRJ Bw P LL' (ψ ^ k) (k • J) := by
  refine Int.induction_on k ?_ ?_ ?_
  · simpa using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL
  · intro i ih
    rw [zpow_add_one, add_smul, one_smul]
    exact GlobalTheory.T.local_character_induced_tied P AI (UpperTheory.Lit.Cmp.locTied_of6 l P AI hT) w A hA O Bw hI LL' hLL _ _ _ _ ih h
  · intro i ih
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact GlobalTheory.T.local_character_induced_tied P AI (UpperTheory.Lit.Cmp.locTied_of6 l P AI hT) w A hA O Bw hI LL' hLL _ _ _ _ ih
      (GlobalTheory.T.local_character_induced_tied_six P AI hT w A hA O Bw hI LL' hLL _ _ h)

theorem isdRJ_prod_hlc {ι' : Type} (s : Finset ι') (ψ : ι' → (↥(Dec (F := E) A) →* (↥LL'.1)ˣ))
    (J : ι' → (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ) (h : ∀ i ∈ s, IsdRJ Bw P LL' (ψ i) (J i)) :
    IsdRJ Bw P LL' (∏ i ∈ s, ψ i) (∑ i ∈ s, J i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.local_character_induced_tied P AI (UpperTheory.Lit.Cmp.locTied_of6 l P AI hT) w A hA O Bw hI LL' hLL _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Jumps

end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

open PositivityTheory.HodgeLocalCharacter.HLC

theorem field_of_ltPeriods (HP : LTPeriods) : GlobalTheory.Published.HeckeLAdicCharacterDeRham := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A hA O _ _ _ Bw hI
  have hT6 := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  obtain ⟨LL', ψ, hLL, hmod, hψμ, hψc, hψn⟩ := GlobalTheory.T.local_character_finite_extension μ hμ w A hA O Bw
  have : Finite {j : w.adicCompletion E →+* Qbar l // Continuous j} := finite_contEmb w
  have : Fintype {j : w.adicCompletion E →+* Qbar l // Continuous j} := Fintype.ofFinite _
  choose lam hlc hln hlJ hlx using
    fun j : {j : w.adicCompletion E →+* Qbar l // Continuous j} =>
      lubinTate_at_embedding HP P AI hT6 w A hA O Bw hI art hart LL' hLL j
  let nj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ :=
    fun j => n ((ι.toRingHom.comp j.1).comp (algebraMap E (w.adicCompletion E)))
  let Jj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ :=
    fun j τ' => if IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' then -1 else 0
  let Λ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ := ∏ j, lam j ^ nj j
  have hΛ : IsdRJ Bw P LL' Λ (∑ j, nj j • Jj j) :=
    isdRJ_prod_hlc P AI hT6 hA Bw hI LL' hLL _ _ _ fun j _ =>
      isdRJ_zpow_hlc P AI hT6 hA Bw hI LL' hLL (hlJ j) (nj j)
  have hne : ∀ j g, ((lam j g : ↥LL'.1) : Qbar l) ≠ 0 := fun j g =>
    norm_ne_zero_iff.mp (by rw [hln j g]; exact one_ne_zero)
  have hΛv : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) = ∏ j, ((lam j g : ↥LL'.1) : Qbar l) ^ nj j := fun g =>
    coe_units_prod_zpow_hlc LL'.1.val.toRingHom lam nj g
  have hΛc : Continuous fun g => ((Λ g : ↥LL'.1) : Qbar l) := by
    simp only [hΛv]
    exact continuous_finsetProd _ fun j _ => (hlc j).zpow₀ _ fun g => Or.inl (hne j g)
  have hΛne : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) ≠ 0 := fun g => by
    rw [hΛv]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hne j g)
  let φ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ := ψ * Λ⁻¹
  have hφv : ∀ g, ((φ g : ↥LL'.1) : Qbar l) = ((ψ g : ↥LL'.1) : Qbar l) * ((Λ g : ↥LL'.1) : Qbar l)⁻¹ := by
    intro g
    simp [φ]
  have hφc : Continuous fun g => ((φ g : ↥LL'.1) : Qbar l) := by
    simp only [hφv]
    exact hψc.mul (hΛc.inv₀ hΛne)
  have hφn : ∀ g, ‖((φ g : ↥LL'.1) : Qbar l)‖ = 1 := by
    intro g
    rw [hφv, norm_mul, norm_inv, hψn, hΛv, norm_prod]
    simp [norm_zpow, hln]
  obtain ⟨U, hUo, hUu, hUχ⟩ := GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one χ w
  obtain ⟨V, hVo, hV⟩ := GlobalTheory.T.galois_open_subgroup_local_units (l := l) art hart w A hA U hUo hUu
  have hφ0 : IsdRJ Bw P LL' φ 0 := by
    refine GlobalTheory.T.local_character_induced_agree P AI hT w A hA O Bw hI LL' hLL φ hφc hφn V hVo ?_
    intro σ hσV hσI
    obtain ⟨x, hxU, hx⟩ := hV σ hσV hσI
    have h1 := GlobalTheory.T.galois_character_artin_compat ι art χ n μ hL w x σ hx
    rw [hUχ x hxU, Units.val_one, map_one, one_mul] at h1
    have h2 : ∀ j, ((lam j σ : ↥LL'.1) : Qbar l) = j.1 x := fun j => hlx j x σ (hUu x hxU) hσI hx
    have hψΛ : ((ψ σ : ↥LL'.1) : Qbar l) = ((Λ σ : ↥LL'.1) : Qbar l) := by
      rw [hψμ, h1, hΛv]
      simp only [h2]
      unfold locPow
      rw [finprod_eq_prod_of_fintype]
    have hψΛ' : ψ σ = Λ σ := Units.ext (Subtype.ext hψΛ)
    show ψ σ * Λ⁻¹ σ = 1
    rw [MonoidHom.inv_apply, hψΛ', mul_inv_cancel]
  have hψJ : IsdRJ Bw P LL' ψ (0 + ∑ j, nj j • Jj j) := by
    have := GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL φ Λ _ _ hφ0 hΛ
    simpa [φ] using this
  refine ⟨⟨LL', _, hmod, hψJ.1⟩, ?_⟩
  intro τ LL'' τ'' hτ
  let τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
    (LL''.1.val.comp τ'').codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split _ x)
  have hτ' : IsInduced Bw τ τ' := fun x => hτ x
  refine ⟨LL', _, hmod, hψJ.1, τ', hτ', fun a => ?_⟩
  rw [hψJ.2 τ' a]
  obtain ⟨j0, hj0, huniq⟩ := GlobalTheory.T.unique_embedding_extension (l := l) w A hA O Bw hI LL' τ'
  have hj0E : j0.1.comp (algebraMap E (w.adicCompletion E)) = τ :=
    RingHom.ext fun x => (hj0 x).trans (hτ' x).symm
  have hsum : (0 + ∑ j, nj j • Jj j) τ' = -n (ι.toRingHom.comp τ) := by
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, zero_add]
    rw [Finset.sum_eq_single j0]
    · simp only [Jj, if_pos hj0, nj, smul_eq_mul, mul_neg, mul_one, ← hj0E, RingHom.comp_assoc]
    · intro b _ hb
      have : ¬ IsInduced Bw (b.1.comp (algebraMap E (w.adicCompletion E))) τ' := fun h => hb (huniq b h)
      simp only [Jj, if_neg this, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  rw [hsum, Multiset.count_singleton]
  split_ifs <;> simp
end PositivityTheory.SecR.Hladr
end
end

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding IsPlaceOver Dec G
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace PositivityTheory.SecR.Hladr2

def TiltLeaf : Prop :=  ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖)

def ProductLeaf : Prop :=  ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1)

variable {l : ℕ} [Fact l.Prime]

theorem actB_rB (g : GQ l) (x : Om l) : actB g (rB l x) = rB l (g x) :=
  GroundTheory.PAdicHodge.gal_smul_algClToBdR (Formalism.Per6.toBot g) x

theorem actB_tch (g : GQ l) (x : Tl l) : actB g (tch l x) = tch l (actT g x) := by
  change Formalism.Per6.toBot g • (GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l (WittVector.teichmuller l x)) = _
  rw [GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus, GroundTheory.PAdicHodge.AInf.gal_smul_teichmuller]
  rfl

theorem thB_rB (x : Om l) : thB l (rB l x) = ((x : Om l) : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l x

theorem thB_actB_zero (g : GQ l) {x : Formalism.Per6.BdRp l} (hx : thB l x = 0) : thB l (actB g x) = 0 := by
  have h := GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul (Formalism.Per6.toBot g) x
  have h2 : GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l x = 0 := by
    rw [← hx]; exact (GroundTheory.PAdicHodge.thetaAlgHom_apply l x).symm
  rw [h2, smul_zero] at h
  rw [← h]
  exact GroundTheory.PAdicHodge.thetaAlgHom_apply l _

theorem actB_FB (g : GQ l) (k : ℕ) (x : Formalism.Per6.BdRp l) (hx : x ∈ FB l k) : actB g x ∈ FB l k := by
  have h1 : Ideal.map (actB g) (RingHom.ker (thB l)) ≤ RingHom.ker (thB l) :=
    Ideal.map_le_iff_le_comap.2 fun y hy => thB_actB_zero g hy
  have h2 := Ideal.mem_map_of_mem (actB g) hx
  rw [FB, Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  simp only [tch, map_pow]

theorem near_pow_of_sub {B : Type} [CommRing B] {S : Subring B} {ϖ : B} {a b : B} (ha : a ∈ S) (hb : b ∈ S)
    (h : ∃ s ∈ S, a - b = ϖ * s) (M : ℕ) : ∃ s ∈ S, a ^ M - b ^ M = ϖ * s := by
  obtain ⟨s, hs, e⟩ := h
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : ↥S) ⟨b, hb⟩ M
  refine ⟨s * c, S.mul_mem hs c.2, ?_⟩
  have h3 : a ^ M - b ^ M = (a - b) * (c : B) := by simpa using congrArg Subtype.val hc
  rw [h3, e]; ring

theorem iter_near {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {Q b : B} (hQ : Q ∈ S)
    (hb : b ∈ S) (h : ∃ s ∈ S, Q - b = ϖ * s) (n : ℕ) :
    ltIter ϖ q n Q ∈ S ∧ ∃ s ∈ S, ltIter ϖ q n Q - b ^ (q ^ n) = ϖ * s := by
  induction n with
  | zero => simpa [ltIter] using ⟨hQ, h⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + ltIter ϖ q n Q ^ q := by
      simp only [ltIter, Function.iterate_succ_apply']
    have hbn : b ^ (q ^ n) ∈ S := S.pow_mem hb _
    obtain ⟨s, hs, e2⟩ := near_pow_of_sub h1 hbn h2 q
    refine ⟨by rw [e]; exact S.add_mem (S.mul_mem hϖ h1) (S.pow_mem h1 _), ltIter ϖ q n Q + s,
      S.add_mem h1 hs, ?_⟩
    rw [e, pow_succ q n, pow_mul]
    linear_combination e2

end PositivityTheory.SecR.Hladr2

namespace PositivityTheory.SecR.Hladr2
variable {l : ℕ} [Fact l.Prime]

theorem pre_period (HT : TiltLeaf) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l)
    (hD : LTData K χ π z) (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)))
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ∃ t, PrePer K χ μ t := by
  have hπ : Irreducible π := hD.1
  obtain ⟨hq2, hlq, hπl, hnπ, hnμ⟩ := GlobalTheory.T.uniformizer_properties_residue K π hπ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let K' : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l)
  haveI : FiniteDimensional ℚ_[l] K' := inferInstance
  haveI : Normal ℚ_[l] K' := inferInstance
  obtain ⟨S, hW, hO, hG, hI, hE⟩ := GlobalTheory.CompanionTheory.LTPer.lattice_main K'
  have hμK : ∀ x, μ x ∈ K' := fun x => AlgHom.fieldRange_le_normalClosure μ ⟨x, rfl⟩
  have hint : ∀ c : ↥(OL K), IsIntegral ℤ_[l] (μ (c : ↥K.1)) := fun c =>
    IsIntegral.map (μ.restrictScalars ℤ_[l]) c.2
  have hoB : ∀ c, oB K μ c ∈ S := fun c => hO _ (hμK _) (hint c)
  have hne : μ (π : ↥K.1) ≠ 0 := by
    have h0 : (π : ↥K.1) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    exact (map_ne_zero_iff μ μ.toRingHom.injective).2 h0
  obtain ⟨E, hnot⟩ := hE _ (hμK _) (hint π) hne (hnμ μ)
  have hϖe : rB l (μ (π : ↥K.1)) = oB K μ π := rfl
  rw [hϖe] at E hnot
  obtain ⟨ϖ', hϖ'⟩ := E.unit.exists_right_inv
  set ϖ := oB K μ π with hϖ
  obtain ⟨r, v, hvq, hv0, hv1, hr, hrg, hrz⟩ := HT K χ π z hD μ
  set q := qOf π with hq
  have hqd : ∃ s ∈ S, (q : Formalism.Per6.BdRp l) = ϖ * s := by
    obtain ⟨d, hd⟩ := hπl
    obtain ⟨q', hq'⟩ := hlq
    refine ⟨oB K μ (d * (q' : ↥(OL K))), hoB _, ?_⟩
    rw [hϖ, ← map_mul, ← mul_assoc, ← hd, hq']
    simp
  have hvS : ∀ n, tch l (v n) ∈ S := fun n => hW _
  have hvB : ∀ n, tch l (v (n + 1)) ^ q = tch l (v n) := fun n => by rw [← tch_pow, hvq]
  obtain ⟨Q, hQS, hQ⟩ := GlobalTheory.T.lubin_tate_iterate_limit_congruence E q hq2 hqd (fun n => tch l (v n)) hvS hvB
  have hθϖ : ‖thB l ϖ‖ < 1 := by
    rw [← hϖe, thB_rB]; exact hnμ μ
  have hθϖ0 : thB l ϖ ≠ 0 := by
    rw [← hϖe, thB_rB]
    exact (map_ne_zero_iff (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l])
      (RingHom.injective _)).2 hne
  have hnil0 := GlobalTheory.T.teichmuller_near_power_exists S hW ϖ hθϖ0 (v 0) hv1
  have hQ0 : ∃ s ∈ S, Q - tch l (v 0) = ϖ * s := by
    obtain ⟨a, ha, e⟩ := hQ 0
    exact ⟨a, ha, by simpa [ltIter] using e⟩
  have hnilQ : ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (Q ^ M) := by
    obtain ⟨M, hM, s, hs, e⟩ := hnil0
    obtain ⟨s', hs', e'⟩ := near_pow_of_sub hQS (hvS 0) hQ0 M
    refine ⟨M, hM, s + s', S.add_mem hs hs', ?_⟩
    have : Q ^ M - ϖ ^ 1 * (s + s') = tch l (v 0) ^ M - ϖ ^ 1 * s := by
      rw [pow_one] at *
      linear_combination e'
    rwa [this]
  obtain ⟨t, ht⟩ := GlobalTheory.T.lubin_tate_scaled_iterate_tends E ϖ' hϖ' q hq2 Q hQS hnilQ
  have hkerF : ∀ x, thB l x = 0 ↔ x ∈ FB l 1 := fun x => by
    rw [FB, pow_one, RingHom.mem_ker]
  refine ⟨t, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨n, hn⟩ := GlobalTheory.T.lubin_tate_iterate_eventually_zero E ϖ' hϖ' (thB l) hkerF hI hθϖ q hq2 Q hQS hnilQ ht
    obtain ⟨-, s, hs, e⟩ := iter_near E.mem q hQS (hvS 0) hQ0 n
    rw [hn, zero_sub, ← tch_pow] at e
    refine hnot (v 0 ^ (q ^ n)) (pow_ne_zero _ hv0) (-s) (S.neg_mem hs) ?_
    rw [mul_neg, ← e, neg_neg]
  · intro g hg hfix
    obtain ⟨a, ha⟩ := GlobalTheory.T.character_values_integral K χ hc ⟨g, hg⟩
    obtain ⟨φ, hφ0, hφ1, hφc⟩ := GlobalTheory.T.lubin_tate_endomorphism_series_exists K π hπ a
    have hφ1' : ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) := by
      rw [hφ1, ha]
    have hσϖ : actB g ϖ = ϖ := by
      rw [← hϖe, actB_rB, hfix]
    have hnil : ∀ n, ‖thB l (tch l (v n))‖ < 1 := fun n => by
      have h1 : ∀ n, tch l (v n) ^ (q ^ n) = tch l (v 0) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', pow_mul, hvB, ih]
      have h2 : ‖thB l (tch l (v n))‖ ^ (q ^ n) < 1 := by
        rw [← norm_pow, ← map_pow, h1]; exact hv1
      by_contra h3
      exact absurd h2 (not_lt.2 (one_le_pow₀ (not_lt.1 h3)))
    have hev1 : ∀ n, EvalMod S (FB l) ϖ (oB K μ) φ (tch l (v n)) (actB g (tch l (v n))) 1 := fun n => by
      rw [actB_tch]
      exact GlobalTheory.T.lubin_tate_series_de_rham_period K μ π S hW hoB E hπl r hr (v n) (actT g (v n)) (hnil n) φ
        (fun D => hrg g hg φ hφ0 hφ1' hφc n D)
    have hevQ := GlobalTheory.T.lubin_tate_commuting_series_unique E (oB K μ) hoB π rfl q hq2 hqd φ hφ0 hφc (actB g) (hG g) (fun k x hx => actB_FB g k x hx)
      hσϖ (fun n => tch l (v n)) hvS hvB hnil0 Q hQS hQ hev1
    have := GlobalTheory.T.lubin_tate_series_commute_linear E ϖ' hϖ' (oB K μ) hoB π rfl q hq2 hqd φ hφ0 hφc (actB g) (hG g)
      (fun k x hx => actB_FB g k x hx) hσϖ Q hQS hnilQ hevQ t ht
    rw [this]
    congr 1
    change rB l (μ (algebraMap ↥(OL K) ↥K.1 (PowerSeries.coeff 1 φ))) = _
    congr 2
  · intro hμ
    have hθQ : thB l Q = 0 := by
      refine GlobalTheory.T.lubin_tate_torsion_approximation E (thB l) hI hθϖ0 hθϖ q hq2 ?_ (fun n => tch l (v n)) hvS (fun n => ((z n : Om l) : ℂ_[l])) ?_ ?_ ?_ Q hQS hQ
      · obtain ⟨s, hs, e⟩ := hqd
        rw [← map_natCast (thB l), e, map_mul, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hI s hs)
      · have := hD.2.1
        rw [this]; simp
      · intro n
        have h := hD.2.2.2.1 n
        have h2 := congrArg (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) h
        rw [map_add (f := _), map_mul, map_pow] at h2
        have e : thB l ϖ = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
          rw [← hϖe, thB_rB, hμ]; rfl
        rw [e]
        exact h2
      · intro n
        have e : thB l ϖ = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
          rw [← hϖe, thB_rB, hμ]; rfl
        rw [e]
        exact hrz hμ n
    exact GlobalTheory.T.lubin_tate_limit_kernel_zero E ϖ' hϖ' (thB l) hkerF hI hθϖ q hq2 Q hθQ t ht

end PositivityTheory.SecR.Hladr2

namespace PositivityTheory.SecR.Hladr2
variable {l : ℕ} [Fact l.Prime]

theorem ker_thB : RingHom.ker (thB l) = RingHom.ker (Formalism.Per6.θD l) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = (0 : ℂ_[l])) (GroundTheory.PAdicHodge.thetaAlgHom_apply l x))

theorem σD_algebraMap (g : GQ l) (y : Formalism.Per6.BdRp l) :
    Formalism.Per6.σD g (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) y) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (actB g y) :=
  GroundTheory.PAdicHodge.galBdRField_algebraMap (Formalism.Per6.toBot g) y

theorem fil_iff {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) (n : ℕ) {x : P.R.BdR}
    {y : Formalism.Per6.BdRp l} (h : T.eD x = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) y) :
    x ∈ (P.PD K).Fil (n : ℤ) ↔ y ∈ FB l n := by
  rw [PositivityTheory.LocInh.filq_tie_fil T K n h, FB, ker_thB]

theorem hasPeriods_main (HT : TiltLeaf) (HP : ProductLeaf) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied6 l P AI))
    (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (hLT : IsLTChar K χ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) : HasPeriods P K χ := by
  obtain ⟨T⟩ := hT
  have hN := GlobalTheory.T.lubin_tate_norm_cyclotomic K χ hLT hc
  obtain ⟨π, z, hD⟩ := hLT
  choose t ht using fun μ => pre_period HT K χ π z hD hc μ
  have hP := HP K χ hN t ht
  intro μ
  obtain ⟨y, hy⟩ : ∃ y : P.R.BdR, T.eD y = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (t μ) :=
    ⟨_, T.eD.apply_symm_apply _⟩
  have f1 := fil_iff T K 1 hy
  have f2 := fil_iff T K 2 hy
  have f0 := fil_iff T K 0 hy
  rw [Nat.cast_one] at f1
  rw [Nat.cast_ofNat] at f2
  rw [Nat.cast_zero] at f0
  have hF1 : thB l (t μ) = 0 → t μ ∈ FB l 1 := fun h => by
    rw [FB, pow_one]; exact h
  refine ⟨y, ?_, ?_, ?_⟩
  · intro g hg hfix
    apply T.eD.injective
    rw [T.actD, map_mul, hy, PositivityTheory.LocInh.tie_o, σD_algebraMap, (ht μ).2.1 g hg hfix, map_mul]
    rfl
  · intro hμ
    exact ⟨f1.2 (hF1 ((ht μ).2.2 hμ)), fun h => (hP μ).1 hμ (f2.1 h)⟩
  · intro hμ
    refine ⟨f0.2 ?_, fun h => (hP μ).2 hμ (f1.1 h)⟩
    rw [FB, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

end PositivityTheory.SecR.Hladr2

theorem PositivityTheory.SecR.Hladr2.field_of_leaves (HT : PositivityTheory.SecR.Hladr2.TiltLeaf) (HP : PositivityTheory.SecR.Hladr2.ProductLeaf) :
    GlobalTheory.Published.HeckeLAdicCharacterDeRham :=
  PositivityTheory.SecR.Hladr.field_of_ltPeriods fun P AI hT K χ hLT hc => PositivityTheory.SecR.Hladr2.hasPeriods_main HT HP P AI hT K χ hLT hc
