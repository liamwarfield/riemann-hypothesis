module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open Filter Topology

namespace GlobalTheory.Mem.UnrAe

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  classical
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
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem tendsto_finSingle (y : ∀ v : HeightOneSpectrum (𝓞 L), v.adicCompletion L) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    Tendsto (fun v => Neutral.B1.finiteSingle L v (y v)) cofinite (𝓝 1) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  let o : ∀ w, A w := fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let g : HeightOneSpectrum (𝓞 L) → ∀ w, A w := fun v => Function.update o v ⟨y v, hy v⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    have h' : w ≠ v := fun h => hv h.symm
    exact (Function.update_of_ne h' _ _).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  refine Tendsto.congr (fun v => ?_) h2
  apply Subtype.ext
  funext w
  show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w
  by_cases hw : w = v
  · subst hw; simp [g]
  · simp [g, o, Function.update_of_ne hw]

theorem tendsto_localIdele (x : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hx : ∀ v, IsUnitAt v (x v)) :
    Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have h1 := tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le
  have h2 := tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by
    have h : Valued.v (x v : v.adicCompletion L) = 1 := hx v
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  have h3 : Tendsto (fun v => ((localIdele L v (x v) : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1
  have h4 : Tendsto (fun v => (((localIdele L v (x v))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2
  exact h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)

theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (m : ℕ) :
    IsUnitAt v (x ^ m) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

theorem finite_ramified (χ : HChar L) : {v | ¬ χ.UnrAt v}.Finite := by
  have h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧
      (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    exact (hc _ (isUnitAt_pow hx m)).1
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp χ.2.1).sub continuous_const).norm
  have h1 := (hc.tendsto 1).comp (tendsto_localIdele x hx)
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)

theorem exists_levelLe (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ∃ n, χ.LevelLe v n := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)


open Classical in
theorem unr_ae_and_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n :=
  fun _ _ _ χ => ⟨finite_ramified χ, exists_levelLe χ⟩

end GlobalTheory.Mem.UnrAe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits diagUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n := by
  first | exact @GlobalTheory.Mem.UnrAe.unr_ae_and_level | exact GlobalTheory.Mem.UnrAe.unr_ae_and_level | (intros; apply GlobalTheory.Mem.UnrAe.unr_ae_and_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General


open Classical in
theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.HostCM

theorem valuation_eq_of_unram (K : Type) [Field K] [NumberField K] [IsCMField K]
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : HeightOneSpectrum (𝓞 K)) (x : maximalRealSubfield K) :
    P.valuation K (algebraMap (maximalRealSubfield K) K x) =
      (P.under (𝓞 (maximalRealSubfield K))).valuation (maximalRealSubfield K) x := by
  have hp := P.isPrime
  have hp' := (P.under (𝓞 (maximalRealSubfield K))).isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 (maximalRealSubfield K))).asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[maximalRealSubfield K] K)
    (P.under (𝓞 (maximalRealSubfield K))).asIdeal P.asIdeal
  have h1 : Nat.card (P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    have key : ∀ z : P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K),
        (z : K ≃ₐ[maximalRealSubfield K] K) = 1 := by
      intro z
      rcases Eta.cases K z.1 with hz | hz
      · exact hz
      · exfalso
        have hm := AddSubgroup.mem_inertia.mp z.2
        rw [hz] at hm
        exact hunr P.asIdeal hp P.ne_bot hm
    rw [key x, key y]
  rw [h1, Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal (K ≃ₐ[maximalRealSubfield K] K)] at hcard
  rw [← HeightOneSpectrum.valuation_liesOver K (P.under (𝓞 (maximalRealSubfield K))) P x,
    ← hcard, pow_one]


open Classical in
theorem host_cm_embedding_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ (IsTotallyReal H.F ∧ IsTotallyComplex H.E ∧ Module.finrank H.F H.E = 2 ∧ c ≠ 1 ∧ Function.Bijective fun g => InfinitePlace.mk (embPsi H g)) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hmem : ∀ g : R.Psi, embPsi H g ∈ H.cmType := fun g => ((factEmb R H).2 g).2 g.2
  have hT := H.der.cmType.1
  refine ⟨IsCMField.complexConj H.E, hc, ⟨inferInstance, inferInstance,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one _,
    ?_, ?_⟩, ?_, hmem, ?_⟩
  · intro g g' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact Subtype.ext ((factEmb R H).1.1 h)
    · have h' := hmem g'
      rw [← h] at h'
      exact absurd h' ((hT _).1 (hmem g))
  · intro w
    by_cases hw : w.embedding ∈ H.cmType
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 w.embedding
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw)⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 (ComplexEmbedding.conjugate w.embedding)
      have hw' : ComplexEmbedding.conjugate w.embedding ∈ H.cmType := by
        by_contra h'
        exact hw ((hT _).2 h')
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw')⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  · intro P k
    have := valuation_eq_of_unram H.E (fun P hP h0 hx => H.der.unramEF P hP h0 fun x => by
      have e : H.conj • x = IsCMField.complexConj H.E • x := Subtype.ext (hc x).symm
      rw [e]
      exact hx x) P k
    unfold ordF
    rw [← this]
    rfl
  · rw [← Nat.card_eq_fintype_card]
    exact (factCardPsi R H).1


open Classical in
theorem host_cm : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ CMData H.F c (embPsi H) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  obtain ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩ := host_cm_embedding_properties R H
  exact ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩

end GlobalTheory.Mem.HostCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.UnitOpen

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_val_le (v : HeightOneSpectrum (𝓞 L)) (m : ℤ) :
    IsOpen {x : v.adicCompletion L | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective L (WithZero.exp (-m))
  have h : IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := Valued.isOpen_valuationSubring _
  convert h.preimage (continuous_mul_const p) using 1
  ext x
  show _ ↔ Valued.v (x * p) ≤ 1
  rw [map_mul, hp, WithZero.exp_neg, mul_inv_le_iff₀ (WithZero.exp_pos), one_mul]
  rfl

theorem continuous_comp (v : HeightOneSpectrum (𝓞 L)) :
    Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 v :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)

theorem isOpen_unitIdl : IsOpen (unitIdl L : Set (Ideles L)) := by
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 L) L | ∀ v, a v ∈ v.adicCompletionIntegers L} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have c1 : Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 := continuous_snd.comp Units.continuous_val
  have c2 : Continuous fun a : Ideles L => ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hV.preimage c1).inter (hV.preimage c2) using 1
  ext a
  constructor
  · intro ha
    exact ⟨fun v => (ha v).le, fun v => ((unitIdl L).inv_mem ha v).le⟩
  · rintro ⟨h1, h2⟩ v
    have h : (a : AdeleRing (𝓞 L) L).2 v * ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 L) L => z.2 v) a.mul_inv
    have h3 := congrArg (Valued.v : Valuation (v.adicCompletion L) _) h
    rw [map_mul, map_one] at h3
    have k1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have k2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm k1 ?_
    rw [← h3]
    exact mul_le_of_le_one_right' k2


open Classical in
theorem unit_open_and_congr_open : ∀ (L : Type) [Field L] [NumberField L], IsOpen (unitIdl L : Set (Ideles L)) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), IsOpen {a : Ideles L | a ∈ unitIdl L ∧ ∀ v ∈ S, Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))} := by
  intro L _ _
  refine ⟨isOpen_unitIdl, fun S n => ?_⟩
  have h : IsOpen (⋂ v ∈ S, {a : Ideles L | Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))}) :=
    isOpen_biInter_finset fun v _ => (isOpen_val_le v _).preimage ((continuous_comp v).sub continuous_const)
  convert isOpen_unitIdl.inter h using 1
  ext a
  simp

end GlobalTheory.Mem.UnitOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoOfForallIntegral
namespace GlobalTheory.TendstoOfIntegrals

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by

  let A : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → Set (v.adicCompletion L) :=
    fun v ↦ (v.adicCompletionIntegers L : Set (v.adicCompletion L))
  let g : ι → (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v :=
    fun i v ↦ ⟨_, hf i v⟩
  let c : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v := fun v ↦ ⟨_, hb v⟩
  have hg : Tendsto g l (𝓝 c) :=
    tendsto_pi_nhds.2 fun v ↦ tendsto_subtype_rng.2 (hl v)
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ v.adicCompletion L)
    (A := A) (𝓕 := cofinite)
  exact (hemb.continuous.tendsto c).comp hg

end GlobalTheory.TendstoOfIntegrals

theorem GlobalTheory.TendstoOfIntegrals.target_check : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {ι : Type} {l : Filter ι} (f : ι → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L) (b : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L), (∀ (i : ι) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), Filter.Tendsto (fun (i : ι) ↦ (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v) l (nhds ((b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v))) → Filter.Tendsto f l (nhds b) := by
  intro L _ _ ι l f b hf hb hl
  exact GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral f b hf hb hl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open Filter Topology

namespace GlobalTheory.Mem.LocTriv

variable {L : Type} [Field L] [NumberField L]

theorem tendsto_finiteAdele {ι : Type} {l : Filter ι} (f : ι → FiniteAdeleRing (𝓞 L) L) (b : FiniteAdeleRing (𝓞 L) L)
    (hf : ∀ i v, f i v ∈ v.adicCompletionIntegers L) (hb : ∀ v, b v ∈ v.adicCompletionIntegers L)
    (h : ∀ v, Tendsto (fun i => f i v) l (𝓝 (b v))) : Tendsto f l (𝓝 b) := by
  first
  | exact @_root_.GlobalTheory.TendstoOfIntegrals.target_check
  | exact _root_.GlobalTheory.TendstoOfIntegrals.target_check
  | (apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TendstoOfIntegrals.target_check <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TendstoOfIntegrals.target_check ..)

def ev (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def part (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  ∏ v ∈ S, localIdele L v (Units.map (ev v) a)

theorem part_inv (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S)⁻¹ = part a⁻¹ S := by
  simp only [part, map_inv, Finset.prod_inv_distrib]

theorem ev_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ev v (localIdele L v x : AdeleRing (𝓞 L) L) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_local_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ev w (localIdele L v x : AdeleRing (𝓞 L) L) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_part_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ev w (part a S : AdeleRing (𝓞 L) L) = ev w (a : AdeleRing (𝓞 L) L) := by
  rw [part, Units.coe_prod, map_prod, Finset.prod_eq_single_of_mem w hw (fun v _ hv => ev_local_ne hv.symm _),
    ev_local_self]
  rfl

theorem ev_part_not_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ S) : ev w (part a S : AdeleRing (𝓞 L) L) = 1 := by
  rw [part, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun v hv => ev_local_ne (fun e : w = v => hw (e ▸ hv)) _

theorem part_fst (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S : AdeleRing (𝓞 L) L).1 = 1 := by
  have h : finPartI L (part a S) = part a S := by
    rw [part, map_prod]
    exact Finset.prod_congr rfl fun v _ => Units.ext rfl
  rw [← h]
  rfl

theorem tendsto_part_val {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : (a : AdeleRing (𝓞 L) L).1 = 1) :
    Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L)) atTop (𝓝 (a : AdeleRing (𝓞 L) L)) := by
  have h2 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).2) atTop (𝓝 (a : AdeleRing (𝓞 L) L).2) := by
    refine tendsto_finiteAdele _ _ (fun S v => ?_) (fun v => (ha v).le) fun v => ?_
    · show ev v (part a S : AdeleRing (𝓞 L) L) ∈ _
      by_cases hv : v ∈ S
      · rw [ev_part_mem a hv]
        exact (ha v).le
      · rw [ev_part_not_mem a hv]
        exact one_mem _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
      exact (ev_part_mem a (hS (Finset.mem_singleton_self v))).symm
  have h3 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).1) atTop (𝓝 (a : AdeleRing (𝓞 L) L).1) := by
    rw [h1]
    exact tendsto_const_nhds.congr fun S => (part_fst a S).symm
  exact h3.prodMk_nhds h2

theorem tendsto_part {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : ∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    Tendsto (part a) atTop (𝓝 a) := by
  have e : finPartI L a = a := finPartI_eq_self h1
  have e' : finPartI L a⁻¹ = a⁻¹ := by rw [map_inv, e]
  have t1 := tendsto_part_val ha (by rw [← e]; rfl)
  have t2 := tendsto_part_val ((unitIdl L).inv_mem ha) (by rw [← e']; rfl)
  simp only [← part_inv] at t2
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp t2)


open Classical in
theorem eq_one_of_local : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  intro L _ _ ψ hψ a ha h1 hl
  have t := (hψ.tendsto a).comp (tendsto_part ha h1)
  have e : ψ ∘ part a = fun _ => 1 := funext fun S => by
    show ψ (part a S) = 1
    rw [part, map_prod]
    exact Finset.prod_eq_one fun v _ => hl v _ rfl
  rw [e] at t
  exact tendsto_nhds_unique t tendsto_const_nhds

end GlobalTheory.Mem.LocTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnitsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits diagUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_character_trivial_on_local_units : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  first | exact @GlobalTheory.Mem.LocTriv.eq_one_of_local | exact GlobalTheory.Mem.LocTriv.eq_one_of_local | (intros; apply GlobalTheory.Mem.LocTriv.eq_one_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x
  convert Pi.mulSingle_eq_same w (x : w.Completion)

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1
  convert Pi.mulSingle_eq_of_ne h (x : w.Completion)

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact infIdele_fst_self F w _
    · intro u _ hu
      exact infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]


open Classical in
def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [localIdele_snd_ne F u v h, one_mul]; simp [h]

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

end Product

theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩


open Classical in
theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.Chr


open Classical in
theorem splitsC_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] → SplitsC H.E p := by
  intro R H p hp h
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hpos : 0 < H.QS * H.q * H.d := Nat.pos_of_ne_zero H.condN_ne_zero
  have hlt : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hpos (dvd_mul_left _ _))
  refine (GlobalTheory.HostSplit.split_of_one_mod R H p hp ?_).1
  rw [h]
  exact Nat.mod_eq_of_lt hlt

end GlobalTheory.Mem.Chr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

end GlobalTheory.BaseChars
end
