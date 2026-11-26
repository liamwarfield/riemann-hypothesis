module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem mem_iff {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (j : W.Emb l w) (x : 𝓞 L) :
    x ∈ w.asIdeal ↔ ‖j.1 (algebraMap L _ (x : L))‖ < 1 := by
  have h : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf]
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [ReciprocityTheory.Aut.adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem (K := L) y).2 hy
    have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun n => ?_)
    exact map_pow j.1 _ n
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h, GlobalTheory.EvExtend.mem_placeOf]
  rfl

private theorem cc {L : Type} [Field L] [NumberField L] [IsCMField L] (x : 𝓞 L) :
    IsCMField.ringOfIntegersComplexConj L (IsCMField.ringOfIntegersComplexConj L x) = x :=
  RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x)

private theorem norm_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) {x : 𝓞 L} (hx : x ∈ u.asIdeal) :
    x ∈ w.asIdeal ∨ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm, cc])
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact w.isPrime.mem_or_mem h1

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  exact hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => (norm_mem hu' hx).elim id (h x)))

private theorem two {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    u = w ∨ ∀ x, x ∈ u.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  haveI := w.isPrime
  have h : (u.asIdeal : Set (𝓞 L)) ⊆ w.asIdeal ∪ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj L) :=
    fun x hx => norm_mem hu hx
  rcases Ideal.subset_union.1 h with h | h
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h))
  · refine Or.inr fun x => ?_
    rw [u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) h, Ideal.mem_comap]

private theorem ex_emb {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (τ : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, x ∈ w.asIdeal ↔ ‖τ x‖ < 1) : ∃ j : W.Emb l w, j.1.comp (algebraMap L _) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [GlobalTheory.EvExtend.mem_placeOf, h])
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

theorem UpperTheory.placeEmbeddings_bijective_infinitePlaces :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Finite (Emb l (fun v : V.frame.Vl => s.w v.1)) ∧ Function.Bijective (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  obtain ⟨hun, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hinj : Function.Injective
      (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · have h1 : ∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective (RingHom.congr_fun h x)
      have h2 : s.w v.1 = s.w v'.1 := HeightOneSpectrum.ext (Ideal.ext fun x => by
        rw [mem_iff j, mem_iff j', h1])
      have h3 : v = v' := Subtype.ext (by rw [← hun v.1, h2, hun])
      subst h3
      refine congrArg (Sigma.mk v) (Subtype.ext (DFunLike.coe_injective ?_))
      exact (HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext h1)
    · have h1 : ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective ((IsCMField.complexEmbedding_complexConj L _ x).trans (RingHom.congr_fun h x))
      have h2 : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ (s.w v.1).asIdeal ↔ x ∈ (s.w v'.1).asIdeal := fun x => by
        rw [mem_iff j, mem_iff j', ← h1]
        rfl
      have h3 : v = v' := Subtype.ext (by
        rw [← hun v.1, ← hun v'.1]
        refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
        change algebraMap _ (𝓞 L) y ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) y ∈ (s.w v'.1).asIdeal
        rw [← h2, (IsCMField.ringOfIntegersComplexConj_eq_self_iff L _).2 ⟨y, rfl⟩])
      subst h3
      refine (not_stable (hsp (s.w v.1) ?_) fun x hx => (h2 x).1 hx).elim
      rw [hun]
      exact s.split _ (Or.inl v.2)
  refine ⟨Finite.of_injective _ hinj, hinj, fun p => ?_⟩
  obtain ⟨φ, rfl⟩ : ∃ φ, InfinitePlace.mk φ = p := ⟨_, p.mk_embedding⟩
  let τ : L →+* Qbar l := ι.symm.toRingHom.comp φ
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) ((l : ℕ) : 𝓞 (Lp L)) ∈ (GlobalTheory.EvExtend.placeOf τ).asIdeal
    rw [map_natCast, GlobalTheory.EvExtend.mem_placeOf]
    simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
  rcases two (hun ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))).symm with h | h
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))) τ fun x => by
      rw [← h, GlobalTheory.EvExtend.mem_placeOf]
    refine ⟨⟨⟨_, hl⟩, j⟩, congrArg InfinitePlace.mk (RingHom.ext fun x => ?_)⟩
    exact (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))))
      (τ.comp (IsCMField.complexConj L).toRingEquiv.toRingHom) fun x => by
        have h1 := h (IsCMField.ringOfIntegersComplexConj L x)
        rw [cc, GlobalTheory.EvExtend.mem_placeOf] at h1
        exact h1.symm
    refine ⟨⟨⟨_, hl⟩, j⟩, InfinitePlace.mk_eq_iff.2 (Or.inr (RingHom.ext fun x => ?_))⟩
    have h1 : ι (j.1 (algebraMap L _ x)) = φ (IsCMField.complexConj L x) :=
      (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
    change starRingEnd ℂ (ι (j.1 (algebraMap L _ x))) = φ x
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicLocalComponentsContinuousLevelsOpen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem nh_loc : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] nh_loc

private theorem nh_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem nh_pow (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (nh_unif.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := nh_unif
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem nh_memKc {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (nh_pow c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem nh_Kc_open (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, nh_memKc, Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), nh_unif] using Valuation.isOpen_closedBall h0

end SlopeTestRemainingChoices

private theorem nh_open {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} : IsOpen ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)) : Set (UA L n)) := by
  let p : UA L n →* GL (Fin n) (Af L) := (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype
  have hp : Continuous p := GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val
  have ho : IsOpen (GlobalTheory.GLIntegral.intSubring L : Set (Af L)) := RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    (fun v => Valued.isOpen_valuationSubring _)
  refine Subgroup.isOpen_mono (H₁ := (GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring L)).comap p) (fun g hg => ?_)
    ((GlobalTheory.GLIntegral.isOpen_glSub _ ho).preimage hp)
  have hv : ∀ (w : Plc L) (x : w.adicCompletion L), x ∈ w.adicCompletionIntegers L → x ∈ 𝒪[w.adicCompletion L] := fun w x hx => by
    haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
    exact hx
  exact Subgroup.mem_iInf.2 fun w => (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => hv w _ (hg.1 i j w), fun i j => hv w _ (hg.2 i j w)⟩

theorem UpperTheory.unitaryAdelic_localComponents_continuous_levels_open :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), (∀ w : Plc L, Continuous (cLoc (E := L) (n := n) w)) ∧ (∀ (w : Plc L) (b : ℕ), IsOpen (Kc (w.adicCompletion L) n b : Set (GLw n w))) ∧ ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ w : Plc L, cLoc w (k : UA L n) ∈ KO (w.adicCompletion L) (Fin n) := by
  intro L _ _ _ n
  refine ⟨fun w => GlobalTheory.DefU.Inert.continuous_cLoc w, fun w b => nh_Kc_open b, ?_⟩
  have h := ((nh_open (L := L) (n := n)).preimage (continuous_subtype_val (p := fun x => x ∈ finU (E := L) (n := n)))).mem_nhds
    (x := (1 : finU (E := L) (n := n))) (one_mem (⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)))
  filter_upwards [h] with k hk w
  exact Subgroup.mem_iInf.1 hk w
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemHeckeLevelOfLocalComponentsMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.mem_heckeLevel_of_local_components_mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) → u ∈ (hset Q τ₀).lev K := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ (T : Finset Q.Q) (u : Ub n s),
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) →
      (∀ q : Q.Q, CaseU.cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) →
      (∀ q ∉ T, CaseU.cmp n (Q.wq q) (u : Ga l L n) = 1) → u ∈ (hset Q τ₀).lev K := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro u hu _ h0
      refine Subgroup.mem_sup_left (S := UQ n Q) ?_
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => hu w hw,
        Subgroup.mem_iInf.2 fun q => MonoidHom.mem_ker.2 (h0 q (Finset.notMem_empty q))⟩
    | insert q T _ ih =>
      intro u hu hK h0
      let x : Ub n s := sec n s (Q.wq q) (CaseU.cmp n (Q.wq q) (u : Ga l L n))
      have hx : x ∈ (hset Q τ₀).lev K :=
        Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨_, hK q, rfl⟩)
      have e1 : ∀ w : Plc L, w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
          CaseU.cmp n w ((x⁻¹ * u : Ub n s) : Ga l L n) = CaseU.cmp n w (u : Ga l L n) := fun w hw => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1 q _ w hw, inv_one, one_mul]
      have e2 : CaseU.cmp n (Q.wq q) ((x⁻¹ * u : Ub n s) : Ga l L n) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, (hsec q).2.1, inv_mul_cancel]
      have hy : x⁻¹ * u ∈ (hset Q τ₀).lev K := by
        refine ih _ (fun w hw => ?_) (fun q' => ?_) fun q' hq' => ?_
        · rw [e1 w fun h => hw (h ▸ hS q)]
          exact hu w hw
        · by_cases h : q' = q
          · subst h
            rw [e2]
            exact one_mem _
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact hK q'
        · by_cases h : q' = q
          · subst h
            exact e2
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact h0 q' fun h' => (Finset.mem_insert.1 h').elim h hq'
      have e : u = x * (x⁻¹ * u) := (mul_inv_cancel_left x u).symm
      rw [e]
      exact Subgroup.mul_mem _ hx hy
  exact fun u hu hK => key Finset.univ u hu hK fun q hq => (hq (Finset.mem_univ q)).elim
end
