module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_cyclic_subextension_over_rat :
    UpperTheory.V.Af.Sol.CycQ := by
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 3)
  obtain ⟨q, hq, -, hqp⟩ := Nat.exists_prime_gt_modEq_one 0 hp.ne_zero
  haveI := Fact.mk hq
  have hpdvd : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hqp.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {q} ℚ (CyclotomicField q ℚ)
  have hcardG : Nat.card Gal(CyclotomicField q ℚ/ℚ) = q - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ),
      Nat.totient_prime hq]
  haveI : IsCyclic Gal(CyclotomicField q ℚ/ℚ) :=
    isCyclic_of_surjective (IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
      (Polynomial.cyclotomic.irreducible_rat hq.pos)).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(CyclotomicField q ℚ/ℚ))
  have hH : Nat.card (Subgroup.zpowers (g ^ p)) = (q - 1) / p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero (by rw [hg, hcardG]; exact hpdvd), hg, hcardG]
  have hfin : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) = p := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ))
    rw [IntermediateField.finrank_fixedField_eq_card, hH,
      IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ), Nat.totient_prime hq] at h1
    obtain ⟨m, hm⟩ := hpdvd
    have hq2 := hq.two_le
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at h1
    exact Nat.eq_of_mul_eq_mul_right hmpos h1
  haveI : IsAbelianGalois ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) :=
    IsAbelianGalois.tower_bot ℚ _ (CyclotomicField q ℚ)
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers (g ^ p)), inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · classical
    rw [NumberField.isTotallyReal_iff]
    have hodd := InfinitePlace.nrRealPlaces_pos_of_odd_finrank
      (K := IntermediateField.fixedField (Subgroup.zpowers (g ^ p)))
      (by rw [hfin]; exact hp.odd_of_ne_two (by omega))
    obtain ⟨w0, hw0⟩ : ∃ w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))),
        w.IsReal := by
      by_contra hne
      push_neg at hne
      have : IsEmpty {w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) //
          w.IsReal} := ⟨fun w => hne w.1 w.2⟩
      simp [InfinitePlace.nrRealPlaces] at hodd
    intro w
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w0) (w' := w)
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isReal_smul_iff.mpr hw0
  · rw [hfin]; exact hp
  · rw [hfin]; omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFactorDualEmbeddingOfNeZeroTensor
open scoped TensorProduct

theorem UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor :
    ∀ (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)] (N : Type) [AddCommGroup N] [Module ℂ N] (Φ : Module.Dual ℂ (⨂[ℂ] i, W i) →ₗ[ℂ] N), Φ ≠ 0 → ∀ y : I, ∃ E : Module.Dual ℂ (W y) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, W i), Φ ∘ₗ E ≠ 0 ∧ ∀ T : ∀ i, W i →ₗ[ℂ] W i, (∀ i, i ≠ y → T i = LinearMap.id) → ∀ m, E m ∘ₗ PiTensorProduct.map T = E (m ∘ₗ T y) := by
  intro I _ W _ _ _ N _ _ Φ hΦ y
  classical
  have := Fintype.ofFinite I
  have hinv := PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse
    (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))
  have hf : ∃ f : ∀ i, Module.Dual ℂ (W i),
      Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0 := by
      apply PiTensorProduct.ext
      ext f
      simpa using h f
    apply hΦ
    rw [← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]
  obtain ⟨f, hf⟩ := hf
  refine ⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩
  · intro h
    apply hf
    have := LinearMap.congr_fun h (f y)
    simpa using this
  · intro T hT m
    apply PiTensorProduct.ext
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply,
      PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hT i hi]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.hasWeightAt_of_tensor_dual_intertwiner :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (φ : I → E →+* ℂ), (Function.Injective fun i => InfinitePlace.mk (φ i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)) (Φ : Module.Dual ℂ (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (UA E n → ℂ)), Φ ≠ 0 → (∀ ℓ, Φ ℓ ∈ σ) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x⁻¹))) → ∀ i, HasWeightAt σ (φ i) (lam i).dual := by
  intro E _ _ _ n hn I _ φ hφ lam σ Φ hΦ hσ heq y
  obtain ⟨F, hF0, hF⟩ := UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor I (fun i => nablaSq ℂ n (lam i)) _ Φ hΦ y
  obtain ⟨e, he⟩ := (GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual n hn (lam y)).symm.trans (GlobalTheory.T.iso_unitaryIrrep_conj_dual n (lam y))
  obtain ⟨u, hu⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (φ y)
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n _, (Φ ∘ₗ F) ∘ₗ e.toLinearMap, fun h0 => hF0 ?_, fun v => hσ _, fun x v => ?_⟩
  · apply LinearMap.ext
    intro m
    obtain ⟨v, rfl⟩ := e.surjective m
    exact LinearMap.congr_fun h0 v
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have hT : ∀ i, i ≠ y → GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x.1⁻¹) = LinearMap.id := by
      intro i hi
      have h1 := (Subgroup.mem_inf.1 x.2).2
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 (φ i)
      rw [Subgroup.mem_iInf] at h2
      have h3 : cEmb (φ i) x.1 = 1 := h2 fun h => hi (hφ h)
      rw [map_inv, h3, inv_one, map_one]
      rfl
    change Φ (F (e (GlobalTheory.Branching.sqRep ℂ n (lam y).dual (cEmb (φ y) x.1) v))) = RU E n x.1 (Φ (F (e v)))
    rw [heq _ _ hx, hF _ hT, map_inv, ← hu x]
    congr 2
    rw [← map_inv]
    exact he (u x) v
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveInfinitePlaceOfEmbAtSplitPlaces
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  have h1 := s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
  have h2 := s.hA v x
  exact h1.symm.trans h2

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

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => ?_))
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm]
    congr 1
    exact RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x))
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu'] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact (w.isPrime.mem_or_mem h1).elim id (h x)

theorem UpperTheory.injective_infinitePlace_of_emb_at_split_places :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Function.Injective fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp y.res) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  rintro ⟨v, j⟩ ⟨v', j'⟩ h
  have h' : (∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x)) ∨
      ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := by
    refine (InfinitePlace.mk_eq_iff.1 h).imp (fun e x => ι.injective (RingHom.congr_fun e x)) fun e x => ι.injective ?_
    exact (IsCMField.complexEmbedding_complexConj L (ι.toRingHom.comp (j.1.comp (algebraMap L _))) x).trans
      (RingHom.congr_fun e x)
  have hv : v = v' := by
    apply Subtype.ext
    rw [← w_under s v.1, ← w_under s v'.1]
    ext x
    change algebraMap _ (𝓞 L) x ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) x ∈ (s.w v'.1).asIdeal
    rw [mem_iff j, mem_iff j']
    rcases h' with e | e
    · rw [e]
    · rw [← e]
      have : IsCMField.complexConj L ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) = ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) :=
        IsCMField.complexConj_apply_eq_self L (x : Lp L)
      rw [this]
  subst hv
  rcases h' with e | e
  · have : j = j' := Subtype.ext (DFunLike.coe_injective
      ((HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext e)))
    rw [this]
  · refine (not_stable (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA _) (s.split _ (Or.inl v.2)) _ (w_under s _)) fun x hx => ?_).elim
    rw [mem_iff j] at hx
    rw [mem_iff j', ← e]
    exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleModuleRestrictionToNormalSubgroup
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem UpperTheory.semisimple_restriction_normal_subgroup {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : G → V →ₗ[K] V)
    (hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v) (hone : ∀ v, ρ 1 v = v)
    (N : Subgroup G) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hC, hUC⟩ := hss (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases htriv : C = ⊥
  · have hU := hUC.sup_eq_top
    rw [htriv, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    have := hv 1
    rwa [hone] at this
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hC g v hv, htriv, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hUC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  exact fun g => key g s hs

theorem UpperTheory.semisimpleModule_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Sol.SsRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  obtain ⟨W', h1, h2⟩ := UpperTheory.semisimple_restriction_normal_subgroup
    (fun g : Γ => Matrix.mulVecLin (r g : Matrix (Fin n) (Fin n) k))
    (by
      intro a b v
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul])
    (by
      intro v
      simp only [Matrix.mulVecLin_apply, map_one, Units.val_one, Matrix.one_mulVec])
    φ.range hN hss W (by
      rintro _ ⟨g, rfl⟩ v hv
      exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableAuxiliaryGaloisExtension
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_auxiliary_galois_extension :
    UpperTheory.V.Af.Sol.ExistsCompositumWithPrimeDegreeGalois := by
  intro M Ω _ _ _ _ _ L _ _ _ hp hlt
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hαi : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set P := minpoly ℚ α with hPdef
  have hPdeg : P.natDegree = Module.finrank ℚ L := by
    rw [← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']
  let φ : L →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  set β := φ α with hβdef
  have hβP : minpoly ℚ β = P := minpoly.algHom_eq φ φ.injective α
  set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαi)
  have hsplit : (Q.map (algebraMap M Ω)).Splits := IsAlgClosed.splits _
  have hSF := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hsep : Q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω := by
    intro y
    rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]
    exact and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩
  have hβroot : β ∈ P.rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩
  have hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β} := by
    intro x
    have h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ := ⟨x, trivial, rfl⟩
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)
    exact h2 h1
  have hPs : (P.map (algebraMap ℚ L)).Splits := Normal.splits inferInstance α
  have hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ := by
    intro y hy
    rw [← hPs.image_rootSet φ] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hroots y ((hroot y).1 hy)
      exact hrange x
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)
  have hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω)) := by
    haveI := hSF
    exact IsGalois.of_separable_splitting_field hsep
  have hgal : IsGalois M (IntermediateField.adjoin M {β}) := heq ▸ hgal0
  have hβQ : IsIntegral ℚ β := hαi.map φ
  have hβM : IsIntegral M β := hβQ.tower_top
  haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) :=
    IntermediateField.adjoin.finiteDimensional hβM
  haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) :=
    Module.Finite.trans M (IntermediateField.adjoin M {β})
  haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}
  let f : L →+* IntermediateField.adjoin M {β} := (φ : L →+* Ω).codRestrict _ hrange
  have hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree :=
    IntermediateField.adjoin.finrank hβM
  have hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L := by
    rw [← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]
    refine Polynomial.natDegree_le_of_dvd ?_ hQ0
    have h4 := minpoly.dvd_map_of_isScalarTower ℚ M β
    rwa [hβP] at h4
  have hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω)
      (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]
    exact hβP
  have hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β}) := by
    have h5 := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ)
      (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))
    rwa [hx, hPdeg] at h5
  have hMpos : 0 < Module.finrank ℚ M := Module.finrank_pos
  have hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β}) := Module.finrank_pos
  have hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)
    · exact le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)
  have htop : Algebra.adjoin M (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ Algebra.adjoin M {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]
      exact z.2
    have hsub : Algebra.adjoin M {β} ≤
        (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ rfl
      exact ⟨f α, ⟨α, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsub hz
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  exact ⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance,
    inferInstance, f, hgal, hdeg, htop⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EtaCondition
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.GalOfCusp

private theorem eta_val (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

private theorem eta_map (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [eta_val, eta_val]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

private theorem eta_loc {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (v : InfinitePlace F) (hs : χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.locInf v (atInf v k) : ℂˣ) : ℂ) * ((‖v.embedding (k : F)‖ : ℝ) : ℂ) = v.embedding (k : F) := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))
  have hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1 := fun x hx => by
    have h0 : e.symm (Real.sqrt (e x)) ≠ 0 := by
      rw [map_ne_zero]
      exact (Real.sqrt_pos.2 hx).ne'
    have e1 : x = Units.mk0 _ h0 ^ 2 := Units.ext (e.injective (by
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))
    rw [e1, map_pow]
    exact h2 _
  have h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  rw [← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · have e1 : atInf v k = -1 * -atInf v k := by simp
    rw [e1, map_mul, hs, hsq _ (by
      rw [Units.val_neg, map_neg]
      exact neg_pos.2 (he ▸ h)), abs_of_neg h]
    simp
  · rw [hsq _ (he ▸ h), abs_of_pos h]
    simp

private theorem eta_inf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (hs : ∀ v, χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ((‖∏ φ : F →+* ℂ, φ (k : F)‖ : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ (k : F) := by
  have hb : Function.Bijective fun v : InfinitePlace F => v.embedding :=
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩
  have e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k) := by
    unfold HChar.inf HChar.locInf infDiag
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k

private theorem eta_norm (E : Type) [Field E] [NumberField E] (k : E) :
    ∏ φ : E →+* ℂ, φ k = ((Algebra.norm ℚ k : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

private theorem eta_abs (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ) (k : (maximalRealSubfield E)ˣ) :
    (((GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k : ℂˣ) : ℂ) =
      ((‖∏ φ : maximalRealSubfield E →+* ℂ, φ (k : maximalRealSubfield E)‖ : ℝ) : ℂ) ^ f := by
  have e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k =
      (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k) :=
    congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)
  rw [e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]
  simp only [← Complex.ofReal_cpow (norm_nonneg _)]
  rw [← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]
  have e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) =
      Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2 := by
    change Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _
    rw [← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow]
  rw [e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem UpperTheory.eta_condition :
    Eta := by
  intro E _ _ _ f
  have hq : ∀ x, (quadChar E).1 x ^ 2 = 1 := fun x => by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  obtain ⟨ξ, m, hm, hξ⟩ := Cq.extReal E
    (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by
      have e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f := rfl
      rw [HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val,
        ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]
  refine ⟨ξ, m, hm, ?_⟩
  have e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) =
      GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ := rfl
  rw [e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmExtensionTower
open NumberField UpperTheory.V.Af.Sol

private theorem exists_proper_nontrivial_normal_of_solvable_not_prime_card (G : Type) [Group G] [Finite G] (hs : IsSolvable G)
    (h1 : Nat.card G ≠ 1) (hp : ¬ (Nat.card G).Prime) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hne
  push_neg at hne
  have hlt : 1 < Nat.card G := by
    have := Nat.card_pos (α := G)
    omega
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hlt
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN => by
        by_cases h : N = ⊥
        · exact Or.inl h
        · exact Or.inr (hne N hN h) }
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hs
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  exact hp (CommGroup.is_simple_iff_prime_card.1 ‹IsSimpleGroup G›)

private theorem rc_of_intermediateField_stable_under_complexConj {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    [IsCMField M] (K : IntermediateField F M)
    (hK : ∀ x ∈ K, IsCMField.complexConj M x ∈ K) : RC K := by
  have hext : ∀ φ : K →+* ℂ, ∃ Φ : M →+* ℂ, ∀ x : K, Φ x = φ x := by
    intro φ
    letI : Algebra K ℂ := φ.toAlgebra
    haveI : Module.IsTorsionFree K ℂ :=
      ⟨fun r hr _ _ hxy => mul_left_cancel₀ ((map_ne_zero φ).2 hr.ne_zero) hxy⟩
    refine ⟨(IsAlgClosed.lift : M →ₐ[K] ℂ).toRingHom, fun x => ?_⟩
    exact (IsAlgClosed.lift : M →ₐ[K] ℂ).commutes x
  let τ : K ≃+* K :=
    { toFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      invFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      left_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      right_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul])
      map_add' := fun x y => Subtype.ext (by simp [map_add (f := _)]) }
  let σ : Gal(K/ℚ) := τ.toRatAlgEquiv
  have hσ : ∀ x : K, ((σ x : K) : M) = IsCMField.complexConj M x := fun x => rfl
  have hconj : ∀ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ := by
    intro φ
    obtain ⟨Φ, hΦ⟩ := hext φ
    unfold ComplexEmbedding.IsConj
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hΦ]
    show _ = φ (σ x)
    rw [← hΦ, hσ, IsCMField.complexEmbedding_complexConj]
  by_cases h1 : σ = 1
  · left
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    have := hconj w.embedding
    rw [h1] at this
    unfold ComplexEmbedding.IsConj at this
    rw [this]
    rfl
  · right
    haveI : IsTotallyComplex K :=
      ⟨fun w => InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff (hconj _)).1 h1)⟩
    obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hord : Nat.card (Subgroup.zpowers σ) = 2 := by
      rw [Nat.card_zpowers]
      exact ComplexEmbedding.orderOf_isConj_two_of_ne_one (hconj φ0) h1
    haveI : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
    haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    let L : IntermediateField ℚ K := FixedPoints.intermediateField (Subgroup.zpowers σ)
    have hfix : ∀ x : L, σ (x : K) = x := fun x => x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    haveI : IsTotallyReal L := ⟨fun w => by
      obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
      dsimp only
      rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
        ComplexEmbedding.isReal_iff]
      ext x
      have h := RingHom.congr_fun (hconj W.embedding) (x : K)
      rw [ComplexEmbedding.conjugate_coe_eq] at h ⊢
      simp only [RingHom.comp_apply] at h ⊢
      rw [show algebraMap L K x = (x : K) from rfl, h]
      exact congrArg W.embedding (hfix x)⟩
    haveI : Algebra.IsQuadraticExtension L K :=
      ⟨by
        rw [Nat.card_eq_fintype_card] at hord
        rw [← hord]
        exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
    exact IsCMField.ofCMExtension L K

theorem UpperTheory.solvable_cm_extension_tower :
    UpperTheory.V.Af.Sol.Tower := by
  intro F M _ _ _ _ _ _ hs hF hM h1 hp
  obtain ⟨N, hN, hbot, htop⟩ := exists_proper_nontrivial_normal_of_solvable_not_prime_card Gal(M/F) hs
    (by rwa [IsGalois.card_aut_eq_finrank]) (by rwa [IsGalois.card_aut_eq_finrank])
  refine ⟨IntermediateField.fixedField N, ?_, ?_, IsGalois.of_fixedField_normal_subgroup N, ?_⟩
  · intro h
    apply htop
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_bot]
  · intro h
    apply hbot
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_top]
  · rcases hM with hM | hM
    · left
      exact IsTotallyReal.of_algebra (IntermediateField.fixedField N) M
    · apply rc_of_intermediateField_stable_under_complexConj
      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      intro n hn
      obtain ⟨Φ⟩ : Nonempty (M →+* ℂ) := inferInstance
      apply Φ.injective
      have h2 := IsCMField.complexEmbedding_complexConj M (Φ.comp n.toRingHom) x
      change Φ (n (IsCMField.complexConj M x)) = (starRingEnd ℂ) (Φ (n x)) at h2
      rw [h2, hx n hn, IsCMField.complexEmbedding_complexConj]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDescentToLevelGroupOfUnramified
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective K L)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  have hc : IsClosed ((K.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    (hK.isCompact.image W.continuous_resP).isClosed
  have hN : NS Ω V.S' ≤ (K.map (W.resP L Ω)).normalCore := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.normalCore_isClosed _ hc)
    intro g hg b
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    have hl : IsLift (RingEquiv.refl (W.Lp L)) (b⁻¹).toRingEquiv := fun x => (b⁻¹).commutes x
    have hAA : ∀ x, (b⁻¹).toRingEquiv x ∈ A ↔ x ∈ A.comap (b⁻¹).toRingEquiv.toRingHom := fun x => Iff.rfl
    have h1 : b * g * b⁻¹ ∈ Ine (F := W.Lp L) (A.comap (b⁻¹).toRingEquiv.toRingHom) := conjGal_mem_Ine hl hAA hg
    have hA' : IsPlaceOver (A.comap (b⁻¹).toRingEquiv.toRingHom) v := fun x => by
      rw [← val_lt_one hAA, ← hA x]
      exact Iff.of_eq (congrArg (fun y => A.valuation y < 1) ((b⁻¹).commutes (x : W.Lp L)))
    obtain ⟨t, ht⟩ := s.unr _ _ hA' h1
    obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA'
    refine ⟨t, hI w (by rw [hwv]; exact hv) _ hw ?_, ht⟩
    rw [← ht] at h1
    exact h1
  intro g hg
  have h1 : W.resP L Ω g ∈ NS Ω V.S' := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hg)
  obtain ⟨t, ht, e⟩ := Subgroup.normalCore_le _ (hN h1)
  have : t = g := AlgEquiv.ext fun x => DFunLike.congr_fun e x
  exact this ▸ ht

private theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

private theorem ker_closed {H k : Type} [Group H] [TopologicalSpace H] [CommRing k] [TopologicalSpace k] [T2Space k] {n : ℕ}
    (r : H →* GL (Fin n) k) (hr : Continuous r) : IsClosed (r.ker : Set H) := by
  have h : (r.ker : Set H) = {g | ∀ i j, (r g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j} :=
    Set.ext fun g => ⟨fun hg i j => by rw [show r g = 1 from hg]; rfl, fun hg => Units.ext (Matrix.ext hg)⟩
  rw [h, Set.setOf_forall]
  refine isClosed_iInter fun i => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun j => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g => (r g).val := Units.continuous_val.comp hr
  exact hv.matrix_elem i j

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.exists_descent_to_level_group_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, r g = 1) → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ ρ.comp V.pr = r ∧ ∀ P, Af.IsPairing s.c r (cycBar L Ω l ^ (1 - (n : ℤ))) P → V.frame.IsForm c.O n ρ P := by
  intro l _ L Ω _ _ _ _ _ _ s n V c r hcont hI
  have hker : V.pr.ker ≤ r.ker :=
    ker_pr_le V _ (ker_closed r hcont) fun w hw A hA t ht => hI w hw A hA t ht
  let ρ : V.frame.G₀ →* GL (Fin n) (Qbar l) := V.pr.liftOfSurjective (pr_surj V) ⟨r, hker⟩
  have hρ : ∀ g, ρ (V.pr g) = r g := fun g => V.pr.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨ρ, ?_, MonoidHom.ext hρ, fun P hP g => ?_⟩
  · haveI := isClosed_NS Ω V.S'
    have hq : Topology.IsQuotientMap V.pr :=
      (V.pr_cont W.continuous_resP).isClosedMap.isQuotientMap (V.pr_cont W.continuous_resP) (pr_surj V)
    exact hq.continuous_iff.2 (hcont.congr fun g => (hρ g).symm)
  · obtain ⟨t, rfl⟩ := pr_surj V g
    obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    have e1 : V.frame.conj (V.pr t) = V.pr t' := Subtype.ext (by
      show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
      rw [ht', map_mul, map_mul, map_inv])
    have e2 := hP t t' ht'
    have e3 : V.ε (V.pr t).1 = cycZ L Ω l t := DFunLike.congr_fun V.hε (W.resP L Ω t)
    have e4 : V.frame.eps c.O (Qbar l) (V.pr t) = cycBar L Ω l t := by
      refine Units.ext ?_
      show ((algebraMap ℤ_[l] c.O (V.ε (V.pr t).1 : ℤ_[l]ˣ) : c.O) : Qbar l) = _
      rw [e3]
      rfl
    rw [e1, e4]
    show (ρ (V.pr t)).val.transpose * _ * (ρ (V.pr t')).val = _
    rw [hρ, hρ]
    exact e2
end
