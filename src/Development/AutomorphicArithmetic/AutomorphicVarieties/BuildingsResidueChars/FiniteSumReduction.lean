module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.finiteSum_reduction :
    SumRed := by
  intro Γ k _ _ a b r r' ha hb hirr
  let W : Submodule k (Fin (a + b) → k) :=
    { carrier := {v | ∀ j : Fin b, v (Fin.natAdd a j) = 0}
      add_mem' := by
        intro x y hx hy j
        simp [hx j, hy j]
      zero_mem' := by
        intro j
        rfl
      smul_mem' := by
        intro c x hx j
        simp [hx j] }
  have hinv : Formalism.MainNotions.N.IsInv (Formalism.MainNotions.SumRepresentations.At.sumRep r r') W := by
    intro g v hv j
    have hM : ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a+b)) k) : Matrix (Fin (a+b)) (Fin (a+b)) k) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (((r g) : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) (0 : Matrix (Fin a) (Fin b) k)
            (0 : Matrix (Fin b) (Fin a) k) (((r' g) : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) := rfl
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    simp [hv _]
  have hne : W ≠ ⊥ := by
    intro h
    have hmem : (Pi.single (Fin.castAdd b ⟨0, ha⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      intro j
      rw [Pi.single_apply, if_neg]
      intro h'
      exact absurd h' (Fin.ne_of_val_ne (by simp; omega))
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem (Fin.castAdd b ⟨0, ha⟩)
    simp at this
  have hntop : W ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (Fin.natAdd a ⟨0, hb⟩) (1 : k) : Fin (a + b) → k) ∈ W := by
      rw [h]
      exact Submodule.mem_top
    have := hmem ⟨0, hb⟩
    simp at this
  rcases hirr.2.2 W le_top hinv with h | h
  · exact hne h
  · exact hntop h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

open GlobalTheory.SplitPts

variable {L : Type} [Field L] [NumberField L]

private theorem ic_mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h

variable [IsCMField L] {n : ℕ}

private theorem ic_sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc

private theorem ic_cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl

end

theorem UpperTheory.mem_maximalCompact_of_under_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n) (w w' : Plc E), w'.under (𝓞 (Lp E)) = w.under (𝓞 (Lp E)) → cLoc w x ∈ KO (w.adicCompletion E) (Fin n) → cLoc w' x ∈ KO (w'.adicCompletion E) (Fin n) := by
  intro E _ _ _ n x w w' h hx
  rcases ic_sameOver h with rfl | rfl
  · exact hx
  · rw [ic_cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.2 j i)))
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.1 j i)))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormCharacterOfFrobeniusCompatibility
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem UpperTheory.norm_character_of_frobenius_compatibility :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.Sol.CharFrob → UpperTheory.V.Af.Sol.NormChar := by
  intro P hC K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι η hη
  rcases hη with rfl | hN
  · exact ⟨1, rfl, Filter.Eventually.of_forall fun v => charEig_one ι v⟩
  obtain ⟨art, ha⟩ := P.litN.aut.art K Ω
  have hm : 0 < Module.finrank K M := Module.finrank_pos
  have hA : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd (χ := η) hm hN.2.1
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι hA
  have hE := hC K Ω l ι η δ ⟨hδc, art, 0, ha, hA, hL⟩
  refine ⟨δ, ?_, hE.mono fun v hv => hv.2⟩
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, CharEig ι (δ.comp (res K Ω M)) w 1 := by
    filter_upwards [hN.2.2, (tendsto_under' (K := K) (K' := M)).eventually hE] with w h1 h2
    have hf := normV_under (K := K) w
    have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ hf).2 δ _ h2.2
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res K Ω M s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom K M Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  exact MonoidHom.ext fun s => congrFun key s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HodgeTateWeightsOfLocalGlobal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl


open Formalism.BasicNotions.Loc in
private theorem ex_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') :
    ∃ j : W.Emb l w, j.1.comp (algebraMap F (w.adicCompletion F)) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
    have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
    refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
    exact iff_of_eq (congrArg (· < 1) h1.symm)
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

theorem UpperTheory.hodge_tate_weights_of_local_global :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w) (r : G L Ω →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ) (τ : SmIrr (GLw n w)) (lam : Wt L l n), Af.HasHT r HT → Af.LocGlob ι r w τ → (∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) = (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) → AtL ι h (r.comp (Dec (F := L) A).subtype) lam τ := by
  intro l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw _ _ _ _ rc hrc hab O _ _ _ Bw hj
  obtain ⟨h1, h2⟩ := hHT w A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj t LL' τ' hτ
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · exact ((hLG A h rc hrc).2 O Bw hj).2 (Or.inr hab) s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusConjOfGaloisConjugatePlaces
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
open scoped Pointwise

private theorem normV_pre {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conj {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem exists_pre {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (w w' : HeightOneSpectrum (𝓞 M)) (h : w'.under (𝓞 K) = w.under (𝓞 K)) :
    ∃ g : M ≃ₐ[K] M, preplace g.toRingEquiv w' = w := by
  have h' : w'.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  have := w.isPrime
  have := w'.isPrime
  have : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨rfl⟩
  have : w'.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := ⟨h'.symm⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (M ≃ₐ[K] M)
  refine ⟨g, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [mem_preplace, ← hg]
  exact Ideal.smul_mem_pointwise_smul_iff (a := g) (x := x)

theorem UpperTheory.frobenius_conj_of_galois_conjugate_places :
    UpperTheory.V.Af.Sol.FrobConj := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r w w' h
  obtain ⟨g, rfl⟩ := exists_pre w w' h
  refine ⟨(normV_pre _ _).symm, fun B hB A' hA' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) g.toRingEquiv
  let s : G K Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, hσ]
    exact congrArg (algebraMap M Ω) (g.commutes x)
  have key : ∀ t : G M Ω, r (resG K M Ω t) = r s * r (resG K M Ω (conjGal hσ t)) * (r s)⁻¹ := fun t => by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => (apply_conjGal hσ t x).symm
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun _ => Iff.rfl
  obtain ⟨h1, h2⟩ := hB _ (isPlaceOver_preplace hσ hA hA')
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have e : r (resG K M Ω (conjGal hσ t)) = 1 := h1 _ (conjGal_mem_Ine hσ hA ht)
    rw [MonoidHom.comp_apply, key, e, mul_one, mul_inv_cancel]
  · have e := h2 (conjGal hσ t) (by rw [normV_pre]; exact isFrob_conj hσ hA ht)
    rw [← e, ← map_inv (conjGal hσ), MonoidHom.comp_apply, MonoidHom.comp_apply, key t⁻¹,
      Units.val_mul, Units.val_mul, Matrix.coe_units_inv (r s), Matrix.charpoly_units_conj]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumHodgeTate
open UpperTheory.V.Af UpperTheory.V.Af.Gu

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst

private theorem map_sum' {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
    (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_sum {L : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {r₂ : ↥Gw →* GL (Fin b) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw r' L r₂) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') L (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) :=
  ⟨h₁.1, by rw [map_sum', h₁.2, h₂.2]⟩

private theorem dR_sum (h : IsdRAt (UpperTheory.V.Loc.PP l) Bw r) (h' : IsdRAt (UpperTheory.V.Loc.PP l) Bw r') :
    IsdRAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨_, _, model_sum n₁ n₂, (GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b _ _).1.2
    ⟨(n₁.isdRAt_iff _).1 h, (n₂.isdRAt_iff _).1 h'⟩⟩

private theorem jumps_sum {τ : E →+* Om l} {J J' : Multiset ℤ}
    (h : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r τ J) (h' : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r' τ J') :
    IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') τ (J + J') := by
  obtain ⟨L₁, r₁, m₁, d₁, τ₁, t₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, d₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  have t : IsInduced Bw τ (LL' := supExt L₁ L₂) ((IntermediateField.inclusion l₁).comp τ₁) := t₁
  have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b
    (mapRep (IntermediateField.inclusion l₁).toRingHom r₁) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
  refine ⟨_, _, model_sum n₁ n₂, S.1.2 ⟨(n₁.isdRAt_iff _).1 ⟨_, _, m₁, d₁⟩, (n₂.isdRAt_iff _).1 ⟨_, _, m₂, d₂⟩⟩,
    _, t, fun c => ?_⟩
  rw [S.2, ← h.count_eq _ n₁ t, ← h'.count_eq _ n₂ t, Multiset.count_add, Nat.cast_add]

end

theorem UpperTheory.sum_hodge_tate :
    SumHT := by
  intro E Ω _ _ _ _ _ l _ a b r r' _ _ HT HT' H H' w A hA O _ _ _ Bw hj
  obtain ⟨d, J⟩ := H w A hA O Bw hj
  obtain ⟨d', J'⟩ := H' w A hA O Bw hj
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e]
  exact ⟨dR_sum d d', fun τ L τ' t => jumps_sum (J τ L τ' t) (J' τ L τ' t)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterThird
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (algebraMap_isometry ℚ_[l] (PadicAlgCl l)).continuous
  have h3 : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l) :=
    h2.comp continuous_subtype_val
  exact (Continuous.units_map _ h3).comp h1
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont F Ω l

private theorem mem_plus {F₀ F : Type} [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F]
    [IsTotallyReal F₀] (x : F₀) : algebraMap F₀ F x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  exact DFunLike.congr_fun
    (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F₀ F)))) x

theorem UpperTheory.cyclotomicCharacter_plusPart :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.CycConj → UpperTheory.V.Af.Sol.ToPolC := by
  intro hA hC F Ω _ _ _ _ _ _ l _ ι n r hpol
  obtain ⟨F₀, _, _, _, _, _, _, hR, μ, c, P, hμ, hs, ⟨j, hj⟩, hp⟩ := hpol
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  letI : Algebra F₀ (maximalRealSubfield F) :=
    ((algebraMap F₀ F).codRestrict (maximalRealSubfield F) mem_plus).toAlgebra
  haveI : IsScalarTower F₀ (maximalRealSubfield F) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply F₀ F Ω x
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hcyc : IsAlgChar ι (cycBar (maximalRealSubfield F) Ω l ^ ((n : ℤ) - 1)) := by
    refine (hA (maximalRealSubfield F) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, (n : ℤ) - 1, 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hres := (hA F₀ Ω l ι).2.2 (maximalRealSubfield F) μ hμ
  obtain ⟨χ, hc, art, a, h1, h2, h3⟩ := ((hA (maximalRealSubfield F) Ω l ι).2.1 _ _ hcyc hres).1
  refine ⟨_, χ, c', P, ⟨hc, art, a, h1, h2, h3⟩, fun d d' hd hd' => ?_, ⟨j, hj⟩, fun s s' hss => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply]
    rw [hC _ Ω l d hd, hC _ Ω l d' hd', hs (resG F₀ _ Ω d) (resG F₀ _ Ω d') hd hd']
  · rw [hp s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hss x)]
    congr 2
    change μ (resG F₀ F Ω s) = cycBar F Ω l s ^ (1 - (n : ℤ)) * (cycBar F Ω l s ^ ((n : ℤ) - 1) * μ (resG F₀ F Ω s))
    rw [← mul_assoc, ← zpow_add]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalFrobeniusCompatibility
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one

private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩

private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (ReciprocityTheory.Gal.one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end UpperTheory.V.Af.Gu

theorem UpperTheory.total_frobenius_compatibility :
    HypothesesH → FrobTot := by
  intro P F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  have hrec : IsRec h rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc
  have hx := (H A h rc hrec).1 hl
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hsp := totPar_spec hrec n c a d ρ S hS
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace HalfDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end HalfDualProof

theorem UpperTheory.half_of_compatible_polarization :
    HypothesesH → Eta → TwistLoc → CompatPol → Half := by
  intro H hEta hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  obtain ⟨ξ, mξ, hξ, hN⟩ := hEta E (e + a - 1)
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  have hd : GlobalTheory.ContraPair.DualIsConj ((P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).twist ξ) := by
    rw [← CuspSub.twist_mul]
    exact Cq.csdTwist E a P 1 _ ((GlobalTheory.ContraPair.dualIsConjBy_one P).2
      (HalfDualProof.dualIsConj_of_isCsd (H.litN.aut.gk E a P) hP)) (by rw [hN, inv_one])
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ ξ mξ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) hξ hd σ hσ
  refine ⟨r, HT, ⟨hr.cont, hr.ss, hr.ht, fun w => (hr.par w).congr fun A h rc hrc => ?_⟩, fun τ => ?_⟩
  · obtain ⟨_, _, _, -, L⟩ := hrc
    rw [← L.nu_eq]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleCase
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC

private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]

private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]

theorem UpperTheory.irreducible_case :
    HypothesesH → IrrCase := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m H hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hn
  subst hn'
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (GlobalTheory.ContraPair.dualIsConjBy_one (P 0)).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E _ (P 0) 1 (by simpa only [inv_one, CuspSub.twist_one] using PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) ((GlobalTheory.GalOfCusp.isConjDualBy_one (P 0)).2 (H.csd 0))),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw⟩
  obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn1 π hπ τ
  rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
  refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
  rw [infOfWeight, Multiset.mem_map] at hz
  obtain ⟨j, -, rfl⟩ := hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationImageSpec
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_representation_image_spec :
    UpperTheory.V.Af.Sol.GalRange := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  let ρ : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hker : (resG K M Ω).range = ρ.ker := by
    ext σ
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨τ, rfl⟩
      ext x
      apply (algebraMap M Ω).injective
      rw [show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp [resG]
    · intro h
      have hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x := by
        intro x
        have := AlgEquiv.restrictNormal_commutes σ M x
        rw [show σ.restrictNormal M = ρ σ from rfl, h] at this
        simpa using this.symm
      refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
      ext x
      rfl
  refine ⟨hker ▸ ρ.normal_ker, ?_⟩
  rw [hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteCharacterOfAlgebraicCyclotomic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.finiteCharacter_of_algebraic_cyclotomic :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.FinChar := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro F Ω _ _ _ _ _ l _ ι δ hopen
    obtain ⟨h1, -, -⟩ := hA F Ω l ι
    have hcont : Continuous δ := by
      refine continuous_of_continuousAt_one δ ?_
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hopen.mem_nhds (Subgroup.one_mem _)] with x hx
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      rw [hx, map_one]
    haveI : Finite (Formalism.ConjugateSelfDual.G F Ω ⧸ δ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
    haveI : δ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    refine h1 δ hcont fun w _ => ?_
    obtain ⟨A, hAw⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hAw, 0, δ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun s _ => ?_⟩
    rw [neg_zero, zpow_zero, mul_one, ← map_pow]
    exact Subgroup.pow_index_mem δ.ker s
  · intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
    let E : IntermediateField K Ω := (IsScalarTower.toAlgHom K M Ω).fieldRange
    haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
    haveI : FiniteDimensional K E :=
      LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M Ω)).toLinearEquiv
    refine Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
    intro g hg
    have hfix : ∀ m : M, g (algebraMap M Ω m) = algebraMap M Ω m := by
      intro m
      exact (IntermediateField.mem_fixingSubgroup_iff E g).mp hg _ ⟨m, rfl⟩
    let g' : Formalism.ConjugateSelfDual.G M Ω := { g.toRingEquiv with commutes' := hfix }
    have hres : UpperTheory.V.Af.resG K M Ω g' = g := by
      ext x; rfl
    rw [MonoidHom.mem_ker, ← hres, ← MonoidHom.comp_apply, hδ, MonoidHom.one_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeBaseChangeAttached
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem exists_not_mem_asIdeal_pow_of_ne_zero (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)) : ∃ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f := by
  refine ⟨(w.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal, ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.asIdeal.under (𝓞 K)) (Ideal.IsPrime.under _ _) (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

private theorem tendsto_under_cofinite' (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] : Filter.Tendsto (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)
  refine Set.Finite.to_subtype (Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hfin.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h))
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨x.isPrime, ⟨rfl⟩⟩

private theorem algSat_pow_map_pow (n q f : ℕ) (B : Multiset ℂˣ) : algSat n (q ^ f) (Multiset.map (fun x => x ^ f) B) = Multiset.map (fun x => x ^ f) (algSat n q B) := by
  unfold algSat
  simp only [Multiset.bind_map, Multiset.map_map, Function.comp_def, Multiset.bind_singleton, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (by positivity)]

theorem UpperTheory.satake_base_change_attached :
    UpperTheory.V.Af.Sol.AttBc := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat sat' huniq hbc hatt hss
  refine ⟨hss, ?_⟩
  have hT := UpperTheory.frobenius_power_compatibility K M Ω l ι
  filter_upwards [hbc, (tendsto_under_cofinite' K M).eventually hatt.2] with w hw hv
  obtain ⟨f, hf⟩ := exists_not_mem_asIdeal_pow_of_ne_zero K M w
  obtain ⟨B, hB, hE⟩ := hv
  obtain ⟨B0, hB0, hB0'⟩ := hw f hf
  obtain rfl := huniq _ _ _ hB hB0
  refine ⟨_, hB0', ?_⟩
  have h2 := (hT w f hf).1 n r _ hE
  rw [hf, algSat_pow_map_pow]
  exact h2
end
