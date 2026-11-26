module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChartSection.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}) ∧
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection IsProjVarF)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)

namespace PairNumberJoinLeft

theorem verticalComponentFibre : VerticalComponentFibre.Statement :=
  VerticalComponentFibre.proof (FibreVarieties.proof GenericFibProps.full GenericDimBound.full
    GenericDimGe.proof SpecialIdealCorresp.full SpecialIdealMultiHomog.full SupSpanMultiHomog.full
    MinimalPrimeMultiHomog.full SpecialQuotDim.full ComponentDim.proof)

theorem pairNum_fieldNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ)
    (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d) (I : IFamily (IsLocalRing.ResidueField O) ι)
    (hI : IsFieldIntersection I) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IsVertDiv O P (y l - y' l) (f l) (g l)) (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hM⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv : IsVerticalDivisor P ϖ (y l - y' l) (f l) (g l) :=
    (VerticalDivisorCharacterisation.proof O K ι P ϖ _ _ _ hϖ hM.multiProj).mp (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P (f l) (g l) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    apply hW'
    simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
  have hVar : IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hVar
  · rfl

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def assocSigma (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl (.inl k), i⟩ => ⟨.inl k, i⟩
    | ⟨.inl (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
    | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl (.inl k), i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inl (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr k, i⟩
  left_inv := by rintro ⟨(k | k) | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | k | k, i⟩ <;> rfl

theorem assocSigma_fst (v : Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) :
    (assocSigma ι ι' ι₂ v).1 = Equiv.sumAssoc K K' K₂ v.1 := by
  obtain ⟨(k | k) | k, i⟩ := v <;> rfl

theorem assocSigma_symm_fst (v : Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) :
    ((assocSigma ι ι' ι₂).symm v).1 = (Equiv.sumAssoc K K' K₂).symm v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem pointIdeal_map_rename {K₁ K₃ : Type} {κ₁ : K₁ → Type} {κ₃ : K₃ → Type} (R : Type) [CommRing R]
    {Ω : Type} [Field Ω] [Algebra R Ω] (e : K₁ ≃ K₃) (σ : (Σ k, κ₁ k) ≃ (Σ k, κ₃ k))
    (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, κ₁ k) → Ω) :
    (pointIdeal R y).map (rename σ) = pointIdeal R (y ∘ σ.symm) := by
  have hp : ∀ p, (σ.symm p).1 = e.symm p.1 := fun p => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  have key : (pointConeMap R y).comp (rename σ.symm) =
      ((rename e.symm).restrictScalars R).comp (pointConeMap R (y ∘ σ.symm)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hp]
  have hmap : (pointIdeal R y).map (rename σ) = (pointIdeal R y).comap (rename σ.symm) := by
    have h := Ideal.map_comap_of_equiv (I := pointIdeal R y) (renameEquiv R σ).toRingEquiv
    exact h
  rw [hmap]
  ext f
  rw [Ideal.mem_comap]
  unfold pointIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  change (pointConeMap R y) (rename σ.symm f) = 0 ↔ _
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ e.symm.injective)

theorem assocDeg_comp (b : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) b ∘ Equiv.sumAssoc K K' K₂ = joinDeg (K' := K₂) b := by
  funext k
  rcases k with (k | k) | k <;> rfl

theorem rename_assocVar {R : Type} [CommRing R] (f : MRing (Sum.elim ι ι') R) :
    rename (assocVar ι₂) f = rename (assocSigma ι ι' ι₂) (joinForm (ι' := ι₂) f) := by
  rw [joinForm, rename_rename]
  refine congrArg (fun φ => rename φ f) ?_
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem fnField_assoc (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (hfn : fnField O (joinCoord x (joinCoord z w)) = fnField O (joinCoord x z)) :
    fnField O (joinCoord (joinCoord x z) w) = fnField O (joinCoord x z) := by
  apply le_antisymm
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨(k | k) | k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, i, j⟩, rfl⟩)
    · rw [← hfn]
      exact Subfield.subset_closure (Or.inr ⟨⟨.inr (.inr k), i, j⟩, rfl⟩)
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)

end PairNumberJoinLeft


open PairNumberJoinLeft in
theorem PairNumberJoinLeft.proof (hPull : PairNumberPullback.Statement)
    (hVert : JoinVerticalDivisorLeft.Statement) (hBir : BirationalJoin.Statement) :
    PairNumberJoinLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  let _ := Classical.decEq K
  let _ := Classical.decEq K'
  let _ := Classical.decEq K₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hvZ : ∀ i, IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w)))
      (assocDeg (K₂ := K₂) (a i) - assocDeg (K₂ := K₂) (a' i))
      (rename (assocVar ι₂) (f i)) (rename (assocVar ι₂) (g i)) := by
    intro i
    have h := hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)
    convert h using 1
    funext k
    rcases k with k | k | k <;> simp [assocDeg]
  rw [pairNum_fieldNum _ d hF I₁ hI₁ _ _ _ _ hv, pairNum_fieldNum _ d hZ I hI _ _ _ _ hvZ,
    BundleExamples.pairNum_eq _ d _ _ _ _ hH, BundleExamples.pairNum_eq _ d _ _ _ _ hH]
  set Gs := fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l H) with hGs
  have hσ := assocSigma_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hσ' := assocSigma_symm_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hPZ : (pointIdeal O (joinCoords (joinCoords x z) w)).map (rename (assocSigma ι ι' ι₂)) =
      mcIdeal O (joinCoord x (joinCoord z w)) := by
    rw [pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂) _ hσ]
    change pointIdeal O _ = pointIdeal O _
    congr 1
    funext p
    obtain ⟨k | k | k, i⟩ := p <;> rfl
  have hZP : (mcIdeal O (joinCoord x (joinCoord z w))).map (rename (assocSigma ι ι' ι₂).symm) =
      pointIdeal O (joinCoords (joinCoords x z) w) := by
    rw [BundleExamples.mcIdeal_eq_pointIdeal,
      pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂).symm _ hσ']
    congr 1
    funext p
    obtain ⟨(k | k) | k, i⟩ := p <;> rfl
  have hrel := (PairNumberRelabel.proof O ϖ ((K ⊕ K') ⊕ K₂) (Sum.elim (Sum.elim ι ι') ι₂)
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) (Equiv.sumAssoc K K' K₂) (assocSigma ι ι' ι₂) hσ
    (pointIdeal O (joinCoords (joinCoords x z) w))).2.2 n (fun i => assocDeg (a i))
    (fun i => assocDeg (a' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs []
  rw [hPZ] at hrel
  simp only [← rename_assocVar, assocDeg_comp, List.map_nil] at hrel
  rw [hrel]
  have hmodF : IsModelOver (pointIdeal O (joinCoords x z)) d := by
    rw [BundleExamples.joinCoords_eq]
    exact ((BundleExamples.isModelOver_iff O _ d).mp hF).2
  have hmodZ : IsModelOver (pointIdeal O (joinCoords (joinCoords x z) w)) (d + 0) := by
    rw [← hZP]
    exact (PairNumberRelabel.proof O ϖ (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) ((K ⊕ K') ⊕ K₂)
      (Sum.elim (Sum.elim ι ι') ι₂) (Equiv.sumAssoc K K' K₂).symm (assocSigma ι ι' ι₂).symm hσ'
      (mcIdeal O (joinCoord x (joinCoord z w)))).1 d ((BundleExamples.isModelOver_iff O _ d).mp hZ).2
  have hbir : IsBirationalJoin O (joinCoords x z) w := by
    rw [BundleExamples.joinCoords_eq]
    exact hBir O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) K₂ ι₂ w (fnField_assoc O x z w hfn)
  have hvF : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords x z)) ϖ (a i - a' i) (f i) (g i) := by
    intro i
    rw [BundleExamples.joinCoords_eq]
    exact (VerticalDivisorCharacterisation.proof O (K ⊕ K') (Sum.elim ι ι') _ ϖ _ _ _ hϖ
      ((BundleExamples.isModelOver_iff O _ d).mp hF).2.multiProj).mp (hv i)
  have hexp := dividedDifferenceExpansion.proof n (d + 1) H hH
  have key := (hPull O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') K₂ ι₂ (joinCoords x z) w d 0 hmodF hmodZ n a a' f g
    hvF (d + 1) H hH Gs hexp [] (by simp)).2 hbir
  rw [BundleExamples.mcIdeal_eq_pointIdeal, ← BundleExamples.joinCoords_eq]
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxPointCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxCentre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpOverLocFibreMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
    ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
      blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes

def BlowUpOverLocPointDeg.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          (letI := (Subring.inclusion h).toAlgebra
           haveI := h𝔫.isPrime
           IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpLocRingFrac.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
          (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeDimLeTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) ≤ (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

def FlagProjTrdegLe.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (Function.Embedding.some o)) O ⧸
          pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) ∧
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O ⧸
          pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in
theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsLocFrac
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 TensorProduct

section Restrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def genPt (F : Type*) [Field F] (Q : Ideal (MRingOver F ι)) :
    (Σ k, ι k) → FractionRing (MRingOver F ι ⧸ Q) :=
  fun p => algebraMap (MRingOver F ι ⧸ Q) _ (Ideal.Quotient.mk Q (X p))

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]

def IsLocFrac (Q : Ideal (MRingOver (kap O) ι)) (F G : MRingOver O ι) : Prop :=
  ∃ α : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F α ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G α ∧ MvPolynomial.map (IsLocalRing.residue O) G ∉ Q

def stalk (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ s, mseg (genPt (kap O) Q) s ≠ 0 ∧
    ∃ e ∈ B.lat s, v = (aeval x F / aeval x G) • e}

def resRel (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :
    Set (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) :=
  {t | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ m m' : stalk O x Q B,
    (m' : V) = (aeval x F / aeval x G) • (m : V) ∧
    t = (aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) F) /
        aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) G)) ⊗ₜ m - 1 ⊗ₜ m'}

abbrev resFibre (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :=
  (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) ⧸
    Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B)

def resMap (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : stalk O x Q B →+ resFibre O x Q B :=
  (Submodule.mkQ _).toAddMonoidHom.comp
    (TensorProduct.mk ℤ (FractionRing (MRingOver (kap O) ι ⧸ Q)) (stalk O x Q B) 1).toAddMonoidHom

def resLat (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (s : ∀ k, ι k) : AddSubgroup (resFibre O x Q B) :=
  ((B.lat s).addSubgroupOf (stalk O x Q B)).map (resMap O x Q B)

def resSub (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (W : Submodule Ω V) :
    Submodule (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resFibre O x Q B) :=
  Submodule.span _ (resMap O x Q B '' {m | (m : V) ∈ W})

end Restrict

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle MRingOver)

def FullFlagRestriction.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ)
    (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (Q : Ideal (MRingOver (IsLocalRing.ResidueField O) ι)) [Q.IsPrime], ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) ≤ Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) = Q ∧
      ∃ B' : ChartBundle (IsLocalRing.ResidueField O)
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q)) N
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resFibre O x Q B),
        B'.lat = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resLat O x Q B ∧
        ∀ fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B,
          ∃ fl' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag (IsLocalRing.ResidueField O)
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) B',
            fl'.deg = fl.deg ∧ ∀ i, fl'.Vs i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resSub O x Q B (fl.Vs i)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpColonFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem pow_add_mul_eq_span_pow_mul {A : Type*} [CommRing A] {I : Ideal A} {k n₀ : ℕ} {y : A}
    (h : I ^ (n₀ + k) = Ideal.span {y} * I ^ n₀) (s : ℕ) :
    I ^ (n₀ + k * s) = Ideal.span {y ^ s} * I ^ n₀ := by
  have hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t) := by
    intro t
    induction t with
    | zero => simpa using h
    | succ t ih =>
      rw [show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih,
        show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ']

theorem mem_div_self_mul_of_mem_div_self {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    {P : Submodule A L} (Q : Submodule A L) {f : L} (hf : f ∈ P / P) : f ∈ (P * Q) / (P * Q) := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hf ⊢
  intro z hz
  refine Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (hf p hp) hq
  · rw [mul_add]
    exact add_mem ha hb

theorem BlowUpColonFinite.proof (h₁ : PowSpanFinrankBounded.Statement.{u})
    (h₂ : PrincipalReductionOfBoundedGens.Statement.{u}) : BlowUpColonFinite.Statement.{u} := by
  intro A _ _ _ _ L _ _ hinj _hdim I hI
  obtain ⟨k, hk, y, hy, n₀, hred⟩ := h₂ A I (h₁ A _hdim I)
  have hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap := LinearMap.ext fun _ => rfl
  have hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n =
      Submodule.map (Algebra.linearMap A L) (J ^ n) := fun J n => by
    rw [hlin]; exact (Submodule.map_pow _ _ n).symm
  set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘

  have hy0 : y ≠ 0 := by
    rintro rfl
    have : I ^ (n₀ + k) = ⊥ := by
      rw [hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
    exact pow_ne_zero _ hI this
  have hy' : algebraMap A L y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))

  have hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀ := by
    intro s
    rw [h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul,
      ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton,
      AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]

  have hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀ := by
    intro n f hf
    have hn : n ≤ n₀ + k * n := by nlinarith
    have hf' := mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf
    rw [← pow_add, Nat.add_sub_cancel' hn, hkey] at hf'
    rw [Submodule.mem_div_iff_forall_mul_mem] at hf' ⊢
    intro z hz
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_span_singleton_mul.mp
      (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))
    have : f * z = w := by
      apply mul_left_cancel₀ (pow_ne_zero n hy')
      rw [hweq]; ring
    rw [this]; exact hw

  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set c := algebraMap A L (a ^ n₀) with hc
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))
  have hcI : c ∈ 𝓘 ^ n₀ := by
    rw [h𝓘, hmap]; exact Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)
  have hfg : (𝓘 ^ n₀).FG := by
    rw [h𝓘, hmap]; exact (IsNoetherian.noetherian (I ^ n₀)).map _
  have hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG := by
    refine Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c)
      (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem] at hf
    rw [LinearMap.mulLeft_apply, mul_comm]
    exact hf c hcI
  exact hcol.of_le (iSup_le hle)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivFibreVariety
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorFibreVariety.proof : VerticalDivisorFibreVariety.Statement := by
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  exact VerticalDivisorSupportFibre.proof O K ι P d hP b f g hV W (Finsupp.mem_support_iff.mp hW)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem subring_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R₁ R₂ : Subring F}
    (h₁ : B ≤ R₁) (h₂ : B ≤ R₂) (𝔭 : Ideal B) [𝔭.IsPrime]
    (hl₁ : letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭)
    (hl₂ : letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) : R₁ = R₂ := by
  have key : ∀ (R₁ R₂ : Subring F) (h₁ : B ≤ R₁) (h₂ : B ≤ R₂),
      (letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭) →
      (letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) → R₁ ≤ R₂ := by
    intro R₁ R₂ h₁ h₂ hl₁ hl₂ z hz
    let _ := (Subring.inclusion h₁).toAlgebra
    let _ := (Subring.inclusion h₂).toAlgebra
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔭.primeCompl (⟨z, hz⟩ : R₁)
    obtain ⟨t, ht⟩ := (IsLocalization.map_units R₂ s).exists_right_inv
    have e₁ : z * ((s : B) : F) = ((b : B) : F) := congrArg Subtype.val hbs
    have e₂ : ((s : B) : F) * (t : F) = 1 := congrArg Subtype.val ht
    have hzt : z = (b : F) * t := by
      calc z = z * (((s : B) : F) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : B) : F)) * t := by ring
        _ = (b : F) * t := by rw [e₁]
    rw [hzt]
    exact R₂.mul_mem (h₂ b.2) t.2
  exact le_antisymm (key R₁ R₂ h₁ h₂ hl₁ hl₂) (key R₂ R₁ h₂ h₁ hl₂ hl₁)

theorem prime_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMax.proof (h₁ : BlowUpOverLocMaxPoint.Statement.{u})
    (h₂ : BlowUpOverLocPointMax.Statement.{u}) (h₃ : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  have hpt := h₁ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hmx := h₂ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  choose f hfT hfloc hfdeg using
    fun 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} => hpt 𝔫.1 𝔫.2

  have hmh : ∀ W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes, IsMultiHomogIdeal W' :=
    fun W' hW' => MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨f 𝔫, hfT 𝔫⟩) ⟨?_, ?_⟩, fun 𝔫 => ⟨hfloc 𝔫, hfdeg 𝔫⟩⟩
  ·
    intro 𝔫₁ 𝔫₂ h12
    have hf : f 𝔫₁ = f 𝔫₂ := congrArg Subtype.val h12
    have hl₁ := hfloc 𝔫₁
    rw [hf] at hl₁
    obtain ⟨k₁, l₁⟩ := hl₁
    obtain ⟨k₂, l₂⟩ := hfloc 𝔫₂
    have := 𝔫₁.2.isPrime
    have := 𝔫₂.2.isPrime
    exact Subtype.ext (prime_eq_of_isLocalization_atPrime k₂ 𝔫₁.1 𝔫₂.1 l₁ l₂)
  ·
    rintro ⟨W', hW'⟩
    obtain ⟨k, 𝔫, h𝔫, hl⟩ := hmx W' hW'.1 hW'.2.1 hW'.2.2
    refine ⟨⟨𝔫, h𝔫⟩, Subtype.ext ?_⟩
    obtain ⟨k', hl'⟩ := hfloc ⟨𝔫, h𝔫⟩
    have := h𝔫.isPrime
    have hring : blowUpLocRing P u (f ⟨𝔫, h𝔫⟩) = blowUpLocRing P u W' :=
      subring_eq_of_isLocalization_atPrime k' k 𝔫 hl' hl
    have hT := hfT ⟨𝔫, h𝔫⟩
    exact h₃ O K ι J P u _ _ hT.1.1.1 (hmh _ hT.1) hT.2.1 (le_trans le_sup_left hT.1.1.2)
      hW'.1.1.1 (hmh _ hW'.1) hW'.2.1 (le_trans le_sup_left hW'.1.1.2) hring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
