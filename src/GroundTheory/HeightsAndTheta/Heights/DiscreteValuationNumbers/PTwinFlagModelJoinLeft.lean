module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar assocDeg assocVar FlagModel)

namespace FlagModelJoinLeftAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_pullDeg (a : K → ℤ) :
    assocDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K' ⊕ K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem assocVar_comp_liftVar :
    assocVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι' ι₂) :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinLeftAlt


open FlagModelJoinLeftAlt in
theorem FlagModelJoinLeftAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinLeft.Statement) (hNum : PairNumberJoinLeft.Statement) :
    FlagModelJoinLeftAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  refine (hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ
    (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r) _ _ _ _ hvert _ hH).trans ?_
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, assocDeg_pullDeg, assocVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold divCycle; rw [dite_eq_right h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : MRing ι O) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold divCycle
    rw [dite_eq_left hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime;
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (MRing (extIdx ι J) O) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (MRing (extIdx ι J) O),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0 := by
          unfold divCycle
          rw [dite_eq_right]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1 := by
    unfold divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPlainValueIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPlainValueIndependence

theorem vEval_intNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (d : ℕ) {m : ℕ} (deg : Fin m → K → ℤ)
    (H : MvPolynomial (Fin m) ℤ) (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d deg H) Z =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
        (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          W d deg H) Z := by
  classical
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hV := hZ W (Finsupp.mem_support_iff.mp hW)
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h
  · rw [Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hV]
  · rfl

theorem pairNum_intNum (hSupp : VerticalDivisorSupportFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V}
    (hM : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (r : ℕ) (L : Fin r → K → ℤ)
    (H : MvPolynomial (Fin (N + r)) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                              (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
                              (Fin.append φ.g fun _ => 1) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
        (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
        (Fin.append φ.g fun _ => 1) H := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  induction l using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact vEval_intNum I hI d _ _ _ fun W hW => hSupp O K ι _ d hM _ _ _ (φ.vert i) W hW
  | right j =>
    simp only [Fin.append_right]
    have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 := sub_self _
    exact vEval_intNum I hI d _ _ _ fun W hW => absurd (by rw [h0]; rfl) hW

theorem exists_isFlagPair (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} (hN : 0 < N) {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V} {ϖ : O}
    (hϖ : Irreducible ϖ) (hM : IsModelOver (pointIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E') :
    ∃ w w' : Module.Basis (Fin N) Ω V, IsFlagPair ϖ x E E' w w' φ.deg φ.deg' φ.f φ.g := by
  have hne : ∀ k, ∃ j, x ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hM.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : ∃ c, segreVec x c ≠ 0 := ⟨c, Finset.prod_ne_zero_iff.mpr fun k _ => hc k⟩
  have hiff := hF O Ω K ι x N V E E' ϖ hϖ hM.multiProj
  obtain ⟨hl, hl'⟩ := hiff.2 hyc φ
  have hrank : Fintype.card (Fin N) = Module.finrank Ω V := by
    rw [Fintype.card_fin, ← finrank_top Ω V, ← φ.top, φ.dim]
    rfl
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl hrank,
    basisOfLinearIndependentOfCardEqFinrank hl' hrank, (hiff.1 _ _ _ _ _ _).mpr ⟨φ, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl hrank).symm
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl' hrank).symm

theorem proof (hFlag : FlagIndependence.Statement) (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hSupp : VerticalDivisorSupportFibre.Statement) : FlagPlainValueIndependence.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r L c Q hc hGc hQ
  rw [pairNum_intNum hSupp hM φ₁ I hI r L, pairNum_intNum hSupp hM φ₂ I hI r L,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ]
  refine Finset.sum_congr rfl fun μ hμ => congrArg (Q.coeff μ * ·) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : φ₁.deg = φ₂.deg := Subsingleton.elim _ _
    have h2 : φ₁.deg' = φ₂.deg' := Subsingleton.elim _ _
    have h3 : φ₁.f = φ₂.f := Subsingleton.elim _ _
    have h4 : φ₁.g = φ₂.g := Subsingleton.elim _ _
    rw [h1, h2, h3, h4]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, hM'⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
    have hS' := (BundleExamples.sameGeneric_iff hϖ x E E').mp hS
    obtain ⟨w₁, w₁', h₁⟩ := exists_isFlagPair hF hN hϖ hM' φ₁
    obtain ⟨w₂, w₂', h₂⟩ := exists_isFlagPair hF hN hϖ hM' φ₂
    have hE := dividedDifferenceExpansion.proof N c G hGc
    exact hFlag O ϖ hϖ Ω K ι x d hM' N V E E' hS' w₁ w₁' w₂ w₂' _ _ _ _ _ _ _ _ h₁ h₂ c G hGc hG _ _ hE hE
      (classList L μ) (by rw [classList_length_of_mem_support L hQ hμ]; omega)

end FlagPlainValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [Algebra O Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra O Φ]
  [IsScalarTower O Ω Φ]

theorem segreVec_algebraMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreVec (fun p => algebraMap Ω Φ (y p)) c = algebraMap Ω Φ (segreVec y c) := by
  simp [segreVec, map_prod]

theorem algebraMap_mem_chartRing_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {z : Ω}
    (hz : z ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Φ z ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c := by
  have hle : chartRing O (segreVec y) c ≤
      (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap
        (IsScalarTower.toAlgHom O Ω Φ) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈
      chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c
    rw [map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]
    exact div_mem_chartRing _ _ _
  exact hle hz

end Lemmas

theorem eq_repr_smul_basis_first {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (w : Module.Basis (Fin N) Ω E) (h0 : 0 < N) (v : E)
    (hv : ∀ j : Fin N, (⟨0, h0⟩ : Fin N) < j → w.repr v j = 0) :
    v = w.repr v ⟨0, h0⟩ • w ⟨0, h0⟩ := by
  conv_lhs => rw [← w.sum_repr v]
  refine Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)
  have hlt : (⟨0, h0⟩ : Fin N) < j := by
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    show 0 < (j : ℕ)
    omega
  rw [hv j hlt, zero_smul]

theorem SegreFlagClosureBirational.proof : SegreFlagClosureBirational.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hcΩ : segreVec y c ≠ 0 := by
    intro h
    apply hc
    rw [segreVec_algebraMap, h, map_zero]
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)
  have hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)

  have hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag.graded c hcΩ i0] at hmem
  obtain ⟨v, hv, hvj, hv0⟩ := hmem
  have hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag'.graded c hcΩ i0] at hmem'
  obtain ⟨v', hv', hvj', hv0'⟩ := hmem'
  have hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0 := by
    rw [← hv0]; exact eq_repr_smul_basis_first w hN v hvj
  have hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0 := by
    rw [← hv0']; exact eq_repr_smul_basis_first w' hN v' hvj'
  have hw' : w' i0 = w.repr (w' i0) i0 • w i0 :=
    eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj
  set u : Ω := w.repr (w' i0) i0 with hudef
  have hu : u ≠ 0 := by
    intro h
    apply w'.ne_zero i0
    rw [hw', h, zero_smul]

  choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv
  choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'
  set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef
  set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef
  have hD : D ≠ 0 := mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)
  have hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m) := by
    intro l m
    have hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k := by
      rw [← hαeq l, hv_eq, map_smul, smul_eq_mul]
    have hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) =
        β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k := by
      rw [← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]
    rw [hDdef, hGdef]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA +
      (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB
  have hprodΦ : ∀ (l : Fin M) (m : Fin M'),
      algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) =
        algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m)) := by
    intro l m
    have := congrArg (algebraMap Ω Φ) (hprod l m)
    simpa only [map_mul] using this

  set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT
  have hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0 := by
    intro j hj
    have : ¬ ((j : ℕ) < 1) := by
      intro h
      apply hj
      ext
      simp only [hi0]
      omega
    simp [flagCoord, this]
  have hfc0 : flagCoord w e t 1 i0 = T := by simp [flagCoord, hi0, hT]
  have hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' =
      (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0))) := by
    intro c'
    rw [segreVec, Fintype.prod_option, Fintype.prod_unique]
    exact congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))

  refine ⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)),
    algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), ?_, ?_⟩
  · intro h0
    apply hc₂
    have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only [mul_zero]
    rw [hseg]
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0
  · have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only
    rw [hseg, hseg]
    have h1 := hprodΦ (c₁ (some ())) (c₁ none)
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 -
      T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
