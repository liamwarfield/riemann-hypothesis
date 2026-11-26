module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocFamilyFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      {Q : Ideal (MRing (extIdx ι J) O) | Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W}.Finite

def MultiHomogPrimeAvoid.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (S : Set (Ideal (MRing ι R))), S.Finite →
    (∀ Q ∈ S, Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q) →
    ∃ (e : K → ℕ) (L : MRing ι R), IsMultiHomog L e ∧ (∀ k, 1 ≤ e k) ∧ ∀ Q ∈ S, L ∉ Q

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCentreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocCentreDom.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)), 𝔫.IsMaximal →
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            ∀ b ∈ 𝔫, ¬ IsUnit (Subring.inclusion h b)

def BlowUpOverLocLocalization.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
        blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔭 : Ideal (blowUpOverLoc P W u))
          (h𝔭 : 𝔭.IsPrime),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔭
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutPreimage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutPreimage.Statement : Prop :=
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
    ∀ (k : ℕ), k < N → ∀ (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      W.IsPrime → IsRelevant W → pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
      ∃ u : MRing (bundleIdx (bundleIdx ι M) M') O, u ∉ W ∧
        ∀ q ∈ pointIdeal O (flagClosurePt y w e φ φ' t k), ∃ n : ℕ,
          u ^ n * q ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔
            (pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k)).map
              (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M')))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocPointLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocPointLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
        blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SegreFlagCutSection.proof (hModel : SegreFlagClosureModel.Statement)
    (hForms : SegreFlagCutForms.Statement) (hDiv : SegreFlagCutDivisor.Statement)
    (hD0 : SegreFlagDegreeZero.Statement) : SegreFlagCutSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk r a ha
  classical
  set I := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hI
  have hIp : I.IsPrime := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht (k + 1) (Nat.le_add_left 1 k) hk).1.multiProj.isPrime
  have hpt : ∀ (j : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t j ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl
  have hlift : ∀ i, liftPairForm M M' (a i) ∉ I := fun i hm =>
    ha i ((liftPairForm_mem_iff (hpt (k + 1)) _).1 hm)
  obtain ⟨f₃, g₃, hD₃, hv₃, hk₃⟩ := hD0 O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk

  let bad : MRing (bundleIdx (bundleIdx ι M) M') O → Set (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) :=
    fun z => {Q | Q ∈ (I ⊔ Ideal.span {z}).minimalPrimes ∧ IsRelevant Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q}
  let T := bad f₃ ∪ bad g₃ ∪ ⋃ i, bad (liftPairForm M M' (a i))
  have hbfin : ∀ z, (bad z).Finite := fun z =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I ⊔ Ideal.span {z})).subset fun Q hQ => hQ.1
  have hTfin : T.Finite := ((hbfin _).union (hbfin _)).union (Set.finite_iUnion fun i => hbfin _)
  have hbad : ∀ z, ∀ Q ∈ bad z, Q.IsPrime ∧ IsRelevant Q ∧ I ≤ Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q :=
    fun _ _ hQ => ⟨Ideal.IsMinimalPrime.isPrime hQ.1, hQ.2.1,
      le_sup_left.trans (Ideal.IsMinimalPrime.le hQ.1), hQ.2.2⟩
  obtain ⟨cs, ch, s, h, hs, hh, hdeg, hsI, hhI, hval, havoid⟩ :=
    hForms O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      hTfin.toFinset (by
        intro Q hQ
        rcases (hTfin.mem_toFinset.1 hQ) with (hQ | hQ) | hQ
        · exact hbad _ Q hQ
        · exact hbad _ Q hQ
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hQ
          exact hbad _ Q hi)
  have hdiv := hDiv O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
    cs ch s h hs hh hdeg hsI hhI hval
  refine ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsI, hhI, hval, hdiv, hD₃, hv₃, hk₃, ?_⟩
  intro H hH hϖH
  by_cases hh0 : divCycle I h H = 0
  ·
    have hs0 : divCycle I s H ≠ 0 := hH.resolve_right (not_not.2 hh0)
    have hne : ratDiv I s h H ≠ 0 := by
      unfold ratDiv
      rw [hh0, sub_zero]
      exact hs0
    rw [hdiv H hϖH] at hne
    split_ifs at hne with hc
    · obtain ⟨hk0, rfl⟩ := hc
      obtain ⟨hf, hg, -⟩ := hk₃ hk0
      exact ⟨hf, hg, fun i hm => ha i ((liftPairForm_mem_iff (hpt k) _).1 hm)⟩
    · exact absurd rfl hne
  ·
    obtain ⟨hmin, hrel⟩ := relevant_minimal_of_divCycle_ne_zero hh0
    have hhH : h ∈ H :=
      Ideal.IsMinimalPrime.le hmin (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    have avoid : ∀ z, z ∉ I → (H ∈ bad z → H ∈ T) → z ∉ H := by
      intro z hz hT hzH
      exact havoid H (hTfin.mem_toFinset.2 (hT ⟨mem_minimalPrimes_sup_span_of_mem hmin hz hzH, hrel, hϖH⟩)) hhH
    exact ⟨avoid f₃ hD₃.num_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_left _ h'),
      avoid g₃ hD₃.den_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_right _ h'),
      fun i => avoid _ (hlift i) fun h' => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, h'⟩)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMaxPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_of_isLocalization_atPrime' {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMaxPoint.proof (h₁ : BlowUpOverLocMaxCentre.Statement.{u})
    (h₂ : BlowUpOverLocFibreMinimal.Statement.{u}) (h₃ : BlowUpOverLocPointDeg.Statement.{u}) :
    BlowUpOverLocMaxPoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  have hmin := h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h', 𝔫', h𝔫', hl', hdeg⟩ :=
    h₃ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hmin hW'r hW'c
  have := h𝔫.isPrime
  have := h𝔫'.isPrime
  have heq : 𝔫 = 𝔫' := prime_eq_of_isLocalization_atPrime' h 𝔫 𝔫' hl hl'
  subst heq
  exact ⟨W', ⟨hmin, hW'r, hW'c⟩, ⟨h, hl⟩, hdeg⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocPointMax.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hiso : BlowUpLocRingIso.Statement.{u}) (hfrac : BlowUpLocRingFrac.Statement.{u}) : BlowUpOverLocPointMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : 𝔫.IsPrime := Ideal.comap_isPrime (Subring.inclusion hBR) (IsLocalRing.maximalIdeal _)
  have h𝔫 : 𝔫.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  have := h𝔫.isPrime
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ :=
      hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagProjTrdegLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagProjTrdegLe

theorem trdeg_quot_ker_eq_range {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (hg : Function.Injective g) :
    Algebra.trdeg R (A ⧸ RingHom.ker f) = Algebra.trdeg R (g.comp f).range := by
  have hker : RingHom.ker (g.comp f) = RingHom.ker f := by
    ext a
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    exact ⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  rw [← hker]
  exact (Ideal.quotientKerEquivRange (g.comp f)).trdeg_eq

theorem rename_comp_pointConeMap {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O).comp
        (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p))) =
      (pointConeMap O pt).comp (rename (FieldNumbers.blockIncl j ι')) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [pointConeMap, FieldNumbers.blockIncl]

theorem trdeg_blocks_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  have hren : Function.Injective ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O) :=
    rename_injective _ j.injective
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), rename_comp_pointConeMap,
    AlgHom.id_comp]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

theorem trdeg_blocks_add_one_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ]
    (hO : Function.Injective (algebraMap O Φ)) {Λ K' : Type} (ι' : Λ → Type) (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ)
    (b : Λ) (hjb : ∀ o, j o ≠ b) (l : ι' b) (hc : pt ⟨b, l⟩ ≠ 0) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) + 1 ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  classical
  let ren : MvPolynomial K' Φ →ₐ[O] MvPolynomial Λ Φ :=
    (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O
  have hren : Function.Injective ren := rename_injective _ j.injective
  let F := ren.comp (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p)))
  let z : MvPolynomial Λ Φ := C (pt ⟨b, l⟩) * X b
  have hLO : Function.Injective (algebraMap O (MvPolynomial Λ Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial Λ Φ)]
    exact (C_injective Λ Φ).comp hO

  let ψ : MvPolynomial Λ Φ →+* Polynomial (MvPolynomial Λ Φ) :=
    eval₂Hom (Polynomial.C.comp C)
      (fun o => if o = b then Polynomial.C (C (pt ⟨b, l⟩)⁻¹) * Polynomial.X else Polynomial.C (X o))
  have hψren : ψ.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom =
      Polynomial.C.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ψ]
    · intro o
      simp [ψ, hjb o]
  have hψz : ψ z = Polynomial.X := by
    simp only [ψ, z, map_mul, eval₂Hom_C, eval₂Hom_X', if_true, RingHom.comp_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one, one_mul]
  have hadj : Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ)) = F.range := Algebra.adjoin_eq _
  have htr : Transcendental (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) z := by
    rw [transcendental_iff]
    intro p hp
    have hψA : ψ.comp (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ)) =
        Polynomial.C.comp (algebraMap _ (MvPolynomial Λ Φ)) := by
      ext ⟨a, ha⟩ : 1
      obtain ⟨q, rfl⟩ : a ∈ F.range := hadj ▸ ha
      exact RingHom.congr_fun hψren _
    have h := congrArg ψ hp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hψA, hψz, map_zero] at h
    exact Polynomial.map_injective (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ))
      Subtype.val_injective (by rw [Polynomial.map_zero]; exact h)
  have hadd := AdjoinTrdegAdd.proof O (MvPolynomial Λ Φ) hLO (F.range : Set (MvPolynomial Λ Φ)) {z} Unit
    (fun _ => z) (by rintro _ ⟨_, rfl⟩; rfl) ((algebraicIndependent_unique_type_iff).2 htr)
    (fun a ha => by
      rw [Set.mem_singleton_iff.1 ha]
      exact isAlgebraic_algebraMap
        (⟨z, Algebra.subset_adjoin (Set.mem_union_right _ ⟨(), rfl⟩)⟩ :
          Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ Set.range fun _ : Unit => z)))
  rw [hadj, Fintype.card_unit, Nat.cast_one] at hadd
  have hle : Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ {z}) ≤ (pointConeMap O pt).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (⟨q, rfl⟩ | hz)
    · exact ⟨rename (FieldNumbers.blockIncl j ι') q,
        (AlgHom.congr_fun (rename_comp_pointConeMap (O := O) ι' j pt) q).symm⟩
    · rw [Set.mem_singleton_iff.1 hz]
      exact ⟨X ⟨b, l⟩, by simp [pointConeMap, z]⟩
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), AlgHom.id_comp]
  change Algebra.trdeg O F.range + 1 ≤ _
  rw [← hadd]
  exact trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective _)

def zeroNewBlocks {O K : Type} [CommRing O] {ι : K → Type} {M M' : ℕ} :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → MRing ι O
  | ⟨some (some k), i⟩ => X ⟨k, i⟩
  | ⟨some none, _⟩ => 0
  | ⟨none, _⟩ => 0

theorem trdeg_flag_zero_le {O Ω K : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : K → Type} {N M M' : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
    (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (flagClosurePt y w e φ φ' t 0)) ≤
      Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) := by
  let ren : MvPolynomial K Φ →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (rename (fun k : K => some (some k)) : MvPolynomial K Φ →ₐ[Φ] _).restrictScalars O
  have hren : Function.Injective ren :=
    rename_injective _ ((Option.some_injective _).comp (Option.some_injective _))
  have hG : pointConeMap O (flagClosurePt y w e φ φ' t 0) =
      (ren.comp (pointConeMap O (fun p => algebraMap Ω Φ (y p)))).comp (aeval (zeroNewBlocks (O := O))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨(_ | _ | k), i⟩ <;>
      simp [ren, pointConeMap, flagClosurePt, pairProjCoord, projCoord, flagCoord, zeroNewBlocks]
  rw [← pointIdeal_algebraMap (O := O) (Φ := Φ) y]
  unfold pointIdeal
  rw [trdeg_quot_ker_eq_range (pointConeMap O (flagClosurePt y w e φ φ' t 0)) (AlgHom.id O _) (fun _ _ h => h),
    trdeg_quot_ker_eq_range (pointConeMap O (fun p => algebraMap Ω Φ (y p))) ren hren, AlgHom.id_comp, hG]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

end FlagProjTrdegLe


open FlagProjTrdegLe in
theorem FlagProjTrdegLe.proof (hTr : SegreFlagClosureTrdeg.Statement) : FlagProjTrdegLe.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hkN

  have hO : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    refine (FaithfulSMul.algebraMap_injective Ω Φ).comp ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := trdeg_flag_zero_le (O := O) y w e φ φ' t
    simp only [Nat.cast_zero, add_zero]
    exact ⟨(trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t 0)).trans h0,
      (trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t 0)).trans h0⟩
  · have hH := hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN.le

    have hne : ∀ kk, ∃ i, y ⟨kk, i⟩ ≠ 0 := fun kk => by
      obtain ⟨i, hi⟩ := hV.multiProj.relevant kk
      refine ⟨i, fun h0 => hi ?_⟩
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    choose c hc using hne
    have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun kk _ => hc kk
    have hli := ht.linearIndependent
    obtain ⟨l', hl'⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ'
      (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN.le
    obtain ⟨l, hl⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ
      (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN.le
    have key : ∀ a : Cardinal, a + 1 ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal) →
        a ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) := by
      intro a ha
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at ha
      exact Cardinal.add_one_le_add_one_iff.1 ha
    refine ⟨key _ ?_, key _ ?_⟩
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t k) none (fun o => Option.some_ne_none o) l' hl'
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t k) (some none) (by rintro (_ | _) h <;> cases h) l hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
