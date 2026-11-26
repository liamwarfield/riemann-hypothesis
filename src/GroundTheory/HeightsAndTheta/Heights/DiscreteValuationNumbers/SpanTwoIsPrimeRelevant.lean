module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthTwoGeneratorQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def commonExcess (ϖ : O) (P : Ideal (MRing ι O)) (f g s : MRing ι O) : ℕ :=
  ⨆ G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G}, (divCycle P s G.1 * ratDiv P f g G.1).toNat

end Defs

section Lemmas

def NoCommonComponentCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def CommonFactorInduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (P' : Ideal (MRing ι' O)) (d' : ℕ), IsModelOver P' (d' + 1) →
      ∀ (b' : K' → ℤ) (f' g' : MRing ι' O), IsEffectiveVertical P' ϖ b' f' g' →
      ∀ (c' : K' → ℕ) (s' : MRing ι' O), IsMultiHomog s' c' → s' ∉ P' →
      (∀ H, divCycle P' s' H ≠ 0 → (C ϖ : MRing ι' O) ∉ H → IsVerticalDivisor H ϖ b' f' g') →
      commonExcess ϖ P' f' g' s' < commonExcess ϖ P f g s →
      ∀ L' : Fin d' → K' → ℤ, cutIdentity ϖ P' b' f' g' c' s' L') →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_map {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibProps.proof : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

private theorem withBot_eq_of_add_one_eq (a : WithBot ℕ∞) (m : ℕ)
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [Nat.cast_add, Nat.cast_one, e] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) = (m + 1 : ℕ) := by
        apply WithBot.coe_injective
        simpa using h
      exact ENat.top_ne_natCast (m + 1) h'
    | coe a =>
      have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have : a + 1 = m + 1 := by exact_mod_cast h'
      have ham : a = m := by omega
      subst ham
      rfl

theorem FibreVarieties.proof
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  obtain ⟨hprime, hhomog, hforms⟩ := hGen O K ι P hP.multiProj hP.noTorsion
  have hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
      ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    congr 1; omega
  refine ⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩
  ·
    intro k
    obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    obtain ⟨-, h⟩ := hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi
    exact ⟨i, by simpa [MvPolynomial.map_X] using h⟩
  ·
    have h1 := hBound O K ι P hP.multiProj hP.noTorsion
    have h2 := hGe O K ι P hP.multiProj.isPrime hP.noTorsion
    rw [hP.dim, hcast] at h1 h2
    exact withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)
  ·
    intro W hW
    have hW0 := hW
    unfold divCycle at hW
    split_ifs at hW with h
    · obtain ⟨hWmin, hWrel⟩ := h
      have hWp : W.IsPrime := hWmin.1.1
      have hϖW : (C ϖ : MRing ι O) ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      obtain ⟨hsp, -, hrel, -⟩ := hCorr O ϖ hϖ K ι P W hWp hϖW
      have hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
        hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)
      have hWh : IsMultiHomogIdeal W := hMin O K ι _ W hJ hWmin
      have hϖP : (C ϖ : MRing ι O) ∉ P := by
        intro hmem
        have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
        rw [hP.noTorsion, Ideal.mem_bot] at this
        exact hϖ.ne_zero this
      refine ⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩
      rw [hQuot O ϖ hϖ K ι W hϖW]
      exact hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW
    · exact absurd rfl hW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorsCommute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem ratDiv_support_finite (h4 : DivCycleFiniteSupport.Statement.{u}) {O : Type u} [CommRing O]
    [IsNoetherianRing O] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) : (Function.support (ratDiv P f g)).Finite := by
  refine ((h4 O K ι P f).union (h4 O K ι P g)).subset ?_
  intro W hW
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem lt_natCast_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem VerticalDivisorsCommute.proof (h1 : CutByEffectiveDivisor.Statement.{u})
    (h2 : Representative.Statement.{u}) (h3 : IntNumAddFirst.Statement.{u})
    (h4 : DivCycleFiniteSupport.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  obtain ⟨c', c'', hc', hc'', hb'⟩ := hD'.degrees
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩
    · exact absurd rfl hW
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧
      (C ϖ : MRing ι O) ∉ H}.Finite :=
    ((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1
  obtain ⟨f₁, g₁, hV₁, hrat, hT₁⟩ := h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨hne, hϖH⟩ := hH
    rcases hne with hne | hne
    · obtain ⟨hm, hmin, hrel⟩ := hmh f' c' hc' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩
    · obtain ⟨hm, hmin, hrel⟩ := hmh g' c'' hc'' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)
  have e1 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L
  have e2 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L
  rw [hrat] at e1 e2

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) -
        vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · have hWg : divCycle P g W ≠ 0 := by
          intro hWg; apply hW; simp [ratDiv, hWf, hWg]
        obtain ⟨hm, hmin, -⟩ := hmh g bg hbg W hWg
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
      · obtain ⟨hm, hmin, -⟩ := hmh f bf hbf W hWf
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    obtain ⟨hWm, hWp, hPW⟩ := hWdata
    have := hWp
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := h10 (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L
    have hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ) := by
      rw [← hb']; funext k; simp
    rw [hsum] at key
    unfold vNum
    rw [key]; ring
  have hZfin := ratDiv_support_finite h4 P f g
  calc cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g)
      = cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c' k : ℤ)) L)) (ratDiv P f g) -
          cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c'' k : ℤ)) L)) (ratDiv P f g) := by
        unfold cycEval
        rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
          (hZfin.subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        by_cases hW : ratDiv P f g W = 0
        · simp [hW]
        · beta_reduce
          rw [hadd W hW, mul_sub]
    _ = _ := by rw [e1, e2]
    _ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by
        unfold cycEval
        rw [← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _))
          ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        rw [← sub_mul]
        change ratDiv P f' g' W * _ = ratDiv P f' g' W * _
        by_cases hW : ratDiv P f' g' W = 0
        · simp [hW]
        · beta_reduce
          rw [if_pos (hD'.vertical W hW)]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Length
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem lengthFormulaDimTwo : LengthFormulaDimTwo.Statement.{u} :=
  ReciprocityTheory.ChartRestriction.G.AI.length_two_generator_quotient

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairNumberRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairNumberRelabel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ P : Ideal (MRing ι₁ O),
      (∀ d : ℕ, IsModelOver P d → IsModelOver (P.map (rename σ)) d) ∧
      (∀ (b : K₂ → ℤ) (f g : MRing ι₁ O), IsVerticalDivisor P ϖ (b ∘ e) f g →
        IsVerticalDivisor (P.map (rename σ)) ϖ b (rename σ f) (rename σ g)) ∧
      (∀ (n : ℕ) (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
        (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)),
        pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs Q =
          pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPowSpanFinrankBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing Module

universe u

theorem PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (h : ringKrullDim A = 1) : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hbot
  have h0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)
  rw [h] at h0
  exact absurd h0 (by decide)

theorem PowSpanFinrankBounded.finrank_quotient_eq_length {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (finrank (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) : ℕ∞) =
      length A (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) := by
  have : Module.Finite (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective]
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact (Module.length_eq_finrank (A ⧸ maximalIdeal A) _).symm

theorem PowSpanFinrankBounded.spanFinrank_le_length {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (N : Ideal A) {x : A} (hx : x ∈ maximalIdeal A) :
    (N.spanFinrank : ℕ∞) ≤ length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N x)) := by
  have hle : LinearMap.range (LinearMap.lsmul A ↥N x) ≤ maximalIdeal A • (⊤ : Submodule A ↥N) := by
    rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  rw [spanFinrank_eq_finrank_quotient N (IsNoetherian.noetherian N),
    PowSpanFinrankBounded.finrank_quotient_eq_length]
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

theorem PowSpanFinrankBounded.proof : PowSpanFinrankBounded.Statement.{u} := by
  intro A _ _ _ _ h I
  obtain ⟨x, hxm, hx0⟩ := PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal h
  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (A := A) h
  have hA := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A A x h hx0
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top A hx0
  rw [finrank_self, Nat.cast_one, one_mul] at hA
  have hord : Ring.ord A x ≠ ⊤ := hA ▸ hfin
  refine ⟨(Ring.ord A x).toNat, fun n => ?_⟩
  have hN := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A ↥(I ^ n) x h hx0
  have hr : finrank A ↥(I ^ n) ≤ 1 := (Submodule.finrank_le (I ^ n)).trans_eq (finrank_self A)
  have key : ((I ^ n).spanFinrank : ℕ∞) ≤ ((Ring.ord A x).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat hord]
    calc ((I ^ n).spanFinrank : ℕ∞)
        ≤ length A (↥(I ^ n) ⧸ LinearMap.range (LinearMap.lsmul A ↥(I ^ n) x)) :=
          PowSpanFinrankBounded.spanFinrank_le_length (I ^ n) hxm
      _ = (finrank A ↥(I ^ n) : ℕ∞) * Ring.ord A x := hN
      _ ≤ 1 * Ring.ord A x := by gcongr; exact_mod_cast hr
      _ = Ring.ord A x := one_mul _
  exact_mod_cast key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

private theorem special_dim_add_one_le {O : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} {ι : K → Type}
    (P : Ideal (MRing ι O)) [P.IsPrime] (hnt : P.comap (C : O →+* MRing ι O) = ⊥) :
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) + 1 ≤
      ringKrullDim (MRing ι O ⧸ P) := by
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

theorem ConservationOfNumberLE.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u}) :
    ConservationOfNumberLE.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP hnt hdim a

  have hPprime : P.IsPrime := hP.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]

  have hsp : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    lt_of_add_one_le_natCast ((special_dim_add_one_le hϖ P hnt).trans hdim)
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom) hsp a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem mem_minimalPrimes_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem ratDiv_one {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by
  funext W
  rw [ratDiv, divCycle_one, sub_zero]

theorem mixedDiff_cons_zero {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by
  unfold mixedDiff
  rw [List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]
  funext m
  simp [diffStep]

theorem eventualValue_zero {K : Type*} : eventualValue (0 : (K → ℤ) → ℤ) = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, hm⟩ := hc.choose_spec.exists
    exact hm.symm
  · rfl

theorem vNum_cons_zero {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by
  rw [vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]

theorem comap_C_eq_bot_of_not_mem {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [Ideal.mem_comap, map_mul, map_pow] at ha
  rcases hH.mem_or_mem ha with hv | hp
  · exact hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))
  · exact hϖH (hH.mem_of_pow_mem n hp)

theorem withBot_le_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((N : ℕ) : WithBot ℕ∞) :=
  by apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption

theorem withBot_lt_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by
  refine lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_
  exact_mod_cast Nat.lt_succ_self N

theorem UniformiserCase.proof (h1 : ConservationOfNumberLE.Statement.{u})
    (h2 : GenericDimBound.Statement.{u}) (h3 : GenericFibProps.Statement.{u})
    (h4 : GenericCycleCorresp.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : DimStrictDrop.Statement.{u})
    (h8 : CutByForm.Statement.{u}) : UniformiserCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    hP.dim
  have := hP.multiProj.isPrime

  have hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) =
      gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
    rw [ratDiv_one]
    exact h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _

  obtain ⟨hGprime, hGhom, hGs⟩ := h3 O K ι P hP.multiProj hP.noTorsion
  obtain ⟨hsG, hsG'⟩ := hGs s c hs hsP
  have hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) <
      ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1 := by omega
    rw [e]
    refine withBot_lt_of_add_one_le _ _ ?_
    have := h2 O K ι P hP.multiProj hP.noTorsion
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  have hcut := h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L
  have hcorr := h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP
    (fun V => intNum (FractionRing O) V L)
  rw [cutIdentity, hL, gNum, hcut, ← hcorr]

  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P s W = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  dsimp only
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · rw [if_pos hϖW, if_pos hϖW, vNum_cons_zero]
  rw [if_neg hϖW, if_neg hϖW]
  obtain ⟨hWmin, hWrel⟩ := mem_minimalPrimes_of_divCycle_ne_zero hW
  obtain ⟨hWprime, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have := hWprime
  have hWhom : IsMultiHomogIdeal W :=
    h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin
  have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2
    (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine withBot_le_of_add_one_le _ _ ?_
    have := h7 (MRing ι O) P W hlt
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  rw [ratDiv_one]
  exact (h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericDimBound.proof (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : AddMonoidAlgebra.coeff f 0 ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  have key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height →
      ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) := by
    intro n hn
    rw [show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩] at hn
    obtain ⟨p, hplast, hplen⟩ :=
      Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn
    have hlt : (p.map g hg).last < top := by
      rw [LTSeries.last_map, hplast]
      exact htop
    have := Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)
    simpa [hplen] using this

  rw [← hht, ringKrullDim_quotient P]
  have h1 := key 0 (by simp)
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) ≠ ⊥ := fun h => by
    rw [h] at h1; simp at h1
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at key ⊢
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases a with _ | k
  · simp
  · have hk : (k : ℕ∞) ≤ m.height := by
      have : (k : ℕ∞) + 1 ≤ m.height + 1 := by exact_mod_cast ha
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
    have := key k hk
    exact_mod_cast this

end GroundTheory.Heights₂.Heights.NumbersDVR
end
