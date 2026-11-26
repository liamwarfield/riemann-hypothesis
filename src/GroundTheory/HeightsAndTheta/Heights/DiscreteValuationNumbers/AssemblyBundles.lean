module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalCongrOnSupport
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVertCutEff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Helpers

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_pair_left {P H : Ideal (MRing ι R)} [hP : P.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hu : u ∉ H)
    (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    exact ⟨u', _, e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, hc⟩
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim

end Helpers

theorem VertCutEff.proof (h1 : VNumCut.Statement.{u}) (h2 : DivisorIdealCycle.Statement.{u})
    (h3 : IntNumAddFirst.Statement.{u}) : VertCutEff.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n hmodel b f g hE W x hxP hWmin hrel hWmh hϖW hcyc L
  have hP : P.IsPrime := hmodel.multiProj.isPrime
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨hV, hreg⟩ := hE
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  obtain ⟨u₀, v₀, hu₀, h₀⟩ := hreg W hWp hPW hrel
  obtain ⟨u, v, e, d, hu, hv, hde, huW, huv⟩ :=
    exists_form_pair_left hmodel.multiProj.multiHomog hPW hf hg hV.num_not_mem hu₀ h₀
  have huP : u ∉ P := fun h => huW (hPW h)

  have hvW : v ∉ W := by
    intro hvW
    have hvP : v ∉ P := by
      intro hvP
      have hufP : u * f ∈ P := by
        have h' := P.add_mem huv (P.mul_mem_right g hvP)
        rwa [sub_add_cancel] at h'
      exact (hP.mem_or_mem hufP).elim huP hV.num_not_mem
    have hmul := mem_minimalPrimes_sup_span_mul (P := P) (x := x) (y := v) hvP hWmin
    have hWv : W ∈ (P ⊔ Ideal.span {v}).minimalPrimes :=
      ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hvW)⟩, fun Q hQ hQW =>
        hmul.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) ((Ideal.span_singleton_le_iff_mem _).mpr
          (Q.mul_mem_left x (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)))))⟩ hQW⟩
    have hpos : divCycle P v W ≠ 0 := by
      unfold divCycle
      rw [dite_eq_left ⟨hWv, hrel⟩]
      have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {v}) W hWv
      have hnz : multAt (P ⊔ Ideal.span {v}) W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
          Ideal.Quotient.eq_zero_iff_mem] at hr0
        exact hr (hWv.1.2 hr0)
      have htn : (multAt (P ⊔ Ideal.span {v}) W).toNat ≠ 0 :=
        fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
      exact_mod_cast htn
    have hu0 : divCycle P u W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact huW (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self u)))
    have e1 := congrFun (DivCycleMul.proof O K ι P u f hP huP hV.num_not_mem) W
    have e2 := congrFun (DivCycleMul.proof O K ι P v g hP hvP hV.den_not_mem) W
    have e3 := congrFun (divCycle_eq_of_sub_mem huv) W
    simp only [Pi.add_apply] at e1 e2
    unfold ratDiv at hcyc
    omega

  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hmodel.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdim : ringKrullDim (MRing ι O ⧸ W) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h' := DimStrictDrop.proof (MRing ι O) P W hlt
    rw [hmodel.dim, show n + 1 + 1 + Fintype.card K = n + 2 + Fintype.card K by omega] at h'
    exact withBotENat_lt_of_add_one_le h'

  have hcu := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim u e hu huW L
  have hcv := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim v d hv hvW L
  have hWbar : (specialIdeal W).IsPrime := (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1
  have hadd := h3 (IsLocalRing.ResidueField O) K ι n (specialIdeal W) hWbar
    (SpecialIdealMultiHomog.proof O K ι W hWmh)
    (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hdim) b (fun k => (e k : ℤ)) L
  have hdeg : (fun k => (d k : ℤ)) = b + fun k => (e k : ℤ) := by
    rw [← hb]
    funext k
    have hk := congrFun hde k
    simp only [Pi.add_apply] at hk ⊢
    omega
  have key : vNum W (Matrix.vecCons b L) = vNum W (Matrix.vecCons (fun k => (d k : ℤ)) L) -
      vNum W (Matrix.vecCons (fun k => (e k : ℤ)) L) := by
    rw [hdeg]
    unfold vNum
    rw [hadd]
    ring
  rw [key, hcv, hcu, ← h2 O K ι P W f g u v hP hWp hPW hV.den_not_mem
    (fun U hU hWU hUrel => hreg U hU (hPW.trans hWU) hUrel) huW hvW huv]

  unfold cycEval ratDiv
  rw [← finsum_sub_distrib
    ((DivCycleFiniteSupport.proof O K ι W v).subset (Function.support_mul_subset_left _ _))
    ((DivCycleFiniteSupport.proof O K ι W u).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun U => ?_
  ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivisorIdealCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section General

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem idealCycle_eq_of_mul_mem {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by
  unfold idealCycle
  by_cases h : U ∈ J.minimalPrimes ∧ IsRelevant U
  · have h' : U ∈ J'.minimalPrimes ∧ IsRelevant U :=
      ⟨mem_minimalPrimes_of_mul_mem hs ht hsJ htJ h.1, h.2⟩
    rw [dite_eq_left h, dite_eq_left h']
    have : U.IsPrime := h.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hs ht hsJ htJ]
  · have h' : ¬ (U ∈ J'.minimalPrimes ∧ IsRelevant U) := fun h' =>
      h ⟨mem_minimalPrimes_of_mul_mem ht hs htJ hsJ h'.1, h'.2⟩
    rw [dite_eq_right h, dite_eq_right h']

theorem divCycle_eq_zero_of_not_mem {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end General

theorem DivisorIdealCycle.proof : DivisorIdealCycle.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W f g u v hP hW hPW hg hloc hu hv huv
  funext U
  by_cases hU : U.IsPrime ∧ W ≤ U ∧ IsRelevant U
  · obtain ⟨hUp, hWU, hUrel⟩ := hU
    obtain ⟨u', v', hu'U, hloc'⟩ := hloc U hUp hWU hUrel
    have hu'W : u' ∉ W := fun h => hu'U (hWU h)
    have h1U : (1 : MRing ι R) ∉ U := (Ideal.ne_top_iff_one U).mp hUp.ne_top

    have hcross : u * v' - u' * v ∈ P := by
      have hmem : (u * v' - u' * v) * g ∈ P := by
        rw [show (u * v' - u' * v) * g = u' * (u * f - v * g) - u * (u' * f - v' * g) by ring]
        exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ hloc')
      exact (hP.mem_or_mem hmem).resolve_right hg
    have hv'W : v' ∉ W := by
      intro h
      have hmem : u' * v ∈ W := by
        rw [show u' * v = u * v' - (u * v' - u' * v) by ring]
        exact W.sub_mem (W.mul_mem_left u h) (hPW hcross)
      exact (hW.mem_or_mem hmem).elim hu'W hv

    have hmul := congrFun (DivCycleMul.proof R K ι W u' v hW hu'W hv) U
    have hmul' := congrFun (DivCycleMul.proof R K ι W u v' hW hu hv'W) U
    have heq : divCycle W (u' * v) U = divCycle W (u * v') U :=
      divCycle_eq_of_mul_sub_mem (P := W) (W := U) (u := 1) (v := 1) h1U h1U (by
        rw [show 1 * (u' * v) - 1 * (u * v') = -(u * v' - u' * v) by ring]
        exact W.neg_mem (hPW hcross))
    have hu'0 : divCycle W u' U = 0 := divCycle_eq_zero_of_not_mem hu'U
    simp only [Pi.add_apply] at hmul hmul'

    have hv'D : v' ∈ divisorIdeal P f g := by
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul,
        show v' * g = u' * f - (u' * f - v' * g) by ring]
      exact Submodule.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
        (Ideal.mem_sup_left hloc')
    have hsJ : ∀ x ∈ W ⊔ Ideal.span {v'}, 1 * x ∈ W ⊔ divisorIdeal P f g := by
      intro x hx
      rw [one_mul]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hv'D) W hx
    have htJ : ∀ x ∈ W ⊔ divisorIdeal P f g, u' * x ∈ W ⊔ Ideal.span {v'} := by
      intro x hx
      obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul] at hd
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hd
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have h1 : (u' * d - a * v') * g ∈ P := by
        have e : (u' * d - a * v') * g = u' * p + a * (u' * f - v' * g) := by
          calc (u' * d - a * v') * g = u' * (d * g) - a * v' * g := by ring
            _ = u' * p + a * (u' * f - v' * g) := by rw [← hpr]; ring
        rw [e]
        exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hloc')
      have h2 : u' * d - a * v' ∈ P := (hP.mem_or_mem h1).resolve_right hg
      rw [show u' * (w + d) = (u' * w + (u' * d - a * v')) + a * v' by ring]
      exact Submodule.add_mem_sup (W.add_mem (W.mul_mem_left _ hw) (hPW h2))
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hR : idealCycle (W ⊔ divisorIdeal P f g) U = divCycle W v' U := by
      rw [divCycle_eq_idealCycle]
      exact (idealCycle_eq_of_mul_mem h1U hu'U hsJ htJ).symm
    rw [hR]
    show divCycle W v U - divCycle W u U = divCycle W v' U
    omega
  · have hcomp : ∀ J : Ideal (MRing ι R), W ≤ J → ¬ (U ∈ J.minimalPrimes ∧ IsRelevant U) := by
      rintro J hWJ ⟨h, hrel⟩
      exact hU ⟨h.1.1, hWJ.trans h.1.2, hrel⟩
    show divCycle W v U - divCycle W u U = idealCycle (W ⊔ divisorIdeal P f g) U
    unfold divCycle idealCycle
    rw [dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left),
      sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem NoCommonComponentCase.proof (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno L
  unfold cutIdentity
  rw [h₁ O ϖ hϖ K ι P d hP b f g hD.1 c s hs hsP hno L,
    h₂ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno L]
  unfold cycEval
  refine finsum_congr fun U => ?_
  beta_reduce
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧
      ¬ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)
  ·
    obtain ⟨hUp, hUm, -, hϖU, hdim⟩ := hU
    have hv : vNum U L = 0 := by
      refine h₄ _ K ι d (specialIdeal U) (SpecialIdealCorresp.proof O ϖ hϖ K ι ⊥ U hUp hϖU).1
        (SpecialIdealMultiHomog.proof O K ι U hUm) (Or.inr ?_) L
      rw [SpecialQuotDim.proof O ϖ hϖ K ι U hϖU]
      exact lt_of_not_ge hdim
    rw [hv, mul_zero, mul_zero]
  ·
    have e := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno U fun hp hm hr hϖU => by
      by_contra h
      exact hU ⟨hp, hm, hr, hϖU, h⟩
    unfold cycEval at e
    rw [e]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVNumCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem VNumCut.proof (h : CutByForm.Statement.{u}) : VNumCut.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs
  set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hπ
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => rfl
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := ker_map_residue_eq_span hϖ

  have hGbp : (specialIdeal G).IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1
  have hGbh : IsMultiHomogIdeal (specialIdeal G) := SpecialIdealMultiHomog.proof O K ι G hGh
  have hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) <
      ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]; exact hdim
  have hsb : IsMultiHomog (π s) c := isWeightedHomogeneous_map_of _ _ hs
  have hsbG : π s ∉ specialIdeal G := by
    intro hm
    apply hsG
    have hcm : (G.map π).comap π = G := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hϖG
    rw [← hcm]
    exact hm

  have hcut := h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb
    hsbG bs

  have hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s} := by
    rw [sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left hϖG
  have hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ) := by
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]
  have hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s} := by
    rw [hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have htr := SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof
    SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s})
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [hmapJ, ← divCycle_eq_idealCycle] at htr
  show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ =
    cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)
  rw [hcut, hdiv, htr]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExceptionalDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpReduction.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorInduction.proof (hpos : ExcessPositive.Statement.{u}) (havoid : AvoidingFormExists.Statement.{u})
    (hhor : HorizontalAvoidingForm.Statement.{u}) (hpieces : BlowUpDecomposition.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hred : BlowUpReduction.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hmul : DivCycleMul.Statement.{u}) : CommonFactorInduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH hcommon IH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hε := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  obtain ⟨e, h, hh, hhP, hle, hhH, hhG, hh0, hmulε⟩ :=
    havoid O ϖ hϖ K ι P d hP b f g hD (fun k => (b k).toNat)
  have hdiv : ∀ W, divCycle P (s * h) W = divCycle P s W + divCycle P h W :=
    fun W => congrFun (hmul O K ι P s h hPp hsP hhP) W
  have hshP : s * h ∉ P := fun hm => (hPp.mem_or_mem hm).elim hsP hhP
  have hshH : ∀ H, divCycle P (s * h) H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g := by
    intro H hH hϖH
    rw [hdiv] at hH
    by_cases h1 : divCycle P s H = 0
    · exact hhH H (by rwa [h1, zero_add] at hH) hϖH
    · exact hsH H h1 hϖH
  have hcommon' : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P (s * h) G ≠ 0 ∧ ratDiv P f g G ≠ 0 := by
    obtain ⟨G, hG, hsG, hDG⟩ := hcommon
    exact ⟨G, hG, by rwa [hdiv, hhG G hG hDG, add_zero], hDG⟩

  set e₂ : K → ℕ := fun k => (((c + e) k : ℕ) - b k : ℤ).toNat with he₂def
  have he₂ : ∀ k, (((c + e) k : ℕ) : ℤ) = b k + e₂ k := by
    intro k
    have h1 : (b k).toNat ≤ e k := hle k
    have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
    simp only [he₂def, Pi.add_apply, Nat.cast_add]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  obtain ⟨m, hm, hmP, hmH⟩ := hhor O ϖ hϖ K ι P d hP (s * h) hshP e₂
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, hH₀⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD (c + e)
    (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm hmP hmH
  obtain ⟨hdrop₁, hdrop₀⟩ := hdrop O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP
    hshH e₂ he₂ m hm hmP hmH hcommon'
  rw [hmulε s hsP] at hdrop₁ hdrop₀

  have hId₁ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hD₁ _ _ hsl hslP
    (fun H hH hϖH => (hH₁ H hH hϖH).1) hdrop₁ (liftDegs L)
  have hId₀ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hE (Pi.single none 1)
    (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀P hH₀ hdrop₀ (liftDegs L)

  have hIdsh := hred O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm
    hmP hmH L hId₁ hId₀
  have hIdh := IH K ι P d hP b f g hD e h hh hhP hhH (by rw [hh0]; exact hε) L

  rw [cutIdentity_iff] at hIdsh hIdh ⊢
  have h1 := hlhs O ϖ hϖ K ι P d hP b f g hD.1 c e L
  have h2 := hrhs O ϖ hϖ K ι P d hP b f g s h hsP hhP L
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RatDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorRemoval.proof (hmul : DivCycleMul.Statement.{u}) : CommonFactorRemoval.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g q s hf hg hq _ hH c L

  have hrat : ∀ W : Ideal (MRing ι O), W.IsPrime → f ∉ W → g ∉ W → q ∉ W →
      ratDiv W (f * q) (g * q) = ratDiv W f g := by
    intro W hW hfW hgW hqW
    funext G
    simp only [ratDiv, hmul O K ι W f q hW hfW hqW, hmul O K ι W g q hW hgW hqW, Pi.add_apply]
    ring
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [hrat P hP.multiProj.isPrime hf hg hq]
  · unfold cutIdentityRightSide cycEval
    congr 1
    funext W
    by_cases hW : divCycle P s W = 0
    · simp [hW]
    · dsimp only
      split_ifs with hϖ
      · rfl
      · obtain ⟨h1, h2, h3⟩ := hH W hW hϖ
        rw [hrat W (isPrime_of_divCycle_ne_zero hW) h1 h2 h3]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExistsMultiHomogNotMemOfIsRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_multiHomog_not_mem_of_isRelevant {H : Ideal (MRing ι R)} (hH : H.IsPrime)
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k) (fun k => c k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
    have hc : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · intro hm
    obtain ⟨k, -, hk⟩ := hH.prod_mem_iff.mp hm
    exact hi k (hH.mem_of_pow_mem _ hk)

theorem exists_multiHomog_not_mem_finset [Infinite R] (c : K → ℕ) (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : R, C a ∈ Q → a = 0) :
    ∃ m : MRing ι R, IsMultiHomog m c ∧ ∀ Q ∈ S, m ∉ Q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  | @insert Q₀ S _ ih =>
    obtain ⟨x, hx, hxS⟩ := ih fun Q h => hS Q (Finset.mem_insert_of_mem h)
    obtain ⟨hQ₀, hrel₀, hC₀⟩ := hS Q₀ (Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hyQ₀⟩ := exists_multiHomog_not_mem_of_isRelevant hQ₀ hrel₀ c

    have hsub : ∀ Q ∈ S, {t : R | x + C t * y ∈ Q}.Subsingleton := by
      intro Q hQS t ht t' ht'
      obtain ⟨hQ, -, hCQ⟩ := hS Q (Finset.mem_insert_of_mem hQS)
      have hd : C (t - t') * y ∈ Q := by
        have h := Q.sub_mem ht ht'
        rw [map_sub]
        convert h using 1
        ring
      rcases hQ.mem_or_mem hd with h | h
      · exact sub_eq_zero.mp (hCQ _ h)
      · exact absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (C t) h)) (hxS Q hQS)
    have hfin : (insert 0 (⋃ Q ∈ S, {t : R | x + C t * y ∈ Q})).Finite :=
      (S.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      not_or, not_exists] at ht
    obtain ⟨ht0, htS⟩ := ht
    by_cases hxQ₀ : x ∈ Q₀
    · refine ⟨x + C t * y, hx.add (by simpa using (isWeightedHomogeneous_C _ t).mul hy), ?_⟩
      intro Q hQ
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · intro h
        have h' : C t * y ∈ Q := by simpa using Q.sub_mem h hxQ₀
        rcases hQ₀.mem_or_mem h' with h'' | h''
        · exact ht0 (hC₀ _ h'')
        · exact hyQ₀ h''
      · exact htS Q hQS
    · refine ⟨x, hx, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQS
      · exact hxQ₀
      · exact hxS Q hQS

end Avoid

theorem HorizontalAvoidingForm.proof : HorizontalAvoidingForm.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP s hs e
  classical
  have : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)

  have hfin : (Function.support (divCycle P s)).Finite := by
    apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s}))
    intro W hW
    by_contra hmin
    apply hW
    unfold divCycle
    rw [dite_eq_right]
    exact fun h => hmin h.1

  have hT : ∀ Q ∈ insert P (hfin.toFinset.filter fun H => (C ϖ : MRing ι O) ∉ H),
      Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : O, C a ∈ Q → a = 0 := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · refine ⟨hP.multiProj.isPrime, hP.multiProj.relevant, fun a ha => ?_⟩
      have h : a ∈ Q.comap (C : O →+* MRing ι O) := ha
      rw [hP.noTorsion] at h
      exact (Submodule.mem_bot O).mp h
    · obtain ⟨hQs, hϖQ⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQp, -, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero
        (Function.mem_support.mp (hfin.mem_toFinset.mp hQs))
      refine ⟨hQp, hrel, fun a ha => ?_⟩
      by_contra ha0
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
      rw [map_mul, map_pow] at ha
      rcases hQp.mem_or_mem ha with h | h
      · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
      · exact hϖQ (hQp.mem_of_pow_mem _ h)
  obtain ⟨m, hm, hmT⟩ := exists_multiHomog_not_mem_finset e _ hT
  refine ⟨m, hm, hmT P (Finset.mem_insert_self _ _), fun H hH hϖH => hmT H ?_⟩
  exact Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (Function.mem_support.mpr hH), hϖH⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LtNatCastOfAddOneLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_natCast_of_add_one_le' {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem TautologicalCase.proof (h3 : IntNumAddFirst.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : TautologicalCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD cf cg hf hg hb L

  have hfin : ∀ x : MRing ι O, (Function.support (divCycle P x)).Finite := fun x =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {x})).subset fun W hW => by
      by_contra hmin
      exact hW (by unfold divCycle; rw [dite_eq_right]; exact fun h => hmin h.1)
  have hZfin : (Function.support (ratDiv P f g)).Finite :=
    ((hfin f).union (hfin g)).subset fun W hW => by
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hW (by simp [ratDiv, h.1, h.2])
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (x : MRing ι O) (e : K → ℕ), IsMultiHomog x e → ∀ W, divCycle P x W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro x e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P x e hPmh he) hW'.1, hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 → vNum W (Matrix.vecCons b L) =
      vNum W (Matrix.vecCons (fun k => (cf k : ℤ)) L) - vNum W (Matrix.vecCons (fun k => (cg k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g cg hg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f cf hf W hWf
    have hdrop := h10 (MRing ι O) P W (lt_of_le_of_ne hPW fun e => hϖP (e ▸ hϖW))
    rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by omega] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      exact lt_natCast_of_add_one_le' hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b (fun k => (cg k : ℤ)) L
    rw [show b + (fun k => (cg k : ℤ)) = fun k => (cf k : ℤ) by rw [← hb]; funext k; simp] at key
    unfold vNum
    rw [key]; ring
  unfold cutIdentityLeftSide cutIdentityRightSide cycEval
  rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
      (hZfin.subset (Function.support_mul_subset_left _ _)),
    ← finsum_sub_distrib ((hfin f).subset (Function.support_mul_subset_left _ _))
      ((hfin g).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  rw [← mul_sub, ← sub_mul]
  change ratDiv P f g W * _ = ratDiv P f g W * _
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [if_pos (hD.vertical W hW), hadd W hW]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalAddOfFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem cycEval_add_of_finite {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (φ : Ideal (MRing ι R) → ℤ) {Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite) :
    cycEval φ (Z₁ + Z₂) = cycEval φ Z₁ + cycEval φ Z₂ := by
  unfold cycEval
  have f₁ : (Function.support fun W => Z₁ W * φ W).Finite :=
    h₁.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => Z₂ W * φ W).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [← finsum_add_distrib f₁ f₂]
  refine finsum_congr fun W => ?_
  simp only [Pi.add_apply]
  ring

theorem RightSideMultiplicativeInForm.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : RightSideMultiplicativeInForm.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g s₁ s₂ hs₁ hs₂ L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cutIdentityRightSide
  rw [h₁ O K ι P s₁ s₂ hPp hs₁ hs₂]
  exact cycEval_add_of_finite _ (h₂ O K ι P s₁) (h₂ O K ι P s₂)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

end GroundTheory.Heights₂.Heights.NumbersDVR
