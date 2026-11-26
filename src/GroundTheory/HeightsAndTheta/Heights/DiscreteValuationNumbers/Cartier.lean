module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Local

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_mul_mem {J J' W : Ideal A} {s t : A} (hs : s ∉ W) (ht : t ∉ W)
    (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) (hW : W ∈ J.minimalPrimes) :
    W ∈ J'.minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, fun x hx => ?_⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, fun x hx => ?_⟩ hQW⟩
  · exact (hWp.mem_or_mem (hW.1.2 (htJ x hx))).resolve_left ht
  · exact (hQ.1.mem_or_mem (hQ.2 (hsJ x hx))).resolve_left (fun h => hs (hQW h))

theorem length_localized_eq_of_le {J J'' W : Ideal A} [W.IsPrime] (hle : J ≤ J'')
    (h : ∀ x ∈ J'', ∃ t ∉ W, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J'')) := by
  let q : (A ⧸ J) →ₗ[A] (A ⧸ J'') := Submodule.factor hle
  let f := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let g := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J'')
  let m := IsLocalizedModule.map W.primeCompl f g q
  have hinj : Function.Injective m := by
    apply IsLocalizedModule.injective_of_map_zero W.primeCompl f
    intro x hx
    rw [IsLocalizedModule.map_apply] at hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective J x
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff W.primeCompl g).mp hx
    have hsy : (s : A) * y ∈ J'' := by
      have : (s : A) • (Submodule.mkQ J'' y) = 0 := hs
      rwa [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul] at this
    obtain ⟨t, ht, hty⟩ := h _ hsy
    refine (IsLocalizedModule.eq_zero_iff W.primeCompl f).mpr ⟨⟨t * s, W.primeCompl.mul_mem ht s.2⟩, ?_⟩
    show ((t * s : A)) • (Submodule.mkQ J y) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      mul_assoc]
    exact hty
  have hsurj : Function.Surjective m :=
    IsLocalizedModule.map_surjective W.primeCompl f g q (Submodule.factor_surjective hle)
  exact ((LinearEquiv.ofBijective m ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

theorem length_localized_eq_of_mul_mem {J J' W : Ideal A} [W.IsPrime] {s t : A} (hs : s ∉ W)
    (ht : t ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J')) := by
  have key : ∀ {J J' : Ideal A} {t : A}, t ∉ W → (∀ x ∈ J', t * x ∈ J) →
      ∀ x ∈ J ⊔ J', ∃ t ∉ W, t * x ∈ J := by
    intro J J' t ht htJ x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨t, ht, by rw [mul_add]; exact J.add_mem (J.mul_mem_left t ha) (htJ a' ha')⟩
  rw [length_localized_eq_of_le le_sup_left (key ht htJ),
    length_localized_eq_of_le le_sup_left (key hs hsJ), sup_comm]

end Local

section Divisors

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_of_mul_sub_mem {P : Ideal (MRing ι R)} {f g u v : MRing ι R}
    {W : Ideal (MRing ι R)} (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) :
    divCycle P f W = divCycle P g W := by
  have h1 : ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)
  have h2 : ∀ x ∈ P ⊔ Ideal.span {g}, v * x ∈ P ⊔ Ideal.span {f} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : v * (p + c * g) = (v * p - c * (u * f - v * g)) + (c * u) * f := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.sub_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * u, rfl⟩)
  unfold divCycle
  by_cases hf : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W :=
      ⟨mem_minimalPrimes_of_mul_mem hu hv h1 h2 hf.1, hf.2⟩
    rw [dite_eq_left hf, dite_eq_left hg]
    have : W.IsPrime := hf.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hu hv h1 h2]
  · have hg : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) := fun hg =>
      hf ⟨mem_minimalPrimes_of_mul_mem hv hu h2 h1 hg.1, hg.2⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem le_and_isRelevant_of_divCycle_ne_zero {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact ⟨hW.1.1.1, le_sup_left.trans hW.1.1.2, hW.2⟩
  · exact absurd rfl h

end Divisors

section Vertical

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem IsVerticalDivisor.of_unit_off_special {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O}
    (degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
      (fun k => (bf k : ℤ) - bg k) = b)
    (hf : f ∉ P) (hg : g ∉ P)
    (hunit : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    IsVerticalDivisor P ϖ b f g := by
  refine ⟨degrees, hf, hg, ?_, hunit⟩
  intro W hW
  by_contra hϖ
  have hsupp : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    by_cases h1 : divCycle P f W = 0
    · have h2 : divCycle P g W ≠ 0 := by
        intro h2; apply hW; unfold ratDiv; rw [h1, h2, sub_zero]
      exact le_and_isRelevant_of_divCycle_ne_zero h2
    · exact le_and_isRelevant_of_divCycle_ne_zero h1
  obtain ⟨u, v, hu, hv, h⟩ := hunit W hsupp.1 hsupp.2.1 hsupp.2.2 hϖ
  apply hW
  unfold ratDiv
  rw [divCycle_eq_of_mul_sub_mem hu hv h, sub_self]

end Vertical

section Graded

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R] {τ : Type*}

end Graded

section BlowUp

variable {O : Type*} [CommRing O]

end BlowUp

section BlowUpModel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end BlowUpModel

section Nodal

variable {O : Type*} [CommRing O] [IsDomain O]

end Nodal

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u v

abbrev LengthFormulaDimTwo.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthMultiplicativity.{u}

def ConservationOfNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ a : Fin d → K → ℤ,
        cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a


open scoped Classical in
open Classical in
def CutByEffectiveDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
          cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
              else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

def VerticalDivisorsCommute.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b b' : K → ℤ) (f g f' g' : MRing ι O),
        IsVerticalDivisor P ϖ b f g → IsVerticalDivisor P ϖ b' f' g' →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g) =
          cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g')

section Examples

theorem isPrime_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.1
  · exact absurd rfl h

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem height_eq_of_isMaximal_mvPolynomial_fin (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp at h
    simpa [h]
  | succ n ih =>
    intro M hM
    let e := (finSuccEquiv F n).toRingEquiv
    rw [← e.height_map M]
    set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef
    have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F)) := ⟨rfl⟩
    rw [Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P,
      ih (P.under (MvPolynomial (Fin n) F)) hc]
    norm_cast

theorem MaximalIdealHeightFG.proof : MaximalIdealHeightFG.Statement.{u} := by
  intro F _ A _ _ _ _ m hm
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F A
  let _ : Algebra (MvPolynomial (Fin s) F) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) A := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : m.IsPrime := hm.isPrime
  have hR : ringKrullDim (MvPolynomial (Fin s) F) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hdim : ringKrullDim A ≤ s := by
    rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin s) F) A)) fun p q hpq => ?_
    exact Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) F) hpq
  let n := m.under (MvPolynomial (Fin s) F)
  have : n.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown n m
  rw [height_eq_of_isMaximal_mvPolynomial_fin F s n inferInstance] at h1
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) (hdim.trans ?_)
  rw [h1]
  exact_mod_cast le_self_add

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Algebra Cardinal Set

noncomputable section

theorem AdjoinTrdegAdd.trdeg_adjoin_eq_of_family {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by
  have := (algebraMap R L).domain_nontrivial
  let v : κ → adjoin R u := fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩
  have hv : AlgebraicIndependent R v := AlgebraicIndependent.of_comp (adjoin R u).val hw
  have heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w) := by
    rw [AlgHom.map_adjoin, ← range_comp]
    rfl
  let e := ((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ heq)
  have hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u) := by
    refine ⟨fun a => ?_⟩
    have h0 : IsAlgebraic (adjoin R u) (a : L) := isAlgebraic_algebraMap a
    have h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a) :=
      h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1
    exact (isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective
      (by ext; rfl)).mp h1
  exact ((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm

theorem AdjoinTrdegAdd.proof : AdjoinTrdegAdd.Statement := by
  intro R _ L _ _ _ hinj s t ι _ x hxt hx hxalg
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  obtain ⟨b, hb⟩ := (AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)
  obtain ⟨hbi, hbs, hbalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hb
  have hbi' : AlgebraicIndependent R ((↑) : b → L) := hbi

  have h1 : trdeg R (adjoin R s) = #b :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi'
      (by rw [Subtype.range_coe]; exact hbalg)

  let _ : Algebra (adjoin R b) (adjoin R s) := (Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra
  have : IsScalarTower (adjoin R b) (adjoin R s) L := .of_algebraMap_eq fun _ => rfl
  have hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x := by
    rw [Subtype.range_coe]
    exact hx.restrictScalars (Subalgebra.inclusion_injective _)
  have hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L)) :=
    AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩
  have hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b := by
    rw [Set.Sum.elim_range, Subtype.range_coe]

  have hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a := fun a ha =>
    (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim
  have hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a := by
    rw [hrange]
    rintro a (ha | ha)
    · exact hs a ha
    · refine (hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_
      rcases hy.1 with hy1 | hy1
      · exact hs y hy1
      · exact (hy.2 (Or.inl hy1)).elim
  have h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b) :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L))
      (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left))
      hsum hst
  rw [h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMultAtOfSaturated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def MultAtOfSaturated.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q : Ideal (MRing ι R)) [Q.IsPrime],
    J ≤ Q → (∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) → Q ∈ J.minimalPrimes ∧ multAt J Q = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def GenericDimGe.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDvrConeDimTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def DvrConeDimTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) =
        (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
