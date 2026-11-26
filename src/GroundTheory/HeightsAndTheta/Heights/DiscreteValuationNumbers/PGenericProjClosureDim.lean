module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenericProjClosureDim

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

def tWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (tWeight K) b (pointConeMap R z f) =
      pointConeMap R z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 : IsWeightedHomogeneous (tWeight K) (pointConeMap R z (monomial d a))
        (Finsupp.weight (blockWeight ι) d) := by
      rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
        Finsupp.sum]
      refine IsWeightedHomogeneous.C_mul ?_ _
      refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
      exact ((isWeightedHomogeneous_X (R := L) (tWeight K) p.1).C_mul (z p)).pow (d p)
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι R)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem isMultiProjPrime_pointIdeal (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (R := R) z b f
    rw [hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap R z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

theorem exists_ne_zero_of_span {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by
  by_contra! h0
  have hall : ∀ l, ψ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have := Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i))
      (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])
    simpa using this i
  have htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥ := by
    rw [← hψ, Submodule.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  have hc : e.coord ⟨0, hN⟩ = 0 := by
    have : e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E)) := htop ▸ Submodule.mem_top
    simpa using this
  have := congrArg (fun f => f (e ⟨0, hN⟩)) hc
  simp at this

end GenericProjClosureDim


open GenericProjClosureDim in
theorem GenericProjClosureDim.proof (hDim : DvrConeDimTrdeg.Statement) (hTr : PairBundleTrdeg.Statement) :
    GenericProjClosureDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k)
    · exact exists_ne_zero_of_span hN e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)
    · exact exists_ne_zero_of_span hN e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)
    · exact ⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  refine ⟨hP, hnt, ?_⟩

  have hdy := hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  rw [hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty,
    ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
    show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]
  norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def flagFurtherTerm_independent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) → ∀ l : Fin r,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
                                  (Fin.append (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y'))
                                  (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                                    (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
            (Fin.append (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y'))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def HomLocRingMem.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    ∀ z : FractionRing (MRing ι R ⧸ P), z ∈ homLocRing P W ↔
      ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
        z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)

def HomLocRingIsLocal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    IsLocalRing (homLocRing P W) ∧
      ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
        ∀ hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ∈
              homLocRing P W,
          IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W

def HomLocRingNoetherian.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      IsNoetherianRing (homLocRing P W)

def HomLocRingDimLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      ringKrullDim (homLocRing P W) ≤ ((W.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def blowUpEval (P : Ideal (MRing ι R)) (u : J → MRing ι R) : MRing (extIdx ι J) R →+* MRing ι R ⧸ P :=
  (Polynomial.evalRingHom 1).comp (aeval (blowUpSubst P u)).toRingHom

variable [DecidableEq K]

def blowUpLocRing (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R)
    (Q : Ideal (MRing (extIdx ι J) R)) : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧
    IsMultiHomog G b ∧ G ∉ Q ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)}

def blowUpOverLoc (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Subring (FractionRing (MRing ι R ⧸ P)) :=
  ⨅ (Q : Ideal (MRing (extIdx ι J) R)) (_ : Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
      blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W),
    blowUpLocRing P u Q


omit [DecidableEq K] in
theorem blowUpEval_liftForm (P : Ideal (MRing ι R)) (u : J → MRing ι R) (f : MRing ι R) :
    blowUpEval P u (liftForm f) = Ideal.Quotient.mk P f := by
  show Polynomial.eval 1 (aeval (blowUpSubst P u) (liftForm f)) = _
  rw [aeval_blowUpSubst_liftForm, Polynomial.eval_C]

theorem homLocRing_le_blowUpOverLoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    homLocRing P W ≤ blowUpOverLoc P W u := by
  refine le_iInf₂ fun Q hQ => Subring.closure_le.mpr ?_
  rintro z ⟨b, f, g, hf, hg, hgW, rfl⟩
  refine Subring.subset_closure ⟨liftMDeg b, liftForm f, liftForm g, isMultiHomog_liftForm hf,
    isMultiHomog_liftForm hg, fun h => hgW (hQ.2.2.2.2 h), ?_⟩
  rw [blowUpEval_liftForm, blowUpEval_liftForm]

instance blowUpOverLoc.instAlgebra {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Algebra (homLocRing P W) (blowUpOverLoc P W u) :=
  (Subring.inclusion (homLocRing_le_blowUpOverLoc P W u)).toAlgebra

end Objects

section Lemmas

def BlowUpLocRingIso.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q : Ideal (MRing (extIdx ι J) R)),
    blowUpOf P u ≤ Q →
    haveI : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
    ∃ φ : homLocRing (blowUpOf P u) Q ≃+* blowUpLocRing P u Q,
      ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R) (hF : IsMultiHomog F b)
        (hG : IsMultiHomog G b) (hGQ : G ∉ Q),
        (φ ⟨_, Subring.subset_closure ⟨b, F, G, hF, hG, hGQ, rfl⟩⟩ : FractionRing (MRing ι R ⧸ P)) =
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)

def BlowUpOverLocFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      Module.Finite (homLocRing P W) (blowUpOverLoc P W u) ∧
        Module.finrank (homLocRing P W) (blowUpOverLoc P W u) = 1

def BlowUpOverLocMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∃ e : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
        ∀ 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal},
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u (e 𝔫).1,
            letI := (Subring.inclusion h).toAlgebra
            haveI := 𝔫.2.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u (e 𝔫).1) 𝔫.1) ∧
          𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section ClassNumPairDiff

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_pairDiff_mul {n e : ℕ} {W : Ideal (MRing ι O)}
    (hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
      vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l))
    (z z' : Fin n → K → ℤ) (j : Fin n) {H : MvPolynomial (Fin n ⊕ Fin n) ℤ} {t : ℕ}
    (hH : H.IsHomogeneous t) (Q : List (K → ℤ)) (ht : e ≤ t + Q.length) :
    classNum (Sum.elim z z') (pairDiff j * H) Q W =
      ∑ μ ∈ H.support,
        H.coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
  have hsub : classNum (Sum.elim z z') (pairDiff j * H) Q W =
      classNum (Sum.elim z z') (X (Sum.inl j) * H) Q W -
        classNum (Sum.elim z z') (X (Sum.inr j) * H) Q W := by
    rw [pairDiff, sub_mul]
    exact map_sub (classNumAddHom (Sum.elim z z') Q W) _ _
  rw [hsub, classNum_X_mul, classNum_X_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : e ≤ (classList (Sum.elim z z') μ ++ Q).length := by
    rw [List.length_append, classList_length_of_mem_support _ hH hμ]
    exact ht
  have h := hadd (z j - z' j) (z' j) _ hlen
  rw [sub_add_cancel] at h
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h]
  ring

end ClassNumPairDiff

theorem cycEval_vNumL_comm (hC2 : VerticalDivisorsCommute.Statement.{0}) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hP : IsModelOver P (l.length + 1)) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g') :
    cycEval (fun W => vNumL W (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => vNumL W (b :: l)) (ratDiv P f' g') := by
  have h := hC2 O ϖ hϖ K ι P l.length hP b b' f g f' g' hD hD' l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

theorem PairNumberExpansionIndependence.proof (hC2 : VerticalDivisorsCommute.Statement.{0}) :
    PairNumberExpansionIndependence.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP n z z' f g hD m A hA As Bs hAs hBs Q hQ
  have hrel : ∑ i, pairDiff i * (As - Bs) i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, pairDiff, ← hAs.expansion,
      ← hBs.expansion, sub_self]
  obtain ⟨Kz, hKa, hKh, hK0, hKs⟩ := koszul_homogeneous (m := m) (As - Bs)
    (fun i => (hAs.homogeneous i).sub (hBs.homogeneous i)) hrel
  rw [← sub_eq_zero, ← pairNumHom_apply, ← pairNumHom_apply, ← map_sub]
  by_cases hm : m - 1 = 0
  · have h0 : As - Bs = 0 := funext fun i => by
      rw [hKs i]
      simp [hK0 hm]
    rw [h0, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hlen : ∀ i j μ, μ ∈ (Kz i j).support → (classList (Sum.elim z z') μ ++ Q).length = e := by
    intro i j μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hKh i j) hμ]
    omega

  let V : Fin n → Fin n → (Fin n ⊕ Fin n →₀ ℕ) → ℤ := fun i j μ =>
    cycEval (fun W => vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)))
      (ratDiv P (f i) (g i))
  let F : Fin n → Fin n → ℤ := fun i j => ∑ μ ∈ (Kz i j).support, (Kz i j).coeff μ * V i j μ
  have hexp : pairNumHom P z z' f g Q (As - Bs) = ∑ i, ∑ j, F i j := by
    rw [pairNumHom_apply]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin := ratDiv_finite_support P (f i) (g i)
    have hW : ∀ W ∈ hfin.toFinset, classNum (Sum.elim z z') ((As - Bs) i) Q W =
        ∑ j, ∑ μ ∈ (Kz i j).support,
          (Kz i j).coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
      intro W hWm
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hWm
      rw [hKs i]
      have h := map_sum (classNumAddHom (Sum.elim z z') Q W) (fun j => pairDiff j * Kz i j)
        Finset.univ
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact classNum_pairDiff_mul (vNumL_add_of_ratDiv_ne_zero hϖ hP (hD i) hWm) z z' j (hKh i j) Q
        (by omega)
    simp only [F, V, cycEval_eq_sum hfin]
    rw [Finset.sum_congr rfl
      (fun W hW' => congrArg (ratDiv P (f i) (g i) W * ·) (hW W hW'))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
    ring
  have hF : ∀ i j, F j i = -F i j := by
    intro i j
    simp only [F]
    rw [hKa j i, support_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hP' : IsModelOver P ((classList (Sum.elim z z') μ ++ Q).length + 1) := by
      rw [hlen i j μ hμ]
      exact hP
    have hc := cycEval_vNumL_comm hC2 hϖ _ hP' (hD i) (hD j)
    simp only [V, coeff_neg]
    rw [hc]
    ring
  rw [hexp]
  have hS : ∑ i, ∑ j, F i j = -∑ i, ∑ j, F i j := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hF i j
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutForms.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (S : Finset (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O))),
      (∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ Q ∧
        (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q) →
      ∃ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs ∧ IsMultiHomog h ch ∧
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧ h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h ∧
        ∀ Q ∈ S, h ∉ Q

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def secondFactorBlocks {K : Type*} : Option K ↪ Option (Option K) where
  toFun o := Option.elim o none fun k => some (some k)
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

def SegreFlagCutProjection.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        FieldNumbers.relDim (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W)) <
          ((d + k : ℕ) : WithBot (WithTop ℤ))) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        FieldNumbers.relDim (FieldNumbers.contractPrime secondFactorBlocks (specialIdeal W)) <
          ((d + k : ℕ) : WithBot (WithTop ℤ)))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Module IsLocalRing

noncomputable section

universe u

namespace FiniteBirationalLength

theorem length_quot_maximal_eq_inertiaDeg {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.length A (B ⧸ 𝔫) = (𝔫.inertiaDeg A : ℕ∞) := by
  have hmax : (𝔫.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫
  have hm : 𝔫.under A = maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : 𝔫.LiesOver (maximalIdeal A) := ⟨hm.symm⟩
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ 𝔫) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫,
    Module.length_eq_of_surjective (R := A ⧸ maximalIdeal A) (S := A) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem full : FiniteBirationalLength.Statement.{u} := by
  intro A B _ _ _ _ _ _ _ _ hdim hinj hrank z hz
  classical
  have hfinMS := Vertical.LengthDecomp.finite_maximalSpectrum (R := A) (B := B)
  have hfin : Finite {𝔫 : Ideal B // 𝔫.IsMaximal} :=
    Finite.of_injective
      (fun 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal} => (⟨𝔫.1, 𝔫.2⟩ : MaximalSpectrum B))
      (fun a b h => Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  refine ⟨hfin, ?_⟩
  let : Fintype {𝔫 : Ideal B // 𝔫.IsMaximal} := Fintype.ofFinite _
  have : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr hinj
  have h1 := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A B z hdim hz
  rw [hrank, Nat.cast_one, one_mul, Ring.ord] at h1
  let hP : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal}, 𝔫.1.IsPrime := fun 𝔫 => 𝔫.2.isPrime
  have h2 := FieldNumbers.FiniteAlgebraLengthSum.proof A B {𝔫 : Ideal B // 𝔫.IsMaximal}
    (fun 𝔫 => 𝔫.1) (fun 𝔫 => 𝔫.2) Subtype.val_injective (fun M hM => ⟨⟨M, hM⟩, rfl⟩)
    (fun 𝔫 => Localization.AtPrime 𝔫.1) (fun 𝔫 => inferInstance) z
  rw [← h1, h2, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have := 𝔫.2
  rw [length_quot_maximal_eq_inertiaDeg, Ring.ord]

end FiniteBirationalLength

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagDegreeZero.Statement : Prop :=
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
      ∃ f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧ g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open Classical in
def SegreFlagCutDivisor.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsMultiHomog s cs → IsMultiHomog h ch →
      (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
      s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
      ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
        ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W = if 0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k) then 1 else 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagConeAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagConeAlg.Statement : Prop :=
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
    ∀ k : ℕ, 1 ≤ k → ∀ hkN : k ≤ N,
    ∃ (l : Fin k → Fin M) (m' : Fin M'),
      LinearIndependent Ω (fun i : Fin k => fun j : Fin k => φ (l i) (w (Fin.castLE hkN j))) ∧
      flagClosurePt y w e φ φ' t k ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin k => C (flagClosurePt y w e φ φ' t k ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none))))
          (C (flagClosurePt y w e φ φ' t k p) * X p.1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PairBundleTrdeg.proof (hadd : AdjoinTrdegAdd.Statement) (hind : PairConeLinesIndep.Statement)
    (halg : PairConeAlg.Statement) : PairBundleTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (pairProjCoord y e φ φ' t p) * X p.1
  let x : Fin N ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O (pairProjCoord y e φ φ' t))).trdeg_eq
    have e2 : (pointConeMap O (pairProjCoord y e φ φ' t)).range = Algebra.adjoin O (Set.range gZ) :=
      aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range x ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  have hind' := hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let f : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    f.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) x :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin N ⊕ Unit) x hxZ
    hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
