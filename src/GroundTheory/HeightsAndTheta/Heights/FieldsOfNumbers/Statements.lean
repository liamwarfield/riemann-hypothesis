module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def relDim [Fintype K] (I : Ideal (MRing ι F)) : WithBot (WithTop ℤ) :=
  WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
    (ringKrullDim (MRing ι F ⧸ I))

def EventuallyPoly (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) : Prop :=
  ∀ᶠ m in Filter.atTop, (h m : ℚ) = MvPolynomial.eval (fun k => (m k : ℚ)) p

def homFracDegZero (P : Ideal (MRing ι F)) [P.IsPrime] :
    IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
  IntermediateField.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ P ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}


open scoped Classical in
open Classical in
def resDeg (P : Ideal (MRing ι F)) : ℕ :=
  if h : P.IsPrime then haveI := h; Module.finrank F (homFracDegZero P) else 0


open scoped Classical in
open Classical in
def topCycle [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) (W : Ideal (MRing ι F)) : ℤ :=
  if h : W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n then
    haveI : W.IsPrime := h.1.1.1
    ((multAt I W).toNat : ℤ)
  else 0

end Objects

section Blocks

variable {K K' : Type*} {F : Type*} [Field F]

def blockIncl (j : K ↪ K') (ι' : K' → Type*) : (Σ k, ι' (j k)) → (Σ k', ι' k') :=
  fun v => ⟨j v.1, v.2⟩

def pullDeg (j : K ↪ K') (b : K → ℤ) : K' → ℤ :=
  Function.extend j b 0

def contractPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) :
    Ideal (MRing (fun k => ι' (j k)) F) :=
  P'.comap (rename (blockIncl j ι'))

instance contractPrime.isPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F))
    [P'.IsPrime] : (contractPrime j P').IsPrime :=
  Ideal.comap_isPrime _ _

def contractQuot (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) :
    (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') →ₐ[F] (MRing ι' F ⧸ P') :=
  Ideal.quotientMapₐ P' (rename (blockIncl j ι')) le_rfl

def contractFracMap (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') →ₐ[F]
      FractionRing (MRing ι' F ⧸ P') :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P'))
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (Ideal.quotientMap_injective))

def relDeg [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] : ℕ :=
  IntermediateField.relfinrank ((homFracDegZero (contractPrime j P')).map (contractFracMap j P'))
    (homFracDegZero P')

end Blocks

def GradedFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (m : K → ℕ),
    FiniteDimensional F (gradedPiece I m) ∧
      hilbFn I (fun k => (m k : ℤ)) = Module.finrank F (gradedPiece I m)

def HilbExactDivide.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∀ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c → ∀ m : K → ℤ,
      hilbFn I m - hilbFn (I.colon (Ideal.span {s})) (m - fun k => (c k : ℤ)) =
        hilbFn (I ⊔ Ideal.span {s}) m

def PolyOfDiffs.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℤ) (d : ℕ),
    (∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < d) ∧
      EventuallyPoly (diffStep (Pi.single k 1) h) q) →
    ∃ p : MvPolynomial K ℚ, p.totalDegree ≤ d ∧ EventuallyPoly h p

def HilbEventuallyPoly.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∃ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p

def HilbDegreeBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    (IsRelevant I → ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
        (p.totalDegree : WithBot (WithTop ℤ)) ≤ relDim I) ∧
      (¬ IsRelevant I → ∀ᶠ m in Filter.atTop, hilbFn I m = 0)

def MixedDiffConst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n →
      (∀ bs : Fin n → K → ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = intNum F I bs) ∧
      (∀ r : ℕ, n < r → ∀ bs : Fin r → K → ℤ,
        ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = 0)

def IntNumSymm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (n : ℕ) (bs : Fin n → K → ℤ)
    (σ : Equiv.Perm (Fin n)), intNum F I (bs ∘ σ) = intNum F I bs

def IntNumAdd.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ),
      intNum F I (Function.update bs i (b + b')) =
        intNum F I (Function.update bs i b) + intNum F I (Function.update bs i b')

def IntNumZeroSlot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)),
    (∀ (n : ℕ) (bs : Fin n → K → ℤ) (i : Fin n), bs i = 0 → intNum F I bs = 0) ∧
      (IsMultiHomogIdeal I → ∀ (n : ℕ) (bs : Fin n → K → ℤ), relDim I < n → intNum F I bs = 0)

def IntNumBase.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P), relDim P = 0 →
    haveI := hP.isPrime
    FiniteDimensional F (homFracDegZero P) ∧
      intNum F P (n := 0) ![] = Module.finrank F (homFracDegZero P)


open Classical in
def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ I ≤ Q j) ∧
      (∀ᶠ m in Filter.atTop, hilbFn I m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ I.minimalPrimes), IsRelevant W → relDim W = relDim I →
        haveI : W.IsPrime := hW.1.1
        ((((Finset.univ.filter fun j => Q j = W).card : ℕ) : ℕ∞) = multAt I W)) ∧
      (∀ j, ¬ IsRelevant (Q j) ∨ relDim (Q j) < relDim I ∨
        (Q j ∈ I.minimalPrimes ∧ relDim (Q j) = relDim I))

def MultEqualsCoeff.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ bs : Fin n → K → ℤ,
      intNum F I bs = cycEval (fun W => intNum F W bs) (topCycle I n)

def CutRegular.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c → s ∉ P →
    ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (c k : ℤ))) =
        cycEval (fun W => intNum F W bs) (divCycle P s)

def CutRational.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (bf bg : K → ℕ) (f g : MRing ι F),
    IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P → ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => intNum F W bs) (ratDiv P f g)

def ExistsForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P → ∀ b : K → ℤ,
    ∃ (bf bg : K → ℕ) (f g : MRing ι F), IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ f ∉ P ∧
      g ∉ P ∧ (fun k => (bf k : ℤ) - bg k) = b

structure IsIntersectionTheory {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (F : Type*) [Field F] (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ) : Prop where
  base : ∀ P : Ideal (MRing ι F), IsMultiProjPrime P → relDim P = 0 → N P 0 ![] = resDeg P
  cut : ∀ (P : Ideal (MRing ι F)) (n : ℕ), IsMultiProjPrime P → relDim P = (n + 1 : ℕ) →
    ∀ (bf bg : K → ℕ) (f g : MRing ι F), IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P →
    ∀ bs : Fin n → K → ℤ,
      N P (n + 1) (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => N W n bs) (ratDiv P f g)

def IntNumUnique.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ),
    IsIntersectionTheory F N → ∀ P : Ideal (MRing ι F), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = n → ∀ bs : Fin n → K → ℤ, N P n bs = intNum F P bs

def IntNumBaseChange.Statement : Prop :=
  (∀ (F : Type u) [Field F] (F' : Type v) [Field F'] [Algebra F F'] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)),
    (∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m) ∧
      ∀ (n : ℕ) (bs : Fin n → K → ℤ),
        intNum F' (I.map (MvPolynomial.map (algebraMap F F'))) bs = intNum F I bs) ∧
  (∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    IsMultiProjPrime (P.map (MvPolynomial.map (algebraMap F (RatFunc F)))))

def ProjectionFormulaContracted.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') < n → ∀ bs : Fin n → K → ℤ,
      intNum F P' (fun i => pullDeg j (bs i)) = 0

def ProjectionFormulaDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') = n → ∀ bs : Fin n → K → ℤ,
      haveI := hP'.isPrime
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' ∧
        intNum F P' (fun i => pullDeg j (bs i)) =
          relDeg j P' * intNum F (contractPrime j P') bs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem isRelevant_iff {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (I : Ideal (MRing ι R)) :
    IsRelevant I ↔ ∀ k, ∃ v : Σ k, ι k, v.1 = k ∧ (X v : MRing ι R) ∉ I := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · intro h k
    obtain ⟨⟨k', i⟩, hk, hi⟩ := h k
    subst hk
    exact ⟨i, hi⟩

theorem extend_zero_inj {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y :=
  ⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)

include hgj

include hgj in
theorem weight_mapDomain (hj : Function.Injective j) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g d) =
      Function.extend j (Finsupp.weight (blockWeight ι) d) 0 := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • blockWeight ι' i)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext k'
  by_cases hk : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hj.extend_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      hj.eq_iff]
  · rw [Function.extend_apply' _ _ _ hk]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      Pi.zero_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [ite_eq_right fun h => hk ⟨v.1, h.symm⟩, smul_zero]


include hgj in
theorem rename_weightedHomogeneousComponent (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain g d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg,
      coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    · rfl


include hgj in
theorem isMultiProjPrime_comap_rename (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) := by
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [rename_weightedHomogeneousComponent hgj hj hg]
    exact hP.multiHomog _ hf _
  · rw [isRelevant_iff]
    intro k
    obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k)
    obtain ⟨v, rfl⟩ := hsurj w ⟨k, hw.symm⟩
    refine ⟨v, hj (by rw [← hgj, hw]), ?_⟩
    rw [Ideal.mem_comap, rename_X]
    exact hwP

end

end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LengthSumLocalizations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module TensorProduct

noncomputable section

namespace LengthSumLocalizations

variable {B : Type*} [CommRing B]

theorem algebraMap_quot_maximalIdeal_surjective (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*)
    [CommRing C] [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    Function.Surjective (algebraMap B (C ⧸ IsLocalRing.maximalIdeal C)) := by
  intro _ y
  obtain ⟨x, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 C).surjective y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨b, by rw [← hx]; rfl⟩

theorem isSimpleModule_quot_maximalIdeal (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] :
    have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
    IsSimpleModule B (C ⧸ IsLocalRing.maximalIdeal C) := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  let : Field (C ⧸ IsLocalRing.maximalIdeal C) := Ideal.Quotient.field _
  rw [← Module.length_eq_one_iff,
    Module.length_eq_of_surjective (algebraMap_quot_maximalIdeal_surjective 𝔪 C)]
  exact Module.length_eq_one _ _

theorem isFiniteLength_of_atPrime (𝔪 : Ideal B) [𝔪.IsMaximal] (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.AtPrime C 𝔪] (M : Type*) [AddCommGroup M] [Module C M]
    [instB : Module B M] [instT : IsScalarTower B C M] (hM : IsFiniteLength C M) :
    IsFiniteLength B M := by
  have : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C 𝔪
  revert instB instT
  induction hM with
  | of_subsingleton => intro _ _; exact .of_subsingleton
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro _ _
    have hN' : IsFiniteLength B (N.restrictScalars B) := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    have := isSimpleModule_quot_maximalIdeal 𝔪 C
    have : IsSimpleModule B (M ⧸ N.restrictScalars B) :=
      IsSimpleModule.congr ((Submodule.Quotient.restrictScalarsEquiv B N).trans
        (e.restrictScalars B))
    exact .of_simple_quotient hN'

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]

omit [Fintype ι] in

omit [Fintype ι] in
theorem length_tensor_quot (hinj : Function.Injective 𝔪) (i j : ι) :
    Module.length (C i) (C i ⊗[B] (B ⧸ 𝔪 j)) = if i = j then 1 else 0 := by
  have : IsLocalRing (C i) := IsLocalization.AtPrime.isLocalRing (C i) (𝔪 i)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i) (𝔪 j)).toLinearEquiv.length_eq]
  split_ifs with h
  · subst h
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal (𝔪 i) (C i)]
    have : IsSimpleModule (C i) (C i ⧸ IsLocalRing.maximalIdeal (C i)) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  · have hne : ¬ 𝔪 j ≤ 𝔪 i := fun hle =>
      h (hinj ((h𝔪 j).eq_of_le (h𝔪 i).ne_top hle)).symm
    obtain ⟨x, hxj, hxi⟩ := Set.not_subset.mp hne
    have htop : (𝔪 j).map (algebraMap B (C i)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxj)
        (IsLocalization.map_units (C i) (⟨x, hxi⟩ : (𝔪 i).primeCompl))
    rw [htop, Module.length_eq_zero_iff]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl

omit [Fintype ι] [DecidableEq ι] in

omit [Fintype ι] [DecidableEq ι] in
theorem pi_mk_injective (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (N : Type*)
    [AddCommGroup N] [Module B N] :
    Function.Injective (LinearMap.pi fun i => TensorProduct.mk B (C i) N 1) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro n hn
  by_contra hne
  have hlt : LinearMap.ker (LinearMap.toSpanSingleton B N n) ≠ ⊤ := by
    intro htop
    apply hne
    have h1 : (1 : B) ∈ LinearMap.ker (LinearMap.toSpanSingleton B N n) := htop ▸ Submodule.mem_top
    simpa using h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hlt
  obtain ⟨i, rfl⟩ := hall M hM
  have : IsLocalizedModule (𝔪 i).primeCompl (TensorProduct.mk B (C i) N 1) :=
    (isLocalizedModule_iff_isBaseChange (𝔪 i).primeCompl (C i) _).mpr
      (TensorProduct.isBaseChange B N (C i))
  have h0 : TensorProduct.mk B (C i) N 1 n = 0 := by
    simpa using congrFun hn i
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝔪 i).primeCompl _).mp h0
  exact s.2 (hle (by rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hs))

theorem length_eq_sum_of_isFiniteLength (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [instA : Module A N] [instT : IsScalarTower A B N]
    (hN : IsFiniteLength B N) :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  revert instA instT
  induction hN with
  | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ P hs hP ih =>
    intro _ _
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain ⟨j, rfl⟩ := hall I hI
    let f : P →ₗ[B] M := P.subtype
    let g : M →ₗ[B] B ⧸ 𝔪 j := e.toLinearMap ∘ₗ P.mkQ
    have hf : Function.Injective f := P.subtype_injective
    have hg : Function.Surjective g := e.surjective.comp P.mkQ_surjective
    have hfg : Function.Exact f g := LinearMap.exact_iff.mpr (by
      rw [LinearEquiv.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype])
    have key : ∀ i, Module.length (C i) (C i ⊗[B] M) =
        Module.length (C i) (C i ⊗[B] P) + if i = j then 1 else 0 := by
      intro i
      have : Module.Flat B (C i) := IsLocalization.flat (C i) (𝔪 i).primeCompl
      rw [Module.length_eq_add_of_exact (AlgebraTensorModule.lTensor (C i) (C i) f)
        (AlgebraTensorModule.lTensor (C i) (C i) g)
        (Module.Flat.lTensor_preserves_injective_linearMap f hf)
        (LinearMap.lTensor_surjective (C i) hg) (Module.Flat.lTensor_exact (C i) hfg),
        length_tensor_quot 𝔪 C hinj i j]
    rw [Module.length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg, ih]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem length_eq_sum (hinj : Function.Injective 𝔪)
    (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (A : Type*) [CommRing A] [Algebra A B]
    (N : Type*) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    Module.length A N = ∑ i, Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
  by_cases hN : IsFiniteLength B N
  · exact length_eq_sum_of_isFiniteLength 𝔪 C hinj hall A N hN
  have hA : Module.length A N = ⊤ := by
    by_contra hA
    apply hN
    have hA' := isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hA)
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hA'.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsFiniteLength (C i) (C i ⊗[B] N) := by
    by_contra! h
    apply hN
    have hpi : Module.length B (∀ i, C i ⊗[B] N) ≠ ⊤ := by
      rw [Module.length_pi_of_fintype, ENat.sum_ne_top]
      exact fun i _ => Module.length_ne_top_iff.mpr
        (isFiniteLength_of_atPrime (𝔪 i) (C i) _ (h i))
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top hpi (Module.length_le_of_injective _ (pi_mk_injective 𝔪 C hall N))
  have : Nontrivial (B ⧸ 𝔪 i) := Ideal.Quotient.nontrivial_iff.mpr (h𝔪 i).ne_top
  have hd : Module.length A (B ⧸ 𝔪 i) ≠ 0 := (Module.length_pos (R := A)).ne'
  have hti : Module.length (C i) (C i ⊗[B] N) = ⊤ := by
    by_contra h'
    exact hi (Module.length_ne_top_iff.mp h')
  rw [hA, eq_comm, ← top_le_iff]
  calc (⊤ : ℕ∞) = Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i) := by
        rw [hti, ENat.top_mul hd]
    _ ≤ _ := Finset.single_le_sum (f := fun i =>
        Module.length (C i) (C i ⊗[B] N) * Module.length A (B ⧸ 𝔪 i))
        (fun _ _ => zero_le) (Finset.mem_univ i)

end LengthSumLocalizations

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module

theorem FiniteAlgebraLengthSum.proof : FiniteAlgebraLengthSum.Statement := by
  classical
  intro A B _ _ _ _ _ ι _ 𝔪 h𝔪 hinj hall C _ _ hC α
  have : ∀ i, (𝔪 i).IsMaximal := h𝔪
  have : ∀ i, IsLocalization.AtPrime (C i) (𝔪 i) := hC
  have hrange : LinearMap.range (LinearMap.lsmul A B α) =
      (Ideal.span {algebraMap A B α}).restrictScalars A := by
    ext b
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ hrange).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B α})).length_eq,
    LengthSumLocalizations.length_eq_sum 𝔪 C hinj hall A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ring.ord, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i)
    (Ideal.span {algebraMap A B α})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u u' v v' w

section Objects

def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) : Prop :=
  ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)



end Objects


section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

universe u v

theorem LocalizedQuotientLength.proof : LocalizedQuotientLength.Statement.{u, v} := by
  intro S _ P W _ x R _ _ hR
  let f : S →+* R := (algebraMap (S ⧸ P) R).comp (Ideal.Quotient.mk P)
  have hu : ∀ t : W.primeCompl, IsUnit (f t) := fun t => IsLocalization.map_units R
    (⟨Ideal.Quotient.mk P t, Submonoid.mem_map_of_mem _ t.2⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  let g : Localization.AtPrime W →+* R := IsLocalization.lift (M := W.primeCompl) hu
  have hg : ∀ s, g (algebraMap S (Localization.AtPrime W) s) = f s := IsLocalization.lift_eq hu
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (W.primeCompl.map (Ideal.Quotient.mk P)) r
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t, ht, hmt⟩ := Submonoid.mem_map.mp m.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) s ⟨t, ht⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec, mul_comm]
    show algebraMap (S ⧸ P) R (Ideal.Quotient.mk P s) = _ * algebraMap (S ⧸ P) R (Ideal.Quotient.mk P t)
    rw [hmt, IsLocalization.mk'_spec]
  let _ : Algebra (Localization.AtPrime W) R := g.toAlgebra
  let _ : Algebra S R := f.toAlgebra
  have _ : IsScalarTower S (Localization.AtPrime W) R := IsScalarTower.of_algebraMap_eq fun s => (hg s).symm
  set J := Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)}
  rw [← Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := R) (M := R ⧸ J) gsurj]
  have hI : P ⊔ Ideal.span {x} ≤ LinearMap.ker (Algebra.linearMap S (R ⧸ J)) := by
    refine sup_le (fun p hp => ?_) (Ideal.span_le.2 ?_)
    · show Ideal.Quotient.mk J (algebraMap (S ⧸ P) R (Ideal.Quotient.mk P p)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero, map_zero]
    · rintro _ rfl
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : (S ⧸ (P ⊔ Ideal.span {x})) →ₗ[S] R ⧸ J := (P ⊔ Ideal.span {x}).liftQ _ hI
  have _ : IsLocalizedModule W.primeCompl φ := by
    constructor
    · intro t
      obtain ⟨u, hu'⟩ := hu t
      rw [Module.End.isUnit_iff]
      have key : ∀ q : R ⧸ J, algebraMap S (Module.End S (R ⧸ J)) t q = (u : R) • q := fun q => by
        rw [Module.algebraMap_end_apply, hu', ← algebraMap_smul R (t : S) q]; rfl
      refine ⟨fun a b hab => ?_, fun q => ⟨(↑u⁻¹ : R) • q, ?_⟩⟩
      · rw [key, key] at hab
        simpa [smul_smul] using congrArg ((↑u⁻¹ : R) • ·) hab
      · rw [key, smul_smul, Units.mul_inv, one_smul]
    · intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk _ s, t⟩, ?_⟩
      show Ideal.Quotient.mk J (f t * g (IsLocalization.mk' _ s t)) = Ideal.Quotient.mk J (f s)
      rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
    · intro a1 a2 h
      obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a1
      obtain ⟨a2, rfl⟩ := Ideal.Quotient.mk_surjective a2
      change Ideal.Quotient.mk J (f a1) = Ideal.Quotient.mk J (f a2) at h
      rw [Ideal.Quotient.eq, ← map_sub, Ideal.mem_span_singleton'] at h
      obtain ⟨r, hr⟩ := h
      obtain ⟨z, rfl⟩ := gsurj r
      obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
      have e : f t * g (IsLocalization.mk' _ b t) = f b := by
        rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec']
      have h2 : f (t * (a1 - a2) - b * x) = 0 := by
        rw [map_sub, map_mul, map_mul, ← hr, ← mul_assoc, e]
        exact sub_self _
      obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff
        (W.primeCompl.map (Ideal.Quotient.mk P)) R (Ideal.Quotient.mk P _)).1 h2
      obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hm
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm0
      refine ⟨⟨u, hu⟩ * t, ?_⟩
      show Ideal.Quotient.mk _ ((u * t) * a1) = Ideal.Quotient.mk _ ((u * t) * a2)
      rw [Ideal.Quotient.eq, show u * t * a1 - u * t * a2 = u * (t * (a1 - a2) - b * x) + u * b * x by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hm0)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)))
  exact ((IsLocalizedModule.iso W.primeCompl φ).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

end GroundTheory.Heights₂.Heights.FieldNumbers
end
