module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalFiniteRank.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.IsTorsionFree (degZeroLoc (contractPrime j P') {W})
          (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.finrank (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) =
          relDeg j P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocalRing.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    (IsNoetherianRing (degZeroLoc P {W}) ∧ IsLocalRing (degZeroLoc P {W})) ∧
      ∀ n : ℕ, relDim P = (n + 1 : ℕ) → relDim W = (n : ℕ) → ringKrullDim (degZeroLoc P {W}) = 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleMinimal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), P.IsPrime →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ a : MRing ι F, a ∉ P →
    ∀ (W : Ideal (MRing ι F)) (hW : W.IsPrime), relDim W = (n : ℕ) → P ⊔ Ideal.span {a} ≤ W →
      haveI := hW
      W ∈ (P ⊔ Ideal.span {a}).minimalPrimes ∧ multAt (P ⊔ Ideal.span {a}) W ≠ ⊤

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeLocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W), P ≤ W →
    ∀ (c : K → ℕ) (a h : MRing ι F), IsMultiHomog a c → IsMultiHomog h c → h ∉ W →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ α : degZeroLoc P {W},
      (α : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P a) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P h) →
        multAt (P ⊔ Ideal.span {a}) W =
          Ring.ord (degZeroLoc P {W}) α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsValuativeCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ValuativeCentre.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P),
    haveI := hP.isPrime
    ∀ R : ValuationSubring (FractionRing (MRing ι F ⧸ P)),
      (∀ c : F, algebraMap F (FractionRing (MRing ι F ⧸ P)) c ∈ R) →
      ∃ y : Ideal (MRing ι F), IsMultiProjPrime y ∧ P ≤ y ∧
        ∀ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
              algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ R ∧
            (f ∈ y ↔ algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
                (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈
              R.nonunits)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
          ∃ N : ℕ, Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) = N ∧
            cycEval M (divCycle P' (rename (blockIncl j ι') a)) = N

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

section Cone

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem primeCompl_map_le_nonZeroDivisors (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) :
    W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι F ⧸ P) := by
  rintro _ ⟨s, hs, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hs (hPW h)

def coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors P W hPW)


omit [DecidableEq K] in
instance coneLocal.isLocalization (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocal P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _

theorem degZeroLoc_le_coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ degZeroLoc P {W}, x ∈ coneLocal P W hPW := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, f, g, -, -, -, hgW, rfl⟩ := hx
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, hgW W rfl, rfl⟩, div_eq_mul_inv _ _⟩
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P)]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

def degZeroLocToCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    degZeroLoc P {W} →+* coneLocal P W hPW :=
  (degZeroLoc P {W}).val.toRingHom.codRestrict (coneLocal P W hPW)
    (fun x => degZeroLoc_le_coneLocal P W hPW x x.2)

instance degZeroLoc.algebraCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (degZeroLoc P {W}) (coneLocal P W hPW) :=
  (degZeroLocToCone P W hPW).toAlgebra

theorem degZeroLoc.algebraMap_cone_coe (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (x : degZeroLoc P {W}) :
    ((algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) x : coneLocal P W hPW) :
      FractionRing (MRing ι F ⧸ P)) = x :=
  rfl

end Cone

def ConeLocalFlat.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})) (_ : IsLocalRing (coneLocal P W hPW)),
      Module.Flat (degZeroLoc P {W}) (coneLocal P W hPW) ∧
        (maximalIdeal (degZeroLoc P {W})).map
            (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) =
          maximalIdeal (coneLocal P W hPW)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
