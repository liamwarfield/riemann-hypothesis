module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

def flagLineCoord (b w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (k : ℕ) (i : Fin N) : Φ :=
  ∑ j, flagCoord w e t k j * algebraMap Ω Φ (b.repr (w j) i)

end Objects


open Classical in
def SegreFlagCutSection.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (r : ℕ) (a : Fin r → MRing ι O), (∀ j, a j ∉ pointIdeal O y) →
      ∃ (cs ch : Option (Option K) → ℕ) (s h f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs ∧ IsMultiHomog h ch ∧
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧ h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h ∧
        (∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
          ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W =
            if 0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k) then 1 else 0) ∧
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃) ∧
        ∀ H, (divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s H ≠ 0 ∨ divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) h H ≠ 0) →
          (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ H →
          f₃ ∉ H ∧ g₃ ∉ H ∧ ∀ j, liftPairForm M M' (a j) ∉ H

def SegreFlagCutContraction.Statement : Prop :=
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
        ∀ l : List (Option (Option K) → ℤ), l.length = d + k → (∀ b ∈ l, b none = 0) → vNumL W l = 0) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        ∀ l : List (Option (Option K) → ℤ), l.length = d + k → (∀ b ∈ l, b (some none) = 0) → vNumL W l = 0)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace DvrConeDimTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  let F := FractionRing O
  have hPp : P.IsPrime := hP.isPrime
  have hG : (genFib P).IsPrime := (GenericFibProps.full.{0} O K ι P hP hPC).1
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    le_antisymm (GenericDimGe.proof.{0} O K ι P hPp hPC) (GenericDimBound.full.{0} O K ι P hP hPC)

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hdim, hB, h1, ← h2]
  rfl

end DvrConeDimTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

def homLocRing (P W : Ideal (MRing ι R)) [P.IsPrime] : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)}

end Objects

section Lemmas

def HomLocRingLocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.isPrime
      IsLocalRing (homLocRing P W) ∧ IsNoetherianRing (homLocRing P W) ∧
        ringKrullDim (homLocRing P W) = 1

def DivCycleHomLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ (W : Ideal (MRing ι O)) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes), IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      haveI : W.IsPrime := hW.1.1
      multAt (P ⊔ Ideal.span {x}) W =
        Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {(⟨_, hz⟩ : homLocRing P W)})

def FiniteBirationalLength.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B], ringKrullDim A = 1 →
    Function.Injective (algebraMap A B) → Module.finrank A B = 1 → ∀ z : A, z ≠ 0 →
      Finite {𝔫 : Ideal B // 𝔫.IsMaximal} ∧
      Module.length A (A ⧸ Ideal.span {z}) =
        ∑ᶠ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
          (haveI := 𝔫.2.isPrime
           Module.length (Localization.AtPrime 𝔫.1)
             (Localization.AtPrime 𝔫.1 ⧸
               Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap A B z)})) *
            (𝔫.1.inertiaDeg A : ℕ∞)

def BlowUpFibreSemilocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.multiProj.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (homLocRing P W) B),
        Module.Finite (homLocRing P W) B ∧ Function.Injective (algebraMap (homLocRing P W) B) ∧
        Module.finrank (homLocRing P W) B = 1 ∧
        ∃ e : {𝔫 : Ideal B // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
            W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
              W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
          ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
            (haveI := 𝔫.2.isPrime
             Module.length (Localization.AtPrime 𝔫.1)
               (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
                 (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) =
              ((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat : ℕ∞) ∧
            𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace plainPolynomialPairNumber

open plainPairNumber (term rename_divDiff_eq_sum)

theorem rename_divDiff_add {r : ℕ} (l : Fin r) (A B : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l (A + B)) =
      rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l A) +
        rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l B) := by
  classical
  rw [rename_divDiff_eq_sum l (A + B) support_add,
    rename_divDiff_eq_sum l A Finset.subset_union_left,
    rename_divDiff_eq_sum l B Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem term_tail {N q : ℕ} (i : Fin N) (μ : Fin N →₀ ℕ) (t : Fin q →₀ ℕ) (ν : Fin (N + q) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd q j) = μ j) (hn : ∀ j, ν (Fin.natAdd N j) = t j) :
    term (Fin.castAdd q i) ν =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q)) (term i μ) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  have hlt : ∀ j : Fin q, ¬ Fin.natAdd N j < Fin.castAdd q i := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hgt : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd N j := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hcc : ∀ j k : Fin N, (Fin.castAdd q j < Fin.castAdd q k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.castAdd q i),
      (X (Sum.inr j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => j < i), X (Sum.inr (Fin.castAdd q j)) ^ μ j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_false, Finset.prod_const_one, mul_one, hcc, hc]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.castAdd q i < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      (∏ j ∈ Finset.univ.filter (fun j => i < j), X (Sum.inl (Fin.castAdd q j)) ^ μ j) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_true, hcc, hc, hn]
  unfold term
  rw [h1, h3, hc i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem rename_monomial_tail {N q : ℕ} (t : Fin q →₀ ℕ) (c : ℤ) :
    rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) (monomial t c) =
      C c * ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, rename_X, rename_C]

theorem rename_divDiff_castAdd_monomial {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (t : Fin q →₀ ℕ) (c : ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) (monomial t c))) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q)))
          (monomial t c) := by
  classical
  set T : Fin (N + q) →₀ ℕ := t.mapDomain (Fin.natAdd N) with hT
  have hinj : Function.Injective
      (fun μ : Fin N →₀ ℕ => Finsupp.mapDomain (Fin.castAdd q) μ + T) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.castAdd_injective _ _) (add_right_cancel h)
  have hsub : (rename (Fin.castAdd q) G * monomial T c).support ⊆
      G.support.image (fun μ => Finsupp.mapDomain (Fin.castAdd q) μ + T) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · have hmem : ν - T ∈ (rename (Fin.castAdd q) G).support :=
        mem_support_iff.mpr (left_ne_zero_of_mul hν)
      rw [support_rename_of_injective (Fin.castAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rename_monomial, ← hT, rename_divDiff_eq_sum (Fin.castAdd q i) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum i G subset_rfl, map_sum,
    Finset.sum_mul, rename_monomial_tail]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.castAdd q j) = μ j := by
    intro j
    have hj : Fin.castAdd q j ∉ Set.range (Fin.natAdd N : Fin q → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective _ _), hT,
      Finsupp.mapDomain_of_notMem_range _ _ hj, add_zero]
  have hn : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.natAdd N j) = t j := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd q : Fin N → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, hT,
      Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective _ _), zero_add]
  rw [coeff_mul_monomial, coeff_rename_mapDomain _ (Fin.castAdd_injective _ _),
    term_tail i μ t _ hc hn, C_mul]
  simp only [map_mul, rename_C]
  ring

theorem rename_divDiff_castAdd_mul {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin q) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q)) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial t c => exact rename_divDiff_castAdd_monomial i G t c
  | add A B hA hB => rw [map_add (f := _), mul_add, rename_divDiff_add, hA, hB, map_add (f := _), mul_add]

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_mul_tail {σ : Type*} [DecidableEq σ] {q : ℕ} (cls : σ → K → ℤ)
    (L : Fin q → K → ℤ) (z : Fin q → σ) (hz : cls ∘ z = L) (A : MvPolynomial σ ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum cls (A * rename z Q) [] W = ∑ μ ∈ Q.support, Q.coeff μ * classNum cls A (classList L μ) W := by
  have hadd : ∀ H : MvPolynomial σ ℤ, classNum cls H [] W = classNumAddHom cls [] W H := fun _ => rfl
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, hadd, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [rename_monomial, show monomial (μ.mapDomain z) (Q.coeff μ) =
      Q.coeff μ • monomial (μ.mapDomain z) (1 : ℤ) by rw [smul_monomial, smul_eq_mul, mul_one],
    mul_smul_comm, map_zsmul, smul_eq_mul, ← hadd, plainPairNumber.classNum_mul_monomial,
    classList_mapDomain, hz, List.append_nil]

theorem proof : plainPolynomialPairNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x x' f g m G hG hm q L Q hQ
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous (d + 1) := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show m + (d + 1 - m) = d + 1 by omega] at h3
  rw [BundleExamples.pairNum_eq P d _ _ _ _ hH]
  unfold pairNum
  have hr : ratDiv P 1 1 = fun _ => 0 := funext fun W => sub_self _
  have hz : ∀ n : Ideal (MRing ι O) → ℤ, cycEval n (fun _ => 0) = 0 := by
    intro n
    simp [cycEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hr, hz, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hZ := ratDiv_finite_support P (f i) (g i)
  simp only [cycEval_eq_sum hZ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hcls : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      Sum.map (Fin.castAdd q) (Fin.castAdd q) = Sum.elim x x' := by
    funext p
    cases p <;> simp [Fin.append_left]
  have hL : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) = L := by
    funext j
    simp [Fin.append_right]
  rw [rename_divDiff_castAdd_mul, classNum_mul_tail _ L _ hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [plainPairNumber.classNum_rename _ (Sum.map_injective.mpr
      ⟨Fin.castAdd_injective _ _, Fin.castAdd_injective _ _⟩), hcls]
  ring

end plainPolynomialPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E')
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
      IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      F₁.value O I₁ G y y' f g Q = F₂.value O I₂ G y y' f g Q

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensExpress.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, ∃ n : ℕ, f ^ n * t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨m, hm⟩ := ht q
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (a q * t q) = (f ^ n * a q) * (f ^ m * t q) := by ring
    rw [this]
    exact mul_mem hn hm

theorem TwistedDualGensExpress.proof : TwistedDualGensExpress.Statement := by
  unfold TwistedDualGensExpress.Statement
  intro R _ ϖ Ω _ _ K _ ι y N E _ _ B B' hsame a a' M M' φ φ' hφ hφ' c hc m
  set A := chartRing R (segreVec y) c with hA
  set w : Ω := algebraMap R Ω ϖ with hw
  have hwA : w ∈ A := Subalgebra.algebraMap_mem _ ϖ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  set ψ : Module.Dual Ω E := (∏ k, y ⟨k, c k⟩ ^ (-a' k)) • φ' m with hψ
  have hψA : ∀ v ∈ B'.lat c, ψ v ∈ A := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := hφ'.sections c hc m v hv
    have : ψ v = s := by
      rw [hψ, LinearMap.smul_apply, hsv, smul_eq_mul, mul_comm s, ← mul_assoc,
        ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
          rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy k))]), one_mul]
    rw [this]
    exact hs
  obtain ⟨k0, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbq : ∀ l q, ∃ n : ℕ, f l ≠ 0 → ∃ e : ℕ, f l ^ e * (w ^ n * ψ (b l q)) ∈ A := by
    intro l q
    by_cases hl : f l = 0
    · exact ⟨0, fun h => (h hl).elim⟩
    obtain ⟨e, he⟩ := (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
        by_cases h : q' = q
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := (hsame c hc).1 _ he
    refine ⟨n, fun _ => ⟨e, ?_⟩⟩
    have h := hψA _ hn
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    rw [show f l ^ e * (w ^ n * ψ (b l q)) = w ^ n * (f l ^ e * ψ (b l q)) by ring]
    exact h
  choose nb hnb using hbq
  set n := Finset.univ.sup (fun p : Fin k0 × Fin N => nb p.1 p.2) with hn
  have hle : ∀ l q, nb l q ≤ n := fun l q =>
    Finset.le_sup (f := fun p : Fin k0 × Fin N => nb p.1 p.2) (Finset.mem_univ (l, q))
  have hmain : ∀ v ∈ B.lat c, (w ^ n • ψ) v ∈ A := by
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
    intro l
    by_cases hl : f l = 0
    · exact ⟨1, by simp [hl]⟩
    obtain ⟨a'', ha'', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨e, he⟩ := TwistedDualGensExpress.sum_mul_mem_localized A (hf l) a''
      (fun q => w ^ n * ψ (b l q)) ha'' (fun q => by
        obtain ⟨e, he⟩ := hnb l q hl
        refine ⟨e, ?_⟩
        rw [← pow_sub_mul_pow w (hle l q)]
        rw [show f l ^ e * (w ^ (n - nb l q) * w ^ nb l q * ψ (b l q)) =
          w ^ (n - nb l q) * (f l ^ e * (w ^ nb l q * ψ (b l q))) by ring]
        exact mul_mem (pow_mem hwA _) he)
    refine ⟨e, ?_⟩
    have : w ^ n * ψ v = ∑ q, a'' q * (w ^ n * ψ (b l q)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hrep, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    rw [smul_eq_mul, this]
    exact he
  obtain ⟨u, hu, hsum'⟩ := hφ.generate c hc (w ^ n • ψ) hmain
  refine ⟨n, u, hu, ?_⟩
  have hY : (∏ k, y ⟨k, c k⟩ ^ a' k) * ∏ k, y ⟨k, c k⟩ ^ (-a' k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hy k))]
  have h1 : w ^ n • φ' m = (∏ k, y ⟨k, c k⟩ ^ a' k) • (w ^ n • ψ) := by
    rw [hψ, smul_comm (w ^ n) (∏ k, y ⟨k, c k⟩ ^ (-a' k)), smul_smul, hY, one_smul]
  rw [h1, hsum', Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_add₀ (hy k), sub_eq_add_neg]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace JoinPointNumbers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fieldNum_spec (F : Type) [Field F] {K' : Type} [Fintype K'] (κ : K' → Type) [∀ k, Fintype (κ k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) ⟨_, IntNumIsFieldIntersection.full F K' κ⟩

theorem redIdeal_map_liftVar {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (W.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).map
        (rename (R := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal
  change Ideal.map (MvPolynomial.map (IsLocalRing.residue O))
      (Ideal.map (rename (R := O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom W) =
    Ideal.map (rename (R := IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom
      (Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp [MvPolynomial.map_rename]

theorem monoList_pullDeg {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).map (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit)) := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]

theorem polyNum_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) (F : Type) [Field F]
    (V : Ideal (MRing ι F)) (d : ℕ) (hVd : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V d) {r : ℕ}
    (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F (Sum.elim ι ptIdx))
                              (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum F V bs) V d deg H := by
  have hV' := hV F K ι V d hVd
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have hl := monoList_pullDeg deg μ
  by_cases h : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d
  · have h' : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rw [hl, List.length_map, h]
    rw [dite_eq_left h', dite_eq_left h, Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full _ (fieldNum_spec F _) _ d _ hV']
    beta_reduce
    rw [← hN F K ι V d]
    congr 1
    funext j
    simp [hl]
  · have h' : ¬ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rwa [hl, List.length_map]
    rw [dite_eq_right h', dite_eq_right h]

theorem vEval_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (d : ℕ) {r : ℕ} (deg : Fin r → K → ℤ)
    (H : MvPolynomial (Fin r) ℤ) (Z : Ideal (MRing ι O) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
      (Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) Z) =
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H) Z := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun W hW => ?_
  rw [redIdeal_map_liftVar]
  beta_reduce
  rw [polyNum_join hV hN _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d (hZ W (Finsupp.mem_support_iff.mp hW))
    deg H]

theorem mem_divSupp_of_ne {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (s : MRing ι R) (W : Ideal (MRing ι R)) (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) :
    W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  classical
  by_contra hW
  apply h
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg hW]

theorem intCycle_join (hD : JoinDivCycle.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
        (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) s)) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s)) := by
  rw [hD R K ι P s, Finsupp.mapDomain_mapRange _ _ _ _ fun x y => Nat.cast_add x y]

theorem proof (hI : JoinPointIdeal.Statement) (hD : JoinDivCycle.Statement)
    (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement)
    (hF : VerticalComponentFibre.Statement) : JoinPointNumbers.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hM r deg H
  rw [hI O Ω K ι y]
  refine ⟨fun b f g hdiv => ?_, fun a ha => ?_⟩
  · have hc : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
        ((pointIdeal O y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g) =
        Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g) := by
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc
      rw [intCycle_join hD, intCycle_join hD, Finsupp.mapDomain_sub]
    rw [hc]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have hvert : (C ϖ : MRing ι O) ∈ W :=
      hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
    obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) f W ≠ 0 ∨
        ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) g W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM f bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM g bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  · have hC : (C a : MRing (Sum.elim ι ptIdx) O) =
        rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) (C a) := (rename_C _ _).symm
    rw [hC, intCycle_join hD]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a) W ≠ 0 := by
      intro h0
      apply hW
      simp [h0]
    have hs := mem_divSupp_of_ne _ _ _ h
    have hWp : W.IsPrime := hs.1.1.1
    have hCa : (C a : MRing ι O) ∈ W := hs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnP : (C a : MRing ι O) ∉ pointIdeal O y := by
      intro hmem
      have hmem' : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
      rw [hM.noTorsion, Ideal.mem_bot] at hmem'
      exact ha hmem'
    have hvert : (C ϖ : MRing ι O) ∈ W := by
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      rw [hu, C_mul, C_pow] at hCa
      rcases hWp.mem_or_mem hCa with h1 | h1
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 ((Units.isUnit u).map C)) hWp.ne_top
      · exact hWp.mem_of_pow_mem n h1
    obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM (C a) 0 (isWeightedHomogeneous_C _ _) hnP W
      hs.1 hs.2 hvert
    exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩

end JoinPointNumbers

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagPlainValueIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (L : Fin r → K → ℤ) (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 →
      G.IsHomogeneous c → Q.IsHomogeneous (d + 1 - c) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ₁.deg L) (Fin.append φ₁.deg' L) (Fin.append φ₁.f fun _ => 1)
                                (Fin.append φ₁.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
          (Fin.append φ₂.deg L) (Fin.append φ₂.deg' L) (Fin.append φ₂.f fun _ => 1)
          (Fin.append φ₂.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)

def PairNumberJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord z w))) d →
    fnField O (joinCoord x (joinCoord z w)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι' ι₂)))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord z w))) d
          (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
          (fun i => rename (assocVar ι₂) (f i)) (fun i => rename (assocVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end
