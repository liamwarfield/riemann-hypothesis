module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

section Generic

variable (k : Type*) [Field k] (e n : ℕ)

abbrev GenParField : Type _ := FractionRing (MvPolynomial (Par e n) k)

def genPar : Par e n → GenParField k e n :=
  fun p => algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)

abbrev GenSec {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k)) : Type _ :=
  SecAlg (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)

end Generic

def ChowNormFormGeneric.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite (GenParField k e n) (GenSec k e Q) ∧
        ∃ c : GenParField k e n, c ≠ 0 ∧
          specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
            C c * normForm (GenSec k e Q)
              (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))

def SecAlgFieldChange.Statement : Prop :=
  ∀ (E₀ E : Type) [Field E₀] [Field E] (φ : E₀ →+* E) (n e : ℕ)
    (Q₀ : Ideal (MvPolynomial (Fin n) E₀)) (y₀ : Par e n → E₀), Module.Finite E₀ (SecAlg Q₀ y₀) →
      Module.Finite E (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀)) ∧
        (normForm (SecAlg Q₀ y₀) (secCoord Q₀ y₀)).map φ =
          normForm (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))
            (secCoord (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))

def SecAlgFinite.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

def GenSecDomain.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsDomain (GenSec k e Q)

def GenSecSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Algebra.IsSeparable (GenParField k e n) (GenSec k e Q)

def ChowSecDvd.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∃ m : ℕ, 0 < m ∧
        (∑ j, X j * C (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y j)) ∣
          ((specRest (algebraMap k E) g y).map
            (algebraMap E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y))) ^ m

def NormFormIrreducible.Statement : Prop :=
  ∀ (E L : Type) [Field E] [CommRing L] [IsDomain L] [Algebra E L] [Module.Finite E L]
    [Algebra.IsSeparable E L] (n : ℕ) (x : Fin n → L) (t : Fin n → E),
    Algebra.adjoin E (Set.range x) = ⊤ → ∑ j, algebraMap E L (t j) * x j = 1 →
      Irreducible (normForm (R := E) L x)

def GenChowIrreducible.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Irreducible (specRest (algebraMap k (GenParField k e n)) g (genPar k e n))

def NormFormDvd.Statement : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (n : ℕ) (x : Fin n → A) (p : MvPolynomial (Fin n) R),
      (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) ∣ p.map (algebraMap R A) →
        normForm A x ∣ p ^ Module.finrank R A

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Objects

variable {K : Type*} [Field K] [NumberField K]

theorem comap_maximalIdeal_parDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (IsLocalRing.maximalIdeal (ParDVR e n v)).comap (algebraMap (𝓞 K) (ParDVR e n v)) = v.asIdeal := by
  have h1 : algebraMap (𝓞 K) (ParDVR e n v) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)).comp C :=
    IsScalarTower.algebraMap_eq _ _ _
  have h2 : (IsLocalRing.maximalIdeal (ParDVR e n v)).comap
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) = parPrime e n v :=
    Localization.AtPrime.under_maximalIdeal
  rw [h1, ← Ideal.comap_comap, h2]
  ext x
  simp only [Ideal.mem_comap, parPrime]
  constructor
  · intro hx
    rw [MvPolynomial.mem_map_C_iff] at hx
    simpa using hx 0
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

def resToKappa (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.ResidueField →+* (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  Ideal.ResidueField.map v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
    (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm

def parYκ (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Par e n → (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  fun p => algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField (parY e n v p)

end Objects

def SpecCompDim.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      IsProjPrime (reduceMod v W) ∧
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ reduceMod v W) = ((e + 1 : ℕ) : WithBot ℕ∞)

def ChartDomain.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n),
    Q.IsPrime → (∀ c : D, C c ∈ Q → c = 0) → X j ∉ Q →
      IsDomain (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)) ∧
        Function.Injective (algebraMap D
          (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)))

def SecAlgField.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsField (SecAlg (Q.map (MvPolynomial.map (algebraMap k (FractionRing (MvPolynomial (Par e n) k)))))
        (fun p => algebraMap (MvPolynomial (Par e n) k) (FractionRing (MvPolynomial (Par e n) k)) (X p)))

def ParFracIsFractionRing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (parToFrac e n v).toAlgebra
    IsFractionRing (ParDVR e n v) (ParFrac K e n)

def ResidueAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (resToKappa e n v).toAlgebra
    AlgebraicIndependent v.asIdeal.ResidueField (parYκ e n v)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecLinNZD
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem eval_specRest {k E : Type*} [CommRing k] [CommRing E] (φ : k →+* E) {n e : ℕ}
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (u : Fin n → k) :
    eval (fun j => φ (u j)) (specRest φ g y) =
      eval₂ φ (fun ij : Fin e × Fin n => y (.inl ij)) (specFirst g u) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [specRest, specFirst]
  | add p q hp hq =>
    simp only [specRest, specFirst, eval₂_add, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ij hp =>
    simp only [specRest, specFirst, eval₂_mul, eval₂_X, map_mul, bind₁_X_right] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [specFirstVar]

theorem SecLinNZD.proof (h1 : ChowNormForm.Statement) (h2 : NormFormEval.Statement)
    (h3 : SpecFirstNeField.Statement) : SecLinNZD.Statement := by
  intro k E _ _ _ _ n e Q g y u hy hQ hg hu
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  obtain ⟨hfin, c, _, hcg⟩ := h1 k E n e Q g y hy hQ hg
  have hy' : AlgebraicIndependent k (fun ij : Fin e × Fin n => y (.inl ij)) :=
    hy.comp _ Sum.inl_injective
  have hne : eval (fun j => algebraMap k E (u j)) (specRest (algebraMap k E) g y) ≠ 0 := by
    rw [eval_specRest]
    exact fun h0 => h3 k n e Q g u hQ hg hu
      (hy'.eq_zero_of_aeval_eq_zero _ (by rw [aeval_def]; exact h0))
  have hsum : (∑ j, algebraMap E (SecAlg QE y) (algebraMap k E (u j)) * secCoord QE y j) =
      secLin QE y (fun j => algebraMap k E (u j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [secLin, linForm, map_sum, map_mul]
    rfl
  have hnorm : Algebra.norm E (secLin QE y (fun j => algebraMap k E (u j))) ≠ 0 := by
    have h := h2 E (SecAlg QE y) n (secCoord QE y) (fun j => algebraMap k E (u j))
    rw [hsum] at h
    rw [hcg, eval_mul, eval_C, h] at hne
    exact right_ne_zero_of_mul hne
  have hunit : IsUnit (Algebra.lmul E (SecAlg QE y) (secLin QE y fun j => algebraMap k E (u j))) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hnorm
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp hunit).2 1
  have hz' : secLin QE y (fun j => algebraMap k E (u j)) * z = 1 := by
    simpa using hz
  exact (isUnit_iff_exists_inv.mpr ⟨z, hz'⟩).mem_nonZeroDivisors

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem parToFrac_algebraMap {K : Type*} [Field K] [NumberField K] (e n : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) x) = kToFrac K e n (algebraMap (𝓞 K) K x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem map_secLin {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secLin, linForm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j) := rfl
  have h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j)) :=
    rfl
  rw [h1, h2, hr]
  exact congrArg _ (hc j)

theorem SecBLinInj.proof (h1 : SecBGeneric.Statement) (h2 : SecBTorsionFree.Statement)
    (h3 : SecLinNZD.Statement) (h4 : ParAlgIndep.Statement) : SecBLinInj.Statement := by
  intro K _ _ n e I f u v hI hf hu
  obtain ⟨φ, hφc, hφr, hloc⟩ := h1 K n e I v hI
  let _ : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨m, hm⟩, hmb⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
      (SecAlg (idealF e I) (parYF K e n)) b).mp hb
    obtain ⟨r, hr, rfl⟩ := hm
    exact h2 K n e I v hI r b (nonZeroDivisors.ne_zero hr) ((Algebra.smul_def r b).trans hmb)
  let _ := (kToFrac K e n).toAlgebra
  have hnzd := h3 K (ParFrac K e n) n e I f (parYF K e n) (fun j => (u j : K)) (h4 K e n) hI hf hu
  have hmap : φ (secLin (modelR e I v) (parY e n v) fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      secLin (idealF e I) (parYF K e n) (fun j => kToFrac K e n (u j : K)) := by
    rw [map_secLin φ (parToFrac e n v) hφc hφr]
    simp only [parToFrac_algebraMap]
  intro b c hbc
  apply hφinj
  have h := congrArg φ hbc
  simp only [map_mul, hmap] at h
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp h

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem isHomogeneous_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by
  classical
  rw [specRest, g.as_sum, eval₂_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [eval₂_monomial, Finsupp.prod]
  have hdeg : ∀ ij : Fin (e + 1) × Fin n,
      (Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
        (fun i => C (y (.inl (i, ij.2)))) ij.1 : MvPolynomial (Fin n) S).IsHomogeneous
        (groupWeight (e + 1) n ij 0) := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [groupWeight] using isHomogeneous_X (R := S) j
    · have h0 : groupWeight (e + 1) n (i.succ, j) 0 = 0 := by simp [groupWeight]
      rw [h0]
      exact isHomogeneous_C _ _
  have hsum : ∑ ij ∈ m.support, groupWeight (e + 1) n ij 0 * m ij = d := by
    have hw := hg (mem_support_iff.mp hm)
    have h0 := congrFun hw 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h := (isHomogeneous_C (σ := Fin n) (φ (AddMonoidAlgebra.coeff g m))).mul
    (IsHomogeneous.prod m.support _ _ fun ij _ => (hdeg ij).pow (m ij))
  rw [zero_add, hsum] at h
  exact h

theorem isHomogeneous_det_linear {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => N (τ i) i) (fun _ => 1) fun i _ => hN (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  simpa using (isHomogeneous_C σ ((τ.sign : ℤ) : R)).mul hp

theorem ChowSecDegree.proof (h1 : ChowNormForm.Statement) (h2 : ChowFormHomog.Statement)
    (h3 : NormFormEval.Statement) : ChowSecDegree.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  classical
  obtain ⟨hfin, c, hc, heq⟩ := h1 k E n e Q g y hy hQ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  have : Module.Finite E (SecAlg QE y) := hfin
  have : Module.Free E (SecAlg QE y) := Module.Free.of_divisionRing E (SecAlg QE y)
  let b : Module.Basis (Module.Free.ChooseBasisIndex E (SecAlg QE y)) E (SecAlg QE y) :=
    Module.Free.chooseBasis E (SecAlg QE y)
  have hN : (normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    rw [normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hone : (∑ j, algebraMap E (SecAlg QE y) (y (.inr j)) * secCoord QE y j) = 1 := by
    have hmem : chartForm y - 1 ∈ secIdeal QE y := Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h := Ideal.Quotient.eq.mpr hmem
    rw [map_one] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [chartForm, linForm, secCoord, map_sum, map_mul]
    rfl
  have hN0 : normForm (R := E) (SecAlg QE y) (secCoord QE y) ≠ 0 := by
    intro h0
    have hv := h3 E (SecAlg QE y) n (secCoord QE y) (fun j => y (.inr j))
    rw [h0, map_zero, hone, map_one] at hv
    exact zero_ne_one hv
  have hG : (specRest (algebraMap k E) g y).IsHomogeneous (chowDegree Q (e + 1)) :=
    isHomogeneous_specRest _ (h2 k n (e + 1) Q g hg) y
  rw [heq] at hG
  have hCN : (C c * normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    simpa using hN.C_mul c
  exact hCN.inj_right hG (mul_ne_zero (C_ne_zero.mpr hc) hN0)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecBGeneric

variable {K : Type*} [Field K] [NumberField K]

theorem parToFrac_comp_algebraMap (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (parToFrac e n v).comp (algebraMap (𝓞 K) (ParDVR e n v)) =
      (kToFrac K e n).comp (algebraMap (𝓞 K) K) := by
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem parToFrac_parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by
  rw [parY, parToFrac, IsLocalization.lift_eq, parYF]

theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]

theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl) fun f hf => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) f.coeffs
  have hb0 : (algebraMap (𝓞 K) K b) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  have hrange : C (algebraMap (𝓞 K) K b) * f ∈ Set.range (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    by_cases h0 : AddMonoidAlgebra.coeff f m = 0
    · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
    · obtain ⟨y, hy⟩ := hb _ (coeff_mem_coeffs m h0)
      exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  obtain ⟨g, hg⟩ := hrange
  have hgI : g ∈ integralModel I := by
    show MvPolynomial.map (algebraMap (𝓞 K) K) g ∈ I
    rw [hg]
    exact I.mul_mem_left _ hf
  have : f = C (algebraMap (𝓞 K) K b)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) g := by
    rw [hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgI)

theorem map_secIdeal {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (secIdeal (modelR e I v) (parY e n v)).map (MvPolynomial.map (parToFrac e n v)) =
      secIdeal (idealF e I) (parYF K e n) := by
  have h1 : (modelR e I v).map (MvPolynomial.map (parToFrac e n v)) = idealF e I := by
    have hc : (MvPolynomial.map (parToFrac e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) : MvPolynomial (Fin n) (𝓞 K) →+* _) =
        (MvPolynomial.map (kToFrac K e n)).comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply, MvPolynomial.map_map, parToFrac_comp_algebraMap]
    rw [modelR, Ideal.map_map, hc, ← Ideal.map_map, map_integralModel, idealF]
  have h2 : (Ideal.span (Set.range (secForm (parY e n v)))).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span (Set.range (secForm (parYF K e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [secForm, map_linForm, parToFrac_parY]
  have h3 : (Ideal.span {chartForm (parY e n v) - 1}).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span {chartForm (parYF K e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    simp only [parToFrac_parY]
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]

end SecBGeneric


open SecBGeneric in
theorem SecBGeneric.proof : SecBGeneric.Statement := by
  intro K _ _ n e I v _
  have hJ := map_secIdeal e I v
  let M : Submonoid (MvPolynomial (Fin n) (ParDVR e n v)) :=
    (nonZeroDivisors (ParDVR e n v)).map (MvPolynomial.C : ParDVR e n v →+* MvPolynomial (Fin n) (ParDVR e n v))
  let φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n) :=
    Ideal.quotientMap _ (MvPolynomial.map (parToFrac e n v)) (hJ ▸ Ideal.le_comap_map)
  refine ⟨φ, fun j => ?_, fun r => ?_, ?_⟩
  · simp [φ, secCoord, Ideal.quotientMap_mk]
  · have hr : algebraMap (ParDVR e n v) (SecB e I v) r =
        Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (C r) := rfl
    rw [hr]
    simp only [φ, Ideal.quotientMap_mk, map_C]
    rfl
  let := φ.toAlgebra
  let : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsFractionRing (ParDVR e n v) (ParFrac K e n) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl _ _
  let : Algebra (MvPolynomial (Fin n) (ParDVR e n v)) (MvPolynomial (Fin n) (ParFrac K e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (ParDVR e n v)) (ParFrac K e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (ParFrac K e n)) (S' := SecAlg (idealF e I) (parYF K e n))
    (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (idealF e I) (parYF K e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  have hM : Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)) =
      M.map (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) := by
    ext x
    simp only [M, Algebra.algebraMapSubmonoid, Submonoid.mem_map, exists_exists_and_eq_and]
    exact Iff.rfl
  rw [hM]
  exact key

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecIdealOfPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def toSecB {K : Type*} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) : MvPolynomial (Fin n) (𝓞 K) →+* SecB e I v :=
  (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))).comp
    (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

def SecIdealOfPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      (secIdealOf e I v W).IsPrime ∧ (secIdealOf e I v W).comap (toSecB e I v) = W

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem NormFormLocalization.proof : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, map_X, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem isChowForm_C_mul {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := hc.isUnit.map C
  rw [hf.2 g, IsUnit.mul_left_dvd hu]

theorem specFirst_C_mul {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by
  simp [specFirst]

theorem Main.proof (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem gaussNormOf_rename {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _

theorem specFirst_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]

theorem gaussNorm_map_eq_one {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem GaussEq.proof (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG

end

end GroundTheory.Heights₂.Heights.Vertical
end
