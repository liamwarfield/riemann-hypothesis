module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiShStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem jT_eq_latDisc (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) :
    jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ :=
  (ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm

theorem pow_twelve_eq_DD (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) (Ω : ℂ)
    (hΩ : Ω ^ 12 = latDisc Λ) : (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ := by
  have hc : c ≠ 0 := h.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ :=
    ReciprocityTheory.ChartRestriction.L1.disc_eq h
  rw [div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]
  field_simp
  ring

theorem jT_eq_and_pow_twelve_eq_DD : ∀ (Λ : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf Λ c τ → jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ ∧ ∀ Ω : ℂ, Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ :=
  fun Λ c τ h => ⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPoint
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom → ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S) (g : Over.mk s ⟶ U), IsStalk O s ∧ ∃ v, g.left v = u := by
  first | (exact @GlobalTheory.EtC.exists_isStalk_over_point) | (exact GlobalTheory.EtC.exists_isStalk_over_point) | (intros; apply GlobalTheory.EtC.exists_isStalk_over_point  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem ker_app_eq_kerIdeal_of_idempotents (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (_h2 : v ≫ u = 0)
    (n : ℕ) : RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    let x := Ideal.Quotient.mkₐ k (kerIdeal (v.app n))
    have hv : ∀ c, x (v.app n c) = algebraMap k _ (counit c) :=
      (kerIdeal_le_ker_iff (v.app n) x).1 fun b hb => by
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hb
    let P := (ptsPush (G.A n) (x : G.A n →ₐ[k] _)).comp toPts
    have hP : P (Hom.conv v n) = 1 := WithConv.ofConv_injective (AlgHom.ext fun c => by
      change x (v.app n c) = _
      rw [hv]
      simp)
    have e : P (Hom.conv (u + v) n) = P (Hom.conv u n) := by
      rw [add_conv, map_mul, hP, mul_one]
    rw [huv] at e
    have e' := congrArg (fun y => y.ofConv a) e
    change x a = x (u.app n a) at e'
    rw [ha, map_zero] at e'
    exact Ideal.Quotient.eq_zero_iff_mem.1 e'
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f : G ⟶ G => Hom.app f n b) h1
    change u.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[k] G.A n)).ofConv b at e
    have hb' : counit (R := k) b = 0 := hb
    refine Eq.trans e ?_
    simp [hb']

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotentsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  first | exact @GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | exact GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | (intros; apply GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  have hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
    IsFractionRing.injective _ _
  have hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧
      WittVector.constantCoeff w = coeff α (u' i) := hu
  choose U hU using hu1
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply hinj
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
        WittVector.constantCoeff w = coeff α f' := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w) := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubstStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k), (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) → (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧ ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c → subst u f ∈ intBy p k τ c := by
  first | exact @GlobalTheory.Katz.red_subst | exact GlobalTheory.Katz.red_subst | (intros; apply GlobalTheory.Katz.red_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.IntAcyc

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def finDiag : Finset B ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin A (t : Set B))
  map {t u} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def finCocone : Cocone (finDiag A B) where
  pt := CommRingCat.of B
  ι := { app := fun t => CommRingCat.ofHom (Algebra.adjoin A (t : Set B)).val.toRingHom
         naturality := fun _ _ _ => by ext; rfl }

def finCoconeIsColimit : IsColimit (finCocone A B) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset B) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (finCocone A B)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    apply Subtype.ext
    exact h

theorem finite_finDiag [Algebra.IsIntegral A B] (t : Finset B) :
    Module.Finite A (Algebra.adjoin A (t : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

end GlobalTheory.EtC.IntAcyc
end

namespace GlobalTheory.EtC.IntAcyc

theorem acycF_of_isIntegral : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      SH A → AcycF R (sp B) F := by
  classical
  intro R _ F hF A B _ _ _ _ hA
  obtain ⟨hHens, hSep⟩ := hA
  intro n hn
  suffices h : ∀ x : H R (sp B) F n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF (Finset B) (finDiag A B) (finCocone A B)
    (finCoconeIsColimit A B) n).1 x
  haveI := finite_finDiag A B j
  obtain ⟨ι, hι, T, hT, hAl, e, hH, hS⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A (Algebra.adjoin A (j : Set B))
  have hac : AcycF R (sp ((finDiag A B).obj j)) F :=
    GlobalTheory.T.acycF_of_pi_sh' R F ι T ((finDiag A B).obj j) ⟨e.toRingEquiv⟩ (fun i => ⟨hH i, (hS i).1⟩)
  haveI := hac n hn
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [← hy, hy0]
  exact map_zero _

end GlobalTheory.EtC.IntAcyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_strictHenselian_acyclic_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], SH A → AcycF R (sp B) F := by
  first | (exact @GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (exact GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (intros; apply GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
open NumberField IsDedekindDomain

namespace GlobalTheory.TjCount

theorem Tj_complex_ne_zero_iff {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ)
    (g : GL (Fin n) L) : Formalism.UG.Tj ℂ n O ϖ j g ≠ 0 ↔ Formalism.UG.Tj ℤ n O ϖ j g ≠ 0 := by
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply_ne_zero, Set.indicator_apply_ne_zero]
  simp

theorem prod_le_pow (q n j : ℕ) (hq : 2 ≤ q) (hj : j ≤ n) :
    0 < ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ∧
    ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ≤ (q : ℤ) ^ (n * j) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hpos : ∀ i ∈ Finset.range j, (0 : ℤ) < (q : ℤ) ^ (n - i) - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : (1 : ℤ) < (q : ℤ) ^ (n - i) := one_lt_pow₀ hq1 (by omega)
    linarith
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1)
      ≤ ∏ _i ∈ Finset.range j, (q : ℤ) ^ n := by
        apply Finset.prod_le_prod₀ (fun i hi => (hpos i hi).le)
        intro i hi
        have : (q : ℤ) ^ (n - i) ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hq1.le (Nat.sub_le n i)
        linarith
    _ = (q : ℤ) ^ (n * j) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem one_le_prod (q j : ℕ) (hq : 2 ≤ q) : 1 ≤ ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : ∀ i ∈ Finset.range j, (1 : ℤ) ≤ (q : ℤ) ^ (i + 1) - 1 := by
    intro i _
    have : (q : ℤ) ≤ (q : ℤ) ^ (i + 1) := by
      calc (q : ℤ) = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ (i + 1) := pow_le_pow_right₀ hq1.le (by omega)
    linarith
  calc (1 : ℤ) = ∏ _i ∈ Finset.range j, (1 : ℤ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

end GlobalTheory.TjCount


open GlobalTheory.TjCount in
theorem GlobalTheory.TjCount.tj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  intro E _ _ w n ϖ hϖ j hj
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w n ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ j hj
  have hq : 2 ≤ Formalism.UG.qV E w := GlobalTheory.LFun.one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} =
      Nat.card {x : GL (Fin n) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ n (Formalism.UG.Ov E w) ϖ j x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Tj_complex_ne_zero_iff _ _ _ _ _)
  obtain ⟨hP, hB⟩ := prod_le_pow (Formalism.UG.qV E w) n j hq hj
  have hA := one_le_prod (Formalism.UG.qV E w) j hq
  rw [← hcard] at h
  set C := Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} with hC
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  have hle : (C : ℤ) ≤ (Formalism.UG.qV E w : ℤ) ^ (n * j) := by
    have : (C : ℤ) ≤ (C : ℤ) * ∏ i ∈ Finset.range j, ((Formalism.UG.qV E w : ℤ) ^ (i + 1) - 1) :=
      le_mul_of_one_le_right (by positivity) hA
    linarith
  refine ⟨?_, by exact_mod_cast hle⟩
  have : Finite {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} := Nat.finite_of_card_ne_zero hCpos.ne'
  exact Set.finite_coe_iff.mp (by exact this)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.SzSum

section

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_zero (r : ℝ) : Sz l lam r 0 := by
  refine ⟨zero_mem _, ?_⟩
  have : (⟨0, zero_mem _⟩ : algebraicClosure ℚ ℂ) = 0 := rfl
  rw [this, map_zero, norm_zero]
  positivity

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_sub {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x - y) := by
  rw [sub_eq_add_neg]
  exact sz_add hx (sz_neg hy)

theorem sz_mul {r s : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam s y) : Sz l lam (r + s) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r s : ℝ} {x : ℂ} (h : r ≤ s) (hx : Sz l lam r x) : Sz l lam s x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_int (n : ℤ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨intCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), intCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := Subtype.ext (by simp)
  rw [this, map_intCast, Real.rpow_zero]
  exact IsUltrametricDist.norm_intCast_le_one _ n

theorem sz_sum {κ : Type*} (t : Finset κ) {r : ℝ} {x : κ → ℂ} (h : ∀ k ∈ t, Sz l lam r (x k)) :
    Sz l lam r (∑ k ∈ t, x k) :=
  Finset.sum_induction x (Sz l lam r) (fun _ _ => sz_add) (sz_zero r) h

end

theorem sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) :=
  fun _ _ _ => ⟨sz_zero, fun _ _ _ hx hy => ⟨sz_add hx hy, sz_sub hx hy⟩, fun _ _ _ _ hx hy => sz_mul hx hy,
    fun _ _ _ h hx => sz_mono h hx, sz_int, fun _ t _ _ h => sz_sum t h⟩

end GlobalTheory.QFam.SzSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) := by
  first | exact @GlobalTheory.QFam.SzSum.sz_ring | exact GlobalTheory.QFam.SzSum.sz_ring | (intros; apply GlobalTheory.QFam.SzSum.sz_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditive
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.LowLaw

theorem eq_single_of_degree_eq_one {σ : Type} {e : σ →₀ ℕ} (h : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add (f := _), Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

theorem coeff_addLaw (R : Type) [CommRing R] (d : ℕ) (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) :
    coeff α (addLaw R d i) =
      if α = Finsupp.single (Sum.inl i) 1 ∨ α = Finsupp.single (Sum.inr i) 1 then 1 else 0 := by
  classical
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · have h2 : α ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h
      exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · rw [if_pos h2, if_pos (Or.inr h2)]
    · rw [if_neg h2, if_neg (by tauto)]

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_inl {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hu := congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)
  simp only [op, at2] at hu
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu
  simpa [coeff_X, Finsupp.single_left_inj] using hu

theorem coeff_inr {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hc := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)
  simp only [swap, at2] at hc
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc
  rw [← hc, ← coeff_inl h i j]
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.Katz.LowLaw

namespace GlobalTheory.Katz


open LowLaw in
theorem coeff_law_of_degree_le_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ)
    (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) (hα : α.degree ≤ 1) :
    coeff α (μ i) = coeff α (addLaw k d i) ∧
      coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  classical
  have h1 : coeff α (μ i) = coeff α (addLaw k d i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const,
        coeff_addLaw, if_neg]
      rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
    · obtain ⟨s, rfl⟩ := eq_single_of_degree_eq_one h1
      rcases s with j | j
      · rw [coeff_inl h, coeff_addLaw]; simp [Finsupp.single_left_inj]
      · rw [coeff_inr h, coeff_addLaw]; simp [Finsupp.single_left_inj]
  refine ⟨h1, ?_⟩
  rw [coeff_lift, h1, coeff_addLaw, coeff_addLaw]
  split_ifs <;> simp

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditiveStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_law_linear_coeff_additive : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw k d i) ∧ coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  first | exact @GlobalTheory.Katz.coeff_law_of_degree_le_one | exact GlobalTheory.Katz.coeff_law_of_degree_le_one | (intros; apply GlobalTheory.Katz.coeff_law_of_degree_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTail
namespace GlobalTheory.IntegralNormAtMostOne

theorem norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hcon
  have h1 : 1 < ‖y‖ := not_le.mp hcon
  have h0 : 0 < ‖y‖ := lt_trans one_pos h1
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, one_smul] at hpy
  have heq : y ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, p.coeff i • y ^ i :=
    eq_neg_of_add_eq_zero_right hpy
  have hlt : ∀ (s : Finset ℕ), (∀ i ∈ s, i < p.natDegree) →
      ‖∑ i ∈ s, p.coeff i • y ^ i‖ < ‖y‖ ^ p.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using pow_pos h0 _
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [zsmul_eq_mul, norm_mul, norm_pow]
        have hc : ‖((p.coeff a : ℤ) : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        calc ‖((p.coeff a : ℤ) : ℂ_[l])‖ * ‖y‖ ^ a ≤ 1 * ‖y‖ ^ a :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg h0.le _)
          _ = ‖y‖ ^ a := one_mul _
          _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ h1 (hs a (Finset.mem_insert_self _ _))
      · exact ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
  have := hlt (Finset.range p.natDegree) fun i hi => Finset.mem_range.mp hi
  rw [← norm_neg, ← heq, norm_pow] at this
  exact lt_irrefl _ this

end GlobalTheory.IntegralNormAtMostOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.SzRules

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem norm_natCast_eq (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_le_one_of_isIntegral {y : ℂ_[l]} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral ..)

theorem mem_of_natCast_mul {n : ℕ} (hn : n ≠ 0) {x : ℂ} (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have := div_mem h (natCast_mem (algebraicClosure ℚ ℂ) n)
  rwa [mul_div_cancel_left₀ _ hn'] at this

theorem norm_natCast_mul (n : ℕ) {x : ℂ} (hx : x ∈ algebraicClosure ℚ ℂ) (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    ‖lam ⟨(n : ℂ) * x, h⟩‖ = ‖(n : ℚ_[l])‖ * ‖lam ⟨x, hx⟩‖ := by
  have : (⟨(n : ℂ) * x, h⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) * ⟨x, hx⟩ := rfl
  rw [this, map_mul, map_natCast, norm_mul, norm_natCast_eq]

theorem sz_of_isIntegral (n : ℕ) (x : ℂ) (hn : ¬ l ∣ n) (h : IsIntegral ℤ ((n : ℂ) * x)) : Sz l lam 0 x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hm : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff'.2 h.tower_top
  have hx := mem_of_natCast_mul hn0 hm
  refine ⟨hx, ?_⟩
  have h1 : IsIntegral ℤ (⟨(n : ℂ) * x, hm⟩ : algebraicClosure ℚ ℂ) :=
    (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom Subtype.val_injective).1 h
  have h2 : ‖lam ⟨(n : ℂ) * x, hm⟩‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int lam h1; exact Subsingleton.elim _ _)
  have h3 : ‖(n : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn
  have h4 := norm_natCast_mul (lam := lam) n hx hm
  rw [h3, one_mul] at h4
  rw [Real.rpow_zero, ← h4]
  exact h2

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_prime_mul (r : ℝ) (x : ℂ) : Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  constructor
  · rintro ⟨h, h'⟩
    have hx := mem_of_natCast_mul hl.out.ne_zero h
    refine ⟨hx, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0] at h'
    rw [Real.rpow_add_one hl0.ne', mul_comm]
    exact h'
  · rintro ⟨hx, h'⟩
    have h : (l : ℂ) * x ∈ algebraicClosure ℚ ℂ := mul_mem (natCast_mem _ l) hx
    refine ⟨h, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0]
    rw [Real.rpow_add_one hl0.ne', mul_comm] at h'
    exact h'

theorem sz_of_sq {r : ℝ} {x : ℂ} (h : Sz l lam r (x ^ 2)) : Sz l lam (r / 2) x := by
  obtain ⟨h, h'⟩ := h
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hx : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 h))
  refine ⟨hx, ?_⟩
  have : (⟨x ^ 2, h⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ ^ 2 := rfl
  rw [this, map_pow, norm_pow] at h'
  have e : (l : ℝ) ^ r = ((l : ℝ) ^ (r / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add hl0]; congr 1; ring
  rw [e] at h'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) :=
  fun _ _ _ => ⟨sz_of_isIntegral, fun _ _ _ => sz_add, fun _ _ _ _ => sz_mul, fun _ _ _ => sz_mono, fun _ _ => sz_neg,
    sz_prime_mul, fun _ _ _ h e => e ▸ sz_of_sq h⟩

end GlobalTheory.SzRules
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) := by
  first | exact @GlobalTheory.SzRules.main | exact GlobalTheory.SzRules.main | (intros; apply GlobalTheory.SzRules.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersion
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {k : Type} [CommRing k]

def liftClosed {K G H : PDivGroup p k} (i : K ⟶ G) (hi : ∀ n : ℕ, Function.Surjective (i.app n))
    (f : H ⟶ G) (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) : H ⟶ K :=
  ⟨fun n => liftSurj (i.app n) (hi n) (f.app n) (hf n), fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi (n + 1) b
    change H.res n (liftSurj (i.app (n + 1)) (hi (n + 1)) (f.app (n + 1)) (hf (n + 1))
        (i.app (n + 1) a)) =
      liftSurj (i.app n) (hi n) (f.app n) (hf n) (K.res n (i.app (n + 1) a))
    rw [liftSurj_apply, res_app, res_app, liftSurj_apply]⟩

theorem liftClosed_comp {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (f : H ⟶ G)
    (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) :
    liftClosed i hi f hf ≫ i = f :=
  Hom.ext (funext fun n => BialgHom.ext fun a => liftSurj_apply (i.app n) (hi n) (f.app n) (hf n) a)

theorem cancel_closed {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (g g' : H ⟶ K) (h : g ≫ i = g' ≫ i) :
    g = g' :=
  Hom.ext (funext fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi n b
    have := DFunLike.congr_fun (congrArg (fun u : H ⟶ G => u.app n) h) a
    simpa using this)

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.factor_closedImmersion : ∀ (p : ℕ) (k : Type) [CommRing k] (K G : PDivGroup p k) (i : K ⟶ G), (∀ n : ℕ, Function.Surjective (i.app n)) → (∀ (H : PDivGroup p k) (f : H ⟶ G), (∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) → ∃ g : H ⟶ K, g ≫ i = f) ∧ ∀ (H : PDivGroup p k) (g g' : H ⟶ K), g ≫ i = g' ≫ i → g = g' :=
  fun _ _ _ _ _ i hi => ⟨fun _ f hf => ⟨liftClosed i hi f hf, liftClosed_comp i hi f hf⟩,
    fun _ g g' h => cancel_closed i hi g g' h⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.ColumnInclusionRenaming

theorem fockS_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockS (rename e f) (rename e g) = fockS f g := by
  classical
  unfold fockS
  rw [support_rename_of_injective he, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  congr 2
  unfold mfact
  rw [Finsupp.mapDomain_support_of_injective he, Finset.prod_image (fun _ _ _ _ h => he h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective he]

def colIncl {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (r : ℕ) : Fin r × Fin n₀ → Fin r × Fin n₁ :=
  fun v => (v.1, Fin.castLE h v.2)

theorem rename_lpMinor {n₀ n₁ r : ℕ} (h : n₀ ≤ n₁) (s : ℕ) (hr : s ≤ r) (hs : s ≤ n₀) :
    rename (colIncl h r) (lpMinor ℂ s hr hs) = lpMinor ℂ s hr (hs.trans h) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [colIncl]

theorem rename_hw {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) :
    rename (colIncl h n₁) (hw ℂ h ν) = hw ℂ (le_refl n₁) (rowNu (r := n₁) ν) := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < n₀ := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    have : rowNu (r := n₁) ν s = 0 := by simp [rowNu, hs']
    rw [this, Nat.zero_sub, pow_zero]
  · intro s _
    rw [map_pow, rename_lpMinor]
    have e1 : rowNu (r := n₁) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    have e2 : nuNext (rowNu (r := n₁) ν) (Fin.castLE h s) = nuNext ν s := by
      unfold nuNext rowNu
      by_cases h1 : s.val + 1 < n₀
      · have h2 : s.val + 1 < n₁ := by omega
        simp [h1, h2]
      · simp [h1]
    rw [e1, e2]
    rfl

end GlobalTheory.Proof.ColumnInclusionRenaming
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem morphisms_eq_spread_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [LocallyOfFiniteType q] (a b : X₀ ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → a ≫ q = f₀ → b ≫ q = f₀ → π ≫ a = π ≫ b → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → π₁ ≫ a = π₁ ≫ b := by
  intro S _ R₀ X X₀ Z f f₀ q π _ _ a b hp ha hb hab
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have hfst : pullback.fst f₀ (spMap (algebraMap R₀ S)) = hp'.isoPullback.inv ≫ π := by
    rw [hp'.isoPullback_inv_fst]
  obtain ⟨R', hR', ⟨s, rfl⟩, h⟩ := Spread.exists_fg_comp_eq_comp (A := S) f₀ q ⊥ Subalgebra.fg_bot
    (pullback.fst _ _ ≫ a) (pullback.fst _ _ ≫ b)
    (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
    (by rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc, hfst, Category.assoc, Category.assoc, hab])
  rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc] at h
  refine ⟨s, fun R₁ h₀ hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h₀ r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  have hm : m ≫ pullback.fst _ _ = π₁ := pullback.lift_fst _ _ _
  rw [← hm, Category.assoc, Category.assoc, h]

end GlobalTheory
end
