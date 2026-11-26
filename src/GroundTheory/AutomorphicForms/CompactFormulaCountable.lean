module

public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
public import GroundTheory.AutomorphicForms.TraceFormulaGeometric
public import GroundTheory.LocalFields.Unramified
public import GroundTheory.AutomorphicForms.WhittakerDistribution
public import GroundTheory.AutomorphicForms.WhittakerCriterion
public import GroundTheory.AutomorphicForms.HeckeIrreducible

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.CompactFormulaCountable
open NumberField IsDedekindDomain Topology Filter TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

variable (K : Type*) [Field K] [NumberField K]

instance secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  let O : Set (v.adicCompletion K) := v.adicCompletionIntegers K
  let U : K → Set (v.adicCompletion K) := fun a => {x | x - algebraMap K _ a ∈ O}
  have hO : IsOpen O := GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hU : ∀ a, IsOpen (U a) := fun a => hO.preimage (continuous_id.sub continuous_const)
  have hSC : ∀ a, SecondCountableTopology (U a) := fun a => by
    have : SecondCountableTopology O :=
      inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
    let φ : U a → O := fun x => ⟨x.1 - algebraMap K _ a, x.2⟩
    have he : IsEmbedding ((Subtype.val : O → v.adicCompletion K) ∘ φ) :=
      (Homeomorph.subRight (algebraMap K (v.adicCompletion K) a)).isEmbedding.comp
        IsEmbedding.subtypeVal
    exact ((IsEmbedding.subtypeVal.of_comp_iff).1 he).secondCountableTopology
  refine secondCountableTopology_of_countable_cover hU ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hV : IsOpen {y : v.adicCompletion K | x - y ∈ O} :=
    hO.preimage (continuous_const.sub continuous_id)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hV
    ⟨x, by simp [O, (v.adicCompletionIntegers K).zero_mem]⟩
  exact ⟨a, ha⟩

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  let R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K
  let A := fun v : HeightOneSpectrum (𝓞 K) =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hAo : ∀ v, IsOpen (A v) := fun v => GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) := fun S => by
    rw [le_principal_iff]
    exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (Πʳ v, [R v, A v]) :=
    fun S => Set.range (RestrictedProduct.inclusion R A (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS S)).isOpen_range
  have hSC : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 :
        SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    have hfin : {v | x.1 v ∉ A v}.Finite := x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    show ∀ᶠ v in 𝓟 ((hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))ᶜ), x.1 v ∈ A v
    rw [eventually_principal]
    intro v hv
    by_contra h
    exact hv (by simpa using h)
  show SecondCountableTopology (Πʳ v, [R v, A v])
  exact @secondCountableTopology_of_countable_cover _ _ _ _ _ hSC hUo hcov

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.AdelicUnitaryGroups
section -- merged from GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Restricted
set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct

noncomputable section

variable {K E : Type*} [Field K] [NumberField K] [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)


variable (K) in
def finiteAdeleEval (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Congr

variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

attribute [local instance] tensorTopology

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S := by
  let b := Module.finBasis K E
  let f := unitaryMap K E H e.toAlgHom
  let f' := unitaryMap K E H e.symm.toAlgHom
  have hrepr :
      (∀ z : R ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis S b).repr (tensorMap E e.toAlgHom z) k =
          e ((Algebra.TensorProduct.basis R b).repr z k)) ∧
      (∀ z : S ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis R b).repr (tensorMap E e.symm.toAlgHom z) k =
          e.symm ((Algebra.TensorProduct.basis S b).repr z k)) := by
    constructor <;> intro z k <;> induction z using TensorProduct.inductionOn with
    | tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hcoords :
      (∀ g p, unitaryCoords H S b (f g) p = e (unitaryCoords H R b g p)) ∧
      (∀ g p, unitaryCoords H R b (f' g) p = e.symm (unitaryCoords H S b g p)) := by
    exact ⟨fun g ⟨i, j, k⟩ => hrepr.1 (unitaryMat g i j) k,
      fun g ⟨i, j, k⟩ => hrepr.2 (unitaryMat g i j) k⟩
  have htensor :
      Continuous (tensorMap (E := E) e.toAlgHom) ∧
        Continuous (tensorMap (E := E) e.symm.toAlgHom) := by
    constructor
    · apply (tensorCoordsHomeomorph S b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he.comp ((continuous_apply k).comp (tensorCoordsHomeomorph R b).continuous)
      change Continuous (fun z => e (tensorCoordsHomeomorph R b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.1] using hk
    · apply (tensorCoordsHomeomorph R b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he'.comp ((continuous_apply k).comp (tensorCoordsHomeomorph S b).continuous)
      change Continuous (fun z => e.symm (tensorCoordsHomeomorph S b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.2] using hk
  refine
    { toFun := f
      invFun := f'
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul f
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro g
    apply unitaryCoords_injective H R b
    funext p
    rw [hcoords.2, hcoords.1, e.symm_apply_apply]
  · intro g
    apply unitaryCoords_injective H S b
    funext p
    rw [hcoords.1, hcoords.2, e.apply_symm_apply]
  · have hm : Continuous fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap E e.toAlgHom) :=
      continuous_id.matrix_map htensor.1
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f g : GL ι (S ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))
  · have hm : Continuous fun M : Matrix ι ι (S ⊗[K] E) => M.map (tensorMap E e.symm.toAlgHom) :=
      continuous_id.matrix_map htensor.2
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f' g : GL ι (R ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))

theorem unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap K E H e.toAlgHom g := rfl

end Congr

variable [NumberField K]

variable (K) in
def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl

variable (K) in
def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl

variable (K) in
def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable (K) in
def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in
def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.TraceFormulaWeil
open MeasureTheory Topology Filter Set Function
open scoped ENNReal NNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Unimodular

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]


omit [LocallyCompactSpace H] [T2Space H] in
theorem isFundamentalDomain_preimage_mul_right (L : Subgroup H) [DiscreteTopology L]
    (ν : Measure H) (g : H) :
    IsFundamentalDomain L ((· * g) ⁻¹' fundamentalDomain L) ν := by
  refine IsFundamentalDomain.mk' ((measurableSet_fundamentalDomain L).preimage
    (measurable_mul_const g)).nullMeasurableSet fun h => ?_
  obtain ⟨l, hl, hlu⟩ := existsUnique_smul_mem_fundamentalDomain L (h * g)
  refine ⟨l, ?_, fun l' hl' => hlu l' ?_⟩
  · show (l • h) * g ∈ fundamentalDomain L
    rw [smul_mul_assoc]
    exact hl
  · have hl'' : (l' • h) * g ∈ fundamentalDomain L := hl'
    rw [smul_mul_assoc] at hl''
    exact hl''

theorem isMulRightInvariant_of_compactSpace (L : Subgroup H) [DiscreteTopology L]
    [CompactSpace (RightCosetSpace L)] (ν : Measure H) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  constructor
  intro g
  have hD := isFundamentalDomain_fundamentalDomain L ν
  have h0 : ν (fundamentalDomain L) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have htop : ν (fundamentalDomain L) ≠ ∞ := by
    rw [← quotientMeasure_univ ν hD]
    exact measure_ne_top _ _
  set c : ℝ≥0 := Measure.haarScalarFactor (Measure.map (· * g) ν) ν
  have hc : Measure.map (· * g) ν = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map (· * g) ν (fundamentalDomain L) = ν (fundamentalDomain L) := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain L)]
    exact (isFundamentalDomain_preimage_mul_right L ν g).measure_eq hD
  have hc1 : c = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have : (c : ℝ≥0∞) * ν (fundamentalDomain L) = 1 * ν (fundamentalDomain L) := by
      rw [h2, one_mul]
    rwa [ENNReal.mul_left_inj h0 htop, ENNReal.coe_eq_one] at this
  rw [hc, hc1, one_smul]


omit [T2Space H] in
theorem inv_eq_self_of_isMulRightInvariant (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.inv = ν := by
  set c : ℝ≥0 := Measure.haarScalarFactor ν.inv ν
  have hc : ν.inv = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv ν) = (c ^ 2 : ℝ≥0) • ν := by
    rw [← Measure.inv_def ν, hc, Measure.map_smul, ← Measure.inv_def ν, hc, smul_smul, pow_two]
    exact continuous_inv.measurable.aemeasurable
  have hν : ν = (c ^ 2 : ℝ≥0) • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have h3 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ν K = 1 * ν K := by
    conv_rhs => rw [hν]
    simp
  have h4 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj ((isOpen_interior.measure_pos ν K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
      K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

end Unimodular

section Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]

end Weil

end RightCosetSpace

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.HermitianClassification
section -- merged from GroundTheory.AutomorphicForms.UnitarySplit
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable (F : Type*) [Field F]

variable {F}

section Split

variable (F) (R : Type*) [CommRing R] [Algebra F R]

noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))

variable {F R}



variable {ι : Type*} [Fintype ι] [DecidableEq ι]



variable (H : Matrix ι ι (F × F))






end Split

section SplitFunctor

open CategoryTheory

universe u

variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]

variable {F ι}

end SplitFunctor

end GroundTheory.Automorphic
end

noncomputable section

namespace GroundTheory.Automorphic

open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

theorem mem_or_mul_inv_mem_of_natCard_eq_two {G : Type*} [CommGroup G] {N : Subgroup G}
    (hN : Nat.card (G ⧸ N) = 2) {t : G} (ht : t ∉ N) (u : G) : u ∈ N ∨ u * t⁻¹ ∈ N := by
  by_contra H
  push Not at H
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).1 hN
  have h1 : (QuotientGroup.mk t : G ⧸ N) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk u : G ⧸ N) ≠ 1 := by rw [Ne, QuotientGroup.eq_one_iff]; exact H.1
  have h3 := QuotientGroup.eq.1 ((hy _ h1).trans (hy _ h2).symm)
  apply H.2
  rwa [mul_comm]

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem mem_range_normUnits_iff (u : Fˣ) :
    u ∈ (normUnits F E).range ↔ ∃ z : E, Algebra.norm F z = u := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (coe_normUnits w).symm⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [Algebra.norm_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [coe_normUnits, Units.val_mk0, hz])⟩

end General

section Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]

theorem natCard_quotient_range_normUnits_eq_two :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by
  obtain ⟨_, _, _, _⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F E
  rw [natCard_units_quotient_range_normUnits, Algebra.IsQuadraticExtension.finrank_eq_two]

namespace HermitianForm

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

end HermitianForm

end Local

end GroundTheory.Automorphic

end
end

section -- merged from GroundTheory.AutomorphicForms.WhittakerLocal
namespace GroundTheory.Automorphic

namespace Whittaker

open MeasureTheory Measure ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem biEquivariantSigmaInvariant_GL (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) :
    BiEquivariantSigmaInvariant (Iwasawa.unipotent F n)
      (fun u => psiN ψ₀ (u : GL (Fin n) F)) sigmaHomeo := by
  intro D hD f
  have key := distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by
    have e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f :=
      Subtype.ext (coe_biTranslL u₁ u₂ f).symm
    rw [e]
    exact hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f
  have e : compHomeoL sigmaHomeo f =
      (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) := Subtype.ext rfl
  rw [e]
  exact key

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul

theorem map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by
  have hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := continuous_theta
  have hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F) := hθc.measurable
  have : (μ.map theta).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc
  set c := haarScalarFactor (μ.map theta) μ
  have e : μ.map theta = c • μ := isMulLeftInvariant_eq_smul (μ.map theta) μ
  have e2 : μ = (c * c) • μ := by
    have h1 : (μ.map theta).map theta = μ := by
      rw [Measure.map_map hθm hθm]
      have : (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id := funext theta_theta
      rw [this, Measure.map_id]
    have h2 : (μ.map theta).map theta = (c * c) • μ := by
      rw [e, Measure.map_smul, e, smul_smul]
      exact hθm.aemeasurable
    exact h1.symm.trans h2
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have hc : c = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h' := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    have hcc : (c * c : NNReal) = 1 := by exact_mod_cast h'
    have hr : ((c : ℝ) * (c : ℝ)) = 1 := by exact_mod_cast hcc
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have eθ : μ.map theta = μ := by rw [e, hc, one_smul]
  have hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta := by
    funext g
    simp [theta]
  rw [hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]
  exact Measures.inv_eq_self_GL F n μ

end Measure

theorem rank_whittaker_le_one_of_contragredient (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne

end Whittaker

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.SphericalCommutative
noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Measure Matrix GLnLocal HeckeAlgebra

namespace Spherical

variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

def transposeInv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  invFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

variable {F n}

@[simp]
theorem coe_transposeInv (g : GL (Fin n) F) :
    ((transposeInv F n g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

@[simp]
theorem coe_inv_transposeInv (g : GL (Fin n) F) :
    (((transposeInv F n g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

theorem transposeInv_transposeInv (g : GL (Fin n) F) : transposeInv F n (transposeInv F n g) = g :=
  (transposeInv F n).left_inv g

theorem transposeInv_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    transposeInv F n k ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hk ⊢
  exact ⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩

theorem transposeInv_mem_integralGL_iff {k : GL (Fin n) F} :
    transposeInv F n k ∈ integralGL F n ↔ k ∈ integralGL F n :=
  ⟨fun h => by simpa [transposeInv_transposeInv] using transposeInv_mem_integralGL h,
    transposeInv_mem_integralGL⟩

theorem inv_transposeInv_diagPow [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (l : Fin n → ℤ) : (transposeInv F n (Cartan.diagPow F n l))⁻¹ = Cartan.diagPow F n l := by
  ext i j
  rw [coe_inv_transposeInv, Cartan.coe_diagPow, diagonal_transpose]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_transposeInv : Continuous (transposeInv F n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin n) F => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact Units.continuous_val.matrix_transpose

def transposeInvHomeomorph : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toEquiv := (transposeInv F n).toEquiv
  continuous_toFun := continuous_transposeInv
  continuous_invFun := continuous_transposeInv

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

theorem map_transposeInv : μ.map (transposeInv F n) = μ := by
  have hH : (μ.map (transposeInv F n)).IsHaarMeasure :=
    (transposeInv F n).isHaarMeasure_map μ continuous_transposeInv
      (transposeInvHomeomorph (F := F) (n := n)).continuous_invFun
  set K := integralGL F n
  have hK0 : μ K ≠ 0 := (isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul (μ.map (transposeInv F n)) μ
  have hpre : transposeInv F n ⁻¹' (K : Set (GL (Fin n) F)) = K := by
    ext x
    exact transposeInv_mem_integralGL_iff
  have hK : μ.map (transposeInv F n) K = μ K := by
    rw [map_apply continuous_transposeInv.measurable (isOpen_integralGL F n).measurableSet, hpre]
  have hc : haarScalarFactor (μ.map (transposeInv F n)) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hK] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]

theorem integral_comp_transposeInv (f : GL (Fin n) F → ℂ) :
    ∫ g, f (transposeInv F n g) ∂μ = ∫ g, f g ∂μ := by
  have := integral_map_equiv (μ := μ) (transposeInvHomeomorph (F := F) (n := n)).toMeasurableEquiv f
  change ∫ g, f g ∂(μ.map (transposeInv F n)) = _ at this
  rw [map_transposeInv] at this
  exact this.symm

theorem apply_inv_transposeInv {f : GL (Fin n) F → ℂ}
    (hf : ∀ k ∈ integralGL F n, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) (g : GL (Fin n) F) :
    f (transposeInv F n g)⁻¹ = f g := by
  obtain ⟨l, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have : (transposeInv F n (k₁ * Cartan.diagPow F n l * k₂))⁻¹ =
      (transposeInv F n k₂)⁻¹ * Cartan.diagPow F n l * (transposeInv F n k₁)⁻¹ := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_transposeInv_diagPow, mul_assoc]
  have h₁ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₁)
  have h₂ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₂)
  rw [this, (hf _ h₁ _).2, (hf _ h₂ _).1, (hf _ hk₂ _).2, (hf _ hk₁ _).1]

variable {μ}

theorem heckeAlgebraLevel_mul_comm
    (a b : HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) : a * b = b * a := by
  have ha := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) a
  have hb := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) b
  have hab := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) (a * b)
  refine HeckeAlgebraLevel.ext (isCompact_integralGL F n) (isOpen_integralGL F n)
    (HeckeAlgebra.ext fun x => ?_)
  rw [HeckeAlgebraLevel.val_mul, HeckeAlgebraLevel.val_mul]
  rw [HeckeAlgebra.mul_apply (b : HeckeAlgebra μ)]
  set c := (transposeInv F n x)⁻¹
  have step1 : ∫ y, (b : HeckeAlgebra μ) y * (a : HeckeAlgebra μ) (y⁻¹ * x) ∂μ =
      ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e1 := apply_inv_transposeInv hb y
    have e2 := apply_inv_transposeInv ha (y⁻¹ * x)
    have hyx : (transposeInv F n (y⁻¹ * x))⁻¹ = c * transposeInv F n y := by
      rw [map_mul, map_inv (transposeInv F n), _root_.mul_inv_rev, inv_inv]
    show _ * _ = _ * _
    rw [← e1, ← e2, hyx]
  have step2 : ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ =
      ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ :=
    integral_comp_transposeInv μ (fun w => (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w))
  have step3 : ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ =
      ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) c := by
    have key := integral_mul_left_eq_self (μ := μ)
      (fun y => (a : HeckeAlgebra μ) y * (b : HeckeAlgebra μ) (y⁻¹ * c)) c
    rw [HeckeAlgebra.mul_apply, ← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
    ring
  rw [step1, step2, step3]
  have := apply_inv_transposeInv hab x
  rw [HeckeAlgebraLevel.val_mul] at this
  exact this.symm

instance instCommRing :
    CommRing (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) :=
  { (inferInstance : Ring (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n))) with
    mul_comm := heckeAlgebraLevel_mul_comm }

end Spherical

namespace HeckeAlgebra.HeckeAlgebraLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

instance : IsScalarTower ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_assoc c a b := ext hKc hKo (by
    change ((c • a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) * (b : HeckeAlgebra μ) =
      c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ))
    rw [val_smul, smul_mul_assoc])

instance : SMulCommClass ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_comm c a b := ext hKc hKo (by
    change c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) =
      (a : HeckeAlgebra μ) * ((c • b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ)
    rw [val_smul, mul_smul_comm])

instance instAlgebra : Algebra ℂ (HeckeAlgebraLevel μ K hKc hKo) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => (mul_smul_comm c a b))

end HeckeAlgebra.HeckeAlgebraLevel

end GroundTheory.Automorphic
end
end
