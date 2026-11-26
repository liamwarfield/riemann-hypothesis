module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOneStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOneOfGoingDownZariski
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOneOfGoingDownZariski
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.ZariskiDescent

theorem dvr_dvd_pow_of_mem_maximalIdeal {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] (x y : V) (hx : x ∈ IsLocalRing.maximalIdeal V) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨n, ⟨z ^ n * ↑u⁻¹, ?_⟩⟩
  rw [hu, mul_pow]
  have : (↑u * ↑u⁻¹ : V) = 1 := Units.mul_inv u
  linear_combination (-(z ^ n * ϖ ^ n)) * this

theorem mem_of_nonunits_of_localization {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] {A : Type} [CommRing A] (ι : A →+* L) (hι : Function.Injective ι)
    (hV : ∀ a, ι a ∈ V)
    (hloc : ∀ s ∈ V, ∃ b d : A, ι d ≠ 0 ∧ (ι d)⁻¹ ∈ V ∧ s = ι b / ι d)
    (P₁ : Ideal A) [P₁.IsPrime] (hne : P₁ ≠ ⊥) (hP₁ : ∀ z ∈ P₁, ι z ∈ V.nonunits) :
    ∀ x, ι x ∈ V.nonunits → x ∈ P₁ := by
  intro x hx
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hyV : (⟨ι y, hV y⟩ : V) ≠ 0 := by
    intro h
    apply hy0
    apply hι
    simpa using congrArg Subtype.val h
  have hxV : (⟨ι x, hV x⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp hx
  obtain ⟨n, w, hw⟩ := dvr_dvd_pow_of_mem_maximalIdeal V _ _ hxV hyV
  obtain ⟨b, d, hd0, hdinv, hwbd⟩ := hloc (w : L) w.2
  have hL : ι x ^ n = ι y * (ι b / ι d) := by
    have := congrArg Subtype.val hw
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul] at this
    rw [this, ← hwbd]
    rfl
  have hA : x ^ n * d = y * b := by
    apply hι
    rw [map_mul, map_mul, map_pow, hL]
    field_simp
  have hmem : x ^ n * d ∈ P₁ := by
    rw [hA]; exact P₁.mul_mem_right b hyP
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› n h
  · exfalso
    have := (ValuationSubring.mem_nonunits_iff_or (A := V)).mp (hP₁ d h)
    rcases this with h1 | h1
    · exact hd0 h1
    · exact h1 hdinv

end GlobalTheory.ZariskiDescent

namespace GlobalTheory.ZariskiDescent

theorem comap_nonunits_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L)
    (x : K) : x ∈ (V.comap φ).nonunits ↔ φ x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem height_le_one_of_going_down :
    ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L)
      [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) →
      R ≤ (V.comap φ).toSubring → ∀ t : Finset L,
      (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) →
      (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t),
        ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) →
      ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) →
      ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := by
  intro K L _ _ φ c V _ R _ hc hRV t ht hloc p hp hp0 hpq
  letI : Algebra R L := (φ.comp R.subtype).toAlgebra
  have halg : ∀ r : R, algebraMap R L r = φ r := fun r => rfl
  set S : Subalgebra R L := Algebra.adjoin R (t : Set L) with hSdef
  have hinjRL : Function.Injective (algebraMap R L) := by
    intro a b h
    rw [halg, halg] at h
    exact Subtype.ext (φ.injective h)
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjRL
    have := congrArg Subtype.val h
    simpa using this
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin (fun x hx => by
    obtain ⟨-, q, hq, hqx⟩ := ht x hx
    exact ⟨q, hq, hqx⟩)
  haveI : Algebra.HasGoingDown R S := inferInstance

  have hSV : ∀ z ∈ S, z ∈ V := by
    intro z hz
    have hz' : z ∈ S.toSubring := hz
    rw [hSdef, Algebra.adjoin_eq_ring_closure] at hz'
    refine (Subring.closure_le (t := V.toSubring)).mpr ?_ hz'
    rintro w (⟨r, rfl⟩ | hw)
    · exact (ValuationSubring.mem_comap).mp (hRV r.2)
    · exact (ht w hw).1

  have hclS : Subring.closure (Set.range (φ.comp c) ∪ ↑t) ≤ S.toSubring := by
    rw [Subring.closure_le]
    rintro w (⟨a, rfl⟩ | hw)
    · have : (φ.comp c) a = algebraMap R L ⟨c a, hc a⟩ := rfl
      rw [this]
      exact S.algebraMap_mem _
    · exact Algebra.subset_adjoin hw
  let ι : S →+* L := algebraMap S L
  have hι : Function.Injective ι := Subtype.val_injective
  let f : S →+* V := ι.codRestrict V (fun z => hSV z.1 z.2)
  let P : Ideal S := Ideal.comap f (IsLocalRing.maximalIdeal V)
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hPmem : ∀ z : S, z ∈ P ↔ (z : L) ∈ V.nonunits := by
    intro z
    show f z ∈ IsLocalRing.maximalIdeal V ↔ _
    exact ValuationSubring.coe_mem_nonunits_iff.symm
  let q : Ideal R := P.comap (algebraMap R S)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver q := ⟨rfl⟩
  have hqmem : ∀ r : R, r ∈ q ↔ (r : K) ∈ (V.comap φ).nonunits := by
    intro r
    show algebraMap R S r ∈ P ↔ _
    rw [hPmem, comap_nonunits_iff]
    rfl
  have hpq' : p ≤ q := fun r hr => (hqmem r).mpr (hpq r hr)
  obtain ⟨P₁, hP₁P, hP₁, hP₁o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) P hpq'
  have hpover : p = P₁.comap (algebraMap R S) := hP₁o.over
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    apply hp0
    rw [hpover, h, eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    apply hinjRL
    have := congrArg Subtype.val hr
    simpa using this
  have key := mem_of_nonunits_of_localization V ι hι (fun a => hSV a.1 a.2)
    (by
      intro s hs
      obtain ⟨b, hb, d, hd, hd0, hdinv, rfl⟩ := hloc s hs
      exact ⟨⟨b, hclS hb⟩, ⟨d, hclS hd⟩, hd0, hdinv, rfl⟩)
    P₁ hP₁ne (fun z hz => (hPmem z).mp (hP₁P hz))
  intro r hr
  rw [hpover, Ideal.mem_comap]
  apply key
  exact (hPmem _).mp ((hqmem r).mpr hr)

end GlobalTheory.ZariskiDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOneOfGoingDownZariskiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_le_one_of_goingDown_zariski : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L) [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) → R ≤ (V.comap φ).toSubring → ∀ t : Finset L, (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) → ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := by
  first | exact @GlobalTheory.ZariskiDescent.height_le_one_of_going_down | exact GlobalTheory.ZariskiDescent.height_le_one_of_going_down | (intros; apply GlobalTheory.ZariskiDescent.height_le_one_of_going_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubringStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisation
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem zariski_descent_heart : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hA : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring
  have hB : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L) [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) → R ≤ (V.comap φ).toSubring → ∀ t : Finset L, (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) → ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := GlobalTheory.T.height_le_one_of_goingDown_zariski
  have hC : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) → ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) → ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := GlobalTheory.T.exists_div_of_center_height_le_one'
  have hD : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := GlobalTheory.T.essFiniteType_of_localization_finiteType_complex
  intro K L _ _ φ c hfin V _ hc t ht htV
  obtain ⟨R, hcR, hft, hRE, hnoeth, hic, hfr, htR⟩ := hA K L φ c hfin V hc t ht htV
  have hB' := hB K L φ c V R hcR hRE t (fun x hx => ⟨(ht x hx).1, htR x hx⟩) htV
  have hC' := hC K R (V.comap φ) hRE hB'
  exact hD K c R hcR (V.comap φ) hc hRE hft hC'
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zariski_descent_dvr_trace_localisation : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.zariski_descent_heart | exact GlobalTheory.zariski_descent_heart | (intros; apply GlobalTheory.zariski_descent_heart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.valuationSubring_fractions_of_essFiniteType | exact GlobalTheory.valuationSubring_fractions_of_essFiniteType | (intros; apply GlobalTheory.valuationSubring_fractions_of_essFiniteType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGenerators
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGeneratorsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractions_unitDenominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.fractions_unit_denominators_replace_generators | exact GlobalTheory.fractions_unit_denominators_replace_generators | (intros; apply GlobalTheory.fractions_unit_denominators_replace_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComap
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

theorem GlobalTheory.dvr_eq_localization_integralClosure : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro K L _ _ _ φ hfin V _ hE s hs
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hfin
  set E : ValuationSubring K := V.comap φ with hEdef
  letI : Algebra E L := (φ.comp E.subtype).toAlgebra
  haveI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsFractionRing E K := inferInstance
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure E L) := integralClosure.isDedekindDomain E K L
  haveI : IsFractionRing (integralClosure E L) L := integralClosure.isFractionRing_of_finite_extension K L

  have hBV : ∀ x : L, IsIntegral E x → x ∈ V := by
    intro x hx
    letI : Algebra E V := ((φ.comp E.subtype).codRestrict V (fun y => y.2)).toAlgebra
    haveI : IsScalarTower E V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h2 : IsIntegral V x := IsIntegral.tower_top hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]; exact y.2

  have hpoly : ∀ x : L, IsIntegral E x →
      ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 := by
    rintro x ⟨p, hpm, hp⟩
    refine ⟨p.map E.subtype, hpm.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff i).2
    · rw [Polynomial.eval₂_map]; exact hp
  set B := integralClosure E L
  let f : B →+* V :=
    { toFun := fun b => ⟨(b : L), hBV _ b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  haveI hnp : n.IsPrime := Ideal.comap_isPrime _ _

  have hn0 : n ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    intro hbot
    have hmem : algebraMap E B ϖ ∈ n := by
      show f (algebraMap E B ϖ) ∈ IsLocalRing.maximalIdeal V
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hϖ.not_isUnit
      have h1 : ((u⁻¹ : Vˣ) : V) * f (algebraMap E B ϖ) = 1 := by rw [← hu]; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V) : L)) * φ ϖ = 1 := congrArg Subtype.val h1
      have h3 : (ϖ : K)⁻¹ ∈ E := by
        show φ ((ϖ : K)⁻¹) ∈ V
        rw [map_inv₀, inv_eq_of_mul_eq_one_left h2]; exact (((u⁻¹ : Vˣ) : V)).2
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h3⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩
    rw [hbot, Ideal.mem_bot] at hmem
    have h4 : φ (ϖ : K) = 0 := congrArg (fun b : B => (b : L)) hmem
    exact hϖ0 ((map_eq_zero φ).1 h4)
  have hunit : ∀ d : B, d ∉ n → (d : L) ≠ 0 ∧ (d : L)⁻¹ ∈ V := by
    intro d hd
    have hu : IsUnit (f d) := by
      by_contra h
      exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu
    have h1 : f d * ((u⁻¹ : Vˣ) : V) = 1 := by rw [← hu]; exact u.mul_inv
    have h2 : (d : L) * ((((u⁻¹ : Vˣ) : V) : L)) = 1 := congrArg Subtype.val h1
    refine ⟨left_ne_zero_of_mul_eq_one h2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h2]; exact (((u⁻¹ : Vˣ) : V)).2
  let O := Localization.AtPrime n
  letI : Algebra O L := IsLocalization.localizationAlgebraOfSubmonoidLe O L n.primeCompl
    (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsScalarTower B O L := IsLocalization.localization_isScalarTower_of_submonoid_le O L
    n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsFractionRing O L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization n.primeCompl O L
  haveI : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 O
  have hO : ∀ z : O, ∃ b d : B, d ∉ n ∧ algebraMap O L z * (d : L) = (b : L) := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl z
    refine ⟨a, t, t.2, ?_⟩
    show algebraMap O L (IsLocalization.mk' O a t) * algebraMap B L t = algebraMap B L a
    rw [IsScalarTower.algebraMap_apply B O L (t : B), IsScalarTower.algebraMap_apply B O L a,
      ← map_mul, IsLocalization.mk'_spec]
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ⟨hBV _ isIntegral_zero, hpoly _ isIntegral_zero⟩,
      ⟨hBV _ isIntegral_one, hpoly _ isIntegral_one⟩, one_ne_zero, by rw [inv_one]; exact V.one_mem, ?_⟩
    rw [hs0, zero_div]
  rcases ValuationRing.isInteger_or_isInteger O s with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    refine ⟨b, d, ⟨hBV _ b.2, hpoly _ b.2⟩, ⟨hBV _ d.2, hpoly _ d.2⟩, (hunit d hd).1,
      (hunit d hd).2, ?_⟩
    rw [← hz, ← hbd, mul_div_cancel_right₀ _ (hunit d hd).1]
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    rw [hz] at hbd
    have hsb : s * (b : L) = d := by rw [← hbd, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hb : b ∉ n := by
      intro hb
      have hb' : ¬ IsUnit (f b) := (IsLocalRing.mem_maximalIdeal _).1 hb
      have hfd : IsUnit (f d) := by
        by_contra h
        exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
      have hm : (⟨s, hs⟩ : V) * f b = f d := Subtype.ext hsb
      rw [← hm] at hfd
      exact hb' (isUnit_of_mul_isUnit_right hfd)
    refine ⟨d, b, ⟨hBV _ d.2, hpoly _ d.2⟩, ⟨hBV _ b.2, hpoly _ b.2⟩, (hunit b hb).1,
      (hunit b hb).2, ?_⟩
    rw [eq_div_iff (hunit b hb).1, hsb]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComapStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_eq_localization_integralClosure_comap : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.dvr_eq_localization_integralClosure | exact GlobalTheory.dvr_eq_localization_integralClosure | (intros; apply GlobalTheory.dvr_eq_localization_integralClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensional
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.RestrictDVR

theorem isDiscreteValuationRing_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (hfin : (letI := φ.toAlgebra; FiniteDimensional K L))
    (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap φ) := by
  letI := φ.toAlgebra
  set E := V.comap φ with hE
  have memE : ∀ x : K, x ∈ E ↔ φ x ∈ V := fun x => ValuationSubring.mem_comap
  let g : E →+* V := (φ.comp E.subtype).codRestrict V (fun x => (memE x).1 x.2)
  have hg : ∀ x : E, ((g x : V) : L) = φ x := fun x => rfl

  have hpid : IsPrincipalIdealRing E := by
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · subst hI; exact bot_isPrincipal
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : E → ℕ∞ := fun y => IsDiscreteValuationRing.addVal V (g y)
    let s : Set E := {y | y ∈ I ∧ y ≠ 0}
    have hs : x ∈ s := ⟨hxI, hx0⟩
    set x0 := Function.argminOn f s ⟨x, hs⟩ with hx0def
    have hx0s : x0 ∈ s := Function.argminOn_mem f s ⟨x, hs⟩
    refine ⟨x0, le_antisymm ?_ ?_⟩
    · intro y hy
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      have hle : f x0 ≤ f y := Function.argminOn_le f s ⟨hy, hy0⟩
      obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hle
      have hx0K : (x0 : K) ≠ 0 := fun h => hx0s.2 (Subtype.ext h)
      have hφx0 : φ x0 ≠ 0 := (map_ne_zero φ).2 hx0K
      have hcL : φ ((y : K) / x0) = (c : L) := by
        have := congrArg Subtype.val hc
        simp only [hg, MulMemClass.coe_mul] at this
        rw [map_div₀, this]; field_simp
      refine ⟨⟨(y : K) / x0, (memE _).2 (hcL ▸ c.2)⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul]
      field_simp
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact hx0s.1

  have hnf : IsLocalRing.maximalIdeal E ≠ ⊥ := by
    intro hbot
    have hall : ∀ x : K, φ x ∈ V := by
      intro x
      rcases E.mem_or_inv_mem x with h | h
      · exact (memE x).1 h
      by_cases hx : x = 0
      · simp [hx]
      have hu : IsUnit (⟨x⁻¹, h⟩ : E) := by
        by_contra hnu
        have : (⟨x⁻¹, h⟩ : E) ∈ IsLocalRing.maximalIdeal E := hnu
        rw [hbot, Ideal.mem_bot] at this
        exact inv_ne_zero hx (congrArg Subtype.val this)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have : x = (u : K) := by
        have h1 := congrArg Subtype.val hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
        field_simp at h1; exact h1.symm
      rw [this]; exact (memE _).1 u.2
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    let ψ : K →+* V := φ.codRestrict V hall
    have hint : IsIntegral K ((π : L)⁻¹) := Algebra.IsIntegral.isIntegral _
    obtain ⟨p, hpm, hp⟩ := hint
    have hintV : IsIntegral V ((π : L)⁻¹) := by
      refine ⟨p.map ψ, hpm.map ψ, ?_⟩
      have hcomp : (algebraMap V L).comp ψ = algebraMap K L := by ext; rfl
      rw [Polynomial.eval₂_map, hcomp]
      exact hp
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hintV
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one y (Subtype.ext ?_)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    have : (y : L) = (π : L)⁻¹ := hy
    rw [this, mul_inv_cancel₀ hπ0]
  exact { hpid with not_a_field' := hnf }

theorem main : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  intro K L _ _ φ hfin V _
  exact isDiscreteValuationRing_comap K L φ hfin V

end GlobalTheory.RestrictDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensionalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  first | exact @GlobalTheory.RestrictDVR.main | exact GlobalTheory.RestrictDVR.main | (intros; apply GlobalTheory.RestrictDVR.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem restrict_dvr_essFiniteType : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hL0 := GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex
  have hL1 := GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional
  have hL2 := GlobalTheory.T.dvr_eq_localization_integralClosure_comap
  have hL4 := GlobalTheory.T.fractions_unitDenominators_replace_generators
  have hL3 := GlobalTheory.T.zariski_descent_dvr_trace_localisation
  intro K L _ _ φ c hfin V _ hc hV
  have hE : IsDiscreteValuationRing (V.comap φ) := hL1 K L φ hfin V
  haveI : CharZero K := RingHom.charZero_iff c.injective |>.mp inferInstance
  obtain ⟨s₀, hs₀V, hs₀⟩ := hL0 L (φ.comp c) V hc hV
  obtain ⟨t, ht, htV⟩ := hL4 L (φ.comp c) V
    (fun x => x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) s₀
    (fun x hx => hL2 K L φ hfin V hE x (hs₀V x hx)) hs₀
  exact ⟨hE, hL3 K L φ c hfin V hc t ht htV⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.restrict_dvr_essFiniteType | exact GlobalTheory.restrict_dvr_essFiniteType | (intros; apply GlobalTheory.restrict_dvr_essFiniteType <;> assumption)
end
