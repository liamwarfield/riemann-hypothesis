module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

namespace GlobalTheory.LatDecomp

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem finiteAdeleMap_algebraMap (a : K) :
    finiteAdeleMap K E (algebraMap K (Af K) a) = algebraMap E (Af E) (algebraMap K E a) :=
  FiniteAdeleRing.ext _ fun w => finiteCompletionMap_coe K E w a

theorem finiteAdeleMap_integral {z : Af K} (hz : ∀ v, Valued.v (z v) ≤ 1) (w : HeightOneSpectrum (𝓞 E)) :
    (finiteAdeleMap K E z) w ∈ w.adicCompletionIntegers E :=
  finiteCompletionMap_mapsTo K E w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz _))

theorem algebraMap_integral (s : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (s : E)) w ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one s

theorem exists_nat_mul_integral (a : Af E) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ w, ((d : Af E) * a) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨β, hβ0, hβ⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hmem : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : 𝓞 E) ∈ Ideal.span {β} := Ideal.absNorm_mem _
  obtain ⟨g0, hg0⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨Ideal.absNorm (Ideal.span {β}), ?_, fun w => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Af E) =
        algebraMap E (Af E) ((g0 : 𝓞 E) : E) * algebraMap E (Af E) (algebraMap (𝓞 E) E β) := by
      rw [← map_mul]
      have := congrArg (fun r : 𝓞 E => algebraMap E (Af E) (r : E)) hg0
      simp only [map_natCast] at this
      rw [← this]; push_cast; rfl
    rw [e, _root_.mul_assoc]
    exact mul_mem (algebraMap_integral g0 w) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hβ w))

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_good {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) (e : E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z : Af E, (∀ w, z w ∈ w.adicCompletionIntegers E) →
      z * algebraMap E (Af E) ((N : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E))
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm c * d, Nat.mul_ne_zero hN hd0, fun z hz => ?_⟩
  have h := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c)
    (y := z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) (fun w => mul_mem (hz w) (hd w))
  have e1 : z * algebraMap E (Af E) (((Ideal.absNorm c * d : ℕ) : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) =
      algebraMap E (Af E) (algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E)) *
        (z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e1]; exact h

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

theorem exists_decomp : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E,
    ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
    ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧
      x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧
      ∀ k (v : HeightOneSpectrum (𝓞 K)),
        Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := by
  intro K _ _ E _ _ _ _ t c y hc x x' hx
  haveI : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  set B := Module.finBasis K E
  set yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E)
  choose N hN0 hN using fun k => exists_nat_mul_good hc y (B k)
  set b : Fin (Module.finrank K E) → E := fun k => (N k : E) * B k with hb
  set a' : Fin (Module.finrank K E) → K := fun k => B.repr x' k / (N k : K) with ha'
  have hNK : ∀ k, (N k : K) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hN0 k)

  have happrox : ∀ z : Af K, ∃ a : K, ∀ v, Valued.v ((z - algebraMap K (Af K) a) v) ≤ 1 := fun z => by
    obtain ⟨a, u, hu, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K 1 one_pos).1 z
    refine ⟨a, fun v => ?_⟩
    rw [e, one_smul, add_sub_cancel_left]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
  choose a ha using fun k => happrox ((t : Af K) * algebraMap K (Af K) (a' k))
  have hx' : x' = ∑ k, algebraMap K E (a' k) * b k := by
    conv_lhs => rw [← B.sum_repr x']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, hb, ha']
    simp only
    rw [← _root_.mul_assoc, ← map_natCast (algebraMap K E), ← map_mul, div_mul_cancel₀ _ (hNK k)]
  refine ⟨Module.finrank K E, b, a, a', fun k r => ?_, hx', ?_, ha⟩
  ·
    have hr : IsIntegral ℤ (algebraMap K E (r : K)) := (RingOfIntegers.isIntegral_coe r).algebraMap
    have h := hN k (algebraMap E (Af E) ((⟨algebraMap K E (r : K), hr⟩ : 𝓞 E) : E))
      (algebraMap_integral ⟨algebraMap K E (r : K), hr⟩)
    rw [mem_lattice, map_mul]
    exact h
  ·
    have hT : (upIdele K E t : Af E) = finiteAdeleMap K E (t : Af K) := rfl
    have hkey : algebraMap E (Af E) (x - ∑ k, algebraMap K E (a k) * b k) * yi =
        -(((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * yi) +
          ∑ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi := by
      have e2 : ∀ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi =
          finiteAdeleMap K E (t : Af K) * (algebraMap E (Af E) (algebraMap K E (a' k) * b k)) * yi -
            algebraMap E (Af E) (algebraMap K E (a k) * b k) * yi := fun k => by
        simp only [map_sub, map_mul, finiteAdeleMap_algebraMap]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum, ← map_sum, ← map_sum, ← hx', hT, map_sub]
      ring
    rw [mem_lattice, hkey]
    refine add_mem (neg_mem hx) (Subring.sum_mem _ fun k _ => ?_)
    exact hN k _ (finiteAdeleMap_integral (ha k))

end GlobalTheory.LatDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint
noncomputable section

namespace GlobalTheory.GeomTrait

section Algebra

open IsLocalRing

theorem dimensionLEOne_of_forall_mem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf : f ≠ 0) (h : ∀ q : Ideal R, q.IsPrime → q ≠ ⊥ → f ∈ q) : Ring.DimensionLEOne R := by
  classical
  refine ⟨fun {q} hq0 hq => ?_⟩
  by_contra hqm
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})
  have hle : q ≤ maximalIdeal R := le_maximalIdeal hq.ne_top
  have hns : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal R)), (id i : Ideal R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun i hi _ _ => (hfin.mem_toFinset.1 hi).1.1)]
    rintro ⟨p, hp, hmp⟩
    have hp' := hfin.mem_toFinset.1 hp
    have h1 : p ≤ q := hp'.2 ⟨hq, (Ideal.span_singleton_le_iff_mem _).2 (h q hq hq0)⟩
      (hle.trans hmp)
    exact hqm (le_antisymm hle (le_trans hmp h1) ▸ maximalIdeal.isMaximal R)
  obtain ⟨g, hgm, hg⟩ := Set.not_subset.1 hns
  have hne : Ideal.span {g} ≠ ⊤ := fun e => hgm (Ideal.span_singleton_eq_top.1 e)
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  have hgp : g ∈ p := hp.1.2 (Ideal.subset_span rfl)
  have hht : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  have hfm : Ideal.span {f} ≠ ⊤ := fun e =>
    hq.ne_top (q.eq_top_of_isUnit_mem (h q hq hq0) (Ideal.span_singleton_eq_top.1 e))
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p', hp'⟩⟩ := Ideal.nonempty_minimalPrimes hfm
    exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', p'.zero_mem⟩)
  have hp0 : p ≠ ⊥ := fun e => hg0 (by simpa [e] using hgp)
  obtain ⟨p', hp', hp'p⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 (h p hpp hp0))
  have hp'p' : p'.IsPrime := hp'.1.1
  have hp'0 : p' ≠ ⊥ := fun e => hf (by simpa [e] using hp'.1.2 (Ideal.subset_span rfl))
  have e : p' = p := by
    by_contra hne'
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hp'p hne')
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp'0)
    have h3 : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := ((add_le_add_left h2 1).trans h1).trans hht
    have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr; exact le_add_self) h3
    exact absurd h4 (by decide)
  exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', e ▸ hgp⟩)

theorem exists_prime_dimensionLEOne {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O}
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) :
    ∃ (P : Ideal O) (_ : P.IsPrime), f ∉ P ∧ Ring.DimensionLEOne (O ⧸ P) := by
  obtain ⟨P, ⟨hP, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian O O)
    {P : Ideal O | P.IsPrime ∧ f ∉ P} ⟨p₀, hp₀, hf⟩
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  refine ⟨P, hP, hfP, dimensionLEOne_of_forall_mem (f := Ideal.Quotient.mk P f)
    (fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 e)) fun q hq hq0 => ?_⟩
  by_contra hn
  refine hmax (q.comap (Ideal.Quotient.mk P)) ⟨inferInstance, hn⟩ (lt_of_le_of_ne ?_ fun e => hq0 ?_)
  · intro a ha
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [eq_bot_iff]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ P := e ▸ ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 this

theorem exists_dvr_of_dimensionLEOne {R Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.DimensionLEOne R] (hR : ¬ IsField R) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : R →+* W) (ι : ResidueField W →+* Ω),
      Function.Injective ψ ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨V, hV, h⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hR
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hi : Function.Injective ((algebraMap R (FractionRing R)).codRestrict V h1) :=
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  letI : Algebra R V := ((algebraMap R (FractionRing R)).codRestrict V h1).toAlgebra
  have : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hloc : IsLocalHom (algebraMap R V) := h2
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (isField_iff_maximalIdeal_eq.not.mp hR)
  have hfin := finite_quotient_span_of_birational (A := R) (B := V) (fun x => by
    obtain ⟨y, c, hc, hx⟩ := IsFractionRing.div_surjective (A := R) (x : FractionRing R)
    refine ⟨c, nonZeroDivisors.ne_zero hc, y, Subtype.ext ?_⟩
    change algebraMap R (FractionRing R) c * x = algebraMap R (FractionRing R) y
    rw [← hx]
    exact mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc)) ha0
  have hle : Ideal.span {algebraMap R V a} ≤ maximalIdeal V :=
    (Ideal.span_singleton_le_iff_mem _).2 (map_nonunit _ a ha)
  have hf2 : Module.Finite R (ResidueField V) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap (Ideal.Quotient.factor_surjective hle)
  have hf3 : Module.Finite (ResidueField R) (ResidueField V) := Module.Finite.of_restrictScalars_finite R _ _
  letI : Algebra (ResidueField R) Ω := (ResidueField.lift φ).toAlgebra
  let ι₀ : ResidueField V →ₐ[ResidueField R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let W := AdicCompletion (maximalIdeal V) V
  let e : ResidueField V ≃+* ResidueField W :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap V W)) (AdicCompletion.residueField_map_bijective V)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, (algebraMap V W).comp (algebraMap R V),
    ι₀.toRingHom.comp e.symm.toRingHom, (algebraMap_adicCompletion_injective_of_dvr V).comp hi, ?_⟩
  ext r
  have h3 : residue W (algebraMap V W (algebraMap R V r)) = e (residue V (algebraMap R V r)) := rfl
  change ι₀ (e.symm (residue W (algebraMap V W (algebraMap R V r)))) = φ r
  rw [h3, e.symm_apply_apply]
  exact ι₀.commutes (residue R r)

theorem exists_dvr {O Ω : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O} (hfm : f ∈ maximalIdeal O)
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) [Field Ω] [IsAlgClosed Ω] (φ : O →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : O →+* W) (ι : ResidueField W →+* Ω),
      ψ f ≠ 0 ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨P, hP, hfP, hd⟩ := exists_prime_dimensionLEOne p₀ hp₀ hf
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hF : ¬ IsField (O ⧸ P) := fun h =>
    hfP (eq_maximalIdeal (Ideal.Quotient.maximal_of_isField P h) ▸ hfm)
  have hk : ∀ a ∈ P, φ a = 0 := fun a ha => by
    by_contra h
    exact hP.ne_top (P.eq_top_of_isUnit_mem ha (isUnit_of_map_unit φ a (IsUnit.mk0 _ h)))
  have : IsLocalHom (Ideal.Quotient.lift P φ hk) := ⟨fun a ha => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (isUnit_of_map_unit φ a ha).map _⟩
  obtain ⟨W, _, _, _, _, ψ, ι, h1, h2⟩ := exists_dvr_of_dimensionLEOne hF (Ideal.Quotient.lift P φ hk)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, ψ.comp (Ideal.Quotient.mk P), ι,
    fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 (h1 (e.trans (map_zero ψ).symm))), ?_⟩
  rw [← RingHom.comp_assoc, h2]
  rfl

end Algebra

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

end GlobalTheory.GeomTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BaseVar

open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem j_mem_range_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Xo.XF c) :
    Y.j x ∈ Set.range X.π := by
  let xF : Sp ((Xo.XF c).residueField x) ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField x
  letI : Algebra c.F ((Xo.XF c).residueField x) := (Spec.preimage (xF ≫ pullback.snd _ _)).hom.toAlgebra
  have hsnd : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F ((Xo.XF c).residueField x)) :=
    (Spec.map_preimage _).symm
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frPt (S := (Xo.XF c).residueField x) (Xo := Xo) (c := c)
    (xF ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, sOf, ← Spec.map_comp]; rfl)
  have hx : xF = GlobalTheory.FlagMod.frX P := GlobalTheory.FlagMod.eq_frX P hP.symm hsnd
  let pt : Sp ((Xo.XF c).residueField x) := IsLocalRing.closedPoint _
  refine ⟨X.ptY P pt, ?_⟩
  have e1 : X.π (X.ptY P pt) = (X.ptY P ≫ X.π) pt := (Scheme.Hom.comp_apply _ _ _).symm
  rw [e1, (X.lies_ptY P).1, ← hx, Scheme.Hom.comp_apply]
  exact congrArg Y.j (Scheme.fromSpecResidueField_apply x _)

theorem surjective_π {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Function.Surjective X.π := by
  have := X.proper
  have hc : IsClosed (Set.range X.π) := X.π.isClosedMap.isClosed_range
  have hd : closure (Set.range Y.j) ⊆ Set.range X.π :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact j_mem_range_π X x) hc
  exact fun y => hd (LogKS.dense_interior Y y)

theorem surjective_π₀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) :
    Function.Surjective (π₀ X Z) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_π X ((barComp Y Z).ι y)
  have hzU : z ∈ X.π ⁻¹ᵁ barComp Y Z := by
    show X.π z ∈ barComp Y Z
    have : (barComp Y Z).ι y ∈ Set.range (barComp Y Z).ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι, ← hz] at this
  obtain ⟨z', hz'⟩ : z ∈ Set.range (inc₀ X Z) := by rwa [Scheme.Opens.range_ι]
  refine ⟨z', (barComp Y Z).ι.isOpenEmbedding.injective ?_⟩
  have e1 := Scheme.Hom.comp_apply (π₀ X Z) (barComp Y Z).ι z'
  have e2 := Scheme.Hom.comp_apply (inc₀ X Z) X.π z'
  rw [morphismRestrict_ι] at e1
  rw [← e1, e2, hz', hz]

theorem exists_var (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed (Xo := Xo) (c := c)) :
    ∃ (B : GlobalTheory.ProjVar.Var c.F) (φ : B.X ⟶ X₀ TF.Y Z), IsIso φ ∧ φ ≫ s₀ TF.Y Z = B.str ∧ B.dim = Dw.dim := by
  have hsm := GlobalTheory.VarFlag.smooth_gen TF.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) TF.Y c.F (RingEquiv.refl _) hF hsm
  have hJ : ∀ w : gen TF.Y, genι TF.Y w ∈ barComp TF.Y Z ↔ w ∈ Set.range (j Z) :=
    GlobalTheory.VarFlag.barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have := (hB Z).1
  have hr : Set.range (j Z ≫ genι TF.Y) ⊆ Set.range (barComp TF.Y Z).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨b, rfl⟩
    exact (hJ _).2 ⟨b, rfl⟩
  let φ := IsOpenImmersion.lift (barComp TF.Y Z).ι (j Z ≫ genι TF.Y) hr
  have hφ : φ ≫ (barComp TF.Y Z).ι = j Z ≫ genι TF.Y := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (φ ≫ (barComp TF.Y Z).ι) := by rw [hφ]; infer_instance
  have : IsOpenImmersion φ := IsOpenImmersion.of_comp φ (barComp TF.Y Z).ι
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w, genι TF.Y w = (barComp TF.Y Z).ι y :=
      ⟨inv (genι TF.Y) ((barComp TF.Y Z).ι y), by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hm : genι TF.Y w ∈ barComp TF.Y Z := by
      have : (barComp TF.Y Z).ι y ∈ Set.range (barComp TF.Y Z).ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι, ← hw] at this
    obtain ⟨b, rfl⟩ := (hJ w).1 hm
    refine ⟨b, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, hw]
  have hiso : IsIso φ := (isIso_iff_isOpenImmersion_and_surjective φ).2 ⟨inferInstance, ⟨hsurj⟩⟩
  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  refine ⟨B Z, φ, hiso, ?_, (hB Z).2.1⟩
  have h3 := (hB Z).2.2.1
  rw [hspid, Category.comp_id] at h3
  rw [← h3, GlobalTheory.VarFlag.genStr_eq, s₀, ← Category.assoc, hφ, Category.assoc]

theorem isVariety_barComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  intro E _ _ _ H Dw l Xo c TF Z hF
  obtain ⟨B, φ, hφ, hs, hd⟩ := exists_var TF Z hF
  have hs' : s₀ TF.Y Z = inv φ ≫ B.str := by rw [← hs, IsIso.inv_hom_id_assoc]
  have : Nonempty (X₀ TF.Y Z) := ⟨φ (genericPoint B.X)⟩
  have hint : IsIntegral (X₀ TF.Y Z) := isIntegral_of_isOpenImmersion (inv φ)
  refine ⟨hint, ?_, ?_, ?_, ⟨surjective_π₀ TF.X Z⟩, ?_, ?_⟩
  · rw [hs', ← hd]
    exact GlobalTheory.VarFlag.smooth_iso _ _ B.smooth
  · obtain ⟨N, i, hi, hs2⟩ := B.isProjOver
    exact ⟨N, inv φ ≫ i, inferInstance, by rw [Category.assoc, hs2, hs']⟩
  · rw [hs']
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (inv φ) (inv φ ≫ B.str) B.str (𝟙 _)) inferInstance
  · haveI : GlobalTheory.IsNormalScheme TF.Y.X := GlobalTheory.IsNormalScheme.of_pred TF.Y.normal
    exact GlobalTheory.IsNormalScheme.of_isOpenImmersion (i₀ TF.Y Z ≫ TF.Y.j)
  · intro v hv
    have : IsOpenImmersion (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) := by rw [j₀_ι]; infer_instance
    have : IsOpenImmersion (j₀ TF.Y Z) := IsOpenImmersion.of_comp _ (barComp TF.Y Z).ι
    have hgen : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
      have hirr : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
      exact IsIrreducible.isGenericPoint_genericPoint hirr (isClosed_of_mem_irreducibleComponents _ Z.2)
    have hsub : Set.range (j₀ TF.Y Z) ⊆ closure {j₀ TF.Y Z v} := by
      rintro _ ⟨w, rfl⟩
      have hw : i₀ TF.Y Z w ∈ (Z : Set (Xo.XF c)) := (j_mem_barComp (Y := TF.Y) Z _).1 w.2
      have h1 : i₀ TF.Y Z v ⤳ i₀ TF.Y Z w := hv ▸ hgen.specializes hw
      have h2 : v ⤳ w := (i₀ TF.Y Z).isOpenEmbedding.isInducing.specializes_iff.1 h1
      exact specializes_iff_mem_closure.1 (h2.map (j₀ TF.Y Z).continuous)
    have hdense : Dense (Set.range (j₀ TF.Y Z)) :=
      (j₀ TF.Y Z).isOpenEmbedding.isOpen_range.dense ⟨_, ⟨v, rfl⟩⟩
    have hg : IsGenericPoint (j₀ TF.Y Z v) (Set.univ : Set (X₀ TF.Y Z)) := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← hdense.closure_eq]
      exact closure_minimal hsub isClosed_closure
    exact hg.eq (genericPoint_spec (X₀ TF.Y Z))

end GlobalTheory.BaseVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectivStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactificationComponent_integral_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  first | exact @GlobalTheory.BaseVar.isVariety_barComp | exact GlobalTheory.BaseVar.isVariety_barComp | (intros; apply GlobalTheory.BaseVar.isVariety_barComp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstant
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace GlobalTheory.EndDivisible

theorem exists_relation_of_cls (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (hf : Smooth f)
    (hp : GlobalTheory.AbLaw.IsProjBy f) (c : Pic X) :
    ∃ n : ℕ, ∀ (B : LB X) (hB : B.IsLB), cls B hB = c → ∀ σ : Fin n → LB.Sec B,
      ∃ a : Fin n → K, a ≠ 0 ∧ ∀ i, ∑ k, GlobalTheory.AbLaw.cst f (B.U i) (a k) * (σ k).f i = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨Q⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy K X f hf hp M hM
  refine ⟨Q.a + 1, fun B hB hc σ => ?_⟩
  obtain ⟨w, hw⟩ := (cls_eq_iff hB hM).1 hc
  let e : LB.Sec B ≃ₗ[Γ(X, ⊤)] LB.Sec M :=
    (GlobalTheory.AbLaw.SecOn.topEquiv B).symm ≪≫ₗ GlobalTheory.AbLaw.SecOn.congr hB hM w hw ⊤ ≪≫ₗ GlobalTheory.AbLaw.SecOn.topEquiv M
  obtain ⟨a, ha, h⟩ := Q.exists_relation (fun k => e (σ k))
  let a' : Fin (Q.a + 1) → Γ(X, ⊤) := fun k =>
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a k))
  have ev : ∀ (N : LB X) (τ : Fin (Q.a + 1) → LB.Sec N) (i : N.ι),
      (∑ k, a' k • τ k).f i = ∑ k, GlobalTheory.AbLaw.cst f (N.U i) (a k) * (τ k).f i := fun N τ i => by
    let F : LB.Sec N →+ Γ(X, N.U i) := AddMonoidHom.mk' (fun s => s.f i) (fun _ _ => rfl)
    exact map_sum F _ _
  have h1 : ∑ k, a' k • e (σ k) = 0 :=
    GlobalTheory.AbLaw.HighTwist.sec_eq_zero _ fun i => (ev M _ i).trans (h i)
  have h2 : ∑ k, a' k • σ k = 0 := by
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, ← h1]
    exact Finset.sum_congr rfl fun k _ => e.map_smul _ _
  exact ⟨a, ha, fun i => (ev B σ i).symm.trans (by rw [h2]; rfl)⟩

theorem eff_nsmul_of_pos {X : Scheme.{0}} [IsIntegral X] (c : Pic X) (hc : GlobalTheory.EffBound.Eff c) (N : ℕ)
    (hN : 1 ≤ N) : GlobalTheory.EffBound.Eff (N • c) := by
  induction N, hN using Nat.le_induction with
  | base => rwa [one_nsmul]
  | succ n _ ih => rw [succ_nsmul]; exact GlobalTheory.EffBound.eff_add _ _ ih hc

theorem exists_pull_monomial {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (t : ℕ)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) (a : ℕ) (ha : a ≤ t) :
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => ((N * t : ℕ) : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) := by
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N) (fun _ => f ≫ w) (fun _ => 1)
      (fun _ : Unit => u) (fun _ => ((N * t : ℕ) : ℤ)) := by
    intro U _ h
    rw [hu]
    simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha, zpow_natCast]
    rw [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem constSt : ConstSt := by
  intro K _ _ A _ hA L hL hamp m
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]; infer_instance⟩
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
    exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL d, n, s, hs⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hamp ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := exists_relation_of_cls K A.left A.hom hA.smooth hproj (N • m)
  refine ⟨n, fun t hnt ψ hψ heff => ?_⟩
  obtain ⟨P, hP, hPc, ε, p₀, hε⟩ := eff_nsmul_of_pos _ heff N hN
  have hQ := LB.isLB_linComb hL (K := Unit) (fun _ => ψ.left) (fun _ => ((N * t : ℕ) : ℤ))
  have hT : cls _ (isLB_tens hP hQ) = N • m := by
    rw [cls_tens hP hQ, hPc, cls_linComb hL, Fintype.sum_unique, natCast_zsmul, nsmul_sub, mul_nsmul',
      sub_add_cancel]
  let w := (A.hom ⁻¹ᵁ ⊤).ι
  let f : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨z⟩ : Nonempty A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good L z J := by
    choose I hI using fun χ : A.left ⟶ A.left => exists_chart hL (χ z)
    exact ⟨I, hI⟩
  obtain ⟨p, hp⟩ := exists_chart hP z
  have hεz : gs (𝟙 _) z (P.U p) (ε.f p) ≠ 0 := by
    rw [gs_eq (𝟙 _) z (P.U p) hp]
    exact GlobalTheory.EffBound.germ_sec_ne_zero ε hε p z hp
  let κ := germPull A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    choose σ hσ using fun a : Fin n =>
      exists_pull_monomial L hL w N (s i) (s j) t f ψ.left hf.symm z J hJ a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn _ _ hT (fun a => GlobalTheory.EffBound.tensSec ε (σ a))
    have hm₂ := hJ.mem (K := Unit) (fun _ => ψ.left) (𝟙 _)
    have hm : (𝟙 A.left : A.left ⟶ A.left) z ∈ P.U p ⊓ LB.wchart L (K := Unit) (fun _ => ψ.left)
      (fun _ => J (𝟙 _ ≫ ψ.left)) := ⟨hp, hm₂⟩
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (p, fun _ => J (𝟙 _ ≫ ψ.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (c k) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ t * gs (𝟙 _) z (P.U p) (ε.f p)) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) A.hom z ⊤ _ le_top hm (E.symm (c k)))
        ((gs_mul (𝟙 _) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z inf_le_left hm _)
          ((gs_res (𝟙 _) z inf_le_right hm _).trans (hσ k))))).symm
      have e₁ : (κ.comp E.symm.toRingHom) (c k) = gs (𝟙 _ ≫ A.hom) z ⊤ (E.symm (c k)) := by
        rw [Category.id_comp]
        exact germPull_apply _ _ _ _ _
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) c hc (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero (hy.pow _).ne_zero hεz))
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have h2 : η[A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  apply Over.OverMorphism.ext
  rw [hp, ← h2, Hom.one_def]
  simp

end GlobalTheory.AmpleRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvFun


open TensorProduct in
theorem alg_inv {R A R' B : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing B] [Algebra R A] [Algebra R R']
    [Algebra R B] [Algebra A B] [Algebra R' B] [IsScalarTower R A B] [IsScalarTower R R' B]
    [Algebra.IsPushout R A R' B] [Module.Flat R A] (hinj : Function.Injective (algebraMap R R'))
    {J : Type} [Finite J] (s : J → (R' →ₐ[R] R')) (hs : ∀ x : R', (∀ i, s i x = x) → x ∈ (algebraMap R R').range)
    (t : J → (B →+* B)) (htA : ∀ i a, t i (algebraMap A B a) = algebraMap A B a)
    (htR : ∀ i r, t i (algebraMap R' B r) = algebraMap R' B (s i r)) :
    Function.Injective (algebraMap A B) ∧ ∀ u : B, (∀ i, t i u = u) → u ∈ Set.range (algebraMap A B) := by
  classical
  cases nonempty_fintype J
  let e := Algebra.IsPushout.equiv R A R' B
  have he : ∀ (a : A) (r : R'), e (a ⊗ₜ r) = algebraMap A B a * algebraMap R' B r := fun a r =>
    Algebra.IsPushout.equiv_tmul R A R' B a r
  have hA : ∀ a : A, algebraMap A B a = e ((Algebra.linearMap R R').lTensor A (a ⊗ₜ 1)) := fun a => by
    simp [he]
  refine ⟨fun a b hab => ?_, fun u hu => ?_⟩
  · rw [hA, hA] at hab
    have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R R') hinj (e.injective hab)
    simpa using congrArg (TensorProduct.rid R A) h₁
  · let d : R' →ₗ[R] (J → R') := LinearMap.pi fun i => (s i).toLinearMap - LinearMap.id
    have hex : Function.Exact (Algebra.linearMap R R') d := by
      intro x
      constructor
      · intro hx
        exact hs x fun i => sub_eq_zero.1 (congrFun hx i)
      · rintro ⟨r, rfl⟩
        ext i
        simp [d]
    have hexA := Module.Flat.lTensor_exact A hex
    obtain ⟨w, rfl⟩ := e.surjective u
    have key : ∀ (w : A ⊗[R] R') (i : J), e (TensorProduct.piRight R R A (fun _ : J => R') (d.lTensor A w) i) =
        t i (e w) - e w := by
      intro w i
      induction w with
      | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
      | tmul a r => simp [d, he, htA, htR, mul_sub, tmul_sub]
    have h0 : d.lTensor A w = 0 := by
      apply (TensorProduct.piRight R R A (fun _ : J => R')).injective
      ext i
      apply e.injective
      rw [key, hu]
      simp
    obtain ⟨v, rfl⟩ := (hexA w).1 h0
    refine ⟨TensorProduct.rid R A v, ?_⟩
    rw [hA]
    congr 2
    exact (TensorProduct.rid R A).symm_apply_apply v

theorem app_comp_appLE {Y Y' : Scheme.{0}} {β : Y' ⟶ Y} {f : Y' ⟶ Y'} (hf : f ≫ β = β) (U : Y.Opens)
    (e : β ⁻¹ᵁ U ≤ f ⁻¹ᵁ (β ⁻¹ᵁ U)) : β.app U ≫ f.appLE (β ⁻¹ᵁ U) (β ⁻¹ᵁ U) e = β.app U := by
  refine (Scheme.Hom.comp_appLE f β U (β ⁻¹ᵁ U) e).symm.trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  simp only [hf]

theorem const_comp_appLE {R : CommRingCat.{0}} {Y : Scheme.{0}} {y : Y ⟶ Spec R} {f : Y ⟶ Y} {s : R ⟶ R}
    (hf : f ≫ y = y ≫ Spec.map s) (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ U) :
    ((Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top) ≫ f.appLE U U e =
      s ≫ (Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top := by
  have e₁ : y.appLE ⊤ U le_top ≫ f.appLE U U e = (Spec.map s).appTop ≫ y.appLE ⊤ U le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f y ⊤ U U le_top e).trans ?_
    simp only [hf]
    exact Scheme.Hom.comp_appLE y (Spec.map s) ⊤ U le_top
  rw [Category.assoc, e₁, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem affine_inv {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (hG : IsGal ρ)
    {Y Y' : Scheme.{0}} {y : Y ⟶ Sp R} {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} [Flat y] (h : IsPullback β y' y (spMap ρ))
    (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β) (hy : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Injective (β.app U).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ U),
      (∀ σ (h : β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app U).hom := by
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := β ⁻¹ᵁ U)
    le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top)
      (CommRingCat.ofHom ρ) (β.app U)
      ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top) := by
    refine hp.of_iso (Scheme.ΓSpecIso _) (.refl _) (Scheme.ΓSpecIso _) (.refl _) (by simp) ?_
      (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    exact Scheme.ΓSpecIso_naturality _
  have hfl : ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (y.flat_appLE (isAffineOpen_top _) hU le_top)
  have hle : ∀ σ, β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U) := fun σ => by
    rw [← Scheme.Hom.comp_preimage, hβ]
  algebraize [ρ, ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom,
    (β.app U).hom,
    ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top).hom,
    (((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top) ≫ β.app U).hom]
  have : IsScalarTower R Γ(Y, U) Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(hp'.w).hom)
  have : Algebra.IsPushout R Γ(Y, U) R' Γ(Y', β ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  have := hG.1
  have H := alg_inv (R := R) (A := Γ(Y, U)) (R' := R') (B := Γ(Y', β ⁻¹ᵁ U)) hρ
    (fun σ : Gal ρ => (⟨Gal.hom σ, σ.2⟩ : R' →ₐ[R] R')) (fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩)
    (fun σ => ((act σ).appLE _ _ (hle σ)).hom) ?_ ?_
  · exact ⟨H.1, fun u hu => H.2 u fun σ => hu σ _⟩
  · intro σ a
    exact congr($(app_comp_appLE (hβ σ) U (hle σ)).hom a)
  · intro σ r
    exact congr($(const_comp_appLE (hy σ) (β ⁻¹ᵁ U) (hle σ)).hom r)

theorem app_res {Y Y' : Scheme.{0}} (β : Y' ⟶ Y) {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)) :
    (β.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom ((β.app V).hom a) :=
  congr($(β.naturality (homOfLE e).op).hom a)

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (e : U ≤ V) (e' : V ≤ W) (a : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE e).op).hom ((Y.presheaf.map (homOfLE e').op).hom a) =
      (Y.presheaf.map (homOfLE (e.trans e')).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem le_iSup_affine {Y : Scheme.{0}} (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUV⟩, hxU⟩

theorem injective_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, IsAffineOpen U → Function.Injective (β.app U).hom) (V : Y.Opens) :
    Function.Injective (β.app V).hom := by
  intro a b hab
  refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a b fun U => H U.1 U.2.1 ?_
  exact (app_res β U.2.2 a).trans ((congrArg _ hab).trans (app_res β U.2.2 b).symm)

theorem mem_range_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, Function.Injective (β.app U).hom) (V : Y.Opens) (u : Γ(Y', β ⁻¹ᵁ V))
    (hu : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (e : U ≤ V),
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom u ∈ Set.range (β.app U).hom) :
    u ∈ Set.range (β.app V).hom := by
  choose a ha using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => hu U.1 U.2.1 U.2.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a (fun i j => H (i.1 ⊓ j.1) (by
      refine (app_res β inf_le_left (a i)).trans (Eq.trans ?_ (app_res β inf_le_right (a j)).symm)
      rw [ha, ha, res_res, res_res]))
  refine ⟨s, Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => β ⁻¹ᵁ U.1) (β ⁻¹ᵁ V)
    (fun U => homOfLE (β.preimage_mono U.2.2)) ?_ _ _ fun U => ?_⟩
  · rw [← β.preimage_iSup]
    exact β.preimage_mono (le_iSup_affine V)
  · exact (app_res β U.2.2 s).symm.trans ((congrArg _ (hs U)).trans (ha U))

theorem invariant_functions : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y →
    IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) →
    (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧
    ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) →
      u ∈ Set.range (β.app V).hom := by
  intro R _ _ R' _ _ _ ρ hF hG Y Y' y y' β _ h act hβ hy V
  have H := fun (U : Y.Opens) (hU : IsAffineOpen U) => affine_inv ρ hF.2.1 hG h act hβ hy hU
  have hinj := injective_of_affine β fun U hU => (H U hU).1
  refine ⟨hinj V, fun u hu => mem_range_of_affine β hinj V u fun U hU e => (H U hU).2 _ fun σ hσ => ?_⟩
  have hle : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hβ]
  have e₁ : Y'.presheaf.map (homOfLE (β.preimage_mono e)).op ≫ (act σ).appLE _ _ hσ =
      (act σ).appLE _ _ hle ≫ Y'.presheaf.map (homOfLE (β.preimage_mono e)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (congr($(e₁).hom u)).trans (congrArg _ (hu σ hle))

end GlobalTheory.Mum.InvFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_invariant_functions_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app V).hom := by
  first | exact @GlobalTheory.Mum.InvFun.invariant_functions | exact GlobalTheory.Mum.InvFun.invariant_functions | (intros; apply GlobalTheory.Mum.InvFun.invariant_functions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionPowScales
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SelfInterPow

theorem isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → ∀ e : ℕ,
      (L.pow e).IsSelfInter ((e : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX L a ha e
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, he⟩ := hΦ.1 fun _ => (e : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.ArInt.isometric_comb_unit_pow k X p L e) hH, he.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

end GlobalTheory.SelfInterPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

end GlobalTheory.LinFrob
end
end
