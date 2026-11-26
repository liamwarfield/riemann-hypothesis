module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalMaxIdeals.proof (h1 : FibreFinite.Statement.{u}) (h2 : FibreRelDim.Statement.{u})
    (h3 : FibreNonempty.Statement.{u}) (h4 : DegZeroLocUnits.Statement.{u})
    (h5 : DegZeroLocSeparate.Statement.{u}) (h6 : DegZeroLocLocalize.Statement.{u})
    (h7 : SemilocalResidueLength.Statement.{u}) : SemilocalMaxIdeals.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have h𝒲 : ∀ W' ∈ fibrePrimes j P' W, IsMultiProjPrime W' ∧ P' ≤ W' :=
    fun W' hW' => ⟨hW'.1, hW'.2.1⟩

  have hanti : ∀ W₁ ∈ fibrePrimes j P' W, ∀ W₂ ∈ fibrePrimes j P' W, W₁ ≤ W₂ → W₁ = W₂ := by
    intro W₁ h₁ W₂ h₂ hle
    by_contra hne
    have := h₁.1.isPrime
    have := h₂.1.isPrime
    obtain ⟨f, hf₂, hf₁⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hd := ringKrullDim_add_one_le hle hf₁ hf₂
    obtain ⟨D₁, -, hD₁⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₁.1.multiHomog T hq) h₁.1.relevant
    obtain ⟨D₂, -, hD₂⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₂.1.multiHomog T hq) h₂.1.relevant
    have e₁ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₁ h₁
    have e₂ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₂ h₂
    rw [relDim_eq_int hD₁, natCast_withBot_withTop] at e₁
    rw [relDim_eq_int hD₂, natCast_withBot_withTop] at e₂
    rw [hD₁, hD₂] at hd
    have e₁' : (D₁ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₁
    have e₂' : (D₂ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₂
    have hd' : D₂ + 1 ≤ D₁ := by exact_mod_cast hd
    omega

  choose 𝔪 h𝔪 hlen using h7 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  have hprime : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsPrime := by
    intro W'
    refine ⟨fun htop => (h𝔪 W'.1 W'.2 1).mp (htop ▸ Submodule.mem_top)
      ⟨1, Subalgebra.one_mem _, by simp⟩, fun {x y} hxy => ?_⟩
    by_contra hc
    rw [not_or, h𝔪, h𝔪, not_not, not_not] at hc
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ := hc
    exact (h𝔪 W'.1 W'.2 _).mp hxy ⟨a * b, Subalgebra.mul_mem _ ha hb, by
      rw [Subalgebra.coe_mul, mul_mul_mul_comm, hxa, hyb, one_mul]⟩

  have hsep : ∀ W₁ W₂ : fibrePrimes j P' W, W₁ ≠ W₂ → ¬ 𝔪 W₁.1 W₁.2 ≤ 𝔪 W₂.1 W₂.2 := by
    intro W₁ W₂ hne hle
    obtain ⟨x, hx, hx₁, hx₂⟩ := h5 F K' ι' P' hP' _ hfin h𝒲 W₁.1 W₁.2 W₂.1 W₂.2
      (fun h => hne (Subtype.ext (hanti _ W₁.2 _ W₂.2 h)))
    exact (h𝔪 W₂.1 W₂.2 ⟨x, hx⟩).mp (hle ((h𝔪 W₁.1 W₁.2 ⟨x, hx⟩).mpr hx₁)) hx₂

  have hne := h3 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have hcov : ∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal →
      ∃ W' : fibrePrimes j P' W, M = 𝔪 W'.1 W'.2 := by
    intro M hM
    let 𝔫 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)) := fun W' => 𝔪 W'.1 W'.2
    have hsub : (M : Set (degZeroLoc P' (fibrePrimes j P' W))) ⊆
        ⋃ W' ∈ ((Finset.univ : Finset (fibrePrimes j P' W)) : Set (fibrePrimes j P' W)),
          ((𝔫 W' : Ideal (degZeroLoc P' (fibrePrimes j P' W))) : Set _) := by
      intro x hx
      have hnu : ¬ IsUnit x := fun hu => hM.ne_top (M.eq_top_of_isUnit_mem hx hu)
      have : ¬ ∀ W' ∈ fibrePrimes j P' W, ∃ y ∈ degZeroLoc P' {W'},
          (x : FractionRing (MRing ι' F ⧸ P')) * y = 1 := by
        rw [← h4 F K' ι' P' hP' _ hne h𝒲 x x.2]
        rintro ⟨y, hy, hxy⟩
        exact hnu (IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext hxy))
      push Not at this
      obtain ⟨W', hW', hx'⟩ := this
      refine Set.mem_iUnion₂.mpr ⟨⟨W', hW'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact (h𝔪 W' hW' x).mpr (fun ⟨y, hy, hxy⟩ => hx' y hy hxy)
    obtain ⟨W', -, hle⟩ := (Ideal.subset_union_prime (f := 𝔫) ⟨hne.some, hne.some_mem⟩
      ⟨hne.some, hne.some_mem⟩ (fun W' _ _ _ => hprime W')).mp hsub
    exact ⟨W', hM.eq_of_le (hprime W').ne_top hle⟩
  have hmax : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsMaximal := by
    intro W'
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (hprime W').ne_top
    obtain ⟨W'', rfl⟩ := hcov M hM
    by_cases h : W' = W''
    · subst h
      exact hM
    · exact absurd hle (hsep W' W'' h)
  refine ⟨fun W' => 𝔪 W'.1 W'.2, hmax, fun W₁ W₂ he => ?_, hcov, fun W' => ⟨?_, hlen W'.1 W'.2⟩⟩
  · by_contra h
    exact hsep W₁ W₂ h (le_of_eq he)

  let := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  refine (isLocalization_iff _ _).mpr ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hs := s.2
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not] at hs
    obtain ⟨t, ht, hst⟩ := hs
    exact IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext hst)
  · obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := h6 F K' ι' P' hP' _ hfin h𝒲 W'.1 W'.2 z z.2
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not]
    exact ⟨t, ht, hst⟩
  · refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val hxy
    have hxy' : x = y := Subtype.ext h'
    rw [hxy']

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LocalIntegralClosureChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_mul_isIntegral_of_eq_mul_inv {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by
  let M : Submonoid R :=
    { carrier := {d | (d : Ω) ≠ 0 ∧ (d : Ω)⁻¹ ∈ A}
      mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by
        rw [Subalgebra.coe_mul, mul_inv]; exact A.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_ne_zero, by rw [Subalgebra.coe_one, inv_one]; exact A.one_mem⟩ }
  let _ : Algebra R A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization M A := by
    refine (isLocalization_iff M A).mpr ⟨fun d => ?_, fun a => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · exact ⟨⟨_, ⟨_, d.2.2⟩, Subtype.ext (mul_inv_cancel₀ d.2.1), Subtype.ext (inv_mul_cancel₀ d.2.1)⟩, rfl⟩
    · obtain ⟨r, hr, d, hd, hd0, hdA, he⟩ := hloc a a.2
      refine ⟨(⟨r, hr⟩, ⟨⟨d, hd⟩, hd0, hdA⟩), Subtype.ext ?_⟩
      change (a : Ω) * d = r
      rw [he, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
    · have e : ((algebraMap R A a : A) : Ω) = (algebraMap R A b : A) := congrArg Subtype.val h
      have e' : (a : Ω) = b := e
      rw [Subtype.ext e']
  obtain ⟨⟨d, hd0, hdA⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (M := M) (Rₘ := A) x hx
  exact ⟨d, d.2, hd0, hdA, hint⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem exists_finset_integral_span (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by
  classical
  let L' := IntermediateField.extendScalars hEL
  let _ : Algebra (Algebra.adjoin F S) L' :=
    ((algebraMap (IntermediateField.adjoin F S) L').comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType F (Algebra.adjoin F S) := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (hN F (Algebra.adjoin F S) (IntermediateField.adjoin F S) L')
  let ι₀ : L' →ₐ[Algebra.adjoin F S] Ω := { L'.val.toRingHom with commutes' := fun _ => rfl }
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective
  let _ : Algebra (Algebra.adjoin F S) A := (Subalgebra.inclusion hRA).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨t.image fun y => ι₀ y.1, ?_, fun x hx hxA => ?_⟩
  · intro e he
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(IntermediateField.mem_extendScalars hEL).mp y.1.2,
      ((isIntegral_algHom_iff ι₀ hι₀).mpr y.2).tower_top⟩
  obtain ⟨d, hd, hd0, hdA, hint⟩ := exists_mul_isIntegral_of_eq_mul_inv _ A hRA hloc hxA
  let z : integralClosure (Algebra.adjoin F S) L' :=
    ⟨⟨d * x, (IntermediateField.mem_extendScalars hEL).mpr
      (mul_mem (hEL (IntermediateField.algebra_adjoin_le_adjoin F S hd)) hx)⟩,
      (isIntegral_algHom_iff ι₀ hι₀).mp hint⟩
  have hz : ι₀ z ∈ Submodule.span (Algebra.adjoin F S) ((t.image fun y => ι₀ y.1 : Finset Ω) : Set Ω) := by
    have hzt : z ∈ Submodule.span (Algebra.adjoin F S) (t : Set _) := ht ▸ Submodule.mem_top
    have := Submodule.mem_map_of_mem
      (f := ι₀.toLinearMap.comp (integralClosure (Algebra.adjoin F S) L').val.toLinearMap) hzt
    rw [Submodule.map_span] at this
    rw [Finset.coe_image]
    exact this
  have e : (⟨d⁻¹, hdA⟩ : A) • (d * x) = x := by
    rw [Subalgebra.smul_def, smul_eq_mul, ← mul_assoc]
    change d⁻¹ * d * x = x
    rw [inv_mul_cancel₀ hd0, one_mul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars (Algebra.adjoin F S) A _ hz)

section Chart

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem isMultiHomog_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have hb : (∑ k, b k • blockWeight ι ⟨k, u k⟩) = b := by
    funext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k)
  unfold IsMultiHomog chartMonomial
  convert h using 1
  exact hb.symm


omit [DecidableEq K] in
theorem chartMonomial_not_mem_of_notMem (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W :=
  (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hu k) _ : chartMonomial u b ∈ W.primeCompl)

theorem degZeroLoc_map_eq_mul_inv (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hW1 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := fun W' h => by
    rw [Set.mem_singleton_iff.mp h]; infer_instance
  have hmem : ∀ p, φ (chartMap P u p) ∈
      Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) := fun p => by
    rw [← aeval_range]
    refine ⟨p, ?_⟩
    change aeval _ p = (φ.comp (chartMap P u)) p
    rw [chartMap, comp_aeval]
    simp
  have hq : ∀ g : MRing ι F, g ∉ P → algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P g) ≠ 0 := fun g hg => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  refine ⟨Algebra.adjoin_le ?_, fun a ha => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (b := blockWeight ι v)
      (isWeightedHomogeneous_X F _ v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (huP v.1) (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hu v.1), ?_⟩
    simp [chartMap]
  obtain ⟨a, haA, rfl⟩ := Subalgebra.mem_map.mp ha
  obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hQ F K ι P {W} hW1 a haA
  have hm := chartMonomial_not_mem_of_notMem (F := F) W u hu b
  have hm0 := hq _ fun h => hm (hPW h)
  have hg0 := hq g hgP
  refine ⟨φ (chartMap P u f), hmem f, φ (chartMap P u g), hmem g, ?_, ?_, ?_⟩
  · rw [hD F K ι P u huP g b hg, map_ne_zero]
    exact div_ne_zero hg0 hm0
  · rw [hD F K ι P u huP g b hg, ← map_inv₀, inv_div]
    exact Subalgebra.mem_map.mpr ⟨_, div_mem_degZeroLoc P {W} (isMultiHomog_chartMonomial u b) hg
      hgP (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hgW W rfl), rfl⟩
  · rw [hD F K ι P u huP f b hf, hD F K ι P u huP g b hg, ← map_inv₀, ← map_mul]
    congr 1
    field_simp

end Chart

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
