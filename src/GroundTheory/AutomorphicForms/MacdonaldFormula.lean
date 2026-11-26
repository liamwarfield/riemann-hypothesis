module

public import GroundTheory.AutomorphicForms.MacdonaldHecke

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.MacdonaldSpherical
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra Parabolic AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

noncomputable local instance fintypeResidue' : Fintype 𝓀[F] := Fintype.ofFinite _

theorem sphericalFun_mul_right {χ : levi F n (id : Fin n → Fin n) →* ℂ} (hχ : IsUnramified χ)
    (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    sphericalFun χ (g * k) = sphericalFun χ g := by
  obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
  rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

theorem sphericalFun_of_mem {χ : levi F n (id : Fin n → Fin n) →* ℂ} (hχ : IsUnramified χ)
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : sphericalFun χ k = 1 := by
  rw [← one_mul k, sphericalFun_mul_right hχ 1 hk, sphericalFun_one hχ]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integral_mul_sphericalFun (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n))
    (y : GL (Fin n) F) :
    ∫ x, (h : HeckeAlgebra μ) x * sphericalFun (paramChar F z) (y * x) ∂μ =
      evalAt z (satakeTransform μ h) * sphericalFun (paramChar F z) y := by
  have hχ := isUnramified_paramChar (F := F) z
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n))
    (charRep (paramChar F z))
  let ev : Module.Dual ℂ (principalSeriesSpace F n (paramChar F z)) :=
    (LinearMap.proj y).comp (principalSeriesSpace F n (paramChar F z)).subtype
  have h1 := dual_heckeAct μ (h : HeckeAlgebra μ).mem (hs (sphericalVector hχ)) ev
  rw [heckeAct_sphericalVector, map_smul] at h1
  simp only [ev, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
    LinearMap.coe_proj, Function.eval, coe_sphericalVector, smul_eq_mul] at h1
  rw [← sphericalCharacter_paramChar z h, sphericalCharacter_apply, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [coe_indRep_apply]
  rfl

theorem sum_sphericalFun_gMat (z : Fin n → ℂˣ) (r : ℕ) (y : GL (Fin n) F) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F],
        sphericalFun (paramChar F z) (y * gMat S c) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
        evalAt z (satakeTransform μ (minusculeHecke μ r)) * sphericalFun (paramChar F z) y := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 := integral_minusculeHecke_mul (μ := μ)
    (fun g k hk => sphericalFun_mul_right (isUnramified_paramChar z) g hk) y r
  rw [integral_mul_sphericalFun] at h1
  rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]


variable (μ) in
def zonalSpherical (z : Fin n → ℂˣ) (g : GL (Fin n) F) : ℂ :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
    ∫ x, (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * g) ∂μ

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem isClopen_integralGL : IsClopen (integralGL F n : Set (GL (Fin n) F)) :=
  ⟨(isCompact_integralGL F n).isClosed, isOpen_integralGL F n⟩

theorem integrable_indicator_mul_sphericalFun (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    Integrable (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * g)) μ := by
  have hφ : Continuous (sphericalFun (paramChar F z)) :=
    continuous_of_mul_right_invariant fun g k hk => sphericalFun_mul_right (isUnramified_paramChar z) g hk
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (isClopen_integralGL.continuous_indicator continuous_const).mul
      (hφ.comp (continuous_mul_const g))
  · refine HasCompactSupport.intro (isCompact_integralGL F n) fun x hx => ?_
    simp only [Set.indicator_of_notMem hx, zero_mul]

theorem zonalSpherical_mul_right (z : Fin n → ℂˣ) (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : zonalSpherical μ z (g * k) = zonalSpherical μ z g := by
  simp only [zonalSpherical, ← mul_assoc,
    sphericalFun_mul_right (isUnramified_paramChar z) _ hk]

theorem zonalSpherical_mul_left (z : Fin n → ℂˣ) {k : GL (Fin n) F} (hk : k ∈ integralGL F n)
    (g : GL (Fin n) F) : zonalSpherical μ z (k * g) = zonalSpherical μ z g := by
  haveI := Measures.isMulRightInvariant_GL F n μ
  simp only [zonalSpherical]
  congr 1
  have h := integral_mul_right_eq_self (μ := μ)
    (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) (x * k⁻¹) *
      sphericalFun (paramChar F z) (x * g)) k
  simp only [mul_inv_cancel_right] at h
  rw [show (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * (k * g))) = fun x =>
      (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * k * g) by simp only [mul_assoc], h]
  congr 1
  funext x
  congr 1
  have : x * k⁻¹ ∈ integralGL F n ↔ x ∈ integralGL F n :=
    ⟨fun h => by simpa using mul_mem h hk, fun h => mul_mem h ((integralGL F n).inv_mem hk)⟩
  by_cases hx : x ∈ integralGL F n
  · rw [Set.indicator_of_mem (show x * k⁻¹ ∈ (integralGL F n : Set (GL (Fin n) F)) from this.2 hx),
      Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx)]
  · rw [Set.indicator_of_notMem (show x * k⁻¹ ∉ (integralGL F n : Set (GL (Fin n) F)) from
      fun h => hx (this.1 h)),
      Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx)]

theorem zonalSpherical_one (z : Fin n → ℂˣ) : zonalSpherical μ z 1 = 1 := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rw [zonalSpherical]
  have : (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * 1)) =
      fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => ((1 : ℝ) : ℂ)) x := by
    funext x
    by_cases hx : x ∈ integralGL F n
    · rw [Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), mul_one,
        sphericalFun_of_mem (isUnramified_paramChar z) hx, one_mul, Complex.ofReal_one]
    · rw [Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]
  rw [this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, Complex.ofReal_one, mul_one]
  exact inv_mul_cancel₀ hK

theorem zonalSpherical_torusPow_comp (z : Fin n → ℂˣ) (μ' : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    zonalSpherical μ z (torusPow F n (μ' ∘ σ)) = zonalSpherical μ z (torusPow F n μ') := by
  rw [← permGL_conj_torusPow, zonalSpherical_mul_right z _ (permGL_mem_integralGL F n σ),
    zonalSpherical_mul_left z ((integralGL F n).inv_mem (permGL_mem_integralGL F n σ))]

theorem sum_zonalSpherical_gMat (z : Fin n → ℂˣ) (r : ℕ) (g : GL (Fin n) F) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F],
        zonalSpherical μ z (g * gMat S c) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
        evalAt z (satakeTransform μ (minusculeHecke μ r)) * zonalSpherical μ z g := by
  set c₀ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹
  set ind := (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ))
  set P := (Finset.univ : Finset (Fin n)).powersetCard r
  have hint : ∀ g' : GL (Fin n) F,
      Integrable (fun x => ind x * sphericalFun (paramChar F z) (x * g')) μ :=
    fun g' => integrable_indicator_mul_sphericalFun z g'
  have e1 : (∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
      ∫ x, ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) ∂μ) =
      ∫ x, ∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
        ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) ∂μ := by
    have e := integral_finsetSum (μ := μ) (f := fun S x => ∑ c : Pairs S → 𝓀[F],
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c))) P
      (fun S _ => MeasureTheory.integrable_finsetSum _ fun c _ => hint _)
    rw [e]
    refine Finset.sum_congr rfl fun S _ => ?_
    have e' := integral_finsetSum (μ := μ) (f := fun c x =>
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c))) Finset.univ (fun c _ => hint _)
    rw [e']
  have e2 : ∀ x, ∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) =
      c₀ * evalAt z (satakeTransform μ (minusculeHecke μ r)) *
        (ind x * sphericalFun (paramChar F z) (x * g)) := by
    intro x
    simp only [← Finset.mul_sum, ← mul_assoc x g]
    rw [sum_sphericalFun_gMat (μ := μ)]
    ring
  simp only [zonalSpherical, ← Finset.mul_sum]
  rw [e1]
  simp_rw [e2]
  rw [integral_const_mul]
  ring

theorem zonalSpherical_recursion (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ}
    (hr : r ≤ n) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * zonalSpherical μ z (torusPow F n l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * zonalSpherical μ z (torusPow F n (l + lamS S)) := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 := sum_zonalSpherical_gMat (μ := μ) z r (torusPow F n l)
  rw [evalAt_satakeTransform_minusculeHecke z hr] at h1
  rw [← Finset.sum_congr rfl fun S _ => sum_gMat_torusPow (f := zonalSpherical μ z)
    (fun u hu g => zonalSpherical_mul_left z hu.2 g) hl S, h1]
  field_simp

theorem recursion_of_integral_eq (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hfK : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hfN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g)
    {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ} (hr : r ≤ n)
    (heig : ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * f (torusPow F n l * x) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * f (torusPow F n l)) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f (torusPow F n l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rw [integral_minusculeHecke_mul hfK, evalAt_satakeTransform_minusculeHecke z hr] at heig
  rw [← Finset.sum_congr rfl fun S _ => sum_gMat_torusPow hfN hl S]
  apply mul_left_cancel₀ hK
  rw [heig]
  ring

end Spherical

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.MacdonaldNormalization
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra Finset

variable {n : ℕ}

def vPoly (m : ℕ) (t : ℂ) : ℂ := ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) / (1 - t)

theorem alternant_comp (μ : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    alternant (μ ∘ σ) = Equiv.Perm.sign σ • alternant μ := by
  have : monomial (μ ∘ σ) = permAct σ⁻¹ (monomial μ) := by
    rw [permAct_monomial]
    rfl
  rw [alternant, this, antisymm_permAct, Equiv.Perm.sign_inv]
  rfl

theorem exists_alternant_eq_smul {ν : Fin n → ℤ} (h0 : ∀ i, 0 ≤ ν i) (h1 : ∀ i, ν i ≤ n - 1) :
    ∃ c : ℂ, alternant ν = c • alternant (staircase n) := by
  by_cases hinj : Function.Injective ν
  · let f : Fin n → Fin n := fun i => ⟨n - 1 - (ν i).toNat, by
      have := h1 i; have := h0 i; have := i.2; omega⟩
    have hf : ∀ i, staircase n (f i) = ν i := by
      intro i
      simp only [staircase, f]
      have := h1 i; have := h0 i; have := i.2
      omega
    have hfi : Function.Injective f := fun i j h => hinj (by rw [← hf i, ← hf j, h])
    let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
    have hν : ν = staircase n ∘ σ := funext fun i => (hf i).symm
    refine ⟨((Equiv.Perm.sign σ : ℤ) : ℂ), ?_⟩
    rw [hν, alternant_comp, Units.smul_def, Int.cast_smul_eq_zsmul]
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact ⟨0, by rw [zero_smul, alternant_eq_zero hne hij]⟩

theorem card_pairs_containing_le (i : Fin n) :
    ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
      (fun p => p.1 = i ∨ p.2 = i)).card ≤ n - 1 := by
  classical
  let g : Fin n → Fin n × Fin n := fun j => if i < j then (i, j) else (j, i)
  have hsub : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
      (fun p => p.1 = i ∨ p.2 = i) ⊆ (Finset.univ.erase i).image g := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hlt, h | h⟩ := hp
    · refine Finset.mem_image.2 ⟨p.2, Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_univ _⟩, ?_⟩
      · rw [h, h'] at hlt
        exact lt_irrefl _ hlt
      · simp only [g, ← h, if_pos hlt]
    · refine Finset.mem_image.2 ⟨p.1, Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_univ _⟩, ?_⟩
      · rw [h, h'] at hlt
        exact lt_irrefl _ hlt
      · simp only [g, ← h, if_neg (not_lt.2 hlt.le)]
  calc _ ≤ ((Finset.univ.erase i).image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase i).card := Finset.card_image_le
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

theorem coeff_prod_ne_zero (t : ℂ) (s : Finset (Fin n × Fin n)) :
    ∀ ν, (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff ν ≠ 0 →
      ∀ i, 0 ≤ ν i ∧ ν i ≤ (s.filter (fun p => p.1 = i ∨ p.2 = i)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ν hν i
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply] at hν
    split_ifs at hν with h
    · subst h
      simp
    · exact absurd rfl hν
  | insert a s ha ih =>
    intro ν hν i
    rw [Finset.prod_insert ha, sub_mul, smul_mul_assoc, AddMonoidAlgebra.coeff_sub,
      AddMonoidAlgebra.coeff_smul, Finsupp.sub_apply, Finsupp.smul_apply, varL, varL, monomial,
      monomial, AddMonoidAlgebra.coeff_single_mul_apply, AddMonoidAlgebra.coeff_single_mul_apply,
      one_mul, one_mul, smul_eq_mul] at hν
    have hcard : ((insert a s).filter (fun p => p.1 = i ∨ p.2 = i)).card =
        (if a.1 = i ∨ a.2 = i then 1 else 0) + (s.filter (fun p => p.1 = i ∨ p.2 = i)).card := by
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.1 h').1), add_comm]
      · simp
    rw [hcard]
    by_cases h1 : (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff (-Pi.single a.1 1 + ν) ≠ 0
    · have := ih _ h1 i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply] at this
      split_ifs at this ⊢ with h2 h3 h3 <;> simp_all <;> omega
    · push Not at h1
      rw [h1, zero_sub] at hν
      have h1' : (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff (-Pi.single a.2 1 + ν) ≠ 0 := by
        intro h
        rw [h, mul_zero, neg_zero] at hν
        exact hν rfl
      have := ih _ h1' i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply] at this
      split_ifs at this ⊢ with h2 h3 h3 <;> simp_all <;> omega

theorem coeff_hlFactor_ne_zero (t : ℂ) {ν : Fin n → ℤ} (hν : (hlFactor n t).coeff ν ≠ 0) (i : Fin n) :
    0 ≤ ν i ∧ ν i ≤ n - 1 := by
  have := coeff_prod_ne_zero t _ ν hν i
  refine ⟨this.1, this.2.trans ?_⟩
  have := card_pairs_containing_le i
  have hn : 0 < n := Fin.pos i
  omega

theorem exists_antisymm_hlFactor_eq (t : ℂ) :
    ∃ c : ℂ, antisymm n (hlFactor n t) = c • alternant (staircase n) := by
  classical
  have key : ∀ ν ∈ (hlFactor n t).coeff.support, ∃ c : ℂ,
      antisymm n (single ν ((hlFactor n t).coeff ν)) = c • alternant (staircase n) := by
    intro ν hν
    have hb := coeff_hlFactor_ne_zero t (Finsupp.mem_support_iff.1 hν)
    obtain ⟨c, hc⟩ := exists_alternant_eq_smul (fun i => (hb i).1) (fun i => (hb i).2)
    refine ⟨(hlFactor n t).coeff ν * c, ?_⟩
    have : (single ν ((hlFactor n t).coeff ν) : LaurentRing n) =
        (hlFactor n t).coeff ν • monomial ν := by
      simp [monomial, smul_single']
    rw [this, map_smul, ← alternant, hc, smul_smul]
  choose c hc using key
  refine ⟨∑ ν ∈ (hlFactor n t).coeff.support.attach, c ν.1 ν.2, ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (hlFactor n t)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum, Finset.sum_smul, ← Finset.sum_attach]
  exact Finset.sum_congr rfl fun ν _ => hc ν.1 ν.2

theorem evalAt_varL (w : Fin n → ℂˣ) (a : Fin n) : evalAt w (varL a) = w a := by
  rw [varL, monomial, evalAt_single, one_mul, monomialChar_apply,
    Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun h => absurd (Finset.mem_univ a) h)]
  simp

theorem evalAt_hlFactor (w : Fin n → ℂˣ) (t : ℂ) :
    evalAt w (hlFactor n t) = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 < p.2), ((w p.1 : ℂ) - t * w p.2) := by
  rw [hlFactor, map_prod]
  simp only [map_sub, map_smul, evalAt_varL, smul_eq_mul]

theorem evalAt_antisymm (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w (antisymm n p) = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (w ∘ σ) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [antisymm_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, evalAt_permAct, zsmul_eq_mul]

theorem alternant_staircase_eq_vdm (hn : 0 < n) :
    alternant (staircase n) =
      vdm.det * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : LaurentRing n) := by
  rw [staircase_eq_natCast, alternant_natCast_eq hn, remMat_staircase hn, Matrix.det_permutation]

theorem evalAt_vdm_det (w : Fin n → ℂˣ) :
    evalAt w vdm.det = (Matrix.vandermonde fun i => (w i : ℂ)).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [vdm, Matrix.of_apply, Matrix.vandermonde_apply, AlgHom.coe_toRingHom]
  rw [map_pow, evalAt_varL]

theorem strictMono_of_forall_succ_lt {f : Fin n → Fin n}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f i < f j) : StrictMono f := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → f a < f b := by
    intro d
    induction d with
    | zero => exact fun a b hab => h a b (by omega)
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d + 1 < n := by omega
      exact (ih a ⟨a + d + 1, hc⟩ rfl).trans (h _ b (by simp only; omega))
  intro a b hab
  exact key (b - a - 1) a b (by have := Fin.lt_def.1 hab; omega)

theorem eq_one_of_strictMono {τ : Equiv.Perm (Fin n)} (hτ : StrictMono τ) : τ = 1 := by
  have hinv : StrictMono τ.symm := by
    intro a b hab
    by_contra h
    rw [not_lt] at h
    have := hτ.monotone h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hab (not_lt.2 this)
  ext i
  have h1 : i ≤ τ i := hτ.le_apply
  have h2 : i ≤ τ.symm i := hinv.le_apply
  have h3 : τ i ≤ i := by
    have := hτ.monotone h2
    rwa [Equiv.apply_symm_apply] at this
  simp [le_antisymm h3 h1]

theorem exists_succ_of_ne_rev {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ Fin.revPerm) :
    ∃ a b : Fin n, a < b ∧ (σ b : ℕ) = σ a + 1 := by
  by_contra hne
  push Not at hne
  apply hσ

  have hmono : StrictMono (Fin.revPerm * σ⁻¹ : Equiv.Perm (Fin n)) := by
    refine strictMono_of_forall_succ_lt fun i j hij => ?_
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
    rcases lt_trichotomy (σ⁻¹ j) (σ⁻¹ i) with h | h | h
    · exact h
    · exact absurd (σ⁻¹.injective h) (fun h' => by rw [h'] at hij; omega)
    · have := hne _ _ h
      rw [show σ (σ⁻¹ j) = j from σ.apply_symm_apply j,
        show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at this
      omega
  have := eq_one_of_strictMono hmono
  rw [mul_eq_one_iff_eq_inv, inv_inv] at this
  rw [← this]

def revPoint (t : ℂ) (ht : t ≠ 0) : Fin n → ℂˣ := fun i => Units.mk0 (t ^ (n - 1 - (i : ℕ))) (pow_ne_zero _ ht)

theorem prod_one_sub_pow_shift (t : ℂ) (m : ℕ) :
    (∏ k ∈ Finset.range m, (1 - t ^ (k + 2))) * (1 - t) =
      (1 - t ^ (m + 1)) * ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_right_comm, ih]
    ring

theorem prod_pow_sub_pow_succ_mul (t : ℂ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1))) * (1 - t) =
      (1 - t ^ (m + 1)) * ∏ i ∈ Finset.range m, (t ^ i - t ^ m) := by
  have e1 : ∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1)) =
      (∏ i ∈ Finset.range m, t ^ i) * ∏ i ∈ Finset.range m, (1 - t ^ (m - 1 - i + 2)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  have e2 : ∏ i ∈ Finset.range m, (t ^ i - t ^ m) =
      (∏ i ∈ Finset.range m, t ^ i) * ∏ i ∈ Finset.range m, (1 - t ^ (m - 1 - i + 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [e1, e2, Finset.prod_range_reflect (fun k => 1 - t ^ (k + 2)) m,
    Finset.prod_range_reflect (fun k => 1 - t ^ (k + 1)) m, mul_assoc, prod_one_sub_pow_shift]
  ring

theorem vPoly_mul_pow (t : ℂ) (ht : t ≠ 1) (m : ℕ) :
    vPoly m t * (1 - t) ^ m = ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) := by
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  rw [vPoly, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    div_mul_cancel₀ _ (pow_ne_zero _ h1)]

theorem prod_pairs_pow_sub_eq_vPoly_mul (t : ℂ) (ht : t ≠ 1) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1)) =
      vPoly m t * ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) := by
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  refine mul_right_cancel₀ (pow_ne_zero m h1) ?_
  rw [mul_right_comm, vPoly_mul_pow t ht]
  induction m with
  | zero => simp
  | succ m ih =>
    have htel := prod_pow_sub_pow_succ_mul t m
    rw [Finset.prod_range_succ (fun j => ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1))),
      Finset.prod_range_succ (fun k => 1 - t ^ (k + 1)),
      Finset.prod_range_succ (fun j => ∏ i ∈ Finset.range j, (t ^ i - t ^ j)), pow_succ (1 - t) m]
    calc _ = ((∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1))) * (1 - t) ^ m) *
          ((∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1))) * (1 - t)) := by ring
      _ = _ := by rw [ih, htel]; ring

theorem prod_pairs_eq_range (g : ℕ → ℕ → ℂ) :
    ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.1 p.2 =
      ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, g i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  rw [← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ Finset.range j, g i j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  dsimp only
  calc (∏ x : Fin n, if x < j then g x j else 1)
      = ∏ x : Fin n, (fun i : ℕ => if i < (j : ℕ) then g i j else 1) x :=
        Finset.prod_congr rfl fun x _ => by simp only [Fin.lt_def]
    _ = ∏ i ∈ Finset.range n, (if i < (j : ℕ) then g i j else 1) :=
        Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < (j : ℕ) then g i j else 1) n
    _ = ∏ i ∈ Finset.range j, g i j := by
        rw [← Finset.prod_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        have := j.2
        omega

theorem hlR_zero (t : ℂ) (ht : Function.Injective fun k : ℕ => t ^ k) :
    hlR t (0 : Fin n → ℤ) = algebraMap ℂ (LaurentRing n) (vPoly n t) := by
  have ht0 : t ≠ 0 := fun h => by
    have := @ht 1 2 (by simp [h])
    omega
  have ht1 : t ≠ 1 := fun h => by
    have := @ht 0 1 (by simp [h])
    omega
  have hne : ∀ a b : ℕ, a ≠ b → t ^ a - t ^ b ≠ 0 := fun a b h h' => h (ht (sub_eq_zero.1 h'))
  obtain ⟨c, hc⟩ := exists_antisymm_hlFactor_eq (n := n) t
  have hR : hlR t (0 : Fin n → ℤ) = algebraMap ℂ (LaurentRing n) c := by
    rw [hlR, show (monomial (0 : Fin n → ℤ) : LaurentRing n) = 1 from rfl, one_mul]
    refine altQuot_eq_of_mul ?_
    rw [hc, Algebra.smul_def, mul_comm]
  rw [hR]
  congr 1
  rcases n.eq_zero_or_pos with hn | hn
  · subst hn

    have hδ : alternant (staircase 0) = 1 := by
      rw [alternant, antisymm_apply, Fintype.sum_unique]
      simp only [Equiv.Perm.default_eq, Equiv.Perm.sign_one, one_smul]
      rw [permAct_one, AlgHom.id_apply,
        show staircase 0 = (0 : Fin 0 → ℤ) from funext fun i => i.elim0]
      rfl
    have hD : hlFactor 0 t = 1 := by
      rw [hlFactor]
      exact Finset.prod_eq_one fun p _ => p.1.elim0
    rw [hD, hδ, antisymm_apply, Fintype.sum_unique] at hc
    simp only [Equiv.Perm.sign_one, one_smul, map_one] at hc
    rw [vPoly, Finset.range_zero, Finset.prod_empty]
    have := congrArg (fun p : LaurentRing 0 => p.coeff 0) hc
    simp [AddMonoidAlgebra.one_def] at this
    exact this.symm

  set z : Fin n → ℂˣ := revPoint t ht0 with hz
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) with hP
  have hzv : ∀ k : Fin n, (z k : ℂ) = t ^ (n - 1 - (k : ℕ)) := fun k => rfl
  have hev := congrArg (evalAt z) hc
  rw [evalAt_antisymm, map_smul, alternant_staircase_eq_vdm hn, map_mul, map_intCast,
    evalAt_vdm_det, smul_eq_mul] at hev
  rw [Finset.sum_eq_single (Fin.revPerm : Equiv.Perm (Fin n))] at hev
  ·
    rw [evalAt_hlFactor] at hev
    have hA : ∏ p ∈ P, (((z ∘ Fin.revPerm) p.1 : ℂ) - t * (z ∘ Fin.revPerm) p.2) =
        ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1)) := by
      rw [← prod_pairs_eq_range (n := n) (fun i j => t ^ i - t ^ (j + 1))]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [Function.comp_apply, hzv, Fin.revPerm_apply, Fin.val_rev]
      rw [← pow_succ']
      congr 2 <;> omega
    have hV : (Matrix.vandermonde fun i => (z i : ℂ)).det =
        ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) := by
      rw [Matrix.det_vandermonde, ← prod_pairs_eq_range (n := n) (fun i j => t ^ i - t ^ j)]
      rw [show (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((z j : ℂ) - z i)) =
          ∏ p ∈ P, ((z p.2 : ℂ) - z p.1) by
        rw [hP, Finset.prod_filter, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_filter]
        congr 1
        ext j
        simp]
      refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1))
        ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Fin.rev_lt_rev.2 hp
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Fin.rev_lt_rev.2 hp
      · intro p _
        simp
      · intro p _
        simp
      · intro p _
        simp only [hzv, Fin.val_rev]
        congr 2 <;> omega
    rw [hA, hV] at hev
    have hs : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
        simp [h]
    have hVne : ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i hi =>
        hne i j (by have := Finset.mem_range.1 hi; omega)
    rw [prod_pairs_pow_sub_eq_vPoly_mul t ht1] at hev
    set V := ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j)
    have h2 : (vPoly n t * V) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) =
        (c * V) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) := by
      rw [mul_comm _ ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ), hev]
      ring
    exact (mul_right_cancel₀ hVne (mul_right_cancel₀ hs h2)).symm
  ·
    intro σ _ hσ
    obtain ⟨a, b, hab, hσab⟩ := exists_succ_of_ne_rev hσ
    rw [evalAt_hlFactor, Finset.prod_eq_zero (i := (a, b)) (by simp [hP, hab]), mul_zero]
    simp only [Function.comp_apply, hzv]
    rw [← pow_succ']
    have := (σ b).2
    rw [show n - 1 - (σ b : ℕ) + 1 = n - 1 - (σ a : ℕ) by omega, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Spherical

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem vPoly_ne_zero {t : ℂ} (ht : Function.Injective fun k : ℕ => t ^ k) (m : ℕ) :
    vPoly m t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero ?_ ?_
  · intro h
    have h' : t ^ (k + 1) = t ^ 0 := by rw [pow_zero]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega
  · intro h
    have h' : t ^ 1 = t ^ 0 := by rw [pow_zero, pow_one]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega

theorem injective_qInv_pow : Function.Injective fun k : ℕ => ((qF F : ℂ))⁻¹ ^ k := by
  have hq : 1 < qF F := Finite.one_lt_card
  have hpos : (0 : ℝ) < (qF F : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast qF_pos)
  have hne : (qF F : ℝ)⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one] at h
    have : (1 : ℝ) < qF F := by exact_mod_cast hq
    linarith
  intro a b hab
  apply pow_right_injective₀ hpos hne
  apply Complex.ofReal_injective
  simp only at hab ⊢
  push_cast
  exact hab

theorem halfModulus_mul_recursion (Q : (Fin n → ℤ) → LaurentRing n)
    (hQ : ∀ r l, esymmL n r * Q l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, Q (l + lamS S))
    (z : Fin n → ℂˣ) {r : ℕ} (hr : r ≤ n) (l : Fin n → ℤ) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * (halfModulus F l * evalAt z (Q l)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * (halfModulus F (l + lamS S) * evalAt z (Q (l + lamS S))) := by
  have h1 : evalAt z (esymmL n r) * evalAt z (Q l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, evalAt z (Q (l + lamS S)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, hQ, map_sum]
  calc _ = sqrtQ F ^ (r * (n - r)) * halfModulus F l * (evalAt z (esymmL n r) * evalAt z (Q l)) := by
        ring
    _ = _ := by
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [halfModulus_add, ← kappa_mul_halfModulus hr (Finset.mem_powersetCard.1 hS).2]
        ring

theorem rhoPair_add (a b : Fin n → ℤ) : rhoPair (a + b) = rhoPair a + rhoPair b := by
  simp only [rhoPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rhoPair_neg (a : Fin n → ℤ) : rhoPair (-a) = -rhoPair a := by
  simp only [rhoPair, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem rhoPair_comp_swap {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : rhoPair (μ ∘ Equiv.swap i j) = rhoPair μ + 2 := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hs : μ ∘ Equiv.swap i j = μ + (Pi.single i 1 + -Pi.single j 1) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply,
      Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> omega
  rw [hs, rhoPair_add, rhoPair_add, rhoPair_neg, rhoPair_single, rhoPair_single]
  push_cast [hij]
  ring

theorem halfModulus_hlR_swap (z : Fin n → ℂˣ) {μ : Fin n → ℤ} {i j : Fin n}
    (hij : (j : ℕ) = i + 1) (hμ : μ j = μ i + 1) :
    halfModulus F (μ ∘ Equiv.swap i j) * evalAt z (hlR ((qF F : ℂ))⁻¹ (μ ∘ Equiv.swap i j)) =
      halfModulus F μ * evalAt z (hlR ((qF F : ℂ))⁻¹ μ) := by
  rw [hlR_swap _ hij hμ, map_smul, smul_eq_mul, halfModulus_eq, halfModulus_eq,
    rhoPair_comp_swap hij hμ, neg_add, zpow_add₀ sqrtQ_ne_zero, ← sqrtQ_sq]
  rw [show (sqrtQ F) ^ (-2 : ℤ) = ((sqrtQ F) ^ 2)⁻¹ by rw [_root_.zpow_neg]; norm_cast]
  ring

theorem evalAt_esymmL_self_ne_zero (z : Fin n → ℂˣ) : evalAt z (esymmL n n) ≠ 0 := by
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [evalAt_esymmL, hp, Finset.sum_singleton, monomialChar_apply]
  exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem schur_zero : schur (0 : Fin n → ℤ) = 1 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_one, zero_add]
  rfl

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem macdonald_formula_hlR (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) :
    vPoly n ((qF F : ℂ))⁻¹ * zonalSpherical μ z (torusPow F n l) =
      halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l) := by
  set t : ℂ := ((qF F : ℂ))⁻¹
  set f : (Fin n → ℤ) → ℂ := fun m =>
    vPoly n t * zonalSpherical μ z (torusPow F n m) - halfModulus F m * evalAt z (hlR t m) with hf
  have hswap : ∀ (m : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → m j = m i + 1 →
      f (m ∘ Equiv.swap i j) = f m := by
    intro m i j hij hm
    simp only [hf]
    rw [zonalSpherical_torusPow_comp, halfModulus_hlR_swap z hij hm]
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := zonalSpherical_recursion (μ := μ) z hm hr
      have h2 := halfModulus_mul_recursion (F := F) (hlR t) (fun r l => esymmL_mul_hlR t r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = vPoly n t * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              zonalSpherical μ z (torusPow F n m)) -
            sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (hlR t m)) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (fun m hm S => Or.inr (by
      obtain ⟨σ, hσ, hfσ⟩ := exists_perm_antitone f hswap hm S
      exact ⟨σ, hσ, hfσ.symm⟩))
    (by
      simp only [hf, torusPow_zero, zonalSpherical_one, halfModulus_zero, one_mul, mul_one]
      rw [hlR_zero t injective_qInv_pow, AlgHom.commutes]
      simp)
  exact sub_eq_zero.1 (key l hl)

theorem casselman_shalika (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (l : Fin n → ℤ) :
    W (torusPow F n l) = if Antitone l then W 1 * halfModulus F l * evalAt z (schur l) else 0 := by
  split_ifs with hl
  swap
  · exact eq_zero_of_not_antitone hψ₁ hWN hWK hl
  have hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, W (u * g) = W g := by
    intro u hu g
    rw [hWN u hu.1, psiN_eq_one_of_mem hψ₀ hu, one_mul]
  set f : (Fin n → ℤ) → ℂ := fun m =>
    W (torusPow F n m) - W 1 * (halfModulus F m * evalAt z (schur m)) with hf
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := recursion_of_integral_eq (μ := μ) z hWK hN hm hr (heig _ _)
      have h2 := halfModulus_mul_recursion (F := F) schur (fun r l => esymmL_mul_schur r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * W (torusPow F n m) -
            W 1 * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (schur m))) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (by
      intro m hm S
      by_cases hant : Antitone (m + lamS S)
      · exact Or.inr ⟨1, by simpa using hant, by simp⟩
      · left
        obtain ⟨i, j, hij, hmij, hiS, hjS⟩ := exists_ascent hm hant
        have hasc : (m + lamS S) j = (m + lamS S) i + 1 := by
          simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hmij]
          ring
        simp only [hf]
        rw [eq_zero_of_not_antitone hψ₁ hWN hWK hant, schur_eq_zero_of_ascent hij hasc, map_zero,
          mul_zero, mul_zero, sub_zero])
    (by simp only [hf, torusPow_zero, halfModulus_zero, schur_zero, map_one, mul_one, sub_self])
  have := key l hl
  simp only [hf] at this
  rw [mul_assoc]
  exact sub_eq_zero.1 this

end Spherical

end GroundTheory.Automorphic
