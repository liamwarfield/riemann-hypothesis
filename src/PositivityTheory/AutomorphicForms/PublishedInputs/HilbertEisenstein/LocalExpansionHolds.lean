module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CharacterPositiveHolds
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CharacterProductHolds

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.InverseSubstitutionHolds
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SecondCountableTopologyUnits
noncomputable section

open MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance secondCountableTopology_units : SecondCountableTopology Kˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

instance sigmaCompactSpace_units : SigmaCompactSpace Kˣ := inferInstance

instance regular_multHaar : (multHaar K).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance isInvInvariant_multHaar : (multHaar K).IsInvInvariant :=
  Measure.IsHaarMeasure.isInvInvariant_of_regular (multHaar K)

theorem inv_subst (f : Kˣ → ℂ) (t : Kˣ) :
    (Integrable f (multHaar K) ↔ Integrable (fun x => f (t * x⁻¹)) (multHaar K)) ∧
    ∫ a, f a ∂multHaar K = ∫ x, f (t * x⁻¹) ∂multHaar K := by
  have h1 : (fun x => f (t * x⁻¹)) = fun x => f (t / x) := by
    funext x
    rw [div_eq_mul_inv]
  rw [h1]
  exact ⟨(integrable_comp_div_left f t).symm, (integral_div_left_eq_self f (multHaar K) t).symm⟩

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse
end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem inverse_substitution_holds : InvSubst := by
  intro F _ _ v f t
  exact MultiplicativeHaarInverse.inv_subst f t

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CoefficientDivisorHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

variable {F : Type} [Field F] [NumberField F]

theorem ordI_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : ordI v w.asIdeal = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
  exact h (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))

theorem ordI_top (v : HeightOneSpectrum (𝓞 F)) : ordI v (⊤ : Ideal (𝓞 F)) = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
  exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))

open Classical in
theorem ordI_pow (v w : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    ordI v (w.asIdeal ^ k) = if v = w then k else 0 := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, ordI_top]; split_ifs <;> rfl
  | succ k ih =>
    rw [pow_succ, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ w.ne_bot) w.ne_bot, ih]
    by_cases h : v = w
    · rw [if_pos h, if_pos h, h, Fresh.ordI_asIdeal_self]
    · rw [if_neg h, if_neg h, ordI_ne h]

theorem prodS_ne_bot (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ w ∈ T, w.asIdeal ^ p w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro w _
  exact pow_ne_zero _ w.ne_bot

open Classical in
theorem ordI_prodS (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : ordI v (∏ w ∈ T, w.asIdeal ^ p w) = if v ∈ T then p v else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, ordI_top]; simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ a.ne_bot) (prodS_ne_bot T p), ordI_pow, ih]
    by_cases h1 : v = a
    · subst h1
      simp [ha]
    · by_cases h2 : v ∈ T
      · simp [h1, h2]
      · simp [h1, h2]

theorem eq_of_ordI {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w : HeightOneSpectrum (𝓞 F), ordI w I = ordI w J) :
    I = J := by
  classical
  have key : Associates.mk I = Associates.mk J := by
    refine Associates.eq_of_eq_counts (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) fun p hp => ?_
    obtain ⟨P, rfl⟩ := Associates.exists_rep p
    have hP : Irreducible P := Associates.irreducible_mk.1 hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP.prime, hP.ne_zero⟩
    have := h v
    unfold ordI at this
    convert this using 2
  exact associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 key)

theorem ordI_le_of_dvd {r m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (h : r ∣ m) (w : HeightOneSpectrum (𝓞 F)) :
    ordI w r ≤ ordI w m := by
  obtain ⟨s, rfl⟩ := h
  have hr : r ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.bot_mul])
  have hs : s ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
  rw [Fresh.ordI_mul_of_ne_bot w hr hs]
  exact Nat.le_add_right _ _

theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})


open Classical in
def ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℕ :=
  if h : w ∈ S then p ⟨w, h⟩ else 0

theorem ordI_prod_ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ordI v (∏ w ∈ S, w.asIdeal ^ ext S p w) = ext S p v := by
  classical
  rw [ordI_prodS]
  unfold ext
  split_ifs <;> rfl

theorem divS_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ w ∉ S, ordI w m = 0) :
    divS ω c m = ∏ w ∈ S, ∑ j ∈ Finset.range (ordI w m + 1), L4.chiW ω c w ^ j := by
  classical
  rw [← Finset.prod_coe_sort S, Finset.prod_univ_sum]
  unfold divS
  rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm)]
  symm
  refine Finset.sum_nbij' (fun p => ∏ w ∈ S, w.asIdeal ^ ext S p w) (fun r => fun w : S => ordI w.1 r) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hp' : ∀ w : S, p w ≤ ordI w.1 m := fun w => by
      have := Fintype.mem_piFinset.1 hp w
      rw [Finset.mem_range] at this
      omega
    refine ⟨∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w), ?_⟩
    have hne : (∏ w ∈ S, w.asIdeal ^ ext S p w) * (∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w)) ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨prodS_ne_bot _ _, prodS_ne_bot _ _⟩
    refine eq_of_ordI hm hne fun v => ?_
    rw [Fresh.ordI_mul_of_ne_bot v (prodS_ne_bot _ _) (prodS_ne_bot _ _), ordI_prod_ext, ordI_prodS]
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have h1 : ext S p v = p ⟨v, hv⟩ := by unfold ext; rw [dite_eq_left hv]
      have h2 : p ⟨v, hv⟩ ≤ ordI v m := hp' ⟨v, hv⟩
      rw [h1]
      omega
    · rw [if_neg hv, hS v hv]
      unfold ext
      rw [dite_eq_right hv]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    rw [Fintype.mem_piFinset]
    intro w
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (ordI_le_of_dvd hm hr w)
  · intro p _
    funext w
    rw [ordI_prod_ext]
    unfold ext
    rw [dite_eq_left w.2]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    have hr0 : r ≠ ⊥ := fun h0 => hm (by rw [h0] at hr; exact zero_dvd_iff.1 hr)
    refine eq_of_ordI (prodS_ne_bot _ _) hr0 fun v => ?_
    rw [ordI_prod_ext]
    unfold ext
    split_ifs with hv
    · rfl
    · have := ordI_le_of_dvd hm hr v
      rw [hS v hv] at this
      omega
  · intro p _
    unfold chiI
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [ordI_prod_ext]
      unfold ext L4.chiW
      rw [dite_eq_left w.2]
    · intro v hv
      by_contra hvS
      apply hv
      beta_reduce
      rw [ordI_prod_ext]
      unfold ext
      rw [dite_eq_right fun h => hvS (Finset.mem_coe.2 h), pow_zero]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open DivisorSumOrder

theorem coefficient_divisor_holds : CoefDiv := by
  intro F _ _ _ ω c z m S hz hS
  classical
  unfold coefAt
  by_cases hpos : ∀ w ∈ S, 0 ≤ m w
  · rw [if_pos hpos]
    have hex : ∃ 𝔪, GenD z 𝔪 := by
      refine ⟨∏ w ∈ S, w.asIdeal ^ (m w).toNat, prodS_ne_bot _ _, fun w => ?_⟩
      rw [hz w, ordI_prodS]
      congr 1
      by_cases hw : w ∈ S
      · rw [if_pos hw, Int.toNat_of_nonneg (hpos w hw)]; rfl
      · rw [if_neg hw, hS w hw]; rfl
    rw [dite_eq_left hex]
    have hspec := hex.choose_spec
    set 𝔪 := hex.choose
    have hord : ∀ w, (ordI w 𝔪 : ℤ) = m w := by
      intro w
      have h := (hspec.2 w).symm.trans (hz w)
      rw [WithZero.exp_inj] at h
      unfold dd at h
      omega
    rw [divS_eq ω c hspec.1 S fun w hw => by have := hord w; rw [hS w hw] at this; omega]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 2
    have := hord w
    omega
  · rw [if_neg hpos, dite_eq_right]
    rintro ⟨𝔪, -, h𝔪⟩
    apply hpos
    intro w _
    have h := (h𝔪 w).symm.trans (hz w)
    rw [WithZero.exp_inj] at h
    unfold dd at h
    omega

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchimedeanIntegralHolds
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Set Filter
open GroundTheory.Global GroundTheory.Global.IdeleGroup InfinitePlace InfinitePlace.Completion Formalism.L2.Host UpperTheory.V.Sd

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalArchimedeanIntegral

theorem gauss_split {y M x : ℝ} (hx : x ≠ 0) :
    (x * y) ^ 2 + (M / x) ^ 2 = (x * y - M / x) ^ 2 + 2 * M * y := by
  field_simp
  ring

def phiP (y M : ℝ) (x : ℝ) : ℝ := x * y - M / x

theorem hasDerivAt_phiP (y M : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (phiP y M) (y + M / x ^ 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x * y) y x := by simpa using (hasDerivAt_id x).mul_const y
  have h2 : HasDerivAt (fun x : ℝ => M * x⁻¹) (M * -(x ^ 2)⁻¹) x := (hasDerivAt_inv hx).const_mul M
  have e1 : phiP y M = fun t => t * y - M * t⁻¹ := by
    funext t; simp only [phiP, div_eq_mul_inv]
  rw [e1]
  exact (h1.sub h2).congr_deriv (by rw [div_eq_mul_inv]; ring)

theorem phiP_strictMonoOn {y M : ℝ} (hy : 0 < y) (hM : 0 < M) : StrictMonoOn (phiP y M) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  simp only [phiP]
  have h1 : a * y < b * y := mul_lt_mul_of_pos_right hab hy
  have h2 : M / b < M / a := div_lt_div_of_pos_left hM ha hab
  linarith

theorem phiP_image {y M : ℝ} (hy : 0 < y) (hM : 0 < M) : phiP y M '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  set s := Real.sqrt (u ^ 2 + 4 * M * y)
  have hs0 : 0 ≤ u ^ 2 + 4 * M * y := by positivity
  have hs2 : s ^ 2 = u ^ 2 + 4 * M * y := Real.sq_sqrt hs0
  have hsu : |u| < s := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hpos : 0 < (u + s) / (2 * y) := by
    apply div_pos _ (by positivity)
    have := neg_abs_le u
    linarith
  refine ⟨(u + s) / (2 * y), hpos, ?_⟩
  simp only [phiP]
  have hne : (u + s) / (2 * y) ≠ 0 := hpos.ne'
  field_simp
  have hus : u + s ≠ 0 := by
    intro h
    have := neg_abs_le u
    linarith
  field_simp
  nlinarith [hs2]

theorem integral_plus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    ∫ x in Ioi (0 : ℝ), (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) =
      Real.exp (-2 * Real.pi * M * y) := by
  have h1 : ∀ x ∈ Ioi (0 : ℝ), (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) =
      Real.exp (-2 * Real.pi * M * y) * (|y + M / x ^ 2| • Real.exp (-Real.pi * (phiP y M x) ^ 2)) := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.1 hx).ne'
    rw [gauss_split hx0, abs_of_pos (by positivity), smul_eq_mul, phiP]
    rw [show -Real.pi * ((x * y - M / x) ^ 2 + 2 * M * y) = -2 * Real.pi * M * y + -Real.pi * (x * y - M / x) ^ 2 by ring,
      Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul]
  have h2 := integral_image_eq_integral_abs_deriv_smul (f := phiP y M) (f' := fun x => y + M / x ^ 2)
    (s := Ioi 0) measurableSet_Ioi (fun x hx => (hasDerivAt_phiP y M (mem_Ioi.1 hx).ne').hasDerivWithinAt)
    (phiP_strictMonoOn hy hM).injOn (fun u => Real.exp (-Real.pi * u ^ 2))
  rw [← h2, phiP_image hy hM, Measure.restrict_univ, integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one,
    mul_one]

theorem integrableOn_plus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    IntegrableOn (fun x : ℝ => (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_plus hy hM]
  exact (Real.exp_pos _).ne'

def psiP (y M : ℝ) (x : ℝ) : ℝ := M / y / x

theorem integral_minus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    ∫ x in Ioi (0 : ℝ), (y - M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) = 0 := by
  set G : ℝ → ℝ := fun x => Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) with hG
  have hP := integrableOn_plus hy hM
  have hGi : IntegrableOn G (Ioi 0) := by
    refine (hP.div_const y).mono' ?_ ?_
    · exact (by fun_prop : Measurable G).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [le_div_iff₀ hy]
      have : 0 ≤ M / x ^ 2 := by positivity
      nlinarith [Real.exp_pos (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))]
  have hG2i : IntegrableOn (fun x => M / x ^ 2 * G x) (Ioi 0) := by
    refine hP.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun x => M / x ^ 2 * G x).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hx
      have h0 : 0 ≤ M / x ^ 2 * G x := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have := Real.exp_pos (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))
      simp only [hG]
      nlinarith

  have hsub : ∫ x in Ioi (0 : ℝ), G x = ∫ x in Ioi (0 : ℝ), M / y / x ^ 2 * G x := by
    have hc : 0 < M / y := div_pos hM hy
    have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (psiP y M) (-(M / y / x ^ 2)) (Ioi 0) x := by
      intro x hx
      have hx0 : x ≠ 0 := (mem_Ioi.1 hx).ne'
      have h2 : HasDerivAt (fun t : ℝ => M / y * t⁻¹) (M / y * -(x ^ 2)⁻¹) x := (hasDerivAt_inv hx0).const_mul (M / y)
      have e1 : psiP y M = fun t => M / y * t⁻¹ := by
        funext t; simp only [psiP, div_eq_mul_inv]
      rw [e1]
      exact (h2.congr_deriv (by rw [div_eq_mul_inv (M / y)]; ring)).hasDerivWithinAt
    have hinj : InjOn (psiP y M) (Ioi 0) := by
      intro a ha b hb hab
      have h1 : M / y / a = M / y / b := hab
      have ha0 : a ≠ 0 := (mem_Ioi.1 ha).ne'
      have hb0 : b ≠ 0 := (mem_Ioi.1 hb).ne'
      rw [div_eq_div_iff ha0 hb0] at h1
      exact (mul_left_cancel₀ hc.ne' h1).symm
    have him : psiP y M '' Ioi 0 = Ioi 0 := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact div_pos hc hx
      · intro hu
        refine ⟨M / y / u, div_pos hc hu, ?_⟩
        simp only [psiP]
        field_simp
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj G
    rw [him] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [abs_neg, abs_of_pos (by positivity), smul_eq_mul]
    congr 1
    simp only [hG, psiP]
    congr 2
    field_simp
    ring
  have hsplit : (fun x : ℝ => (y - M / x ^ 2) * G x) = fun x => y * G x - M / x ^ 2 * G x := by
    funext x; ring
  rw [hsplit, integral_sub (hGi.const_mul y) hG2i, integral_const_mul, hsub]
  have : ∫ x in Ioi (0 : ℝ), M / y / x ^ 2 * G x = y⁻¹ * ∫ x in Ioi (0 : ℝ), M / x ^ 2 * G x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    field_simp
  rw [this, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul, sub_self]

def kR (y ξ : ℝ) (x : ℝ) : ℝ := (y + ξ / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (ξ / x) ^ 2))

theorem kR_abs (y ξ x : ℝ) : kR y ξ |x| = kR y ξ x := by
  simp only [kR, sq_abs, div_pow, mul_pow]

theorem integrableOn_abs_Iic {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi 0)) :
    IntegrableOn (fun x => f |x|) (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact hf

theorem integrable_of_abs {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have h := (integrableOn_abs_Iic hf).union hf
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integrable_kR {y ξ : ℝ} (hy : 0 < y) (hξ : ξ ≠ 0) : Integrable (kR y ξ) := by
  have hM : 0 < |ξ| := abs_pos.2 hξ
  have hdom : IntegrableOn (fun x => kR y |ξ| |x|) (Ioi 0) := by
    refine (integrableOn_plus hy hM).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    simp only [kR, abs_of_pos hx0]
  have hi := integrable_of_abs hdom
  refine hi.mono' (by unfold kR; fun_prop : Measurable (kR y ξ)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [kR_abs]
  simp only [kR, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : (ξ / x) ^ 2 = (|ξ| / x) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [h1]
  gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos hy, abs_div, abs_of_nonneg (sq_nonneg x)]

theorem integral_kR {y ξ : ℝ} (hy : 0 < y) (hξ : ξ ≠ 0) :
    ∫ x, kR y ξ x = if 0 < ξ then 2 * Real.exp (-2 * Real.pi * ξ * y) else 0 := by
  have h : ∫ x, kR y ξ x = 2 * ∫ x in Ioi (0 : ℝ), kR y ξ x := by
    rw [← integral_comp_abs]
    simp only [kR_abs]
  rw [h]
  split_ifs with hpos
  · rw [show (∫ x in Ioi (0 : ℝ), kR y ξ x) = Real.exp (-2 * Real.pi * ξ * y) from integral_plus hy hpos]
  · have hneg : 0 < -ξ := by
      rcases lt_or_gt_of_ne hξ with h' | h'
      · linarith
      · exact absurd h' hpos
    have := integral_minus hy hneg
    have e : ∀ x, kR y ξ x = (y - -ξ / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (-ξ / x) ^ 2)) := by
      intro x
      simp only [kR, neg_div, sub_neg_eq_add, neg_sq]
    simp only [e]
    rw [this, mul_zero]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem omega_ofInfinite (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) :
    ((ω.1 (ofInfinite a) : ℂˣ) : ℂ) = ∏ v, ((ω.locInf v (infiniteComponent v a) : ℂˣ) : ℂ) := by
  rw [ofInfinite_eq_prod, map_prod, Units.coe_prod]
  rfl

theorem locInf_pow_eq_one {ω : HChar F} (hfin : IsOfFinOrder ω) :
    ∃ N : ℕ, 0 < N ∧ ∀ v (z : (v.Completion)ˣ), ω.locInf v z ^ N = 1 := by
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  refine ⟨N, hN, fun v z => ?_⟩
  have h1 : (ω ^ N).1 = 1 := by rw [hpow]; rfl
  rw [HChar.locInf, MonoidHom.comp_apply, ← MonoidHom.pow_apply, ← Subgroup.coe_pow, h1, MonoidHom.one_apply]

def rv (v : InfinitePlace F) (z : v.Completion) : ℝ := ringEquivRealOfIsReal (IsTotallyReal.isReal v) z

theorem locInf_sign {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (v : InfinitePlace F)
    (z : (v.Completion)ˣ) : ((ω.locInf v z : ℂˣ) : ℂ) = if 0 < rv v (z : v.Completion) then 1 else -1 := by
  obtain ⟨N, hN, hpow⟩ := locInf_pow_eq_one H.fin
  set e := ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hpos : ∀ z' : (v.Completion)ˣ, 0 < e z' → ω.locInf v z' = 1 := by
    intro z' hz'
    set r := e z'
    have hb : (r ^ ((N : ℝ)⁻¹)) ≠ 0 := (Real.rpow_pos_of_pos hz' _).ne'
    set b : (v.Completion)ˣ := Units.mk0 (e.symm (r ^ ((N : ℝ)⁻¹))) (by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]; exact hb)
    have hbN : b ^ N = z' := by
      apply Units.ext
      apply e.injective
      rw [Units.val_pow_eq_pow_val, map_pow]
      change (e (e.symm (r ^ ((N : ℝ)⁻¹)))) ^ N = r
      rw [RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hz'.le,
        inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]
    rw [← hbN, map_pow, hpow]
  have hodd := H.odd v
  split_ifs with h
  · rw [hpos z h, Units.val_one]
  · have h' : e z ≠ 0 := by
      intro h0
      exact z.ne_zero (e.injective (by rw [h0, map_zero]))
    have hneg : e z < 0 := lt_of_le_of_ne (not_lt.1 h) h'
    have hz : z = -1 * (-z) := by rw [neg_mul, one_mul, neg_neg]
    have hz' : 0 < e ((-z : (v.Completion)ˣ) : v.Completion) := by
      rw [Units.val_neg, map_neg]; linarith
    rw [hz, map_mul, hodd, hpos _ hz', mul_one, Units.val_neg, Units.val_one]

omit [NumberField F] in
theorem integrable_units_iff {v : InfinitePlace F} (G : v.Completion → ℂ) :
    Integrable (fun a : (v.Completion)ˣ => G a) (infinitePlaceUnitsMeasure v) ↔
      Integrable (fun x : ℝ => G ((isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm x) / ((|x| : ℝ) : ℂ)) := by
  have hv := IsTotallyReal.isReal v
  have he := measurableEmbedding_units_val (F := v.Completion)
  set ν := (infinitePlaceMeasure v).withDensity fun x => ENNReal.ofReal (‖x‖ ^ v.mult)⁻¹ with hν
  have hr : Set.range (Units.val : (v.Completion)ˣ → v.Completion) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  have hac : ν ≪ infinitePlaceMeasure v := withDensity_absolutelyContinuous _ _
  have h0 := he.integrable_map_iff (g := G) (μ := Measure.comap Units.val ν)
  rw [he.map_comap, hr, Measure.restrict_eq_self_of_ae_mem (s := ({0} : Set v.Completion)ᶜ)
    (compl_mem_ae_iff.2 (hac (infinitePlaceMeasure_zero v)))] at h0
  have h1 : Integrable (fun a : (v.Completion)ˣ => G a) (infinitePlaceUnitsMeasure v) ↔ Integrable G ν := by
    show Integrable (G ∘ Units.val) (Measure.comap Units.val ν) ↔ _
    exact h0.symm
  have hme : MeasurableEmbedding (isometryEquivRealOfIsReal hv).symm :=
    (isometryEquivRealOfIsReal hv).symm.toHomeomorph.measurableEmbedding
  rw [h1, hν, integrable_withDensity_iff_integrable_smul' (measurable_density_unitsMeasure v.mult)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), infinitePlaceMeasure_of_isReal hv,
    hme.integrable_map_iff]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  have hn : ‖(isometryEquivRealOfIsReal hv).symm x‖ = |x| := by
    rw [← Real.norm_eq_abs, ← (isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero]
    change (ringEquivRealOfIsReal hv).symm 0 = 0
    exact map_zero _
  simp only [Function.comp_apply, hv.mult_eq_one, pow_one, hn,
    ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x)), Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

def gv (ω : HChar F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (v : InfinitePlace F) (u : (v.Completion)ˣ) : ℂ :=
  ((((rv v u * y.val v + (rv v u)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rv v u * y.val v) ^ 2 + ((rv v u)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ))) *
      ((ω.locInf v u : ℂˣ) : ℂ)⁻¹

theorem reAt_ne_zero (v : InfinitePlace F) {ξ : F} (hξ : ξ ≠ 0) : reAt v ξ ≠ 0 := by
  have hv := IsTotallyReal.isReal v
  have h := NumberField.InfinitePlace.embedding_of_isReal_apply hv ξ
  have h2 : reAt v ξ = NumberField.InfinitePlace.embedding_of_isReal hv ξ := by
    rw [reAt, ← h, Complex.ofReal_re]
  rw [h2]
  exact (map_ne_zero _).2 hξ

theorem local_int {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : (UpperTheory.V.TR.Rinf F)ˣ)
    (hy : ∀ v, 0 < y.val v) (ξ : Fˣ) (v : InfinitePlace F) :
    Integrable (gv ω y (ξ : F) v) (infinitePlaceUnitsMeasure v) ∧
      ∫ u, gv ω y (ξ : F) v u ∂infinitePlaceUnitsMeasure v =
        if 0 < reAt v (ξ : F) then 2 * Complex.exp (-(2 * Real.pi : ℂ) * ((reAt v (ξ : F) : ℂ) * (y.val v : ℂ))) else 0 := by
  have hv := IsTotallyReal.isReal v
  have hξ0 : reAt v (ξ : F) ≠ 0 := reAt_ne_zero v ξ.ne_zero
  set yv := y.val v with hyv
  set m := reAt v (ξ : F) with hm
  set G : v.Completion → ℂ := fun z => (((rv v z * yv + (rv v z)⁻¹ * m : ℝ) : ℂ) *
      ((Real.exp (-Real.pi * ((rv v z * yv) ^ 2 + ((rv v z)⁻¹ * m) ^ 2)) : ℝ) : ℂ)) *
      (if 0 < rv v z then (1 : ℂ) else -1)⁻¹ with hGdef
  have hgv : gv ω y (ξ : F) v = fun u : (v.Completion)ˣ => G (u : v.Completion) := by
    funext u
    simp only [gv, hGdef, locInf_sign H v u, Complex.ofReal_exp]
    congr 3
    push_cast
    ring
  have hae : (fun x : ℝ => G ((isometryEquivRealOfIsReal hv).symm x) / ((|x| : ℝ) : ℂ)) =ᵐ[volume]
      fun x => ((kR yv m x : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hr : rv v ((isometryEquivRealOfIsReal hv).symm x) = x := (ringEquivRealOfIsReal hv).apply_symm_apply x
    simp only [hGdef, hr, kR, inv_mul_eq_div]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · rw [if_neg (not_lt.2 hneg.le), abs_of_neg hneg]
      push_cast
      field_simp
    · rw [if_pos hpos, abs_of_pos hpos]
      push_cast
      field_simp
  refine ⟨?_, ?_⟩
  · rw [hgv, integrable_units_iff G]
    exact (integrable_kR (hy v) hξ0).ofReal.congr hae.symm
  · rw [hgv, integral_infinitePlaceUnitsMeasure_of_isReal hv G, integral_congr_ae hae, integral_complex_ofReal,
      integral_kR (hy v) hξ0]
    split_ifs
    · push_cast
      congr 2
      ring
    · simp

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalArchimedeanIntegral

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open LocalArchimedeanIntegral L4

theorem archimedean_integral_holds : ArchInt := by
  intro F _ _ _ ω c H y hy ξ
  have he : MeasurableEmbedding (infiniteUnitsEquiv F).symm :=
    (infiniteUnitsEquiv F).symm.toHomeomorph.measurableEmbedding
  have hpt : ∀ z : (Π v : InfinitePlace F, (v.Completion)ˣ),
      archK y (ξ : F) ((infiniteUnitsEquiv F).symm z) * (ωI ω ((infiniteUnitsEquiv F).symm z))⁻¹ =
        ∏ v, gv ω y (ξ : F) v (z v) := by
    intro z
    rw [archK, ωI, omega_ofInfinite, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rfl
  have hloc := fun v => local_int H y hy ξ v
  constructor
  · rw [infiniteIdeleMeasure, he.integrable_map_iff]
    refine (Integrable.fintype_prod_dep (fun v => (hloc v).1)).congr ?_
    exact Eventually.of_forall fun z => (hpt z).symm
  · rw [infiniteIdeleMeasure, he.integral_map]
    simp only [Function.comp_apply, hpt]
    rw [integral_fintype_prod_eq_prod]
    simp only [fun v => (hloc v).2]
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies]
    split_ifs
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Complex.exp_sum, Finset.mul_sum]
    · rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

omit [IsTotallyReal F] in
theorem ω_split (ω : HChar F) (τ : IdeleGroup F) :
    ((ω.1 τ : ℂˣ) : ℂ) = ωI ω (toInfinite F τ) * ωF ω (toFinite F τ) := by
  conv_lhs => rw [← ofFinite_mul_ofInfinite τ]
  rw [map_mul, Units.val_mul, mul_comm]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

theorem pInf_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : UpperTheory.V.TR.pInf F (yAd y yf) = y.val := by
  have hs : ∀ x, UpperTheory.V.TR.pInf F (UpperTheory.V.TR.sInf F x) = x := fun x => (UpperTheory.V.TR.infEq F).symm_apply_apply x
  have hf : ∀ x, UpperTheory.V.TR.pInf F (sFin F x) = 0 := fun x => map_zero (UpperTheory.V.TR.infEq F).symm
  have h1 : UpperTheory.V.TR.pInf F ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = y.val := by
    change UpperTheory.V.TR.pInf F (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val) = y.val
    rw [map_add (f := _), map_sub, map_one, hs, hs]; ring
  have h2 : UpperTheory.V.TR.pInf F ((finId F yf : (Ad F)ˣ) : Ad F) = 1 := by
    change UpperTheory.V.TR.pInf F (1 - sFin F 1 + sFin F (yf : Af F)) = 1
    rw [map_add (f := _), map_sub, map_one, hf, hf]; ring
  rw [yAd, Units.val_mul, map_mul, h1, h2, mul_one]

theorem pFin_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : pFin F (yAd y yf) = (yf : Af F) := by
  have h1 : pFin F ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = 1 := by
    change pFin F (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val) = 1
    rw [map_add (f := _), map_sub, map_one]
    change (1 : Af F) - 0 + 0 = 1
    ring
  have h2 : pFin F ((finId F yf : (Ad F)ˣ) : Ad F) = yf := by
    change pFin F (1 - sFin F 1 + sFin F (yf : Af F)) = yf
    rw [map_add (f := _), map_sub, map_one]
    change (1 : Af F) - 1 + (yf : Af F) = yf
    ring
  rw [yAd, Units.val_mul, map_mul, h1, h2, one_mul]

theorem reAt_eq' (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem pInf_alg' (v : InfinitePlace F) (x : F) : UpperTheory.V.TR.pInf F (algebraMap F (Ad F) x) v = reAt v x := by
  rw [reAt_eq']
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

theorem pInf_tau (τ : IdeleGroup F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F (τ : Ad F) v = rc (toInfinite F τ) v := rfl

theorem pInf_tau_inv (τ : IdeleGroup F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F ((τ⁻¹ : IdeleGroup F) : Ad F) v = (rc (toInfinite F τ) v)⁻¹ := by
  rw [← pInf_tau]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Pi.mul_apply, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, Pi.one_apply]

theorem kernF_split (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (ξ : F)
    (τ : IdeleGroup F) :
    kernF c ((τ : Ad F) * yAd y yf) (τ⁻¹ • algebraMap F (Ad F) ξ) =
      archK y ξ (toInfinite F τ) * finK c yf ξ (toFinite F τ) := by
  have hA : ∀ v, UpperTheory.V.TR.pInf F ((τ : Ad F) * yAd y yf) v = rc (toInfinite F τ) v * y.val v := by
    intro v
    rw [map_mul, Pi.mul_apply, pInf_yAd, pInf_tau]
  have hZ : ∀ v, UpperTheory.V.TR.pInf F (τ⁻¹ • algebraMap F (Ad F) ξ) v = (rc (toInfinite F τ) v)⁻¹ * reAt v ξ := by
    intro v
    rw [Units.smul_def, smul_eq_mul, map_mul, Pi.mul_apply, pInf_tau_inv, pInf_alg']
  have hA' : pFin F ((τ : Ad F) * yAd y yf) = (toFinite F τ : Af F) * (yf : Af F) := by
    rw [map_mul, pFin_yAd]; rfl
  have hZ' : pFin F (τ⁻¹ • algebraMap F (Ad F) ξ) =
      (((toFinite F τ)⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ := by
    rw [Units.smul_def, smul_eq_mul, map_mul, ← map_inv]; rfl
  rw [kernF, archK, finK, hA', hZ']
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hA, hZ]
  push_cast
  ring_nf

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

omit [IsTotallyReal F] in
theorem ordAt_eq_zero {b : (Af F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (h : IsIntegralUnitAt b w) : ordAt b w = 0 := by
  have hb0 : pLoc F w (b : Af F) ≠ 0 := by
    intro h0
    have := congrArg (fun a : Af F => pLoc F w a) b.mul_inv
    simp only [map_mul, map_one, h0, zero_mul] at this
    exact zero_ne_one this
  have h1 : Valued.v (pLoc F w (b : Af F)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h.1
  have h2 : Valued.v (pLoc F w ((b⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h.2
  have hm : pLoc F w (b : Af F) * pLoc F w ((b⁻¹ : (Af F)ˣ) : Af F) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have h3 : Valued.v (pLoc F w (b : Af F)) = 1 := by
    refine le_antisymm h1 ?_
    have := congrArg Valued.v hm
    rw [map_mul, map_one] at this
    calc (1 : WithZero (Multiplicative ℤ)) = _ := this.symm
      _ ≤ Valued.v (pLoc F w (b : Af F)) := mul_le_of_le_one_right' h2
  have := valued_eq_exp_neg_ord hb0
  rw [h3, ← WithZero.exp_zero, WithZero.exp_inj] at this
  unfold ordAt
  omega

omit [IsTotallyReal F] in
theorem isIntegralUnitAt_mul {b b' : (Af F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (h : IsIntegralUnitAt b w)
    (h' : IsIntegralUnitAt b' w) : IsIntegralUnitAt (b * b') w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem h.1 h'.1
  · rw [mul_inv_rev, Units.val_mul]
    exact mul_mem h'.2 h.2

omit [IsTotallyReal F] in
theorem pLoc_unit_ne_zero (b : (Af F)ˣ) (w : HeightOneSpectrum (𝓞 F)) : pLoc F w (b : Af F) ≠ 0 := by
  intro h0
  have := congrArg (fun a : Af F => pLoc F w a) b.mul_inv
  simp only [map_mul, map_one, h0, zero_mul] at this
  exact zero_ne_one this

theorem fin_int (hLI : LocInt) (hFS : FinSplit) (hOP : OmegaProd) (hCD : CoefDiv) (hR : LocRam)
    (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp ω c) :
    ∃ Cf : ℂ, Cf ≠ 0 ∧ ∀ (yf : (Af F)ˣ) (ξ : Fˣ),
      Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        Cf * (ωF ω (xiF ξ))⁻¹ * coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) := by
  classical
  have hfin0 : {w : HeightOneSpectrum (𝓞 F) | c w ≠ 0 ∨ dd w ≠ 0}.Finite := by
    change ({w | c w ≠ 0} ∪ {w | dd w ≠ 0}).Finite
    refine (L2.finite_support H).union ((Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).subset ?_)
    intro w hw
    have hw' : ordI w (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      intro h0
      apply hw
      simp [dd, h0]
    exact (Associates.count_ne_zero_iff_dvd (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) w.irreducible).1 hw'
  set S0 := hfin0.toFinset with hS0
  refine ⟨∏ v ∈ S0, cst ω c v, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    unfold cst
    split_ifs with hcv
    · exact zpow_ne_zero _ (Units.ne_zero _)
    · exact (hR F ω c H v hcv).2
  intro yf ξ
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S0 ∪ (finite_setOf_not_isIntegralUnitAt yf).toFinset ∪
    (finite_setOf_not_isIntegralUnitAt (xiF ξ)).toFinset with hSdef
  have hS : ∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w := by
    intro w hw
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hcon <;> apply hw <;> simp [hSdef, hS0, hcon]
  have hloc := fun v => hLI F ω c H yf ξ v
  obtain ⟨hint, heq⟩ := hFS F ω c H yf ξ S hS (fun v => (hloc v).1)
  refine ⟨hint, ?_⟩
  rw [heq, Finset.prod_congr rfl (fun v _ => (hloc v).2), Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hxi : ωF ω (xiF ξ) =
      ∏ v ∈ S, ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ) := by
    rw [hOP F ω c H (xiF ξ) S (fun w hw => ⟨(hS w hw).1, (hS w hw).2.2.2⟩)]
    refine Finset.prod_congr rfl fun v _ => ?_
    congr 3
  rw [← hxi]
  set m : HeightOneSpectrum (𝓞 F) → ℤ := fun w => ordAt (xiF ξ * yf) w + dd w with hm
  have hite : ∀ v ∈ S, (if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
      cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j) =
      if 0 ≤ m v then cst ω c v * ∑ j ∈ Finset.range ((m v).toNat + 1), chiW ω c v ^ j else 0 := by
    intro v _
    by_cases h0 : 0 ≤ ordAt (xiF ξ * yf) v + dd v
    · rw [if_neg (not_lt.2 h0), if_pos h0]
    · rw [if_pos (lt_of_not_ge h0), if_neg h0]
  rw [Finset.prod_congr rfl hite, Finset.prod_ite_zero]
  have hz : (algebraMap F (Af F) (ξ : F) * (yf : Af F)) = ((xiF ξ * yf : (Af F)ˣ) : Af F) := by
    rw [Units.val_mul]; rfl
  have hcd := hCD F ω c (algebraMap F (Af F) (ξ : F) * (yf : Af F)) m S (fun w => by
      have hne := pLoc_unit_ne_zero (xiF ξ * yf) w
      rw [hz, valued_eq_exp_neg_ord hne]
      congr 1
      simp only [hm, ordAt]
      ring)
    (fun w hw => by
      have h1 := hS w hw
      simp only [hm, ordAt_eq_zero (isIntegralUnitAt_mul h1.2.2.2 h1.2.2.1), h1.2.1, add_zero])
  rw [hcd]
  have hcst : ∏ v ∈ S, cst ω c v = ∏ v ∈ S0, cst ω c v := by
    symm
    refine Finset.prod_subset (fun v hv => by simp [hSdef, hv]) fun v _ hv0 => ?_
    have h1 : c v = 0 := by
      by_contra h; apply hv0; simp [hS0, h]
    have h2 : dd v = 0 := by
      by_contra h; apply hv0; simp [hS0, h]
    simp [cst, h1, h2]
  split_ifs with hall
  · rw [Finset.prod_mul_distrib, hcst]
    ring
  · ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

theorem sLocal_of (hA : ArchInt) (hLI : LocInt) (hFS : FinSplit) (hOP : OmegaProd) (hCD : CoefDiv) (hR : LocRam)
    (hPos : OmegaPos) : SFin → SKern → SLocal := by
  intro hfin hK F _ _ _ ω c H
  obtain ⟨κ, hκ, hκF⟩ := hK F c (hfin F ω c H)
  obtain ⟨Cf, hCf, hfinI⟩ := fin_int hLI hFS hOP hCD hR ω c H
  refine ⟨κ * (2 : ℂ) ^ Fintype.card (InfinitePlace F) * Cf, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hκ (pow_ne_zero _ two_ne_zero)) hCf
  intro y hy yf ξ
  set gI : (InfiniteAdeleRing F)ˣ → ℂ := fun a => archK y (ξ : F) a * (ωI ω a)⁻¹
  set gF : (Af F)ˣ → ℂ := fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹
  have hpt : ∀ τ : IdeleGroup F, kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) =
      κ * (gI (toInfinite F τ) * gF (toFinite F τ)) := by
    intro τ
    simp only [kern, hκF, kernF_split, ω_split, gI, gF]
    have h1 : ((ideleModule F τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ideleModule F τ).2.ne'
    field_simp
  obtain ⟨hAi, hAe⟩ := hA F ω c H y hy ξ
  obtain ⟨hFi, hFe⟩ := hfinI yf ξ
  have hprod : Integrable (fun p : (InfiniteAdeleRing F)ˣ × (Af F)ˣ => κ * (gI p.1 * gF p.2))
      ((infiniteIdeleMeasure F).prod (finiteIdeleMeasure F)) :=
    (hAi.mul_prod hFi).const_mul κ
  have hmap : ∀ p : (InfiniteAdeleRing F)ˣ × (Af F)ˣ,
      toInfinite F ((prodEquiv F).symm p) = p.1 ∧ toFinite F ((prodEquiv F).symm p) = p.2 :=
    fun p => ⟨toInfinite_symm p, toFinite_symm p⟩
  constructor
  · have : Integrable (fun τ : IdeleGroup F => κ * (gI (toInfinite F τ) * gF (toFinite F τ))) (ideleMeasure F) := by
      rw [ideleMeasure]
      refine (integrable_map_equiv (prodEquiv F).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
      convert hprod using 2 with p
      exact congrArg₂ (fun a b => κ * (gI a * gF b)) (hmap p).1 (hmap p).2
    exact this.congr (Filter.Eventually.of_forall fun τ => (hpt τ).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_ideleMeasure]
    simp only [(hmap _).1, (hmap _).2]
    rw [integral_const_mul, integral_prod_mul, hAe, hFe]
    split_ifs with hξ
    · rw [hPos F ω c H ξ hξ, inv_one, mul_one]
      ring
    · ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem local_expansion_holds : SFin → SKern → SLocal :=
  sLocal_of archimedean_integral_holds (local_integral_of_substitution inverse_substitution_holds) finite_split_holds character_product_holds coefficient_divisor_holds local_ramified_holds
    character_positive_holds

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
