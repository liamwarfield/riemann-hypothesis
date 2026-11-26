module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem FibreNormPrimeBound.block_ne_zero {y : (Σ k, ι k) → Ω} {e : K → ℕ} {f : MRing ι}
    (he : ∀ k, 1 ≤ e k) (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f e) (hy : aeval y f ≠ 0) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  by_contra h
  push Not at h
  apply hy
  rw [aeval_def, eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum : ∑ i, m ⟨k, i⟩ ≠ 0 := by rw [hf m hm k]; exact (Nat.one_le_iff_ne_zero.mp (he k))
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, i⟩) ?_)
  rw [h i, zero_pow hi]


omit [Fintype K] in
theorem FibreNormPrimeBound.exists_chart (V : ValuationSubring Ω) {y : (Σ k, ι k) → Ω}
    (hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ q : Σ k, ι k, y q / y ⟨q.1, c q.1⟩ ∈ V := by
  classical
  have hmax : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 ∧ ∀ i', V.valuation (y ⟨k, i'⟩) ≤ V.valuation (y ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hm⟩ := Finset.exists_max_image (Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0)
      (fun i => V.valuation (y ⟨k, i⟩)) (by obtain ⟨i0, h0⟩ := hblk k; exact ⟨i0, by simp [h0]⟩)
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases h : y ⟨k, i'⟩ = 0
    · rw [h, map_zero]; exact zero_le
    · exact hm i' (by simp [h])
  choose c hc0 hcm using hmax
  refine ⟨c, hc0, fun ⟨k, i⟩ => ?_⟩
  have hv : V.valuation (y ⟨k, c k⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 k)
  rw [← V.valuation_le_one_iff, div_eq_mul_inv, map_mul, map_inv₀]
  calc V.valuation (y ⟨k, i⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹
      ≤ V.valuation (y ⟨k, c k⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹ := mul_le_mul_left (hcm k i) _
    _ = 1 := mul_inv_cancel₀ hv

theorem FibreNormPrimeBound.mem_of_isIntegral (V : ValuationSubring Ω) {S : Subalgebra ℤ Ω} (hS : ∀ s ∈ S, s ∈ V)
    {u : Ω} (hu : IsIntegral S u) : u ∈ V := by
  let φ : S →+* V :=
    { toFun := fun r => ⟨r, hS r r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  obtain ⟨f, hf, hfu⟩ := hu
  have hint : IsIntegral V u := ⟨f.map φ, hf.map φ, by rw [Polynomial.eval₂_map]; exact hfu⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact hv ▸ v.2

theorem FibreNormPrimeBound.proof (hG : PullFormsGeneric.Statement) (hN : NormFormGaussBound.Statement)
    (hC : ChartPrimePowerInverse.Statement) : FibreNormPrimeBound.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hAr hBir he hhomL hnz p hp
  have hM : ∀ j, ∃ M : ℕ, aeval y (L j) ≠ 0 → ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro j
    by_cases hj : aeval y (L j) = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨M, hM⟩ := hC K ι Ω y D e L hhomL hnz p hp j hj
      exact ⟨M, fun _ => hM⟩
  choose M hM using hM
  refine ⟨Module.finrank (pullField y L) Ω * (∑ j, M j) * q, ?_⟩
  intro τ s hs j c hc μ
  obtain ⟨hLj, hfd, -, hhom, hcp⟩ := hc
  have := hfd
  set S := ∑ j, M j with hS
  set Sset : Set Ω := {z | ∃ i k, z = aeval y (L i) / aeval y (L k)} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}
  have key : ∀ V : ValuationSubring Ω, Sset ⊆ V.toSubring →
      (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈ V := by
    intro V hSV
    obtain ⟨c, hc0, hcV⟩ :=
      FibreNormPrimeBound.exists_chart V (FibreNormPrimeBound.block_ne_zero he (hhomL j) hLj)
    set Z := ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) with hZ
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hY
    have hu : s * Z ∈ V := by
      refine FibreNormPrimeBound.mem_of_isIntegral V (S := chartRingZ y c) ?_ (hs c hc0)
      intro t ht
      rw [chartRingZ, Algebra.adjoin_int] at ht
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ ht
      rintro _ ⟨q', rfl⟩
      exact hcV q'
    have hw : (p : Ω) ^ M j * Y / aeval y (L j) ∈ V := by
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ (hM j hLj c hc0)
      rintro z ((⟨q', rfl⟩ | ⟨i, rfl⟩) | hz)
      · exact hcV q'
      · exact hSV (Or.inl ⟨i, j, rfl⟩)
      · exact hSV (Or.inr hz)
    have hpV : (p : Ω) ∈ V := natCast_mem V p
    obtain ⟨r, hr⟩ : ∃ r, S = M j + r :=
      ⟨S - M j, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))).symm⟩
    have hZY : Z * Y ^ (q * τ) = 1 := by
      rw [hZ, hY, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← pow_mul, ← zpow_natCast (y _) (e k * (q * τ)), ← zpow_add₀ (hc0 k)]
      have h0 : -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) + ((e k * (q * τ) : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [h0, zpow_zero]
    have heq : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) =
        (s * Z) * ((p : Ω) ^ r) ^ (q * τ) * ((p : Ω) ^ M j * Y / aeval y (L j)) ^ (q * τ) := by
      rw [hr]
      calc (p : Ω) ^ ((M j + r) * (q * τ)) * (s / aeval y (L j) ^ (q * τ))
          = s * (Z * Y ^ (q * τ)) * (p : Ω) ^ ((M j + r) * (q * τ)) / aeval y (L j) ^ (q * τ) := by
            rw [hZY]; ring
        _ = _ := by ring
    rw [heq]
    exact mul_mem (mul_mem hu (pow_mem (pow_mem hpV _) _)) (pow_mem hw _)
  have hint : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
      integralClosure (Subring.closure Sset) Ω := by
    have hmem : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
        (integralClosure (Subring.closure Sset) Ω).toSubring := by
      rw [← iInf_valuationSubring_superset]
      exact Subring.mem_iInf.mpr fun V => key V.1 V.2
    exact hmem
  have h := hN Ω D (fun i => aeval y (L i)) (pullField y L) rfl
    (hG K ι Ω y D e L hAr hBir he hhomL hnz) p hp j (S * (q * τ))
    (Module.finrank (pullField y L) Ω * (q * τ)) (s / aeval y (L j) ^ (q * τ)) c
    (hhom _ le_rfl) hcp hint μ
  have hn : Module.finrank (pullField y L) Ω * (S * (q * τ)) =
      Module.finrank (pullField y L) Ω * S * q * τ := by ring
  rw [hn] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartPrimePowerInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem aeval_mul_blockScale_of_isMultiHomog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [CommRing Ω] {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (t : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => y p * t p.1) f = aeval y f * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ x, t k ^ d ⟨k, x⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal {K : Type*} [Fintype K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω] {y : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) (t : K → Ω) : aeval (fun p => y p * t p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1) :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  rw [← hcomp, AlgHom.comp_apply, h0, map_zero]

theorem ChartPrimePowerInverse.proof : ChartPrimePowerInverse.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L hhom hL p hp j hj
  obtain ⟨N, hN⟩ := PullConeNull.proof K ι Ω y D L hL
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ,
      (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro c hc
    set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R := fun n => R.pow_mem (natCast_mem R p) n

    let G : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R}
        mul_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z) := by ring
          rw [this]
          exact R.mul_mem ha hb
        add_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z) := by
            ring
          rw [this]
          exact R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)
        algebraMap_mem' := by
          intro q
          obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'
          refine ⟨b, ?_⟩
          have hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω) := by exact_mod_cast hden
          have hd0 : (d' : Ω) ≠ 0 := by
            intro h0
            have : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            rw [hden', h0, mul_zero] at this
            exact this rfl
          have : (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹ := by
            rw [eq_ratCast, Rat.cast_def, hden']
            field_simp
          show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R
          rw [this]
          exact R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }
    have hmemG : ∀ x ∈ R, x ∈ G := fun x hx => ⟨0, by simpa using hx⟩
    let r : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, c q.1⟩
    let χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval r
    let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
    have hχG : ∀ g, χ g ∈ G := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C q => simpa [χ] using G.algebraMap_mem q
      | add f g hf hg => simpa using G.add_mem hf hg
      | mul_X f q hf =>
        simpa [χ] using G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))
    have hχmap : ∀ f : MRing ι,
        χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f := by
      intro f
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      simp only [r, t, div_eq_mul_inv]

    let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
      { carrier := {f | χ f * (Y / aeval y (L j)) ∈ G}
        add_mem' := by
          intro f g hf hg
          simpa [add_mul] using G.add_mem hf hg
        zero_mem' := by simp
        smul_mem' := by
          intro g f hf
          simpa [smul_eq_mul, mul_assoc] using G.mul_mem (hχG g) hf }
    have hIJ : coneNullIdeal y L ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]
        exact G.zero_mem
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]
        have : aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) =
            aeval y (L i) / aeval y (L j) := by
          have hprod : (∏ k, t k ^ e k) = Y⁻¹ := by
            rw [hYdef, ← Finset.prod_inv_distrib]
            exact Finset.prod_congr rfl fun k _ => inv_pow _ _
          rw [hprod]
          field_simp
        rw [this]
        exact hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))
    have h1 := hIJ (hN c)
    have hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1 := by
      simp [χ, r, div_self (hc _)]
    obtain ⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by
      have : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G := h1
      rwa [hone, one_mul] at this
    exact ⟨a, by rw [mul_div_assoc]; exact ha⟩
  choose! a ha using key
  refine ⟨Finset.univ.sup a, fun c hc => ?_⟩
  have hle : a c ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ c)
  have e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) =
      (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j)) := by
    rw [← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]
    ring
  rw [e1]
  exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubmodules
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubmodules

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_of_weighted {q : MRingOver S ι} {c : K → ℤ}
    (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q (fun k => (c k).toNat) := by
  by_cases h0 : q = 0
  · intro m hm
    simp [h0] at hm
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    refine (QuotPartGraded.isMultiHomog_iff q _).2 ?_
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rw [hcc]
    exact hq

theorem smul_mem_of_weighted {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    {c e : K → ℤ} (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) {m : M} (hm : m ∈ 𝓜 e) :
    q • m ∈ 𝓜 (e + c) := by
  by_cases h0 : q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    have h := hM.2 _ e q m (isMultiHomog_of_weighted hq) hm
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open Classical in
theorem component_smul_eq_zero {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜)
    {f : MRingOver S ι} (hf : f ∈ Module.annihilator (MRingOver S ι) M) (i : K → ℤ) {e : K → ℤ} {m : M}
    (hm : m ∈ 𝓜 e) :
    ((DirectSum.decompose (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)) f i :
      MRingOver S ι)) • m = 0 := by
  set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
  set s := (DirectSum.decompose 𝒜 f).support
  have hsum : ∑ c ∈ s, ((DirectSum.decompose 𝒜 f c : MRingOver S ι)) • m = 0 := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 f]
    exact Module.mem_annihilator.1 hf m
  obtain ⟨g, hg⟩ : ∃ g : (K → ℤ) → MRingOver S ι, ∀ c, g c = (DirectSum.decompose 𝒜 f c : MRingOver S ι) :=
    ⟨_, fun _ => rfl⟩
  have hgm : ∀ c, g c ∈ 𝒜 c := fun c => (hg c).symm ▸ (DirectSum.decompose 𝒜 f c).2
  simp only [← hg] at hsum
  suffices h : g i • m = 0 by rw [hg] at h; exact h
  by_cases hi : i ∈ s
  · have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝓜).1 hM.1.submodule_iSupIndep
    have hinj : Set.InjOn (fun c : K → ℤ => e + c) s := fun a _ b _ h => add_left_cancel h
    have key := hind (s.image fun c => e + c)
      (fun d => g (d - e) • m)
      (by
        intro d hd
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
        rw [add_sub_cancel_left]
        exact smul_mem_of_weighted hM ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (hgm c)) hm)
      (by
        rw [Finset.sum_image hinj]
        simpa only [add_sub_cancel_left] using hsum)
      (e + i) (Finset.mem_image_of_mem _ hi)
    simpa only [add_sub_cancel_left] using key
  · rw [hg, DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, zero_smul]

theorem mem_annihilator_of_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    (hq : ∀ e, ∀ m ∈ 𝓜 e, q • m = 0) : q ∈ Module.annihilator (MRingOver S ι) M := by
  refine Module.mem_annihilator.2 fun m => ?_
  have hm : m ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction 𝓜 (motive := fun x => q • x = 0) hm (fun e x hx => hq e x hx) (smul_zero q) ?_
  intro x y hx hy
  rw [smul_add, hx, hy, add_zero]

def prodSet (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) : Set M :=
  {y | ∃ (p : MRingOver S ι) (a : K → ℕ) (m : M) (c : K → ℤ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a ∧ p ∈ P ∧ m ∈ 𝓜 c ∧ y = p • m}

theorem prodSet_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) :
    ∀ y ∈ prodSet 𝓜 P, ∃ c, y ∈ 𝓜 c := by
  rintro _ ⟨p, a, m, c, hp, -, hm, rfl⟩
  exact ⟨_, hM.2 a c p m hp hm⟩

theorem smul_top_eq_span {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)}
    (hP : IsMultiHomogIdeal P) :
    (P • ⊤ : Submodule (MRingOver S ι) M) = Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
  apply le_antisymm
  · obtain ⟨T, hT, hPT⟩ := hP
    rw [Submodule.smul_le]
    intro r hr n _
    rw [hPT] at hr
    induction hr using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha⟩ := hT t ht
      have htP : t ∈ P := hPT ▸ Ideal.subset_span ht
      have hn : n ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
      have h0 : t • (0 : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
        rw [smul_zero]
        exact Submodule.zero_mem _
      refine Submodule.iSup_induction 𝓜
        (motive := fun x => t • x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P))
        hn (fun e x hx => Submodule.subset_span ⟨t, a, x, e, ha, htP, hx, rfl⟩) h0 ?_
      intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, a, m, c, -, hp, -, rfl⟩
    exact Submodule.smul_mem_smul hp Submodule.mem_top

theorem mem_iSup_span_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {x : M} (hx : x ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, (Submodule.span (MRingOver S ι) H).restrictScalars S ⊓ 𝓜 c := by
  have hx' := GradedSubquot.span_le_span_monTimes (S := S) (ι := ι) H hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := GradedSubquot.monTimes_homog hM hH hy
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.2 ⟨GradedSubquot.monTimes_subset_span H hy, hc⟩)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul s y _ hy => exact Submodule.smul_mem _ s hy

end GradedSubmodules


open GradedSubmodules in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open Classical in
theorem GradedSubmodules.proof : GradedSubmodules.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hM
  refine ⟨?_, fun P hP => ?_⟩
  ·
    set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
    refine ⟨{q | (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q a) ∧ q ∈ Module.annihilator (MRingOver S ι) M}, fun q hq => hq.1, ?_⟩
    apply le_antisymm
    · intro f hf
      rw [← DirectSum.sum_support_decompose 𝒜 f]
      refine Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨⟨_, isMultiHomog_of_weighted
        ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (DirectSum.decompose 𝒜 f i).2)⟩, ?_⟩
      exact mem_annihilator_of_homog hM fun e m hm => component_smul_eq_zero hM hf i hm
    · exact Ideal.span_le.2 fun q hq => hq.2
  · have hspan := smul_top_eq_span hM hP
    refine ⟨?_, ?_⟩
    · have hind1 : iSupIndep (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) :=
        GradedSubquot.iSupIndep_comap hM.1.submodule_iSupIndep
          ((P • ⊤ : Submodule (MRingOver S ι) M).subtype.restrictScalars S) (fun a b h => Subtype.ext h)
      have hsup1 : ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        have hx : (x : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ x.2
        have h := GradedSubquot.mem_iSup_inf hM (prodSet_homog hM P) hspan.ge x hx
        exact (show (⨆ c, ((Submodule.span (MRingOver S ι) (prodSet 𝓜 P)).comap
            (P • ⊤ : Submodule (MRingOver S ι) M).subtype).restrictScalars S ⊓
            subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c) ≤
              ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c from
          iSup_mono fun c => inf_le_right) h
      exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind1 hsup1,
        fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩
    · set L := (P • ⊤ : Submodule (MRingOver S ι) M) with hLdef
      set f := L.mkQ.restrictScalars S with hfdef
      have hker : LinearMap.ker f = L.restrictScalars S := by
        ext x
        simp [hfdef]
      have hind := hM.1.submodule_iSupIndep
      have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ 𝓜 c) := by
        rw [hker]
        intro x hx
        have hx' : x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ hx
        have := mem_iSup_span_inf hM (prodSet_homog hM P) hx'
        rwa [← hspan] at this
      have hind2 := GradedSubquot.iSupIndep_map_of_ker_le hind f hL
      have hsup2 : ⨆ c, quotGrading 𝓜 L c = ⊤ := by
        change ⨆ c, (𝓜 c).map f = ⊤
        rw [← Submodule.map_iSup, hM.1.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact Submodule.mkQ_surjective L
      refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
      rintro a c p _ hp ⟨x, hx, rfl⟩
      exact ⟨p • x, hM.2 a c p x hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGraphDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameGraphDeg.proof
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPt : ProjFrameFibrePt.Statement) (hDeg : ProjFrameFibreDeg.Statement) : ProjFrameGraphDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF
  have : (coordIdeal ℤ x).IsPrime := hP.2.1.1
  have := ProjFrameGraph.graphIdeal_isPrime (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
    (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
  let G := Inter.genFibreOf (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
    (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e)))
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr)
  have hch := ProjFrameGraph.isChart_fibreChart G (e 0).2 (ProjFrameGraph.frame_ne_zero hF 0)
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ (hPt D Ω κ x e hP hF G) hch, hDeg D Ω κ x e hP hF G _ hch]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtFibreLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatioFieldDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RatioFieldDeg

variable {ι : Type}

def quotCone {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ)) (hu : coordIdeal ℤ u = I) :
    MvPolynomial ι ℤ ⧸ I →+* Polynomial E :=
  Ideal.Quotient.lift I (coneMap ℤ u).toRingHom (fun a ha => by rw [← hu] at ha; exact ha)

theorem quotCone_injective {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : Function.Injective (quotCone u I hu) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, ← hu, coordIdeal, RingHom.mem_ker]
  simpa [quotCone] using ha

theorem isDomain_quot {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : IsDomain (MvPolynomial ι ℤ ⧸ I) :=
  Function.Injective.isDomain _ (quotCone_injective u I hu)

theorem charZero_frac {E : Type} [Field E] [CharZero E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) [IsDomain (MvPolynomial ι ℤ ⧸ I)] :
    CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I)) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  refine ⟨fun n m h => ?_⟩
  have h' := congrArg (IsFractionRing.lift hg) h
  simp only [map_natCast] at h'
  exact Nat.cast_injective h'

section

variable (I : Ideal (MvPolynomial ι ℤ)) [IsDomain (MvPolynomial ι ℤ ⧸ I)]

def coord (i : ι) : FractionRing (MvPolynomial ι ℤ ⧸ I) :=
  algebraMap _ _ (Ideal.Quotient.mk I (X i))

variable [CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I))]

def ratField {κ : Type} (s : κ → ι) : IntermediateField ℚ (FractionRing (MvPolynomial ι ℤ ⧸ I)) :=
  IntermediateField.adjoin ℚ {t | ∃ k l, t = coord I (s k) / coord I (s l)}

theorem projDeg_eq {E : Type} [Field E] [CharZero E] (u : ι → E) (hu : coordIdeal ℤ u = I) {D : ℕ}
    (e : Fin (D + 1) → ι) :
    projDeg u e = IntermediateField.relfinrank (ratField I e) (ratField I id) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  let f : FractionRing (MvPolynomial ι ℤ ⧸ I) →ₐ[ℚ] RatFunc E := (IsFractionRing.lift hg).toRatAlgHom
  let c : E →ₐ[ℚ] RatFunc E := (RatFunc.C : E →+* RatFunc E).toRatAlgHom
  have hx : ∀ i, f (coord I i) = RatFunc.C (u i) * RatFunc.X := by
    intro i
    simp [f, coord, IsFractionRing.lift_algebraMap, quotCone, coneMap, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
  have hr : ∀ i j, f (coord I i / coord I j) = c (u i / u j) := by
    intro i j
    rw [map_div₀, hx, hx, mul_div_mul_right _ _ RatFunc.X_ne_zero]
    simp [c, map_div₀]
  have hmap : ∀ {κ : Type} (s : κ → ι), (ratField I s).map f = (fnField (u ∘ s)).map c := by
    intro κ s
    rw [ratField, fnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, (hr _ _).symm⟩
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, hr _ _⟩
  rw [← IntermediateField.relfinrank_map_map (ratField I e) (ratField I id) f, hmap, hmap,
    IntermediateField.relfinrank_map_map]
  rfl

end

theorem proof : RatioFieldDeg.Statement := by
  intro ι E₁ E₂ _ _ _ _ u v D e h
  have : IsDomain (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u) := isDomain_quot u _ rfl
  have : CharZero (FractionRing (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u)) := charZero_frac u _ rfl
  rw [projDeg_eq (coordIdeal ℤ u) u rfl e, projDeg_eq (coordIdeal ℤ u) v h.symm e]

end RatioFieldDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtGenUniform
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter.AvoidRing (isMultiHomog_mul isMultiHomog_pow)

noncomputable section

namespace ClosedPtGenUniform

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem genNear_of_mul_eq_pow {d : K → ℤ} {a q b : MRingOver S ι} {α β δ : K → ℕ} {m : ℕ}
    (h : GenNear S ι 𝓜 d a α) (hq : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q β) (hab : a * q = b ^ m) (hdeg : m • δ = α + β) :
    GenNear S ι 𝓜 d b δ := by
  intro I x hx
  obtain ⟨n, t, c, r, p, z, ht, htc, hp, hz, he⟩ := h I x hx
  refine ⟨m * n, t, c, r, fun j => q ^ n * p j, z, ht, htc, fun j => ?_, hz, ?_⟩
  · have h' := Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_pow hq n) (hp j)
    convert h' using 1
    funext k
    have hk := congrFun hdeg k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [mul_comm m n, mul_assoc, hk]
    ring
  · rw [pow_mul, ← hab, mul_pow, show a ^ n * q ^ n * t = q ^ n * (a ^ n * t) by ring, mul_smul, he,
      Finset.smul_sum]
    simp_rw [mul_smul]

theorem genNear_mul_pow (hM : GenNearMul.Statement) (hgr : KH.IsMGraded S ι 𝓜) {W : Ideal (MRingOver S ι)}
    (hW : W ≤ Module.annihilator (MRingOver S ι) M) {d n : K → ℤ} {f g : MRingOver S ι} {δ γ : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ) (hfd : GenNear S ι 𝓜 d f δ)
    (hgn : GenNear S ι (KH.quotPart S W) n g γ) :
    ∀ a : ℕ, GenNear S ι 𝓜 (d + a • n) (f * g ^ a) (δ + a • γ) := by
  intro a
  induction a with
  | zero => simpa using hfd
  | succ a ih =>
    have h' := hM S K ι M 𝓜 W (d + a • n) n (f * g ^ a) g (δ + a • γ) γ hgr hW
      (Inter.AvoidRing.isMultiHomog_mul hf (Inter.AvoidRing.isMultiHomog_pow hg a)) hg ih hgn
    rw [succ_nsmul, succ_nsmul, pow_succ, ← mul_assoc, ← add_assoc, ← add_assoc]
    exact h'

end ClosedPtGenUniform


open ClosedPtGenUniform in
theorem ClosedPtGenUniform.proof (hG : GradedSubmodules.Statement) (hF : ClosedPtFibreLift.Statement)
    (hN : ChartNakayamaGen.Statement) (hM : GenNearMul.Statement) : ClosedPtGenUniform.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e P hP
  classical
  obtain ⟨hPprime, hPhom, hPrel⟩ := hP.1
  choose i hi using hPrel

  let I : KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hI : ∀ k, ∀ j ∈ I.1 k, (X ⟨k, j⟩ : MRingOver S ι) ∉ P := by
    intro k j hj
    rw [Finset.mem_singleton.mp hj]
    exact hi k
  have : IsNoetherianRing (MRingOver S ι) := inferInstance

  obtain ⟨hWhom, hMsub⟩ := hG S K ι M 𝓜 hgr
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVPM : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) M) :=
    hV.trans (LinearMap.annihilator_le_of_injective (P • ⊤ : Submodule (MRingOver S ι) M).subtype
      (P • ⊤ : Submodule (MRingOver S ι) M).injective_subtype)
  obtain ⟨cM, hcM⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) M) (subGrading 𝓜 (P • ⊤)) inferInstance
    (hMsub P hPhom).1 hVPM e
  obtain ⟨fM, δM, hfM, hfMP, hgenM⟩ := hN S K ι M 𝓜 P (e + cM • N) hS hfin hgr hPprime hPhom I hI
    (hF S K ι M 𝓜 P (e + cM • N) hS hfin hgr hP (hcM cM le_rfl) I hI)

  set W := Module.annihilator (MRingOver S ι) M with hWdef
  have hWgr : KH.IsMGraded S ι (KH.quotPart S W) := QuotPartGraded.proof S K ι W hWhom
  have hQfin : Module.Finite (MRingOver S ι) (MRingOver S ι ⧸ W) := inferInstance
  obtain ⟨-, hQsub⟩ := hG S K ι (MRingOver S ι ⧸ W) (KH.quotPart S W) hWgr
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ W) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVQ : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ W) := by
    rw [Ideal.annihilator_quotient]
    exact hV
  have hVPQ : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)) :=
    hVQ.trans (LinearMap.annihilator_le_of_injective
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).subtype
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).injective_subtype)
  obtain ⟨cO, hcO⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W))
    (subGrading (KH.quotPart S W) (P • ⊤)) inferInstance (hQsub P hPhom).1 hVPQ 0
  have hgenO : ∀ n : ℕ, cO ≤ n → ∃ (g : MRingOver S ι) (γ : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ ∧ g ∉ P ∧
      GenNear S ι (KH.quotPart S W) (0 + n • N) g γ := fun n hn =>
    hN S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hPprime hPhom I hI
      (hF S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hP (hcO n hn) I hI)
  set n₁ := cO + 1 with hn₁
  obtain ⟨g₁, γ₁, hg₁, hg₁P, hgen₁⟩ := hgenO n₁ (by omega)
  obtain ⟨g₂, γ₂, hg₂, hg₂P, hgen₂⟩ := hgenO (n₁ + 1) (by omega)

  refine ⟨fM * g₁ * g₂, δM + γ₁ + γ₂, cM + n₁ * n₁, Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hfM hg₁) hg₂, ?_, ?_⟩
  · intro hmem
    rcases hPprime.mem_or_mem hmem with h | h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hfMP h
      · exact hg₁P h
    · exact hg₂P h
  intro c hc
  have hpos : 0 < n₁ := by omega
  set q := (c - cM) / n₁ with hq
  set s := (c - cM) % n₁ with hs
  have hdm : n₁ * q + s = c - cM := Nat.div_add_mod (c - cM) n₁
  have hsn : s < n₁ := Nat.mod_lt _ hpos
  have hqn : n₁ ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hpos]
    omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_trans hsn.le hqn)
  have hca : c = cM + a * n₁ + s * (n₁ + 1) := by
    have h1 : c - cM + cM = c := Nat.sub_add_cancel (by omega)
    rw [← h1, ← hdm, ha]
    ring
  have hA := genNear_mul_pow hM hgr le_rfl hfM hg₁ hgenM hgen₁ a
  have hB := genNear_mul_pow hM hgr le_rfl (Inter.AvoidRing.isMultiHomog_mul hfM (Inter.AvoidRing.isMultiHomog_pow hg₁ a)) hg₂ hA hgen₂ s
  have htw : e + cM • N + a • (0 + n₁ • N) + s • (0 + (n₁ + 1) • N) = e + c • N := by
    rw [hca]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    push_cast
    ring
  rw [htw] at hB
  refine genNear_of_mul_eq_pow hB
    (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_pow hfM (a + s)) (Inter.AvoidRing.isMultiHomog_pow hg₁ (s + 1)))
      (Inter.AvoidRing.isMultiHomog_pow hg₂ (a + 1))) (m := a + s + 1) (by ring) ?_
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
