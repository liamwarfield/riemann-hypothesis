module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfHerm

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UnitaryClassMass
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def TensLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ δ : 𝓞 F, δ ≠ 0 ∧ ∀ (t : HeightOneSpectrum (𝓞 F)) (e : E) (c : 𝓞 F),
      (∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) →
      ∃ r ∈ Sw F E t, ∃ y : 𝓞 E, (r : E) * (algebraMap F E (δ : F) * e) = algebraMap F E (c : F) * (y : E)

def LatClose : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsFullLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ S : Submonoid (𝓞 E), (∀ r ∈ S, σ (r : E) = r) →
      (∀ i j, ∃ r ∈ S, ∃ y : 𝓞 E,
        (r : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) =
          algebraMap F E (D' : F) * (y : E)) →
      locS S (gmap (linOf b γ) L0) = locS S (gmap (linOf b g) L0)

theorem closeLoc_of (hT : TensLoc) (hL : LatClose) : CloseLoc := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  obtain ⟨δ, hδ, hTδ⟩ := hT F E
  obtain ⟨D, hD, hDcl⟩ := hL F E σ V M J b L0 hσσ hH hdet hL0 g hg
  refine ⟨δ * D, mul_ne_zero hδ hD, fun D' hD' γ hγ t hcong => ?_⟩
  obtain ⟨k, rfl⟩ := hD'
  refine hDcl (D * k) (dvd_mul_right D k) γ hγ (Sw F E t) ?_ ?_
  · rintro r ⟨a, -, rfl⟩
    change σ (algebraMap F E (a : F)) = algebraMap F E (a : F)
    exact σ.commutes _
  · intro i j
    obtain ⟨s, hs, he⟩ := hcong i j
    obtain ⟨r, hr, y, hry⟩ := hTδ t (((g : Matrix (Fin M) (Fin M) E) i j) - (γ : Matrix (Fin M) (Fin M) E) i j)
      (δ * D * k) ⟨s, hs, by rw [map_sub]; exact he⟩
    refine ⟨r, hr, y, ?_⟩
    have hδF : (δ : F) ≠ 0 := by simpa using hδ
    have hδE : algebraMap F E (δ : F) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hδF
    apply mul_left_cancel₀ hδE
    have e1 : ((δ * D * k : 𝓞 F) : F) = (δ : F) * ((D * k : 𝓞 F) : F) := by push_cast; ring
    rw [e1, map_mul] at hry
    linear_combination hry

theorem hermitian_approximation_of_parts (hL : LocSw) (hT : TensLoc) (hC : LatClose) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := hermApprox_of hL (closeLoc_of hT hC) hW hB hG

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermT
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LocInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) (z : F) (c : 𝓞 F)
    (u : t.adicCompletion F), u ∈ t.adicCompletionIntegers F →
    algebraMap F (t.adicCompletion F) z = algebraMap F (t.adicCompletion F) (c : F) * u →
    ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F, z * (d : F) = (c : F) * (a : F)

def tcoord {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ TensorProduct.map (B.coord k) LinearMap.id

theorem tcoord_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] (x : E) (y : R) :
    tcoord B k R (x ⊗ₜ[F] y) = B.coord k x • y := by
  simp [tcoord]

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LocalIntegralOfSubstitution
open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem local_integral_of_substitution : LocInt := by
  intro F _ _ t z c u hu hz
  by_cases hc : (c : F) = 0
  · refine ⟨1, t.asIdeal.primeCompl.one_mem, 0, ?_⟩
    rw [hc, map_zero, zero_mul] at hz
    have hz0 : z = 0 := (algebraMap F (t.adicCompletion F)).injective (by rw [hz, map_zero])
    simp [hz0]
  · have hxu : algebraMap F (t.adicCompletion F) (z / (c : F)) = u := by
      rw [map_div₀, hz, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hc)]
    have hu' : algebraMap F (t.adicCompletion F) (z / (c : F)) ∈ t.adicCompletionIntegers F :=
      hxu ▸ hu
    have e : ∀ x : F, Valued.v (algebraMap F (t.adicCompletion F) x) = t.valuation F x := by
      intro x
      first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation x
      | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      | rfl
    have hv : t.valuation F (z / (c : F)) ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hu'
      rw [← e]
      exact hu'
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (z / (c : F))
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hvm : t.intValuation m ≠ 0 := HeightOneSpectrum.intValuation_ne_zero t m hm0
    have hnm' : t.intValuation n ≤ t.intValuation m := by
      rw [← hnm, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap] at hv
      exact (div_le_one₀ (zero_lt_iff.2 hvm)).1 hv
    have hI0 : Ideal.span {m} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hm0
    obtain ⟨k, J, hJt, hmJ⟩ := WfDvdMonoid.max_power_factor hI0 t.irreducible
    have hnk : n ∈ t.asIdeal ^ k := by
      have hdm : t.asIdeal ^ k ∣ Ideal.span {m} := ⟨J, hmJ⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hdm
      have hdn := (HeightOneSpectrum.intValuation_le_pow_iff_dvd t n k).1 (hnm'.trans hdm)
      exact Ideal.dvd_span_singleton.1 hdn
    have hJ : ¬ J ≤ t.asIdeal := fun h => hJt (Ideal.dvd_iff_le.2 h)
    obtain ⟨d, hdJ, hdt⟩ := SetLike.not_le_iff_exists.1 hJ
    have hdn : d * n ∈ Ideal.span {m} := by
      rw [hmJ, mul_comm d n]
      exact Ideal.mul_mem_mul hnk hdJ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hdn
    refine ⟨d, hdt, a, ?_⟩
    have hmF : algebraMap (𝓞 F) F m ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have ha' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F m =
        algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F n := by
      rw [← map_mul, ← map_mul, ha]
    have hzm : z * algebraMap (𝓞 F) F m = (c : F) * algebraMap (𝓞 F) F n := by
      have h3 : z = (c : F) * (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F m) := by
        rw [hnm]
        field_simp
      rw [h3, mul_assoc, div_mul_cancel₀ _ hmF]
    show z * algebraMap (𝓞 F) F d = (c : F) * algebraMap (𝓞 F) F a
    apply mul_right_cancel₀ hmF
    linear_combination (algebraMap (𝓞 F) F d) * hzm - (c : F) * ha'

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.TcoordBound
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

namespace HX

section T

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tensA (t : HeightOneSpectrum (𝓞 F)) : AddSubgroup (E ⊗[F] t.adicCompletion F) :=
  AddSubgroup.closure {w | ∃ x ∈ PI.UnitaryApproxDefs.intOE E, ∃ y ∈ t.adicCompletionIntegers F, w = x ⊗ₜ[F] y}

theorem tensA_mul (t : HeightOneSpectrum (𝓞 F)) {a b : E ⊗[F] t.adicCompletion F}
    (ha : a ∈ tensA (E := E) t) (hb : b ∈ tensA (E := E) t) : a * b ∈ tensA (E := E) t := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha' =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb' =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ha'
      obtain ⟨x', hx', y', hy', rfl⟩ := hb'
      apply AddSubgroup.subset_closure
      exact ⟨x * x', (PI.UnitaryApproxDefs.intOE E).mul_mem hx hx', y * y',
        mul_mem hy hy', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
    | zero => rw [mul_zero]; exact (tensA (E := E) t).zero_mem
    | add b c _ _ hb hc => rw [mul_add]; exact (tensA (E := E) t).add_mem hb hc
    | neg b _ hb => rw [mul_neg]; exact (tensA (E := E) t).neg_mem hb
  | zero => rw [zero_mul]; exact (tensA (E := E) t).zero_mem
  | add a c _ _ ha hc => rw [add_mul]; exact (tensA (E := E) t).add_mem ha hc
  | neg a _ ha => rw [neg_mul]; exact (tensA (E := E) t).neg_mem ha

theorem tensInt_le (t : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] t.adicCompletion F}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring) :
    s ∈ tensA (E := E) t := by
  unfold PI.UnitaryApproxDefs.tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact AddSubgroup.subset_closure ⟨x, hx, 1, (t.adicCompletionIntegers F).one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, y, hy, rfl⟩
  | zero => exact (tensA (E := E) t).zero_mem
  | one => exact AddSubgroup.subset_closure ⟨1, (PI.UnitaryApproxDefs.intOE E).one_mem, 1,
      (t.adicCompletionIntegers F).one_mem, rfl⟩
  | add a b _ _ ha hb => exact (tensA (E := E) t).add_mem ha hb
  | neg a _ ha => exact (tensA (E := E) t).neg_mem ha
  | mul a b _ _ ha hb => exact tensA_mul t ha hb

theorem intInt (t : HeightOneSpectrum (𝓞 F)) {z : F} (hz : IsIntegral ℤ z) :
    algebraMap F (t.adicCompletion F) z ∈ t.adicCompletionIntegers F := by
  obtain ⟨r, rfl⟩ : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = z := ⟨⟨z, hz⟩, rfl⟩
  first
  | exact HeightOneSpectrum.coe_mem_adicCompletionIntegers t r
  | (rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
     exact HeightOneSpectrum.intValuation_le_one t r)
  | (rw [HeightOneSpectrum.mem_adicCompletionIntegers]
     simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
       HeightOneSpectrum.intValuation_le_one])

theorem tcoord_bound {ι : Type} (B : Module.Basis ι F E) (m : ℤ)
    (hm : ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x)) (t : HeightOneSpectrum (𝓞 F))
    (c : 𝓞 F) (k : ι) {s : E ⊗[F] t.adicCompletion F} (hs : s ∈ tensA (E := E) t) :
    ∃ u ∈ t.adicCompletionIntegers F, (m : t.adicCompletion F) *
        tcoord B k (t.adicCompletion F) (PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) =
      algebraMap F (t.adicCompletion F) (c : F) * u := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hs'
    refine ⟨algebraMap F (t.adicCompletion F) ((m : F) * B.coord k x) * y,
      mul_mem (intInt t (hm x hx k)) hy, ?_⟩
    have e1 : PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) *
        (x ⊗ₜ[F] y) = (algebraMap F E (c : F) * x) ⊗ₜ[F] y := by
      simp [PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, tcoord_tmul, ← Algebra.smul_def (c : F) x, map_smul, smul_eq_mul, Algebra.smul_def]
    simp only [map_mul, map_intCast]
    ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u1, hu1, e1⟩ := ha
    obtain ⟨u2, hu2, e2⟩ := hb
    refine ⟨u1 + u2, add_mem hu1 hu2, ?_⟩
    rw [mul_add, map_add (f := _), mul_add, e1, e2, mul_add]
  | neg a _ ha =>
    obtain ⟨u1, hu1, e1⟩ := ha
    refine ⟨-u1, neg_mem hu1, ?_⟩
    rw [mul_neg, map_neg, mul_neg, e1, mul_neg]

private theorem exists_int_mul_isIntegral' {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * e) := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hI : Ideal.span {d} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hc : (Ideal.span {d}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ := fun h =>
    hI (Ideal.eq_bot_of_comap_eq_bot h)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hm
  obtain ⟨k, hk⟩ := hm
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hmE : (m : E) = algebraMap (𝓞 E) E k * algebraMap (𝓞 E) E d := by
    rw [← map_mul, hk]
    simp
  have hw : algebraMap (𝓞 E) E (k * n) = (m : E) * e := by
    rw [← hnd, hmE, map_mul]
    field_simp
    try ring
  refine ⟨m, hm0, ?_⟩
  rw [← hw]
  exact NumberField.RingOfIntegers.isIntegral_coe (k * n)

theorem coordBound {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x) := by
  classical
  let bw := NumberField.RingOfIntegers.basis E
  choose m hm hmi using fun (p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × ι) =>
    exists_int_mul_isIntegral' (B.coord p.2 (algebraMap (𝓞 E) E (bw p.1)))
  refine ⟨∏ p, m p, Finset.prod_ne_zero_iff.2 fun p _ => hm p, fun x hx k => ?_⟩
  obtain ⟨w, rfl⟩ := hx
  have hx' : algebraMap (𝓞 E) E w = ∑ i, ((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i) := by
    conv_lhs => rw [← bw.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [show B.coord k (((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i)) =
      ((bw.repr w i : ℤ) : F) * B.coord k (algebraMap (𝓞 E) E (bw i)) by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, k))
  have hq' : IsIntegral ℤ (((q * (bw.repr w i) : ℤ)) : F) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F (q * bw.repr w i)))
  convert hq'.mul (hmi (i, k)) using 1
  rw [hq]
  push_cast
  ring

theorem basisInt {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k, IsIntegral ℤ ((n : E) * B k) := by
  classical
  choose m hm hmi using fun k => exists_int_mul_isIntegral' (B k)
  refine ⟨∏ k, m k, Finset.prod_ne_zero_iff.2 fun k _ => hm k, fun k => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
  have hq' : IsIntegral ℤ ((q : E)) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E q))
  rw [hq, Int.cast_mul, mul_comm ((m k : ℤ) : E), mul_assoc]
  exact hq'.mul (hmi k)

end T

end HX


open HX in
theorem tensLocX_of (hI : LocInt) : TensLoc := by
  intro F E _ _ _ _ _
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨m, hm0, hm⟩ := coordBound B
  obtain ⟨n, hn0, hn⟩ := basisInt B
  refine ⟨((m * n : ℤ) : 𝓞 F), Int.cast_ne_zero.2 (mul_ne_zero hm0 hn0), ?_⟩
  rintro t e c ⟨s, hs, hse⟩
  have hsA := tensInt_le t hs
  have hk : ∀ k, ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F,
      ((m : F) * B.coord k e) * (d : F) = (c : F) * (a : F) := by
    intro k
    obtain ⟨u, hu, hue⟩ := tcoord_bound B m hm t c k hsA
    rw [← hse] at hue
    have h2 : tcoord B k (t.adicCompletion F)
        (PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e) =
          algebraMap F (t.adicCompletion F) (B.coord k e) := by
      simp [PI.UnitaryApproxDefs.inclE, tcoord_tmul, Algebra.smul_def]
    rw [h2] at hue
    exact hI F t ((m : F) * B.coord k e) c u hu (by rw [map_mul, map_intCast]; exact hue)
  choose d hd a ha using hk
  let D : 𝓞 F := ∏ k, d k
  have hD : D ∈ t.asIdeal.primeCompl := prod_mem fun k _ => hd k
  choose q hq using fun k => Finset.dvd_prod_of_mem d (Finset.mem_univ k)
  let β : _ → 𝓞 E := fun k => ⟨(n : E) * B k, hn k⟩
  have hcoeF : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (x : F) := by
    intro x
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have key : ∀ k, ((D : 𝓞 F) : F) * ((m : F) * B.coord k e) = (c : F) * ((a k * q k : 𝓞 F) : F) := by
    intro k
    have h1 : ((D : 𝓞 F) : F) = ((d k * q k : 𝓞 F) : F) := congrArg (fun x : 𝓞 F => (x : F)) (hq k)
    rw [h1]
    push_cast
    linear_combination (q k : F) * ha k
  refine ⟨algebraMap (𝓞 F) (𝓞 E) D, Submonoid.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hD,
    ∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k, ?_⟩
  have hy : ((∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k : 𝓞 E) : E) =
      ∑ k, algebraMap F E ((a k * q k : 𝓞 F) : F) * ((n : E) * B k) := by
    show algebraMap (𝓞 E) E (∑ k, algebraMap (𝓞 F) (𝓞 E) (a k * q k) * β k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) (hcoeF _) rfl
  rw [hcoeF, hy]
  conv_lhs => rw [← B.sum_repr e]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, ← Module.Basis.coord_apply]
  have hk2 := congrArg (algebraMap F E) (key k)
  push_cast at hk2 ⊢
  simp only [map_mul, map_intCast] at hk2 ⊢
  linear_combination ((n : E) * B k) * hk2

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LatticesCloseLocally
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.GmapLeLocS
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Glob

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

private theorem mem_locS_iff' (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) (x : V) :
    x ∈ locS S X ↔ ∃ s ∈ S, s • x ∈ X := Iff.rfl

theorem locS_mono (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h : X ≤ Y) : locS S X ≤ locS S Y := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := hx
  exact (mem_locS_iff' S Y x).2 ⟨s, hs, h hx⟩

theorem le_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : X ≤ locS S X := fun x hx => (mem_locS_iff' S X x).2 ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_locS (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) : locS S (locS S X) = locS S X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, t, ht, hx⟩ := hx
    exact (mem_locS_iff' S X x).2 ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩
  · exact le_locS S _

theorem locS_eq_of (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h1 : X ≤ locS S Y) (h2 : Y ≤ locS S X) :
    locS S X = locS S Y := le_antisymm ((locS_mono S h1).trans (locS_locS S Y).le) ((locS_mono S h2).trans (locS_locS S X).le)

theorem osmul_comm (u : V ≃ₗ[E] V) (s : 𝓞 E) (w : V) : u (s • w) = s • u w := by
  rw [← algebraMap_smul E s w, map_smul, algebraMap_smul]

theorem gmap_locS (u : V ≃ₗ[E] V) (S : Submonoid (𝓞 E)) (X : Submodule (𝓞 E) V) :
    gmap u (locS S X) = locS S (gmap u X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    mem_locS_iff']
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, osmul_comm u s y⟩
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨u.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have hsz : s • u.symm x = z := by
      apply u.injective
      rw [osmul_comm, LinearEquiv.apply_symm_apply, hzx]
    rw [hsz]
    exact hz

theorem gmap_comp (u w : V ≃ₗ[E] V) (X : Submodule (𝓞 E) V) : gmap (u * w) X = gmap u (gmap w X) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨w y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem gmap_le_locS (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (S : Submonoid (𝓞 E))
    (K : GL (Fin M) E)
    (h : ∀ x ∈ crdOf b L0, ∃ s ∈ S, (algebraMap (𝓞 E) E s) • (K : Matrix (Fin M) (Fin M) E).mulVec x ∈ crdOf b L0) :
    gmap (linOf b K) L0 ≤ locS S L0 := by
  intro y hy
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hx : (b.repr v : Fin M → E) ∈ crdOf b L0 := by
    show ∑ i, b.repr v i • b i ∈ L0
    rw [b.sum_repr]
    exact hv
  obtain ⟨s, hs, hK⟩ := h _ hx
  refine (mem_locS_iff' S L0 _).2 ⟨s, hs, ?_⟩
  have e : linOf b K v = ∑ j, ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v)) j • b j := by
    simp only [linOf, LinearEquiv.ofLinear_apply, Matrix.toLin_apply]
  have hK' : ∑ i, ((algebraMap (𝓞 E) E s) • ((K : Matrix (Fin M) (Fin M) E).mulVec (b.repr v))) i • b i ∈ L0 := hK
  rw [e, ← algebraMap_smul E s, Finset.smul_sum]
  convert hK' using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

private theorem sum_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type}
    (t : Finset ι) (z : ι → Fin M → E) (hz : ∀ i ∈ t, z i ∈ crdOf b L0) :
    ∑ i ∈ t, z i ∈ crdOf b L0 := by
  show ∑ j, (∑ i ∈ t, z i) j • b j ∈ L0
  simp only [Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact L0.sum_mem fun i hi => hz i hi

private theorem algebraMap_smul_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 E)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • x ∈ crdOf b L0 := by
  show ∑ j, ((algebraMap (𝓞 E) E s) • x) j • b j ∈ L0
  have h := L0.smul_mem s (show ∑ j, x j • b j ∈ L0 from hx)
  rw [Finset.smul_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]

private theorem add_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {x y : Fin M → E} (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ j, (x + y) j • b j ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy

theorem glob_stab {F : Type} [Field F] [Algebra F E] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {u k : ℕ} (hu : ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ crdOf b L0)
    (Y : Matrix (Fin M) (Fin M) E) (s : 𝓞 E) (e : Fin M → Fin M → E) (he : ∀ i j, IsIntegral ℤ (e i j))
    (hY : ∀ i j, (algebraMap (𝓞 E) E s) * (Y - 1) i j = ((u * k : ℕ) : E) * e i j)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • Y.mulVec x ∈ crdOf b L0 := by
  have key : ∀ i0, (algebraMap (𝓞 E) E s) * (Y.mulVec x) i0 =
      (algebraMap (𝓞 E) E s) * x i0 + ∑ j, ((k : F) • (e i0 j * ((u : F) • x j))) := by
    intro i0
    have hsplit : ∀ j, (algebraMap (𝓞 E) E s) * Y i0 j =
        ((u * k : ℕ) : E) * e i0 j + (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin M) (Fin M) E) i0 j := by
      intro j
      have hj := hY i0 j
      rw [Matrix.sub_apply, mul_sub] at hj
      linear_combination hj
    show (algebraMap (𝓞 E) E s) * ∑ j, Y i0 j * x j = _
    simp only [Finset.mul_sum, ← mul_assoc, hsplit, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Algebra.smul_def, map_natCast]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hvec : (algebraMap (𝓞 E) E s) • Y.mulVec x = (algebraMap (𝓞 E) E s) • x +
      ∑ i, ∑ j, Pi.single i ((k : F) • (e i j * ((u : F) • x j))) := by
    funext i0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [key i0]
    congr 1
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hvec]
  exact add_mem_crdOf b L0 (algebraMap_smul_mem_crdOf b L0 s hx)
    (sum_mem_crdOf b L0 _ _ fun i _ => sum_mem_crdOf b L0 _ _ fun j _ =>
      hk i _ ((he i j).mul (hu x hx j)))

end Glob

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Lin

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}

theorem linOf_mul (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, LinearEquiv.mul_apply, equivFun_linOf, equivFun_linOf, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem linOf_one (b : Module.Basis (Fin M) E V) : linOf b (1 : GL (Fin M) E) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, Units.val_one, Matrix.one_mulVec]
  rfl

end Lin

theorem gmap_one {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (X : Submodule (𝓞 E) V) : gmap (1 : V ≃ₗ[E] V) X = X := by
  ext v
  simp [gmap, Submodule.mem_map]

theorem lattices_close_locally : LatClose := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  classical
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL0
  obtain ⟨u, hu, hu'⟩ := up_nat (crdOf b L0) ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat (crdOf b L0) ⟨c2, hc2, hlow⟩
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹
  obtain ⟨dg, hdg, hdgi⟩ := mat_den ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
  set Nn : ℕ := dg * dI * dJ * (u * k) with hNn
  have hNpos : 0 < Nn := by positivity
  refine ⟨(Nn : 𝓞 F), by exact_mod_cast hNpos.ne', fun D' hD' γ hγ S hS hcong => ?_⟩
  obtain ⟨c, rfl⟩ := hD'
  choose r hr y hy using hcong
  set R : 𝓞 E := ∏ q : Fin M × Fin M, r q.1 q.2 with hRd
  have hRS : R ∈ S := Submonoid.prod_mem _ fun q _ => hr q.1 q.2
  set cE : E := algebraMap F E ((c : 𝓞 F) : F) with hcE
  have hcEi : IsIntegral ℤ cE := c.isIntegral_coe.algebraMap
  have hz : ∀ i j, ∃ z : E, IsIntegral ℤ z ∧
      (R : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) = (Nn : E) * cE * z := by
    intro i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun q : Fin M × Fin M => r q.1 q.2) (Finset.mem_univ (i, j))
    refine ⟨(q : E) * (y i j : E), q.isIntegral_coe.mul (y i j).isIntegral_coe, ?_⟩
    have e1 : (R : E) = (r i j : E) * (q : E) := by rw [hRd, hq]; push_cast; rfl
    rw [e1, mul_comm (r i j : E) (q : E), mul_assoc, hy i j]
    have e2 : algebraMap F E (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : E) * cE := by
      have e5 : (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : F) * ((c : 𝓞 F) : F) := by push_cast; ring
      rw [e5, map_mul, map_natCast]
    rw [e2]; ring
  choose z hzi hze using hz
  set gi : Matrix (Fin M) (Fin M) E := ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hgi
  set K : GL (Fin M) E := g⁻¹ * γ with hKd
  set Km : Matrix (Fin M) (Fin M) E := (K : Matrix (Fin M) (Fin M) E) with hKm
  have hgig : gi * (g : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  set e0 : Fin M → Fin M → E := fun i j => -cE * ∑ l, ((dg : E) * gi i l) * z l j with he0d
  have he0i : ∀ i j, IsIntegral ℤ (e0 i j) := fun i j =>
    (hcEi.neg).mul (IsIntegral.sum _ fun l _ => (hdgi i l).mul (hzi l j))
  have hK1 : ∀ i j, (algebraMap (𝓞 E) E R) * (Km - 1) i j = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * e0 i j) := by
    intro i j
    have eK : Km - 1 = gi * ((γ : Matrix (Fin M) (Fin M) E) - (g : Matrix (Fin M) (Fin M) E)) := by
      rw [hKm, hKd, Units.val_mul, Matrix.mul_sub, hgig]
    rw [eK, Matrix.mul_apply, Finset.mul_sum, he0d]
    simp only [Matrix.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hze l j
    change (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) = _
    have e3 : (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) =
        -(gi i l * ((R : E) * ((g : Matrix (Fin M) (Fin M) E) l j - (γ : Matrix (Fin M) (Fin M) E) l j))) := by ring
    rw [e3, this, hNn]
    push_cast
    ring

  have hKu : K ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J := (PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).mul_mem ((PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).inv_mem hg) hγ
  have hKu' : PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km = J := hKu
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  set KImage : Matrix (Fin M) (Fin M) E := ((K⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hKim
  have hKK : Km * KImage = 1 := by rw [hKm, hKim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKinv : KImage = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by
    calc KImage = J⁻¹ * J * KImage := by rw [hJJ, Matrix.one_mul]
      _ = J⁻¹ * (PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km) * KImage := by rw [hKu']
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * (Km * KImage) := by simp only [Matrix.mul_assoc]
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by rw [hKK, Matrix.mul_one]
  have hcs : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) = PI.UnitaryApproxDefs.cT (σ : E →+* E) Km - 1 := by
    have h1 := PI.UnitaryApproxDefs.cT_one (n := Fin M) (σ : E →+* E)
    unfold PI.UnitaryApproxDefs.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hKi1 : KImage - 1 = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) * J := by
    rw [hKinv, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hR0 : σ (algebraMap (𝓞 E) E R) = algebraMap (𝓞 E) E R := hS R hRS
  have hK2 : ∀ i j, (algebraMap (𝓞 E) E R) * (KImage - 1) i j = ((u * k : ℕ) : E) *
      (∑ a, ∑ b', ((dI : E) * J⁻¹ i a) * σ (e0 b' a) * ((dJ : E) * J b' j)) := by
    intro i j
    rw [hKi1]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => ?_
    have hσK : (algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a) = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * σ (e0 b' a)) := by
      rw [← hR0, ← map_mul, hK1 b' a, map_mul, map_mul, map_natCast, map_natCast]
    have hX : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) a b' = σ ((Km - 1) b' a) := rfl
    rw [hX]
    calc (algebraMap (𝓞 E) E R) * (J⁻¹ i a * σ ((Km - 1) b' a) * J b' j)
        = J⁻¹ i a * ((algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a)) * J b' j := by ring
      _ = _ := by rw [hσK]; push_cast; ring

  have h1 : gmap (linOf b K) L0 ≤ locS S L0 := gmap_le_locS b L0 S K fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' Km R _ (fun i j => (isIntegral_natCast _).mul (he0i i j)) hK1 hx⟩
  have h2 : gmap (linOf b K⁻¹) L0 ≤ locS S L0 := gmap_le_locS b L0 S K⁻¹ fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' KImage R _ (fun i j => IsIntegral.sum _ fun a _ =>
      IsIntegral.sum _ fun b' _ => ((hdIi i a).mul (int_sigma (σ : E →+* E) (he0i b' a))).mul (hdJi b' j)) hK2 hx⟩
  have h3 : L0 ≤ locS S (gmap (linOf b K) L0) := by
    have e4 : gmap (linOf b K) (gmap (linOf b K⁻¹) L0) = L0 := by
      rw [← gmap_comp, ← linOf_mul, mul_inv_cancel, linOf_one, gmap_one]
    calc L0 = gmap (linOf b K) (gmap (linOf b K⁻¹) L0) := e4.symm
      _ ≤ gmap (linOf b K) (locS S L0) := Submodule.map_mono h2
      _ = locS S (gmap (linOf b K) L0) := gmap_locS _ S L0
  have hKeq : locS S (gmap (linOf b K) L0) = locS S L0 := locS_eq_of S h1 h3
  have hγK : γ = g * K := by rw [hKd, mul_inv_cancel_left]
  rw [hγK, linOf_mul, gmap_comp, ← gmap_locS, hKeq, gmap_locS]

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermXB
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem local_switching_lattice : LocSw := by
  intro F E _ _ _ _ _ _ σ hσ hfix V _ _ p hp t ht X
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, star_star]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have hcomm : ∀ c : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c) =
      algebraMap F E (algebraMap (𝓞 F) F c) := by
    intro c
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hSw : Sw F E t ≤ hcompl (K := E) p := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.1 hs
    apply Submonoid.subset_closure
    rw [Set.mem_setOf_eq]
    have hcp : algebraMap (𝓞 F) (𝓞 E) c ∉ p := by
      intro h'
      apply Ideal.mem_primeCompl_iff.1 hc
      rw [ht, Ideal.mem_comap]
      exact h'
    refine ⟨hcp, fun t' ht' => ?_⟩
    have h3 : t' = algebraMap (𝓞 F) (𝓞 E) c := by
      apply hinj
      rw [ht', hcomm, ← hσ, AlgHom.commutes]
    rw [h3]
    exact hcp
  have key : ∀ s ∈ hcompl (K := E) p, ∃ r : 𝓞 E, r * s ∈ Sw F E t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨hsp, hconj⟩ := hs
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E s)) :=
        (NumberField.RingOfIntegers.isIntegral_coe s).map σ.toRingHom.toIntAlgHom
      let sb : 𝓞 E := ⟨σ (algebraMap (𝓞 E) E s), hint⟩
      have hsb : algebraMap (𝓞 E) E sb = star (algebraMap (𝓞 E) E s) := by
        rw [← hσ]
        rfl
      have hsbp : sb ∉ p := hconj sb hsb
      have hfixN : σ (algebraMap (𝓞 E) E (sb * s)) = algebraMap (𝓞 E) E (sb * s) := by
        rw [map_mul, map_mul, hsb, ← hσ, hσσ, mul_comm]
      obtain ⟨c, hc⟩ := hfix _ hfixN
      have hcint : IsIntegral ℤ c := by
        rw [← isIntegral_algebraMap_iff (B := E), hc]
        exact NumberField.RingOfIntegers.isIntegral_coe (sb * s)
      let c' : 𝓞 F := ⟨c, hcint⟩
      have hc' : algebraMap (𝓞 F) (𝓞 E) c' = sb * s := by
        apply hinj
        rw [hcomm, ← hc]
        rfl
      refine ⟨sb, Submonoid.mem_map.2 ⟨c', ?_, hc'⟩⟩
      rw [Ideal.mem_primeCompl_iff, ht, Ideal.mem_comap, hc']
      exact fun h' => (hp.isPrime.mem_or_mem h').elim hsbp hsp
    | one => exact ⟨1, by rw [one_mul]; exact (Sw F E t).one_mem⟩
    | mul x y _ _ hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      refine ⟨r1 * r2, ?_⟩
      rw [show r1 * r2 * (x * y) = r1 * x * (r2 * y) by ring]
      exact (Sw F E t).mul_mem h1 h2
  unfold loc
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := key s hs
    exact (show ∃ s ∈ Sw F E t, s • x ∈ X from
      ⟨r * s, hr, by rw [mul_smul]; exact X.smul_mem r hsx⟩)
  · rintro ⟨s, hs, hsx⟩
    exact (show ∃ s ∈ hcompl (K := E) p, s • x ∈ X from ⟨s, hSw hs, hsx⟩)

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermC
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem wPlace : WPlace := by
  intro F E _ _ _ _ _ p hp h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)
    (Ideal.eq_bot_of_comap_eq_bot h)

theorem bcU : BcU := by
  intro F E _ _ _ σ M J R _ _ g hg
  have key : ∀ A : Matrix (Fin M) (Fin M) E,
      PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ R)
          (A.map (PI.UnitaryApproxDefs.inclE (F := F) R)) =
        (PI.UnitaryApproxDefs.cT (σ : E →+* E) A).map (PI.UnitaryApproxDefs.inclE (F := F) R) := by
    intro A
    ext i j
    simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
  have hg' : PI.UnitaryApproxDefs.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
      (g : Matrix (Fin M) (Fin M) E) = J := hg
  change PI.UnitaryApproxDefs.cT _ _ * _ * _ = _
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.mapMatrix_apply]
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem gramOK : GramOK := by
  intro F E _ _ _ _ σ hσ V _ _ _ h M b hsy hnd
  refine ⟨?_, ?_⟩
  · unfold PI.UnitaryApproxDefs.IsHerm PI.UnitaryApproxDefs.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, AlgHom.coe_toRingHom, hσ, gramOf]
    rw [← starRingEnd_apply]
    exact hsy.eq (b j) (b i)
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hc0
    have hbw : ∀ i, h (b i) (∑ j, c j • b j) = 0 := by
      intro i
      have hi := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply] at hi
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hw : ∀ x, h x (∑ j, c j • b j) = 0 := by
      intro x
      generalize hwd : (∑ j, c j • b j) = w at hbw ⊢
      rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbw, smul_zero,
        Finset.sum_const_zero]
    have hw0 := hnd.2 _ hw
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hw0 j

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem tensor_localization : TensLoc := tensLocX_of local_integral_of_substitution

theorem hermitian_approximation : HermApprox :=
  hermitian_approximation_of_parts local_switching_lattice tensor_localization lattices_close_locally wPlace bcU gramOK

theorem unitary_class_mass : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_herm hermitian_approximation

set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.tensor_localization
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

theorem unitary_class_mass_hermitian : PI.UJClassMass2.UJClassMass :=
  PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
