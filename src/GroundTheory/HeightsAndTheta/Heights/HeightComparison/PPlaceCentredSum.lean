module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain Ideal

namespace PlaceCentredSum

variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

noncomputable def below (v : FinitePlace K) : HeightOneSpectrum (𝓞 L) where
  asIdeal := v.maximalIdeal.asIdeal.under (𝓞 L)
  isPrime := inferInstance
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    exact comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

instance (v : FinitePlace K) : v.maximalIdeal.asIdeal.LiesOver (below (L := L) v).asIdeal := ⟨rfl⟩

noncomputable def deg (L : Type) [Field L] [NumberField L] [Algebra L K] (v : FinitePlace K) : ℕ :=
  v.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) * v.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)

lemma toNNReal_pow {b c : NNReal} (hc : c ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0) (h : c = b ^ f)
    (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hc z = WithZeroMulInt.toNNReal hb z ^ f := by
  subst h
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ hz, WithZeroMulInt.toNNReal_neg_apply _ hz,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem apply_algebraMap (v : FinitePlace K) (x : L) :
    v (algebraMap L K x) = FinitePlace.mk (below v) x ^ deg L v := by
  have hQ : (below (L := L) v).asIdeal ≠ ⊥ := (below v).ne_bot
  have hf : (below (L := L) v).asIdeal.inertiaDeg' v.maximalIdeal.asIdeal ≠ 0 :=
    (inertiaDeg'_pos' _ _).ne'
  have hN := absNorm_eq_pow_inertiaDeg'_of_liesOver v.maximalIdeal.asIdeal (below (L := L) v).asIdeal
    inferInstance hQ
  rw [← FinitePlace.norm_embedding_eq v, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    FinitePlace.norm_embedding', ← HeightOneSpectrum.valuation_liesOver K (below (L := L) v) v.maximalIdeal, map_pow,
    toNNReal_pow _ (NumberField.HeightOneSpectrum.absNorm_ne_zero (below (L := L) v)) hf (by rw [hN]; push_cast; rfl), deg,
    inertiaDeg'_eq_inertiaDeg, ← pow_mul]
  push_cast
  rw [mul_comm]

lemma deg_ne_zero (v : FinitePlace K) : deg L v ≠ 0 := by
  refine mul_ne_zero ?_ (inertiaDeg_pos _ _).ne'
  rw [← ramificationIdx'_eq_ramificationIdx _ _ (below (L := L) v).ne_bot]
  exact IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (below v).ne_bot

theorem centred_iff (O : Subalgebra ℤ L) (m : Ideal O) (v : FinitePlace K) :
    AbsCentredAt O m (fun u ↦ v (algebraMap L K u)) ↔
      AbsCentredAt O m (fun u ↦ FinitePlace.mk (below v) u) := by
  have h1 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v ≤ 1 ↔ a ≤ 1) := fun a ha ↦
    pow_le_one_iff_of_nonneg ha (deg_ne_zero v)
  have h2 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v < 1 ↔ a < 1) := fun a ha ↦
    pow_lt_one_iff_of_nonneg ha (deg_ne_zero v)
  unfold AbsCentredAt
  simp only [apply_algebraMap]
  exact and_congr (forall_congr' fun u ↦ h1 _ (apply_nonneg _ _))
    (forall_congr' fun u ↦ by rw [h2 _ (apply_nonneg _ _)])

theorem neg_log_apply (v : FinitePlace K) (t : L) :
    -Real.log (v (algebraMap L K t)) = deg L v * -Real.log (FinitePlace.mk (below v) t) := by
  rw [apply_algebraMap, Real.log_pow]
  ring

noncomputable def fibreEquiv (Q : HeightOneSpectrum (𝓞 L)) :
    {v : FinitePlace K // below v = Q} ≃ Q.asIdeal.primesOver (𝓞 K) where
  toFun v := ⟨v.1.maximalIdeal.asIdeal, inferInstance, ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
  invFun P := ⟨FinitePlace.mk ⟨P.1, P.2.1, ne_bot_of_liesOver_of_ne_bot Q.ne_bot P.1⟩, by
    ext1
    simp only [below, FinitePlace.maximalIdeal_mk]
    exact P.2.2.over.symm⟩
  left_inv v := Subtype.ext (FinitePlace.mk_maximalIdeal v.1)
  right_inv P := Subtype.ext (by simp only [FinitePlace.maximalIdeal_mk])

noncomputable instance (Q : HeightOneSpectrum (𝓞 L)) : Fintype {v : FinitePlace K // below v = Q} :=
  Fintype.ofEquiv _ (fibreEquiv Q).symm

theorem sum_fibre (Q : HeightOneSpectrum (𝓞 L)) :
    ∑ v : {v : FinitePlace K // below v = Q}, deg L v.1 = Module.finrank L K := by
  rw [← (fibreEquiv Q).symm.sum_comp, IsFractionRing.finrank_eq (𝓞 L) L (𝓞 K) K,
    ← sum_ramification_inertia_eq_finrank Q.asIdeal (𝓞 K)]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  simp only [deg, fibreEquiv, Equiv.coe_fn_symm_mk, FinitePlace.maximalIdeal_mk]

lemma finsum_fibre {α β : Type*} (π : α → β) [∀ b, Fintype {a // π a = b}] (n : α → ℕ) (N : ℕ)
    (g : β → ℝ) (hg : g.support.Finite) (hsum : ∀ b, ∑ a : {a // π a = b}, n a.1 = N) :
    ∑ᶠ a, (n a : ℝ) * g (π a) = N * ∑ᶠ b, g b := by
  classical
  have hfin : ∀ b, (π ⁻¹' {b}).Finite := fun b ↦
    Set.finite_coe_iff.mp (Finite.of_fintype {a // π a = b})
  have hA : (π ⁻¹' g.support).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact hg.biUnion fun b _ ↦ hfin b
  rw [finsum_eq_sum_of_support_subset _ (s := hA.toFinset) ?_,
    finsum_eq_sum_of_support_subset _ (s := hg.toFinset) (by simp), Finset.mul_sum]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := hA.toFinset) (t := hg.toFinset) (g := π)
      (fun a ha ↦ by simpa using ha)]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.sum_subtype (p := fun a ↦ π a = b) _ (fun a ↦ by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact ⟨And.right, fun h ↦ ⟨by rw [h]; simpa using hb, h⟩⟩)]
    have : ∀ a : {a // π a = b}, (n a.1 : ℝ) * g (π a.1) = n a.1 * g b := fun a ↦ by rw [a.2]
    rw [Fintype.sum_congr _ _ this, ← Finset.sum_mul, ← Nat.cast_sum, hsum]
  · intro a ha
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Function.mem_support]
    exact right_ne_zero_of_mul ha

theorem proof : PlaceCentredSum.Statement := by
  intro L K _ _ _ _ _ O m t
  classical
  let g : HeightOneSpectrum (𝓞 L) → ℝ := fun Q ↦
    if AbsCentredAt O m (fun u ↦ FinitePlace.mk Q u) then -Real.log (FinitePlace.mk Q t) else 0
  have hL : ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t) =
      ∑ᶠ Q, g Q := by
    rw [finsum_mem_def, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun Q ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, FinitePlace.equivHeightOneSpectrum,
      Equiv.coe_fn_symm_mk]
    exact if_congr Iff.rfl rfl rfl
  have hK : ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
      -Real.log (v (algebraMap L K t)) = ∑ᶠ v : FinitePlace K, (deg L v : ℝ) * g (below v) := by
    rw [finsum_mem_def]
    refine finsum_congr fun v ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, centred_iff, neg_log_apply]
    split_ifs <;> simp
  have hg : g.support.Finite := by
    rcases eq_or_ne t 0 with rfl | ht
    · refine Set.finite_empty.subset fun Q hQ ↦ ?_
      simp [g] at hQ
    · refine ((FinitePlace.hasFiniteMulSupport ht).preimage
        (fun a _ b _ h ↦ FinitePlace.mk_eq_iff.mp h)).subset fun Q hQ ↦ ?_
      simp only [Function.mem_support, g] at hQ
      split_ifs at hQ
      · simp only [Set.mem_preimage, Function.mem_mulSupport]
        intro h1
        exact hQ (by simp [h1])
      · exact absurd rfl hQ
  rw [hK, hL]
  exact finsum_fibre below (deg L) _ g hg sum_fibre

end PlaceCentredSum

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain

namespace CentredRingNormal

variable {L : Type} [Field L] [NumberField L]


omit [NumberField L] in
theorem isIntegral_of_comp {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R L] [Algebra R' L]
    (f : R →+* R') (hf : (algebraMap R' L).comp f = algebraMap R L) {x : L}
    (hx : IsIntegral R x) : IsIntegral R' x := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hf]; exact hpx⟩

theorem mem_valuationSubring_iff_place (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    x ∈ (v.valuation L).valuationSubring ↔ FinitePlace.mk v x ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    NNReal.coe_le_one,
    ← map_one (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)),
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le]

theorem exists_place_of_valuationSubring (V : ValuationSubring L) (hV : V ≠ ⊤) :
    ∃ w : FinitePlace L, ∀ x : L, x ∈ V ↔ w x ≤ 1 := by
  have hint : ∀ a : 𝓞 L, algebraMap (𝓞 L) L a ∈ V := fun a ↦ by
    have h : IsIntegral V (algebraMap (𝓞 L) L a) :=
      isIntegral_of_comp (Int.castRingHom V) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]
    exact y.2
  let φ : 𝓞 L →+* V := (algebraMap (𝓞 L) L).codRestrict V hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal V).comap φ
  have hinv : ∀ s : 𝓞 L, s ∉ P → (algebraMap (𝓞 L) L s)⁻¹ ∈ V := fun s hs ↦ by
    have h1 : V.valuation (φ s : L) = 1 := by
      rcases V.valuation_lt_one_or_eq_one (φ s) with h | h
      · exact absurd ((V.valuation_lt_one_iff (φ s)).mpr h) hs
      · exact h
    rw [← V.valuation_le_one_iff, map_inv₀]
    change (V.valuation (φ s : L))⁻¹ ≤ 1
    rw [h1, inv_one]
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hV
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have hbP : b ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hint a) (hinv b hbP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hle : HeightOneSpectrum.valuationSubringAtPrime L v ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    exact mul_mem (hint a) (hinv s hs)
  refine ⟨FinitePlace.mk v, fun x ↦ ?_⟩
  rw [← mem_valuationSubring_iff_place,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) v,
    ValuationSubring.eq_of_le_of_ne_top _ hle hV]

theorem absCentredAt_of_le_one (O : Subalgebra ℤ L) [IsFractionRing O L] (m : Ideal O) [m.IsMaximal]
    (w : FinitePlace L)
    (hA : ∀ y ∈ Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors,
      w y ≤ 1)
    (x : L) (hx : 1 < w x) : AbsCentredAt O m fun t ↦ w t := by
  have hO : ∀ u : O, w u ≤ 1 := fun u ↦ hA _ (Subalgebra.algebraMap_mem _ u)
  let q : Ideal O :=
    { carrier := {u | w u < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        change w ((a : L) + b) < 1
        exact (FinitePlace.add_le w _ _).trans_lt (max_lt ha hb)
      smul_mem' := fun c a ha ↦ by
        change w ((c : L) * a) < 1
        rw [map_mul]
        exact (mul_le_of_le_one_left (apply_nonneg w _) (hO c)).trans_lt ha }
  have hmem : ∀ u : O, u ∈ q ↔ w u < 1 := fun _ ↦ Iff.rfl
  have hq_prime : q.IsPrime := by
    refine ⟨fun h ↦ ?_, fun {a b} hab ↦ ?_⟩
    · have h1 : (1 : O) ∈ q := h ▸ Submodule.mem_top
      rw [hmem] at h1
      simp at h1
    · by_contra hne
      rw [not_or, hmem, hmem, not_lt, not_lt] at hne
      rw [hmem] at hab
      change w ((a : L) * b) < 1 at hab
      rw [map_mul, le_antisymm (hO a) hne.1, le_antisymm (hO b) hne.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hq_ne : q ≠ ⊥ := by
    intro hq
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb1 : w (algebraMap O L b) = 1 := by
      refine le_antisymm (hO b) (not_lt.mp fun h ↦ nonZeroDivisors.ne_zero hb ?_)
      rw [← Ideal.mem_bot, ← hq]
      exact h
    rw [map_div₀, hb1, div_one] at hx
    exact absurd (hO a) (not_le.mpr hx)
  have hq_max : q.IsMaximal := SubringPrimeMaximal.proof L O q hq_prime hq_ne
  have hqm : q ≤ m := fun u hu ↦ by
    by_contra hum
    have hu0 : (u : L) ≠ 0 := fun h ↦ hum (by rw [show u = 0 from Subtype.ext h]; exact m.zero_mem)
    have hinv : w (u : L)⁻¹ ≤ 1 := hA _ ⟨1, u, hum, by rw [map_one, one_mul]; rfl⟩
    have hprod : w (u : L) * w (u : L)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hu' : w u < 1 := hu
    nlinarith [apply_nonneg w (u : L), apply_nonneg w (u : L)⁻¹]
  have hqe : q = m := hq_max.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hqm
  refine ⟨hO, fun u ↦ ?_⟩
  rw [← hqe]
  exact (hmem u).symm

theorem proof : CentredRingNormal.Statement := by
  intro L _ _ O _ _ m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hcent : ∀ w : FinitePlace L, AbsCentredAt O m (fun t ↦ w t) → ∀ y ∈ A, w y ≤ 1 := by
    rintro w ⟨hO, hm⟩ y ⟨a, s, hs, rfl⟩
    have hs1 : w (algebraMap O L s) = 1 := le_antisymm (hO s) (not_lt.mp fun h ↦ hs ((hm s).mp h))
    rw [map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact hO a
  ext x
  rw [mem_placesRing, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · intro hx
    have hall : x ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.mpr fun ⟨V, hAV⟩ ↦ ?_
      by_cases hV : V = ⊤
      · have h : x ∈ V := hV ▸ ValuationSubring.mem_top x
        exact h
      obtain ⟨w, hw⟩ := exists_place_of_valuationSubring V hV
      by_contra hxV
      have hwx : 1 < w x := not_le.mp fun h ↦ hxV ((hw x).mpr h)
      have hc := absCentredAt_of_le_one O m w (fun y hy ↦ (hw y).mp (hAV hy)) x hwx
      exact hxV ((hw x).mpr (hx w hc))
    rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
    refine isIntegral_of_comp ((algebraMap (Subring.closure (A : Set L)) L).codRestrict A fun y ↦ ?_) (RingHom.ext fun _ ↦ rfl) hall
    exact (Subring.closure_le (t := A.toSubring)).mpr (fun z hz ↦ hz) y.2
  · intro hx w hw
    let v := FinitePlace.maximalIdeal w
    have hAV : ∀ y ∈ A, y ∈ (v.valuation L).valuationSubring := fun y hy ↦ by
      rw [mem_valuationSubring_iff_place, FinitePlace.mk_maximalIdeal]
      exact hcent w hw y hy
    have hxV : IsIntegral (v.valuation L).valuationSubring x :=
      isIntegral_of_comp ((algebraMap A L).codRestrict _ fun y ↦ hAV y y.2)
        (RingHom.ext fun _ ↦ rfl) hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxV
    have h := (mem_valuationSubring_iff_place v x).mp (hy ▸ y.2)
    rwa [FinitePlace.mk_maximalIdeal] at h

end CentredRingNormal

end GroundTheory.Heights₂.Heights
end
