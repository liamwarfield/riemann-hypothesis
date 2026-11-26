module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing

noncomputable section

namespace DimTwoSumReading

variable {A : Type*} [CommRing A]

theorem length_loc_eq_ordLoc (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by
  have h := length_localizedModule_quot_eq (T := Localization.AtPrime W) W.primeCompl ⊥ a
    (fun s hs => IsLocalization.map_units _ (⟨s, hs⟩ : W.primeCompl))
    (fun y => by
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj W.primeCompl y
      exact ⟨r, s, s.2, hy.symm⟩)
    (fun r hr => by
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W.primeCompl _ r).mp hr
      exact ⟨s, s.2, (Ideal.mem_bot).mpr hs⟩)
    (fun v hv => by rw [(Ideal.mem_bot).mp hv, map_zero])
  rw [bot_sup_eq] at h
  exact h

theorem length_max_eq_ordMod [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by
  have h := length_localizedModule_quot_eq (T := A ⧸ W) (maximalIdeal A).primeCompl W b
    (fun s hs => (notMem_maximalIdeal.mp hs).map _)
    (fun y => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, 1, (maximalIdeal A).primeCompl.one_mem, by simp⟩)
    (fun r hr => ⟨1, (maximalIdeal A).primeCompl.one_mem, by
      rw [one_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mp hr⟩)
    (fun v hv => Ideal.Quotient.eq_zero_iff_mem.mpr hv)
  rw [h, ordMod, Ring.ord, Ideal.Quotient.algebraMap_eq]

variable [IsDomain A] [IsNoetherianRing A]

theorem mem_minimalPrimes_iff {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  constructor
  · intro hW
    have haW : a ∈ W := hW.1.2 (Ideal.subset_span rfl)
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) W hW
    have h0 : W.height ≠ 0 := fun h => ha ((Ideal.mem_bot).mp (Ideal.height_eq_zero_iff_eq_bot.mp h ▸ haW))
    exact ⟨le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), haW⟩
  · rintro ⟨h1, haW⟩
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := W)
      ((Ideal.span_singleton_le_iff_mem W).mpr haW)
    rcases hQW.lt_or_eq with hlt | rfl
    · have := hQ.1.1
      have haQ : a ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
      have hbQ : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun h => ha ((Ideal.mem_bot).mp (h ▸ haQ))
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbQ
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at e1
      rw [h1] at e2
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add e1 le_rfl) e2
      exact absurd this (by decide)
    · exact hQ


omit [IsDomain A] [IsNoetherianRing A] in
theorem max_mem_minimalPrimes [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by
  have hle : W ⊔ Ideal.span {b} ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hW.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, hle⟩, fun Q hQ hQm => ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < maximalIdeal A := lt_of_le_of_ne hQm fun h => hne (h ▸ le_rfl)
  have hWQ : W < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
    hbW (h ▸ hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hWQ
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [h2, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hm
  rw [WithBot.coe_injective hm] at e2
  rw [h1] at e1
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := le_trans (add_le_add e1 le_rfl) e2
  exact absurd this (by decide)

end DimTwoSumReading


open DimTwoSumReading in
theorem DimTwoSumReading.proof : DimTwoSumReading.Statement := by
  intro A _ _ _ _ h2 a b ha hab
  classical
  have hT : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)).subset
      (fun p hp => (mem_minimalPrimes_iff ha p.asIdeal).mpr hp)
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal →
      (locCycle (Ideal.span {a}) p.asIdeal = ((ordLoc p a).toNat : ℤ) ∧ ordLoc p a ≠ ⊤) ∧
      (locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = ((ordMod p b).toNat : ℤ) ∧
        ordMod p b ≠ ⊤) := by
    intro p hp
    have hmin := (mem_minimalPrimes_iff ha p.asIdeal).mpr hp
    have hlA := length_loc_eq_ordLoc p.asIdeal a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold locCycle; rw [dite_eq_left hmin]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlA
    · rw [← hlA]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmin
    by_cases hbm : b ∈ maximalIdeal A
    · have hmm := max_mem_minimalPrimes h2 p.asIdeal hp.1 (hab _ p.isPrime hp.1 hp.2) hbm
      have hlB := length_max_eq_ordMod p.asIdeal b
      refine ⟨?_, ?_⟩
      · unfold locCycle; rw [dite_eq_left hmm]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlB
      · rw [← hlB]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmm
    · have h0 : ordMod p b = 0 := Ring.ord_of_isUnit ((notMem_maximalIdeal.mp hbm).map _)
      have hnm : maximalIdeal A ∉ (p.asIdeal ⊔ Ideal.span {b}).minimalPrimes := fun h =>
        hbm (h.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      rw [h0]
      refine ⟨?_, ENat.zero_ne_top⟩
      unfold locCycle; rw [dite_eq_right hnm]; rfl
  have hsupp : Function.support (fun W : Ideal A => locCycle (Ideal.span {a}) W *
      locCycle (W ⊔ Ideal.span {b}) (maximalIdeal A)) ⊆
      (hT.toFinset.map ⟨PrimeSpectrum.asIdeal, by intro p q h; exact PrimeSpectrum.ext h⟩ : Finset (Ideal A)) := by
    intro W hW
    have hne : locCycle (Ideal.span {a}) W ≠ 0 := left_ne_zero_of_mul hW
    have hmin : W ∈ (Ideal.span {a}).minimalPrimes := by
      by_contra h
      exact hne (by unfold locCycle; rw [dite_eq_right h])
    have := hmin.1.1
    rw [Finset.coe_map, Set.Finite.coe_toFinset]
    exact ⟨⟨W, hmin.1.1⟩, (mem_minimalPrimes_iff ha W).mp hmin, rfl⟩
  refine ⟨∑ p ∈ hT.toFinset, (ordLoc p a).toNat * (ordMod p b).toNat, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    show locCycle (Ideal.span {a}) p.asIdeal * locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = _
    rw [hk.1.1, hk.2.1]
  · refine (finsum_mem_eq_finite_toFinset_sum (fun p => ordLoc p a * ordMod p b) hT).trans ?_
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    rw [ENat.natCast_toNat hk.1.2, ENat.natCast_toNat hk.2.2]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalChartLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section ChartLength

theorem chartLength_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem chartLength_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  let _ := RingHomInvPair.of_ringEquiv τ
  let _ := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

theorem chartLength_quotient_self {A : Type*} [CommRing A] (I : Ideal A) :
    Module.length A (A ⧸ I) = Module.length (A ⧸ I) (A ⧸ I) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_aeval_chartSubst_eq_C_pow_mul (a : J → MRing ι R) (j₀ : J) (h : Polynomial (MRing ι R)) :
    ∃ (d : ℕ) (H : MRing (extIdx ι J) R),
      aeval (chartSubst a) H = Polynomial.C (a j₀ ^ d) * h := by
  refine ⟨h.natDegree, ∑ k ∈ Finset.range (h.natDegree + 1),
    liftForm (h.coeff k * a j₀ ^ (h.natDegree - k)) * newVar j₀ ^ k, ?_⟩
  have hs : Polynomial.C (a j₀ ^ h.natDegree) * h = ∑ k ∈ Finset.range (h.natDegree + 1),
      Polynomial.C (a j₀ ^ h.natDegree) * (Polynomial.C (h.coeff k) * Polynomial.X ^ k) := by
    rw [← Finset.mul_sum, ← h.as_sum_range_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ h.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : a j₀ ^ h.natDegree = a j₀ ^ (h.natDegree - k) * a j₀ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [map_mul, map_pow, aeval_chartSubst_liftForm, e]
  simp only [newVar, aeval_X, chartSubst, map_mul, map_pow]
  ring

end ChartLength

theorem BlowUpHorizontalChartLength.full : BlowUpHorizontalChartLength.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨-, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  set 𝔮 := W₀.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with h𝔮
  set Jx := (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) with hJx
  set I := blowUpOf P u ⊔ Ideal.span {liftForm x} with hI
  let φ : MRing (extIdx ι J) O →+* Polynomial (MRing ι O) := (aeval (R := O) (chartSubst a)).toRingHom
  have hφ : ∀ F, φ F = aeval (chartSubst a) F := fun _ => rfl
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hW𝔮 : W = 𝔮.comap φ := by
    refine le_antisymm ?_ ?_
    · refine hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩
        (fun G hG => ?_)
      · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
      · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
        exact Ideal.mem_map_of_mem _ hxW
      · exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
    · intro G hG
      exact mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hlfa : ∀ m : ℕ, liftForm (a j₀ ^ m) ∉ W := fun m h =>
    ha₀ (hW₀p.mem_of_pow_mem m (show a j₀ ^ m ∈ W₀ from h))
  have hCa : ∀ e : ℕ, Polynomial.C (a j₀ ^ e) ∉ 𝔮 := by
    intro e h
    have h1 := Ideal.mem_map_C_iff.mp h 0
    rw [Polynomial.coeff_C_zero] at h1
    exact ha₀ (hW₀p.mem_of_pow_mem _ h1)
  have hq : 𝔮.IsPrime := inferInstance

  have hlift : ∀ t, t ∉ 𝔮 → ∃ (e : ℕ) (T : MRing (extIdx ι J) O),
      φ T = Polynomial.C (a j₀ ^ e) * t ∧ T ∉ W := by
    intro t ht
    obtain ⟨e, T, hT⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ t
    refine ⟨e, T, hT, fun hTW => ?_⟩
    have h1 : φ T ∈ 𝔮 := by rw [hW𝔮] at hTW; exact hTW
    rw [hφ, hT] at h1
    exact (hq.mem_or_mem h1).elim (hCa e) ht

  have hIJ : I ≤ Jx.comap φ := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono le_sup_left (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, hφ, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  have memI : ∀ G, φ G ∈ Jx → ∃ m : ℕ, liftForm (a j₀ ^ m) * G ∈ I := by
    intro G hG
    rw [hJx, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at hG
    obtain ⟨y, hy, z, hz, hyz⟩ := hG
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    have h1 : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) ∈
        Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P := by
      have e : aeval (chartSubst a) (liftForm (a j₀ ^ d) * G - H * liftForm x) =
          Polynomial.C (a j₀ ^ d) * y := by
        rw [map_sub, map_mul, map_mul, aeval_chartSubst_liftForm, aeval_chartSubst_liftForm, hH, ← hφ G,
          ← hyz]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hy
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem (P := P) (u := u) j₀ hrelB h1
    have hPB : Ideal.map (liftForm (J := J) : MRing ι O →ₐ[O] MRing (extIdx ι J) O) P ≤ blowUpOf P u :=
      Ideal.map_le_iff_le_comap.mpr fun p hp => liftForm_mem_blowUpOf hp
    have hm' := sup_le le_rfl hPB hm
    refine ⟨m + d, ?_⟩
    have e : liftForm (a j₀ ^ (m + d)) * G =
        liftForm (a j₀ ^ m) * (liftForm (a j₀ ^ d) * G - H * liftForm x) +
          (liftForm (a j₀ ^ m) * H) * liftForm x := by
      rw [pow_add, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hm')
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

  let Φ := Localization.localRingHom W 𝔮 φ hW𝔮
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨h, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    obtain ⟨d, H, hH⟩ := exists_aeval_chartSubst_eq_C_pow_mul a j₀ h
    obtain ⟨e, T, hT, hTW⟩ := hlift t t.2
    have hs : T * liftForm (a j₀ ^ d) ∈ W.primeCompl := W.primeCompl.mul_mem hTW (hlfa d)
    refine ⟨IsLocalization.mk' _ (H * liftForm (a j₀ ^ e)) ⟨_, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    change (t : Polynomial (MRing ι O)) * φ (H * liftForm (a j₀ ^ e)) = φ (T * liftForm (a j₀ ^ d)) * h
    rw [map_mul, map_mul, hT]
    simp only [hφ, aeval_chartSubst_liftForm, hH]
    ring
  have hker : I.map (algebraMap _ (Localization.AtPrime W)) =
      (Jx.map (algebraMap _ (Localization.AtPrime 𝔮))).comap Φ := by
    ext z
    obtain ⟨⟨F, T⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [Ideal.mem_comap, Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨s, hs, hsF⟩
      refine ⟨φ s, fun h => hs (by rw [hW𝔮]; exact h), ?_⟩
      rw [← map_mul]
      exact hIJ hsF
    · rintro ⟨t, ht, htF⟩
      obtain ⟨e, T', hT', hT'W⟩ := hlift t ht
      obtain ⟨m, hm⟩ := memI (T' * F) (by
        rw [map_mul, hT', mul_assoc]
        exact Ideal.mul_mem_left _ _ htF)
      exact ⟨liftForm (a j₀ ^ m) * T', W.primeCompl.mul_mem (hlfa m) hT'W, by rw [mul_assoc]; exact hm⟩
  have hsurj' : Function.Surjective
      ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) :=
    Ideal.Quotient.mk_surjective.comp hsurj
  have hker' : I.map (algebraMap _ (Localization.AtPrime W)) =
      RingHom.ker ((Ideal.Quotient.mk (Jx.map (algebraMap _ (Localization.AtPrime 𝔮)))).comp Φ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hker
  let τ := (Ideal.quotEquivOfEq hker').trans (RingHom.quotientKerEquivOfSurjective hsurj')
  unfold multAt
  rw [chartLength_localizedModule_quotient, chartLength_localizedModule_quotient,
    chartLength_quotient_self, chartLength_quotient_self]
  exact chartLength_self_eq_of_ringEquiv τ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
