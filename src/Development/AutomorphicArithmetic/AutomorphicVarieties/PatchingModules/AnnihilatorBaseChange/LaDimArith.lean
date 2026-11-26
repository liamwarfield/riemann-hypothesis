module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaRegPrime
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfQuot
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem card_le_dim (R : Type) [CommRing R] [IsRegularLocalRing R] (r : ℕ) (x : Fin r → R)
    (hx : CotInd R x) : (r : WithBot ℕ∞) ≤ ringKrullDim R := by
  obtain ⟨s, y, -, -, hc⟩ := cotInd_extend R _ x hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc, Fintype.card_fin]
  exact_mod_cast Nat.le_add_right r s

private theorem exists_max (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) :
    ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ (∀ k, x k ∈ I) ∧
      I ≤ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 := by
  classical
  let P : ℕ → Prop := fun r => ∃ x : Fin r → R, CotInd R x ∧ ∀ k, x k ∈ I
  have h0 : P 0 := ⟨Fin.elim0, ⟨fun k => k.elim0, fun _ _ k => k.elim0⟩, fun k => k.elim0⟩
  have hb : ∀ r, P r → r ≤ (maximalIdeal R).spanFinrank := by
    rintro r ⟨x, hx, -⟩
    have := card_le_dim R r x hx
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at this
    exact_mod_cast this
  obtain ⟨x, hx, hxI⟩ : P (Nat.findGreatest P (maximalIdeal R).spanFinrank) :=
    Nat.findGreatest_spec (Nat.zero_le _) h0
  refine ⟨_, x, hx, hxI, fun t ht => ?_⟩
  by_contra hn
  have h1 : P (Nat.findGreatest P (maximalIdeal R).spanFinrank + 1) := by
    refine ⟨Fin.cons t x, ⟨?_, ?_⟩, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact hI ht
      · exact hx.mem j
    · intro a ha
      rw [Fin.sum_univ_succ] at ha
      simp only [Fin.cons_zero, Fin.cons_succ] at ha
      have ha0 : a 0 ∈ maximalIdeal R := by
        by_contra hu
        have hu' : IsUnit (a 0) := by simpa using hu
        apply hn
        rw [← Ideal.unit_mul_mem_iff_mem _ hu']
        have h2 : ∑ i, a i.succ * x i ∈ Ideal.span (Set.range x) :=
          Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
        have h3 := sub_mem (Ideal.mem_sup_right (S := Ideal.span (Set.range x)) ha)
          (Ideal.mem_sup_left h2)
        simpa using h3
      have h4 : a 0 * t ∈ maximalIdeal R ^ 2 := by
        rw [sq]
        exact Ideal.mul_mem_mul ha0 (hI ht)
      have h5 : ∑ i, a i.succ * x i ∈ maximalIdeal R ^ 2 := by
        simpa using sub_mem ha h4
      intro k
      exact Fin.cases ha0 (fun j => hx.indep (fun i => a i.succ) h5 j) k
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ht
      · exact hxI j
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hb _ h1) h1

theorem UpperTheory.V.AlgebraTools.exists_cotInd_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ Ideal.span (Set.range x) = I := by
  intro R _ _ I _
  have hne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hI : I ≤ maximalIdeal R := le_maximalIdeal hne
  obtain ⟨r, x, hx, hxI, hle⟩ := exists_max R I hI
  refine ⟨r, x, hx, ?_⟩
  have hJ : Ideal.span (Set.range x) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hxI k
  obtain ⟨s, y, hxy, -, hc⟩ := cotInd_extend R _ x hx
  obtain ⟨-, hd, hp⟩ := regular_quotient_cotInd R _ x hx
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : CotInd (R ⧸ I) (fun j => Ideal.Quotient.mk I (y j)) := by
    refine ⟨fun j => hmax ▸ Ideal.mem_map_of_mem _ (hxy.mem (Sum.inr j)), fun a ha => ?_⟩
    choose b hb using fun j => Ideal.Quotient.mk_surjective (a j)
    have h1 : Ideal.Quotient.mk I (∑ j, b j * y j) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R ^ 2) := by
      rw [Ideal.map_pow, hmax]
      simpa [hb] using ha
    rw [Ideal.mem_quotient_iff_mem_sup] at h1
    have h2 : ∑ j, b j * y j ∈ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 :=
      sup_le le_sup_right hle h1
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
    have h3 : ∑ k, Sum.elim (fun i => - c i) b k * Sum.elim x y k ∈ maximalIdeal R ^ 2 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, ← huv, neg_mul, Finset.sum_neg_distrib]
      simpa using hv
    intro j
    rw [← hb j, ← hmax]
    exact Ideal.mem_map_of_mem _ (hxy.indep _ h3 (Sum.inr j))
  have hs := card_le_dim _ s _ hy
  refine le_antisymm hJ fun t ht => ?_
  by_contra hn
  have : IsDomain (R ⧸ Ideal.span (Set.range x)) := (Ideal.Quotient.isDomain_iff_prime _).2 hp
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range x)) t ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h4 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hJ)
    (Ideal.Quotient.factor_surjective hJ) (mem_nonZeroDivisors_of_ne_zero h0)
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ht)
  have h5 : ((s : WithBot ℕ∞) + 1) + (Fintype.card (Fin r) : ℕ) ≤ ringKrullDim R := by
    rw [← hd]
    gcongr
    exact le_trans (by gcongr) h4
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc] at h5
  have h6 : s + 1 + Fintype.card (Fin r) ≤ Fintype.card (Fin r) + s := by exact_mod_cast h5
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotLoc
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prime_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) : (Ideal.span (x '' (s : Set κ))).IsPrime := by
  have h := (regular_quotient_cotInd R s (x ∘ ((↑) : s → κ)) (hx.comp _ Subtype.val_injective)).2.2
  have e : Set.range (x ∘ ((↑) : s → κ)) = x '' (s : Set κ) := by
    rw [Set.range_comp]
    congr 1
    ext a
    simp
  rwa [e] at h

private theorem not_mem_sub (R : Type) [CommRing R] [IsLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) (a : κ) (ha : a ∉ s) :
    x a ∉ Ideal.span (x '' (s : Set κ)) := by
  classical
  intro hmem
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp hmem
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul R (x i))] at hlx
  simp only [smul_eq_mul] at hlx
  let b : κ → R := Pi.single a 1
  have h0 : ∑ k, (b k - l k) * x k ∈ maximalIdeal R ^ 2 := by
    have hz : ∑ k, (b k - l k) * x k = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, hlx]
      simp [b, Pi.single_apply]
    rw [hz]
    exact zero_mem _
  have h1 := hx.indep _ h0 a
  rw [(Finsupp.mem_supported' R l).mp hl a ha, sub_zero] at h1
  simp only [b, Pi.single_eq_same] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem height_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) :
    (s.card : ℕ∞) ≤ (Ideal.span (x '' (s : Set κ))).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    haveI := prime_sub R κ x hx s
    haveI := prime_sub R κ x hx (insert a s)
    have hlt : Ideal.span (x '' (s : Set κ)) < Ideal.span (x '' ((insert a s : Finset κ) : Set κ)) := by
      refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) fun e => ?_
      apply not_mem_sub R κ x hx s a ha
      rw [e]
      exact Ideal.subset_span ⟨a, by simp, rfl⟩
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    exact Order.add_one_le_of_lt (ih.trans_lt h1)

theorem UpperTheory.V.AlgebraTools.regular_localization_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∀ (p : Ideal R) [p.IsPrime], p = Ideal.span (Set.range x) →
      p.height = (Fintype.card κ : ℕ) ∧ IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  intro R _ _ κ _ x hx p _ hp
  have hge : ((Fintype.card κ : ℕ) : ℕ∞) ≤ p.height := by
    have h1 := height_sub R κ x hx Finset.univ
    rwa [Finset.card_univ, Finset.coe_univ, Set.image_univ, ← hp] at h1
  have hle : p.height ≤ ((Fintype.card κ : ℕ) : ℕ∞) := by
    have e : Ideal.span ((Finset.univ.image x : Finset R) : Set R) = p := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hp]
    have hmin : p ∈ (Ideal.span ((Finset.univ.image x : Finset R) : Set R)).minimalPrimes := by
      rw [e, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton p
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_image_le
  have heq : p.height = ((Fintype.card κ : ℕ) : ℕ∞) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
    IsLocalization.AtPrime.under_maximalIdeal _ p, heq, ← Localization.AtPrime.map_eq_maximalIdeal]
  have hmap : Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span (Set.range x)) := congrArg _ hp
  rw [hmap, Ideal.map_span, ← Set.range_comp]
  have h3 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime p)
    (Set.finite_range (algebraMap R (Localization.AtPrime p) ∘ x))
  have h4 : (Set.range (algebraMap R (Localization.AtPrime p) ∘ x)).ncard ≤ Fintype.card κ := by
    rw [← Set.image_univ, ← Finset.coe_univ]
    exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
  exact_mod_cast h3.trans h4
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_localization_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (R ⧸ p)],
      IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro R _ _ p _ _
  obtain ⟨r, x, hx, hsp⟩ := exists_cotInd_of_regular_quotient R p
  obtain ⟨-, hdim, -⟩ := regular_quotient_cotInd R _ x hx
  obtain ⟨hh, hreg⟩ := regular_localization_cotInd R _ x hx p hsp.symm
  refine ⟨hreg, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hh, add_comm]
  rw [hsp] at hdim
  rw [← hdim]
  rfl
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem laDim_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := IsLocalHom.of_surjective _ h, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem laDim_surj (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Algebra O K] (σ : Type) [Finite σ] (s : σ)
    (g : MvPowerSeries σ O →ₐ[O] PowerSeries K) (h : Function.Surjective (algebraMap O K))
    (hg : g (MvPowerSeries.X s) = PowerSeries.X) : Function.Surjective g := by
  haveI : IsCO O K := laDim_co O K h
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : IsCO O (PowerSeries K) := co_mvps O K Unit
  refine co_surj O _ _ g (le_trans ?_ le_sup_left)
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le, Set.singleton_subset_iff, ← hg]
  refine Ideal.mem_map_of_mem _ fun hu => ?_
  have := MvPowerSeries.isUnit_constantCoeff _ hu
  simp at this

private theorem laDim_arith (x : WithBot ℕ∞) (n : ℕ) (h : x + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    x = (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    have h' : y + 1 = ((n : ℕ∞) + 1) := by exact_mod_cast h
    have : y = (n : ℕ∞) := WithTop.add_right_cancel ENat.one_ne_top h'
    rw [this]; rfl

private theorem laDim_gen (R : Type) [CommRing R] [IsRegularLocalRing R] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (p : Ideal R) (e : (R ⧸ p) ≃+* S) (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra R La),
      IsCplAt R p La ∧ IsRegularLocalRing La ∧ ringKrullDim La = (n : WithBot ℕ∞) := by
  haveI : IsDomain (R ⧸ p) := e.toMulEquiv.isDomain _
  haveI hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 inferInstance
  haveI : IsRegularLocalRing (R ⧸ p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hq : ringKrullDim (R ⧸ p) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsDiscreteValuationRing.ringKrullDim_eq_one]
  obtain ⟨h1, h2⟩ := regular_localization_of_regular_quotient R p
  have hc := isCplAt_cplAt R p
  obtain ⟨h3, h4⟩ := IsCplAt.regular _ _ _ hc h1
  refine ⟨CplAt R p, inferInstance, inferInstance, inferInstance, hc, h3, ?_⟩
  rw [h4]
  apply laDim_arith
  rw [hq] at h2
  rw [h2, hdim]

theorem UpperTheory.V.Pa.Core.laDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Finite K] [Algebra O K] (D : ℕ) (g : abelian₂ O Unit D →ₐ[O] PowerSeries K), Function.Surjective (algebraMap O K) → g (MvPowerSeries.X (.inl ())) = PowerSeries.X → ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra (abelian₂ O Unit D) La), IsCplAt (abelian₂ O Unit D) (RingHom.ker g) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ((1 + D : ℕ) : WithBot ℕ∞) := by
  intro O _ _ _ _ K _ _ _ D g h hg
  have hs : Function.Surjective g := laDim_surj O K _ _ g h hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hreg, hdim, -⟩ := mvPowerSeries_cotInd O ϖ hϖ (Unit ⊕ Fin D)
  haveI : IsRegularLocalRing (abelian₂ O Unit D) := hreg
  refine laDim_gen (abelian₂ O Unit D) (PowerSeries K) (RingHom.ker g)
    (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv (1 + D) ?_
  rw [hdim, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
