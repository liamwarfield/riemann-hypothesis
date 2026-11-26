module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

@[expose] public section

section -- merged from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.IsCMOfIsRegularLocalRing
section -- merged from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RegGens
section -- merged from ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RegGensA
namespace ReciprocityTheory.CA.RegA

namespace IsRegularLocalRing

open IsLocalRing

universe u

theorem spanFinrank_span_finset_le {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h2 : (Ideal.span (s : Set R)).FG := Submodule.fg_span s.finite_toSet
  have h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R)) :=
    Submodule.spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank h2] at h1
  have h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1

theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  have h1 := congrArg (b.repr.symm) h0
  simpa using h1

theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  by_cases hij : i = j
  · rw [hij]
    have hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)
    have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]
      abel
    have hkey : b.repr v j • b j ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      rw [← hsub]
      exact Submodule.sub_mem _ hmem1 hmem2
    have h2 := Submodule.smul_mem _ (b.repr v j)⁻¹ hkey
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)

theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem spanFinrank_maximalIdeal_quotient_succ_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (Module.finBasis (ResidueField R) (CotangentSpace R)) hv0
  obtain ⟨z, hz⟩ : ∃ z : Fin (Module.finrank (ResidueField R) (CotangentSpace R)) →
      (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) =
        Module.finBasis (ResidueField R) (CotangentSpace R) i := by
    have hsurj : Function.Surjective (maximalIdeal R).toCotangent :=
      Ideal.toCotangent_surjective _
    choose z hz using fun i => hsurj (Module.finBasis (ResidueField R) (CotangentSpace R) i)
    exact ⟨z, hz⟩
  set s : Set (maximalIdeal R) :=
    insert (⟨x, hx⟩ : maximalIdeal R) (z '' ↑(Finset.univ.erase j)) with hsdef
  have htop : Submodule.span R s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff]
    have himg : (maximalIdeal R).toCotangent '' s =
        insert ((maximalIdeal R).toCotangent ⟨x, hx⟩)
          (⇑(Module.finBasis (ResidueField R) (CotangentSpace R)) ''
            ↑(Finset.univ.erase j)) := by
      rw [hsdef, Set.image_insert_eq, Set.image_image]
      simp [hz]
    rw [himg]
    exact span_insert_image_erase_eq_top _ _ hj
  have hmspan : Ideal.span ((Subtype.val : maximalIdeal R → R) '' s) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, Submodule.map_subtype_top] at h
    simpa using h
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) (maximalIdeal R) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine Ideal.mem_map_of_mem _ ?_
      by_contra hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
      exact hy (hr.map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))))
    · refine IsLocalRing.le_maximalIdeal ?_
      intro h
      rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
      obtain ⟨r, hrm, hr1⟩ := h
      have h2 : r - 1 ∈ Ideal.span ({x} : Set R) := by
        rw [← Ideal.Quotient.eq]
        simpa using hr1
      have h3 : (1 : R) ∈ maximalIdeal R := by
        have h4 := sub_mem hrm (hIle h2)
        simp at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hx0 : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have himg : (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) ''
      ((Subtype.val : maximalIdeal R → R) '' s) =
      insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hsdef, Set.image_image, Set.image_insert_eq, Set.image_image]
    simp [hx0]
  have hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) ((z i : R))) ''
        ↑(Finset.univ.erase j)) := by
    rw [hmapS]
    conv_lhs => rw [← hmspan]
    rw [Ideal.map_span, himg]
    exact Submodule.span_insert_zero
  have hcard : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) ≤
      (Finset.univ.erase j).card := by
    rw [hquot, ← Finset.coe_image]
    exact le_trans (spanFinrank_span_finset_le _) Finset.card_image_le
  have hjpos : 0 < Module.finrank (ResidueField R) (CotangentSpace R) := Fin.pos j
  have hcard2 : (Finset.univ.erase j).card =
      Module.finrank (ResidueField R) (CotangentSpace R) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  omega

theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [hm]
  · rw [hn]
    norm_cast

theorem spanFinrank_quotient_eq_and_ringKrullDim_add_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hdn := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞)
      = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hP2 : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) :
        WithBot ℕ∞) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  have hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R := by
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hP3 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (Ideal.span ({x} : Set R)) hIj
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have h := spanFinrank_span_finset_le ({x} : Finset R)
    simpa using h
  have hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h1
  have hP3' : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 :=
    hP3.trans (add_le_add le_rfl hcast)
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Module.finrank (ResidueField R) (CotangentSpace R))
    (by rw [hRdim]; exact hP3') hP2 hdn
  refine ⟨hA.symm, ?_⟩
  rw [hB, hRdim]

theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1

theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle

theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R

theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h

theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh

theorem quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2

theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hple⟩ := hmin
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpm : p = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple
    have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
      intro q hq
      refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
      rw [← hpm]
      exact le_of_le_of_mem_minimalPrimes hp hq
        (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)
    have h2 : ringKrullDim R ≤ 0 := by
      have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
        intro P Q
        apply PrimeSpectrum.ext
        rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
      have : Subsingleton (PrimeSpectrum R) := ⟨hPQ⟩
      exact Order.krullDim_nonpos_of_subsingleton
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have := isLocalRing_quotient_span_singleton hx
    have hpos := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
    have hdim : ringKrullDim R =
        (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
      ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
    rw [hdim] at h2
    have hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
    omega
  · obtain ⟨x, hx, hx2, hxp⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
    have := isLocalRing_quotient_span_singleton hx
    have hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
      quotient_span_singleton hx hx2
    have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
        Submodule.spanFinrank (maximalIdeal R) := by
      have h1 := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
      have h2 : Submodule.spanFinrank (maximalIdeal R)
          = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      omega
    have hdom := IH (R ⧸ Ideal.span ({x} : Set R)) hlt
    have hprime : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpbot : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp (hple hy)
      have ha : a ∈ p := by
        rcases hpp.mem_or_mem hy with hh | hh
        · exact absurd hh (hxp p hp)
        · exact hh
      exact Ideal.mul_mem_mul hx ha
    rw [hpbot] at hpp
    have := hpp
    exact IsDomain.of_bot_isPrime R

theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S (by omega)

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

end IsRegularLocalRing

end ReciprocityTheory.CA.RegA
end

open CategoryTheory CategoryTheory.Abelian IsLocalRing RingTheory.Sequence

universe u v

namespace ReciprocityTheory.CA.RegGens

open Pointwise in
theorem exists_regular_generators_maxIdeal : ∀ (d : ℕ) (P : Type u) [CommRing P] [IsRegularLocalRing P],
    ringKrullDim P = d →
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P := by
  intro d
  induction d with
  | zero =>
    intro P _ _ hd
    have hsf : (maximalIdeal P).spanFinrank = 0 := by
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd] at h
      exact_mod_cast h
    have hbot : maximalIdeal P = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hsf
    exact ⟨[], rfl, IsRegular.nil P P, by rw [Ideal.ofList_nil, hbot]⟩
  | succ d IH =>
    intro P _ _ hd
    have hsq : ¬ maximalIdeal P ≤ maximalIdeal P ^ 2 := by
      intro hle
      have hbot := RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq P hle
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd, hbot, Submodule.spanFinrank_bot] at h
      have : (0 : ℕ) = d + 1 := by exact_mod_cast h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal P ∧ x ∉ maximalIdeal P ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    set I : Ideal P := Ideal.span ({x} : Set P) with hI
    have hreg : IsRegularLocalRing (P ⧸ I) :=
      RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
    have hdim : ringKrullDim (P ⧸ I) = d := by
      have h1 := RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hx hx2
      have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P ⧸ I)
      rw [← h2] at h1 ⊢
      rw [hd] at h1
      have h3 : (maximalIdeal (P ⧸ I)).spanFinrank + 1 = d + 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : (maximalIdeal (P ⧸ I)).spanFinrank = d)
    obtain ⟨rs', hlen, hrs', hgen⟩ := IH (P ⧸ I) hdim
    let lift : P ⧸ I → P := fun y => Quotient.out y
    have hlift : ∀ y, Ideal.Quotient.mk I (lift y) = y := fun y => Ideal.Quotient.mk_out y
    have hmap : (rs'.map lift).map (Ideal.Quotient.mk I) = rs' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id rs']
      exact List.map_congr_left fun y _ => hlift y
    refine ⟨x :: rs'.map lift, by simp [hlen], ?_, ?_⟩
    · rw [isRegular_cons_iff', hmap]
      refine ⟨?_, ?_⟩
      · have hx0 : x ≠ 0 := by
          rintro rfl
          exact hx2 (zero_mem _)
        exact (IsRegular.of_ne_zero hx0).left
      · have hsm : (x • ⊤ : Submodule P P) = I := by
          rw [hI, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
        let e : QuotSMulTop x P ≃ₗ[P] P ⧸ I := Submodule.quotEquivOfEq _ _ hsm
        refine (e.toAddEquiv.isRegular_congr (as := rs') (bs := rs') ?_).mpr hrs'
        refine List.forall₂_same.mpr fun r _ y => ?_
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rfl
    · rw [Ideal.ofList_cons]
      have h1 : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I)
          (Ideal.ofList (rs'.map lift))) = Ideal.ofList (rs'.map lift) ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
      rw [Ideal.map_ofList, hmap, hgen] at h1
      have h2 : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I)) = maximalIdeal P := by
        have : (Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I))).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        exact IsLocalRing.eq_maximalIdeal this
      rw [← h2, h1, sup_comm]

theorem exists_regular_gens (P : Type u) [CommRing P] [IsRegularLocalRing P] (d : ℕ)
    (hd : ringKrullDim P = d) :
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P :=
  exists_regular_generators_maxIdeal d P hd

end ReciprocityTheory.CA.RegGens
end

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by
  have hd : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨inferInstance, (maximalIdeal R).spanFinrank, hd, ?_⟩
  obtain ⟨rs, hlen, reg, hm⟩ := ReciprocityTheory.CA.RegGens.exists_regular_gens R _ hd
  refine ⟨rs, hlen, fun r hr => ?_, reg⟩
  rw [← hm]
  exact Ideal.subset_span hr

end ReciprocityTheory.CA
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF

theorem height_eq_of_isMaximal_of_field {k B : Type*} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨s, hs⟩ := exists_height_of_isMaximal_of_field k B
  rw [hs M hM, hs N hN]

theorem height_eq_of_isMaximal_of_intCast_eq_zero {B : Type*} [CommRing B] [IsDomain B]
    [Algebra.FiniteType ℤ B] (n : ℤ) (hn0 : n ≠ 0) (hnB : (n : B) = 0)
    (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) : M.height = N.height := by
  obtain ⟨p, hpC⟩ := CharP.exists B
  have hdvd : (p : ℤ) ∣ n := by
    first
      | exact (CharP.intCast_eq_zero_iff B p n).mp hnB
      | exact (CharP.int_cast_eq_zero_iff B p n).mp hnB
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hdvd
    exact hn0 hdvd
  have hp : p.Prime := (CharP.char_is_prime_or_zero B p).resolve_right hp0
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) B := ZMod.algebra B p
  haveI : Algebra.FiniteType (ZMod p) B := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) B
  exact height_eq_of_isMaximal_of_field (k := ZMod p) M N hM hN

theorem height_eq_ringKrullDim_of_forall {B : Type*} [CommRing B]
    (hB : ∀ M N : Ideal B, M.IsMaximal → N.IsMaximal → M.height = N.height)
    (M : Ideal B) (hM : M.IsMaximal) : (M.height : WithBot ℕ∞) = ringKrullDim B := by
  haveI := hM.isPrime
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun p => ?_
    obtain ⟨N, hN, hpN⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    haveI := hN.isPrime
    have h1 : Order.height p ≤ Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) :=
      Order.height_mono (show p ≤ ⟨N, hN.isPrime⟩ from hpN)
    have h2 : N.height = Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) :=
      PrimeSpectrum.height_eq_orderHeight (⟨N, hN.isPrime⟩ : PrimeSpectrum B)
    rw [hB M N hM hN, h2]
    exact_mod_cast h1

theorem finiteRingKrullDim_mvPolynomialInt_quot {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] : FiniteRingKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℤ ⧸ P)
    rw [hb] at h0
    exact absurd h0 (by simp)
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_quotient_le P)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  change ((1 : ℕ∞) : WithBot ℕ∞) + (ENat.card σ : WithBot ℕ∞) ≠ ⊤
  rw [← WithBot.coe_add]
  exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.add_lt_top.2 ⟨by simp, ENat.card_lt_top_of_finite⟩))

theorem finiteRingKrullDim_quot {B : Type*} [CommRing B] [FiniteRingKrullDim B] (q : Ideal B)
    [q.IsPrime] : FiniteRingKrullDim (B ⧸ q) := by
  have hle : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_quotient_le q
  have htop : ringKrullDim B ≠ ⊤ := (finiteRingKrullDim_iff_ne_bot_and_top.mp inferInstance).2
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  have hne : ringKrullDim (B ⧸ q) ≠ ⊥ :=
    (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial).ne'
  exact ⟨hne, ne_top_of_le_ne_top htop hle⟩

private theorem ideal_height_eq_order_height_primeSpectrum {R : Type*} [CommRing R] (N : Ideal R) [hN : N.IsPrime] :
    N.height = Order.height (⟨N, hN⟩ : PrimeSpectrum R) := by
  exact PrimeSpectrum.height_eq_orderHeight (⟨N, hN⟩ : PrimeSpectrum R)

theorem height_int_of_isMaximal (M : Ideal ℤ) (hM : M.IsMaximal) : M.height = 1 := by
  haveI := hM.isPrime
  rw [ideal_height_eq_order_height_primeSpectrum M]
  have hMbot : M ≠ ⊥ := by
    intro h
    subst h
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hM)
  have hmin : ∀ z : PrimeSpectrum ℤ, z < ⟨M, hM.isPrime⟩ → IsMin z := by
    intro z hz
    have hz' : z.asIdeal < M := hz
    have hz0 : z.asIdeal = ⊥ := by
      by_contra hne
      have hmax : z.asIdeal.IsMaximal := by
        first
          | exact z.isPrime.isMaximal hne
          | exact Ring.DimensionLEOne.maximalOfPrime hne z.isPrime
          | exact Ideal.IsPrime.to_maximal_ideal z.isPrime hne
      exact (ne_of_lt hz') (hmax.eq_of_le hM.ne_top (le_of_lt hz'))
    intro w _
    show z.asIdeal ≤ w.asIdeal
    rw [hz0]
    exact bot_le
  have hx : ¬ IsMin (⟨M, hM.isPrime⟩ : PrimeSpectrum ℤ) := by
    intro h
    have hlt : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ) < ⟨M, hM.isPrime⟩ :=
      show (⊥ : Ideal ℤ) < M from bot_lt_iff_ne_bot.mpr hMbot
    exact lt_irrefl _ (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
  apply le_antisymm
  · first
      | (rw [Order.height_eq_iSup_lt_height]
         refine iSup₂_le fun z hz => ?_
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         simp)
      | (show Order.height _ ≤ ((1 : ℕ) : ℕ∞)
         rw [Order.height_le_coe_iff]
         intro z hz
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         exact zero_lt_one)
  · first
      | exact Order.one_le_height_iff.mpr hx
      | exact ENat.one_le_iff_ne_zero.mpr (fun h0 => hx (Order.height_eq_zero.mp h0))

theorem height_mvPolynomial_int_fin_of_isMaximal :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) ℤ)), M.IsMaximal → M.height = n + 1
  | 0, M, hM => by
    let e := MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_int_of_isMaximal _ hM']
    simp
  | n + 1, M, hM => by
    have := int_isJacobsonRing
    let e := (MvPolynomial.finSuccEquiv ℤ n).toRingEquiv
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_polynomial_of_isMaximal
      (height_mvPolynomial_int_fin_of_isMaximal n) _ hM']
    push_cast
    ring

private theorem order_height_comap_ringEquiv_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : PrimeSpectrum A) :
    Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x) = Order.height x := by
  have sm1 : StrictMono (PrimeSpectrum.comap (e.symm : B →+* A)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.symm.surjective (congrArg PrimeSpectrum.asIdeal h)
  have sm2 : StrictMono (PrimeSpectrum.comap (e : A →+* B)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.surjective (congrArg PrimeSpectrum.asIdeal h)
  have hcomp : PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x) = x := by
    apply PrimeSpectrum.ext
    ext a
    simp
  apply le_antisymm
  · calc Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x)
        ≤ Order.height (PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x)) :=
          Order.height_le_height_apply_of_strictMono _ sm2 _
      _ = Order.height x := by rw [hcomp]
  · exact Order.height_le_height_apply_of_strictMono _ sm1 x

theorem height_eq_of_isMaximal_mvPolynomial_int {σ : Type*} [Finite σ]
    (M N : Ideal (MvPolynomial σ ℤ)) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  let e : MvPolynomial σ ℤ ≃+* MvPolynomial (Fin n) ℤ := (MvPolynomial.renameEquiv ℤ eσ).toRingEquiv
  have key : ∀ I : Ideal (MvPolynomial σ ℤ), I.IsMaximal → I.height = n + 1 := by
    intro I hI
    haveI := hI
    haveI := hI.isPrime
    have hJ : (Ideal.comap (e.symm : MvPolynomial (Fin n) ℤ →+* MvPolynomial σ ℤ) I).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    haveI := hJ.isPrime
    have h1 := height_mvPolynomial_int_fin_of_isMaximal n _ hJ
    rw [ideal_height_eq_order_height_primeSpectrum] at h1 ⊢
    rw [← h1]
    exact (order_height_comap_ringEquiv_symm e _).symm
  rw [key M hM, key N hN]

theorem height_eq_height_add_of_isRegularRing {R : Type*} [CommRing R] [IsRegularRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hA : ReciprocityTheory.CA.IsCM (Localization.AtPrime q) :=
    ReciprocityTheory.CA.isCM_of_isRegularLocalRing _
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  have : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p inferInstance hdisj
  have e := hA.height_add_ringKrullDim_quotient (p.map (algebraMap R (Localization.AtPrime q)))
  rw [IsLocalization.height_map_of_disjoint q.primeCompl p hdisj,
    ReciprocityTheory.CA.ringKrullDim_localization_quotient_eq_height p q hpq,
    IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at e
  exact_mod_cast e.symm

theorem le_add_one_of_add_eq (a b D : WithBot ℕ∞) (x c : ℕ∞) (hx : x ≠ ⊤) (hc : c ≤ 1)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hD : D ≠ ⊤) (h1 : a + x = D) (h2 : b + ((x + c : ℕ∞) : WithBot ℕ∞) = D) :
    a ≤ b + 1 := by
  lift a to ℕ∞ using ha
  lift b to ℕ∞ using hb
  subst h1
  have h2' : b + (x + c) = a + x := by exact_mod_cast h2
  have hD' : a + x ≠ ⊤ := by
    intro h; apply hD; rw [← WithBot.coe_add, h] <;> rfl
  have ha' : a ≠ ⊤ := fun h => hD' (by rw [h, top_add])
  have hb' : b ≠ ⊤ := fun h => hD' (by rw [← h2', h, top_add])
  have hc' : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc
  lift a to ℕ using ha'
  lift b to ℕ using hb'
  lift x to ℕ using hx
  lift c to ℕ using hc'
  have hc2 : c ≤ 1 := by exact_mod_cast hc
  have h3 : b + (x + c) = a + x := by exact_mod_cast h2'
  have h4 : a ≤ b + 1 := by omega
  exact_mod_cast h4

theorem specialFibre_dim_ge {σ : Type*} [Finite σ] (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap MvPolynomial.C = ⊥) (ℓ : ℤ) (hℓ : Prime ℓ)
    (q : Ideal (MvPolynomial σ ℤ ⧸ P))
    (hq : q ∈ (Ideal.span {((ℓ : ℤ) : MvPolynomial σ ℤ ⧸ P)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ ringKrullDim ((MvPolynomial σ ℤ ⧸ P) ⧸ q) + 1 := by
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨Q, hQdef⟩ : ∃ Q : Ideal (MvPolynomial σ ℤ), Q = q.comap (Ideal.Quotient.mk P) := ⟨_, rfl⟩
  have hQp : Q.IsPrime := hQdef ▸ Ideal.comap_isPrime _ _
  have hPQ : P ≤ Q := fun x hx => by
    rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact q.zero_mem
  have hQq : Q.map (Ideal.Quotient.mk P) = q := by
    rw [hQdef]; exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q

  have : (Ideal.span {((ℓ : ℤ) : MvPolynomial σ ℤ ⧸ P)}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hq1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq

  have hcat := height_eq_height_add_of_isRegularRing P Q hPQ
  rw [hQq] at hcat

  have := int_isJacobsonRing
  have hfin : FiniteRingKrullDim (MvPolynomial σ ℤ) := by
    have h0 := finiteRingKrullDim_mvPolynomialInt_quot (⊥ : Ideal (MvPolynomial σ ℤ))
    rw [finiteRingKrullDim_iff_ne_bot_and_top] at h0 ⊢
    rwa [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial σ ℤ))] at h0
  have hdP := dim_quot_add_height height_eq_of_isMaximal_mvPolynomial_int P
  have hdQ := dim_quot_add_height height_eq_of_isMaximal_mvPolynomial_int Q
  rw [hcat] at hdQ
  have hAq : ringKrullDim ((MvPolynomial σ ℤ ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P)) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
  rw [hQq] at hAq
  rw [hAq]
  exact le_add_one_of_add_eq _ _ _ _ _ Ideal.height_ne_top_of_isPrime hq1
    (ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial)
    (ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial) ringKrullDim_ne_top hdP hdQ

theorem height_eq_of_isMaximal_int_charZero {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : P.comap MvPolynomial.C = ⊥)
    (M : Ideal (MvPolynomial σ ℤ ⧸ P)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  set A := MvPolynomial σ ℤ ⧸ P
  have := finiteRingKrullDim_mvPolynomialInt_quot P
  have hAft : Algebra.FiniteType ℤ A := (inferInstance : Algebra.FiniteType ℤ (MvPolynomial σ ℤ)).of_surjective
    (Ideal.Quotient.mkₐ ℤ P) (Ideal.Quotient.mkₐ_surjective ℤ P)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top) ?_

  have hcast : ∀ n : ℤ, ((n : ℤ) : A) = Ideal.Quotient.mk P (MvPolynomial.C n) := fun n => by
    rw [← map_intCast (Ideal.Quotient.mk P), ← map_intCast (MvPolynomial.C : ℤ →+* _), Int.cast_id]
  set Mz := M.comap (Int.castRingHom A)
  have hMz : Mz ≠ ⊥ := by
    intro h0
    have hb : M.comap ((Ideal.Quotient.mk P).comp MvPolynomial.C) = ⊥ := by
      rw [← h0]
      congr 1
    obtain ⟨q', hq', hlt⟩ := exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective M hM.isPrime hb
    exact hlt.ne (hM.eq_of_le hq'.ne_top hlt.le)
  obtain ⟨ℓ, hℓMz, hℓ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.comap_isPrime _ _) hMz
  have hℓM : ((ℓ : ℤ) : A) ∈ M := hℓMz
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {((ℓ : ℤ) : A)}) (J := M)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hℓM))
  have hqp : q.IsPrime := hq.1.1
  have hℓq : ((ℓ : ℤ) : A) ∈ q := hq.1.2 (Ideal.subset_span rfl)
  have hℓ0 : ((ℓ : ℤ) : A) ≠ 0 := by
    intro h
    rw [hcast, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP, Ideal.mem_bot] at h
    exact hℓ.ne_zero h
  have hq0 : q ≠ ⊥ := fun h => hℓ0 (by rw [h, Ideal.mem_bot] at hℓq; exact hℓq)
  have hqh : 1 ≤ q.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]; exact hq0
  have := finiteRingKrullDim_quot q
  have : @Algebra.FiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
    convert hAft.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)
    exact Subsingleton.elim _ _
  have hEq : ∀ M N : Ideal (A ⧸ q), M.IsMaximal → N.IsMaximal → M.height = N.height :=
    height_eq_of_isMaximal_of_intCast_eq_zero (B := A ⧸ q) ℓ hℓ.ne_zero (by
      rw [← map_intCast (Ideal.Quotient.mk q), Ideal.Quotient.eq_zero_iff_mem]; exact hℓq)
  have hMb : (M.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
  have h1 := height_add_height_map_le (q := q) (M := M) hqM
  have h2 := height_eq_ringKrullDim_of_forall hEq _ hMb
  have h3 := specialFibre_dim_ge P hP ℓ hℓ q hq
  calc ringKrullDim A ≤ ringKrullDim (A ⧸ q) + 1 := h3
    _ = ((M.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [h2]; rfl
    _ ≤ ((M.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) + (q.height : WithBot ℕ∞) :=
        add_le_add le_rfl (WithBot.coe_le_coe.mpr hqh)
    _ = ((q.height + (M.map (Ideal.Quotient.mk q)).height : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add, add_comm]
    _ ≤ M.height := WithBot.coe_le_coe.mpr h1

theorem height_eq_of_isMaximal_int {σ : Type*} [Finite σ] (P : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] (M N : Ideal (MvPolynomial σ ℤ ⧸ P)) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  by_cases hP : P.comap MvPolynomial.C = ⊥
  · have h1 := height_eq_of_isMaximal_int_charZero P hP M hM
    have h2 := height_eq_of_isMaximal_int_charZero P hP N hN
    exact_mod_cast h1.trans h2.symm
  · obtain ⟨n, hnP, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hq : Algebra.FiniteType ℤ (MvPolynomial σ ℤ ⧸ P) := by
      first
        | infer_instance
        | exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ ℤ P)
            (Ideal.Quotient.mkₐ_surjective ℤ P)
    refine @height_eq_of_isMaximal_of_intCast_eq_zero _ _ _ ?_ n hn0 ?_ M N hM hN
    · first
        | exact hq
        | (convert hq using 1 <;> first
            | exact Subsingleton.elim _ _
            | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm)
    have e1 : (MvPolynomial.C n : MvPolynomial σ ℤ) = (n : MvPolynomial σ ℤ) := eq_intCast MvPolynomial.C n
    have e2 : ((n : ℤ) : MvPolynomial σ ℤ ⧸ P) = Ideal.Quotient.mk P (n : MvPolynomial σ ℤ) :=
      (map_intCast _ n).symm
    rw [e2, Ideal.Quotient.eq_zero_iff_mem, ← e1]
    exact hnP

end ReciprocityTheory.ChartRestriction.G.Geo.DimF
