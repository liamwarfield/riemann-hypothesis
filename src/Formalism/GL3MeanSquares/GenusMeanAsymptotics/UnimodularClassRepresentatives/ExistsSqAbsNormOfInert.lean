module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSubMemOfInert
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NotIsPrimeMapOfSplit
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem surj_of_invol (hσ : ∀ x, σ (σ x) = x) : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩

theorem comap_isMaximal_invol (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (surj_of_invol hσ)

theorem fix_ι (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a :=
  (hfix _).2 ⟨a, rfl⟩

theorem comap_ι_comap (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by
  ext a
  simp only [Ideal.mem_comap, fix_ι hfix]

theorem comap_eq_comap_iff (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P Q : Ideal B} (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap ι = Q.comap ι ↔ Q = P ∨ Q = P.comap σ := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP

    have hout : ∀ R : Ideal B, R.IsMaximal → Q ≠ R → ∃ y ∈ Q, y ∉ R := by
      intro R hR hQR
      by_contra hc
      push_neg at hc
      exact hQR (hQ.eq_of_le hR.ne_top hc)
    obtain ⟨y, hyQ, hyP⟩ := hout P hP hne.1
    obtain ⟨z, hzQ, hzP'⟩ := hout _ hP' hne.2

    have hx : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.comap σ := by
      by_cases hy' : y ∈ P.comap σ
      · by_cases hz' : z ∈ P
        · refine ⟨y + z, Q.add_mem hyQ hzQ, fun h' => hyP ?_, fun h' => hzP' ?_⟩
          · simpa using P.sub_mem h' hz'
          · simpa using (P.comap σ).sub_mem h' hy'
        · exact ⟨z, hzQ, hz', hzP'⟩
      · exact ⟨y, hyQ, hyP, hy'⟩
    obtain ⟨x, hxQ, hxP, hxP'⟩ := hx
    have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hσ, mul_comm]
    obtain ⟨a, ha⟩ := (hfix _).1 hfx
    have haQ : a ∈ Q.comap ι := by
      rw [Ideal.mem_comap, ha]
      exact Q.mul_mem_right _ hxQ
    rw [← h, Ideal.mem_comap, ha] at haQ
    rcases hP.isPrime.mem_or_mem haQ with h1 | h1
    · exact hxP h1
    · exact hxP' h1
  · rintro (rfl | rfl)
    · rfl
    · exact (comap_ι_comap hfix P).symm

theorem exists_sub_mem_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) (b : B) : ∃ a : A, b - ι a ∈ P := by
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  rw [Ideal.mem_comap] at hv
  have hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v) := by rw [map_add (f := _), hσ, add_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  refine ⟨a, ?_⟩
  have hv' : v = 1 - u := by rw [← huv]; ring
  have : b - ι a = b * u - σ b * σ v := by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring
  rw [this]
  exact P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)

theorem card_quot_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) :
    Nat.card (A ⧸ P.comap ι) = Nat.card (B ⧸ P) := by
  let f : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_of_split hσ hfix hP hc b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    simpa using P.neg_mem ha
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem not_isPrime_map_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) : ¬ ((P.comap ι).map ι).IsPrime := by
  intro hpr
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  have hu' : u ∉ P.comap σ := by
    intro h
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))
  have hle1 : (P.comap ι).map ι ≤ P := Ideal.map_comap_le
  have hle2 : (P.comap ι).map ι ≤ P.comap σ := by
    rw [← comap_ι_comap hfix P]
    exact Ideal.map_comap_le
  have hfx : σ (u * σ u) = u * σ u := by rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  have hmem : u * σ u ∈ (P.comap ι).map ι := by
    rw [← ha]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ha]
    exact P.mul_mem_right _ hu
  rcases hpr.mem_or_mem hmem with h1 | h1
  · exact hu' (hle2 h1)
  · exact hu' (by rw [Ideal.mem_comap]; exact hle1 h1)

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
end

namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

private theorem exists_sub_iota_mem_of_sub_involution_mem (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P)
    (x : B) (hx : x - σ x ∈ P) : ∃ a : A, x - ι a ∈ P := by
  have hσP : ∀ p ∈ P, σ p ∈ P := fun p hp => Ideal.mem_comap.1 (hc.symm ▸ hp)
  have hσδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have hDP : (θ - σ θ) * (θ - σ θ) ∉ P := fun h => hθ ((hP.isPrime.mem_or_mem h).elim id id)
  obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hDP
  have hσi : σ i ∈ P := hσP i hi
  have h2 : σ u * ((θ - σ θ) * (θ - σ θ)) + σ i = 1 := by
    have := congrArg σ hui
    rwa [map_add, map_mul, map_mul, hσδ, map_one, neg_mul_neg] at this

  set y := ((x * θ - σ x * σ θ) * (θ - σ θ)) * (u * σ u * ((θ - σ θ) * (θ - σ θ))) with hy_def
  have hy : σ y = y := by
    rw [hy_def]
    simp only [map_mul, map_sub, hσ]
    ring
  obtain ⟨a, ha⟩ := (hfix y).1 hy
  refine ⟨a, ?_⟩
  rw [ha]
  have e : x - y = x * i + x * σ i - x * i * σ i -
      (x - σ x) * (σ θ * (θ - σ θ) * u * σ u * ((θ - σ θ) * (θ - σ θ))) := by
    rw [hy_def]
    linear_combination (-x * σ u * ((θ - σ θ) * (θ - σ θ))) * hui + (-x * (1 - i)) * h2
  rw [e]
  exact P.sub_mem (P.sub_mem (P.add_mem (P.mul_mem_left _ hi) (P.mul_mem_left _ hσi))
    (P.mul_mem_left _ hσi)) (P.mul_mem_right _ hx)

private theorem card_quotient_comap_sq_eq_card_quotient_of_involution (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    Nat.card (A ⧸ P.comap ι) ^ 2 = Nat.card (B ⧸ P) := by
  classical
  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  have hle : P ≤ P.comap σ := le_of_eq hc.symm
  set sb : B ⧸ P →+* B ⧸ P := Ideal.quotientMap P σ hle with hsb
  set φ : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl with hφ
  have hsbmk : ∀ x, sb (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) :=
    fun x => Ideal.quotientMap_mk
  have hsb2 : ∀ c, sb (sb c) = c := by
    intro c
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hsbmk, hsbmk, hσ]
  have hφmk : ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk P (ι a) :=
    fun a => Ideal.quotientMap_mk
  have hsbφ : ∀ c, sb (φ c) = φ c := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hφmk, hsbmk, (hfix (ι a)).2 ⟨a, rfl⟩]
  have hφinj : Function.Injective φ := Ideal.quotientMap_injective
  have hlift : ∀ c, sb c = c → ∃ a, φ a = c := by
    intro c hcfix
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hsbmk] at hcfix
    have hx : x - σ x ∈ P := Ideal.Quotient.eq.1 hcfix.symm
    obtain ⟨a, ha⟩ := exists_sub_iota_mem_of_sub_involution_mem hσ hfix hP hc hθ x hx
    exact ⟨Ideal.Quotient.mk _ a, by rw [hφmk]; exact (Ideal.Quotient.eq.2 ha).symm⟩
  set th := Ideal.Quotient.mk P θ with hth
  have hδ : th - sb th ≠ 0 := by
    rw [hth, hsbmk, ← map_sub, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hθ

  let f : (A ⧸ P.comap ι) × (A ⧸ P.comap ι) → B ⧸ P := fun p => φ p.1 + φ p.2 * th
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [f] at h
      have h2 := congrArg sb h
      simp only [map_add (f := _), map_mul, hsbφ] at h2
      have hb : φ b = φ b' := by
        have h3 : (φ b - φ b') * (th - sb th) = 0 := by linear_combination h - h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact sub_eq_zero.1 h4
        · exact absurd h4 hδ
      have ha : φ a = φ a' := by
        rw [hb] at h
        exact add_right_cancel h
      exact Prod.ext (hφinj ha) (hφinj hb)
    · intro y
      set bb := (y - sb y) / (th - sb th) with hbb_def
      have hbb : sb bb = bb := by
        rw [hbb_def, map_div₀, map_sub, map_sub, hsb2, hsb2,
          show sb y - y = -(y - sb y) by ring, show sb th - th = -(th - sb th) by ring,
          neg_div_neg_eq]
      have hmul : bb * (th - sb th) = y - sb y := div_mul_cancel₀ _ hδ
      set aa := y - bb * th with haa_def
      have haa : sb aa = aa := by
        rw [haa_def, map_sub, map_mul, hbb]
        linear_combination hmul
      obtain ⟨a, ha⟩ := hlift aa haa
      obtain ⟨b, hb⟩ := hlift bb hbb
      refine ⟨(a, b), ?_⟩
      simp only [f, ha, hb, haa_def]
      ring
  rw [sq, ← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem exists_sq_card_quot (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal)
    (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) : ∃ q : ℕ, Nat.card (B ⧸ P) = q ^ 2 := by
  classical
  set S : Subring B := RingHom.eqLocus σ (RingHom.id B) with hS
  have hfix' : ∀ x, σ x = x ↔ x ∈ Set.range (S.subtype) := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.2
  exact ⟨Nat.card (S ⧸ P.comap S.subtype), (card_quotient_comap_sq_eq_card_quotient_of_involution (ι := S.subtype) hσ hfix' hP hc hθ).symm⟩

theorem card_quot_inert (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    Nat.card (A ⧸ P.comap ι) ^ 2 = Nat.card (B ⧸ P) := by
  exact card_quotient_comap_sq_eq_card_quotient_of_involution hσ hfix hP hc hθ

theorem map_comap_of_inert (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ = P) {θ : B} (hθ : θ - σ θ ∉ P) :
    (P.comap ι).map ι = P := by
  have hσP : ∀ p ∈ P, σ p ∈ P := fun p hp => Ideal.mem_comap.1 (hc.symm ▸ hp)

  have hmem : ∀ z, σ z = z → z ∈ P → z ∈ (P.comap ι).map ι := by
    intro z hz hzP
    obtain ⟨a, rfl⟩ := (hfix z).1 hz
    exact Ideal.mem_map_of_mem ι (Ideal.mem_comap.2 hzP)
  refine le_antisymm Ideal.map_comap_le fun y hy => ?_
  have hσδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have hDP : (θ - σ θ) * (θ - σ θ) ∉ P := fun h => hθ ((hP.isPrime.mem_or_mem h).elim id id)
  obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hDP
  have h2 : σ u * ((θ - σ θ) * (θ - σ θ)) + σ i = 1 := by
    have := congrArg σ hui
    rwa [map_add, map_mul, map_mul, hσδ, map_one, neg_mul_neg] at this
  set v := u * σ u * ((θ - σ θ) * (θ - σ θ)) with hv
  set j := 1 - v * ((θ - σ θ) * (θ - σ θ)) with hj
  have hjfix : σ j = j := by
    rw [hj, hv]
    simp only [map_sub, map_mul, map_one, hσ]
    ring
  have hjP : j ∈ P := by
    have e : j = i + σ i - i * σ i := by
      rw [hj, hv]
      linear_combination (-σ u * ((θ - σ θ) * (θ - σ θ))) * hui + (-(1 - i)) * h2
    rw [e]
    exact P.sub_mem (P.add_mem hi (hσP i hi)) (P.mul_mem_left _ (hσP i hi))
  have hT : ∀ w ∈ P, w + σ w ∈ (P.comap ι).map ι := fun w hw =>
    hmem _ (by rw [map_add (f := _), hσ, add_comm]) (P.add_mem hw (hσP w hw))
  have e : y = y * j + ((y * θ + σ (y * θ)) - σ θ * (y + σ y)) * (v * (θ - σ θ)) := by
    rw [hj, map_mul]
    ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmem j hjfix hjP))
    (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (hT _ (P.mul_mem_right _ hy))
      (Ideal.mul_mem_left _ _ (hT y hy))))

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have hr : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      have h2 : (r : K) = star (s : K) := hrs
      rw [h2, star_star]
    show conjO K r ∈ P
    rw [hr]
    exact hs
  · intro x hx
    apply Ideal.subset_span
    refine ⟨conjO K x, hx, ?_⟩
    show (x : K) = star ((conjO K x : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  refine ⟨θ, ?_⟩
  have hθt : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rwa [hθt]

omit [StarRing K] in
theorem absNorm_eq_card (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rfl
  | (rw [Ideal.absNorm_apply]; rfl)
  | (rw [Ideal.absNorm_apply, Submodule.cardQuot_apply])

theorem conjIdeal_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
  rw [conjIdeal_eq_comap]
  haveI := hP
  exact Ideal.comap_isMaximal_of_surjective (conjO K) (fun y => ⟨conjO K y, conjO_conjO y⟩)

theorem conjIdeal_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
  ext x
  simp only [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO]

theorem conjIdeal_eq_map (P : Ideal (𝓞 K)) : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (conjO K) := by
  rw [conjIdeal_eq_comap]
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (conjO K) (show conjO K x ∈ P from hx)
    rwa [conjO_conjO] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa only [Ideal.mem_comap, conjO_conjO] using hx

theorem absNorm_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by
  rw [absNorm_eq_card, absNorm_eq_card]
  let e : 𝓞 K ≃+* 𝓞 K :=
    { conjO K with
      invFun := conjO K
      left_inv := fun x => conjO_conjO x
      right_inv := fun x => conjO_conjO x }
  have h : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [conjIdeal_eq_map]
    rfl
  exact (Nat.card_congr (Ideal.quotientEquiv P _ e h).toEquiv).symm

theorem exists_sq_absNorm_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    ∃ q : ℕ, Ideal.absNorm P = q ^ 2 := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card]
  exact SplitPrimeIdeals.exists_sq_card_quot conjO_conjO hP hc hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem conjO_eq_iff_mem_range (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
  constructor
  · intro hx
    have hfix : star (x : K) = x := by rw [← conjO_coe, hx]
    obtain ⟨a, ha⟩ := (hF _).1 hfix
    have hint : IsIntegral ℤ (algebraMap F K a) := by
      rw [ha]
      first
      | exact RingOfIntegers.isIntegral_coe x
      | exact x.2
    have ha' : IsIntegral ℤ a := (isIntegral_algebraMap_iff ).1 hint
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply RingOfIntegers.ext
    show algebraMap F K a = (x : K)
    exact ha
  · rintro ⟨y, rfl⟩
    apply RingOfIntegers.ext
    rw [conjO_coe]
    have hy : ((algebraMap (𝓞 F) (𝓞 K) y : 𝓞 K) : K) = algebraMap F K (y : F) := rfl
    rw [hy]
    exact (hF _).2 ⟨_, rfl⟩

theorem comap_eq_comap_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [conjIdeal_eq_comap]
  exact SplitPrimeIdeals.comap_eq_comap_iff conjO_conjO (conjO_eq_iff_mem_range hF) hP hQ

theorem exists_maximal_over (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact FaithfulSMul.algebraMap_injective _ _
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       exact congrArg (fun z : 𝓞 K => (z : K)) hab)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hker

theorem absNorm_comap_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem absNorm_comap_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc

theorem etaF_comap (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by
  rw [conjIdeal_eq_comap]
  unfold etaF
  by_cases hc : P.comap (conjO K) = P
  · obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    rw [SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ, if_pos hP.isPrime,
      if_pos hc]
  · rw [if_neg (SplitPrimeIdeals.not_isPrime_map_of_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc),
      if_neg hc]

end WithF

end Formalism.HermitianLattices.Ext.L3
