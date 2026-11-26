module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatching
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem descend (hS : SameNormBasic) {B ι : Type} [CommRing B] [Fintype ι] {a b : B} (hab : a ∣ b)
    {u u' : Multiset (ι → B)} (h : SameNorm (redMod b u) (redMod b u')) :
    SameNorm (redMod a u) (redMod a u') := by
  have hle : Ideal.span {b} ≤ Ideal.span {a} := Ideal.span_singleton_le_span_singleton.2 hab
  have := (hS (B ⧸ Ideal.span {b}) ι).1 (B ⧸ Ideal.span {a}) (Ideal.Quotient.factor hle) _ _ h
  simpa only [redMod, Multiset.map_map, Function.comp_def, Ideal.Quotient.factor_mk] using this

private theorem red_cons {B ι : Type} [CommRing B] (a : B) (x : ι → B) (u : Multiset (ι → B)) :
    redMod a (x ::ₘ u) = (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) ::ₘ redMod a u := by
  simp [redMod]

private theorem red_eq {B ι : Type} [CommRing B] {a : B} {x y : ι → B} (h : ∀ k, a ∣ x k - y k) :
    (fun k => Ideal.Quotient.mk (Ideal.span {a}) (x k)) = fun k => Ideal.Quotient.mk (Ideal.span {a}) (y k) := by
  funext k
  exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h k))

private theorem main (hS : SameNormBasic) (hM : MatchStep) {B : Type} [CommRing B] (ϖ : B)
    (h0 : ϖ ∈ nonZeroDivisors B) (h1 : ¬ IsUnit ϖ) {ι : Type} [Fintype ι] (N : ℕ) :
    ∀ c, c ≤ N → ∀ (u u' : Multiset (ι → B)), u.card = c → u'.card ≤ N →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ (N + 1) ^ N → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k, ∀ j ≤ N, x k - y k ∣ ϖ ^ (N + 1) ^ j ∨ ϖ ^ (N + 1) ^ j ∣ x k - y k) →
    SameNorm (redMod (ϖ ^ (N + 1) ^ c) u) (redMod (ϖ ^ (N + 1) ^ c) u') →
    redMod ϖ u = redMod ϖ u' := by
  have hnu : ∀ j : ℕ, j ≠ 0 → ¬ IsUnit (ϖ ^ j) := fun j hj h => h1 ((isUnit_pow_iff hj).mp h)
  intro c
  induction c with
  | zero =>
    intro _ u u' hu _ _ _ hsn
    have hu0 : u = 0 := Multiset.card_eq_zero.mp hu
    subst hu0
    haveI : Nontrivial (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ 0}) := by
      refine nontrivial_of_ne 1 0 ?_
      intro h
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ ^ (N + 1) ^ 0})),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h
      exact hnu _ (by positivity) h
    have hc := (hS _ ι).2.2.1 inferInstance _ _ hsn
    have hu'0 : u' = 0 := by
      simp only [redMod, Multiset.card_map, Multiset.card_zero, Multiset.map_zero] at hc
      exact Multiset.card_eq_zero.mp hc.symm
    subst hu'0
    rfl
  | succ c ih =>
    intro hc u u' hu hu' hdiv hcmp hsn
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hu]; exact Nat.succ_pos c)
    obtain ⟨u0, rfl⟩ := Multiset.exists_cons_of_mem hx
    have hxm : x ∈ x ::ₘ u0 := Multiset.mem_cons.mpr (Or.inl rfl)
    have hm : 0 < (N + 1) ^ c := by positivity
    have hle : (N + 1) ^ c ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
    have hsn' : SameNorm (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) (x ::ₘ u0))
        (redMod (ϖ ^ ((N + 1) ^ c * (N + 1))) u') := by
      rw [← pow_succ]; exact hsn
    obtain ⟨y, hy, hxy⟩ := hM B ϖ h0 h1 ι N ((N + 1) ^ c) hm (x ::ₘ u0) u' hu' hsn' x hxm
      (fun y hy k k' h => hdiv x hxm y hy k k' (h.trans (pow_dvd_pow ϖ hle)))
      (fun y hy k => hcmp x hxm y hy k c (by omega))
    obtain ⟨u0', rfl⟩ := Multiset.exists_cons_of_mem hy
    have hsn2 : SameNorm (redMod (ϖ ^ (N + 1) ^ c) (x ::ₘ u0)) (redMod (ϖ ^ (N + 1) ^ c) (y ::ₘ u0')) :=
      descend hS (pow_dvd_pow ϖ (Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_succ c))) hsn
    rw [red_cons, red_cons, red_eq hxy] at hsn2
    have hsn3 := (hS _ ι).2.1 _ _ _ hsn2
    have ih' := ih (by omega) u0 u0' (by simpa using hu) (by simp at hu'; omega)
      (fun a ha b hb => hdiv a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      (fun a ha b hb => hcmp a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb)) hsn3
    rw [red_cons, red_cons, ih', red_eq (fun k => (dvd_pow_self ϖ hm.ne').trans (hxy k))]

theorem UpperTheory.Gal.crystallineComparison.matching_of :
    SameNormBasic → MatchStep → Matching := by
  intro hS hM B _ ϖ h0 h1 ι _ N u u' hu hu' hsn hdiv hcmp
  apply main hS hM ϖ h0 h1 N u.card hu u u' rfl hu' hdiv hcmp
  exact descend hS (pow_dvd_pow _ (Nat.pow_le_pow_right (Nat.succ_pos N) hu)) hsn
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtChart
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem ring_step {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    (a : R) (f : R →+* R') (g : S →+* S') (h : R' →+* S') (hc : h.comp f = g.comp (algebraMap R S))
    (hf : letI := f.toAlgebra; IsLocalization.Away a R')
    (hg : letI := g.toAlgebra; IsLocalization.Away (algebraMap R S a) S') (het : h.Etale) :
    Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[R] S) := by
  classical
  letI : Algebra R R' := f.toAlgebra
  letI : Algebra S S' := g.toAlgebra
  letI : Algebra S (Localization.Away a ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) =
      Submonoid.powers (algebraMap R S a) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' := by
    rw [hM]; exact hg
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization.Away a ⊗[R] S) := IsLocalization.tensorRight _ (Submonoid.powers a)
  let e1 := IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) R'
  let e2 := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
    (Localization.Away a ⊗[R] S) S'
  have key : algebraMap (Localization.Away a) (Localization.Away a ⊗[R] S) =
      e2.symm.toRingEquiv.toRingHom.comp (h.comp e1.toRingEquiv.toRingHom) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    have h1 : e1 (algebraMap R (Localization.Away a) r) = f r := by
      rw [AlgEquiv.commutes]; rfl
    have h2 : h (f r) = g (algebraMap R S r) := by
      rw [← RingHom.comp_apply, hc, RingHom.comp_apply]
    have h3 : e2.symm (g (algebraMap R S r)) =
        algebraMap S (Localization.Away a ⊗[R] S) (algebraMap R S r) := by
      rw [← AlgEquiv.commutes e2.symm]; rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv]
    rw [h1, h2, h3]
    simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← RingHom.etale_algebraMap, key]
  exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ het)

private theorem appLE_step {Y Z : Scheme.{0}} (p : Z ⟶ Y) (D U' : Y.Opens) [Etale (p ∣_ D)] (hUD : U' ≤ D)
    (hU' : IsAffineOpen U') (W' : Z.Opens) (hW' : IsAffineOpen W') (e : W' ≤ p ⁻¹ᵁ U') :
    (p.appLE U' W' e).hom.Etale := by
  have hV : IsAffineOpen (D.ι ⁻¹ᵁ U') :=
    hU'.preimage_of_isOpenImmersion D.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUD)
  have hW : IsAffineOpen ((p ⁻¹ᵁ D).ι ⁻¹ᵁ W') :=
    hW'.preimage_of_isOpenImmersion _
      (by rw [Scheme.Opens.opensRange_ι]; exact e.trans (fun x hx => hUD hx))
  have e' : (p ⁻¹ᵁ D).ι ⁻¹ᵁ W' ≤ (p ∣_ D) ⁻¹ᵁ (D.ι ⁻¹ᵁ U') := by
    intro x hx
    have h1 := e hx
    have h2 : D.ι ((p ∣_ D) x) = p ((p ⁻¹ᵁ D).ι x) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    change D.ι ((p ∣_ D) x) ∈ U'
    rw [h2]
    exact h1
  have H := HasRingHomProperty.appLE @Etale (p ∣_ D) ‹_›
    ⟨D.ι ⁻¹ᵁ U', hV⟩ ⟨(p ⁻¹ᵁ D).ι ⁻¹ᵁ W', hW⟩ e'
  rw [morphismRestrict_appLE] at H
  refine (Scheme.Hom.appLE_congr _ _ ?_ ?_ (fun f => f.hom.Etale)).mp H
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUD]
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (e.trans (fun x hx => hUD hx))]

theorem UpperTheory.Gal.crystallineComparison.etChart_of :
    EtChart := by
  unfold EtChart
  intro l Y T U hU
  letI := T.alg U
  haveI := T.fin
  haveI := T.et
  have hZU : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have e0 : T.Z.basicOpen ((T.p.app U).hom (l : Γ(Y, U))) ≤
      T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, U)) := (Scheme.preimage_basicOpen T.p _).ge
  have hUD : Y.basicOpen (l : Γ(Y, U)) ≤ Y.basicOpen (l : Γ(Y, ⊤)) := by
    have hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (l : Γ(Y, ⊤)) =
        (l : Γ(Y, U)) := map_natCast _ l
    rw [← hres, Scheme.basicOpen_res]
    exact inf_le_right
  have het := appLE_step T.p (Y.basicOpen (l : Γ(Y, ⊤))) (Y.basicOpen (l : Γ(Y, U))) hUD
    (hU.basicOpen _) _ (hZU.basicOpen _) e0
  refine ring_step (l : Γ(Y, U))
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (l : Γ(Y, U)))).op).hom
    (T.Z.presheaf.map (homOfLE (T.Z.basicOpen_le ((T.p.app U).hom (l : Γ(Y, U))))).op).hom
    (T.p.appLE _ _ e0).hom ?_ (hU.isLocalization_basicOpen _) (hZU.isLocalization_basicOpen _) het
  rw [← CommRingCat.hom_comp]
  change _ = CommRingCat.Hom.hom (T.p.app U ≫ _)
  congr 1
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValLocal
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem UpperTheory.Gal.crystallineComparison.one_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) :
    (1 : B) ∉ 𝔪 :=
  fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h)

private theorem UpperTheory.Gal.crystallineComparison.good_or {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime) (e : B) :
    e ∉ 𝔪 ∨ 1 - e ∉ 𝔪 := by
  by_contra h
  push_neg at h
  exact one_not_mem h𝔪 (by simpa using 𝔪.add_mem h.1 h.2)

private theorem UpperTheory.Gal.crystallineComparison.mul_not_mem {B : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    {a b : B} (ha : a ∉ 𝔪) (hb : b ∉ 𝔪) : a * b ∉ 𝔪 :=
  fun h => (h𝔪.mem_or_mem h).elim ha hb

private theorem UpperTheory.Gal.crystallineComparison.dvd_st {B : Type} [CommRing B] {a b e : B} (e' : B) (h : a ∣ e * b) :
    a ∣ e' * e * b := by
  rw [mul_assoc]
  exact Dvd.dvd.mul_left h e'

private theorem UpperTheory.Gal.crystallineComparison.good_combine {B ι : Type} [CommRing B] {𝔪 : Ideal B} (h𝔪 : 𝔪.IsPrime)
    (s : Finset ι) (Q : ι → B → Prop) (st : ∀ i e e', Q i e → Q i (e' * e))
    (ex : ∀ i ∈ s, ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ Q i e) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ ∀ i ∈ s, Q i e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, by simp⟩
  | insert a s ha ih =>
    obtain ⟨e, he, hem, hQ⟩ := ih fun i hi => ex i (Finset.mem_insert_of_mem hi)
    obtain ⟨e', he', hem', hQ'⟩ := ex a (Finset.mem_insert_self a s)
    refine ⟨e' * e, he'.mul he, mul_not_mem h𝔪 hem' hem, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_comm]
      exact st _ _ _ hQ'
    · exact st _ _ _ (hQ i hi)

private theorem UpperTheory.Gal.crystallineComparison.power_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (d : B) (m : ℕ) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧ (d ∣ e * ϖ ^ m ∨ ϖ ^ m ∣ e * d) := by
  obtain ⟨e, he, h1, h2⟩ := hv d (ϖ ^ m) ⟨m, Ideal.subset_span (by simp)⟩
  rcases good_or h𝔪 e with g | g
  · exact ⟨e, he, g, Or.inr h1⟩
  · exact ⟨1 - e, he.one_sub, g, Or.inl h2⟩

private theorem UpperTheory.Gal.crystallineComparison.pair_good {B : Type} [CommRing B] {ϖ : B} (hv : ValLike ϖ) {𝔪 : Ideal B}
    (h𝔪 : 𝔪.IsPrime) (M : ℕ) (d d' : B) :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔪 ∧
      ((∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M) → d ∣ e * d' ∨ d' ∣ e * d) := by
  by_cases h : ∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ d ∣ e₀ * ϖ ^ M
  · obtain ⟨e₀, h0, hm0, c, hc⟩ := h
    have h0' : e₀ * e₀ = e₀ := h0
    obtain ⟨f, hfd⟩ : ∃ f : B, f = e₀ * d + (1 - e₀) := ⟨_, rfl⟩
    have hf : e₀ * f = e₀ * d := by
      rw [hfd]
      linear_combination (d - 1) * h0'
    have hmem : ϖ ^ M ∈ Ideal.span {f, d'} := by
      have hP : ϖ ^ M = (e₀ * c + (1 - e₀) * ϖ ^ M) * f := by
        rw [hfd]
        linear_combination (-(c * d - c - d * ϖ ^ M + 2 * ϖ ^ M)) * h0' + e₀ * hc
      rw [hP]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    obtain ⟨e₁, h1, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hv f d' ⟨M, hmem⟩
    have A : d' ∣ (e₀ * e₁) * d := ⟨e₀ * a, by linear_combination e₀ * ha - e₁ * hf⟩
    have C : d ∣ (e₀ * (1 - e₁)) * d' := ⟨e₀ * b, by linear_combination e₀ * hb + b * hf⟩
    rcases good_or h𝔪 e₁ with g | g
    · exact ⟨e₀ * e₁, h0.mul h1, mul_not_mem h𝔪 hm0 g, fun _ => Or.inr A⟩
    · exact ⟨e₀ * (1 - e₁), h0.mul h1.one_sub, mul_not_mem h𝔪 hm0 g, fun _ => Or.inl C⟩
  · exact ⟨1, IsIdempotentElem.one, one_not_mem h𝔪, fun h' => absurd h' h⟩

theorem UpperTheory.Gal.crystallineComparison.valLocal_of :
    ValLocal := by
  intro B _ ϖ hv 𝔪 h𝔪 D M
  obtain ⟨e₁, i₁, g₁, q₁⟩ := good_combine h𝔪 (D ×ˢ Finset.range (M + 1))
    (fun p e => p.1 ∣ e * ϖ ^ p.2 ∨ ϖ ^ p.2 ∣ e * p.1)
    (fun p e e' h => h.elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => power_good hv h𝔪 p.1 p.2)
  obtain ⟨e₂, i₂, g₂, q₂⟩ := good_combine h𝔪 (D ×ˢ D)
    (fun p e => (∃ e₀ : B, IsIdempotentElem e₀ ∧ e₀ ∉ 𝔪 ∧ p.1 ∣ e₀ * ϖ ^ M) →
      p.1 ∣ e * p.2 ∨ p.2 ∣ e * p.1)
    (fun p e e' h h' => (h h').elim (fun h => Or.inl (dvd_st e' h)) (fun h => Or.inr (dvd_st e' h)))
    (fun p _ => pair_good hv h𝔪 M p.1 p.2)
  refine ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, ?_, ?_⟩
  · intro d hd m hm
    have := q₁ (d, m) (Finset.mk_mem_product hd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
    exact this.elim (fun h => Or.inl (dvd_st e₂ h)) (fun h => Or.inr (dvd_st e₂ h))
  · intro d hd d' hd' hdv
    have := q₂ (d, d') (Finset.mk_mem_product hd hd') ⟨e₂ * e₁, i₂.mul i₁, mul_not_mem h𝔪 g₂ g₁, hdv⟩
    rw [mul_comm e₂ e₁]
    exact this.elim (fun h => Or.inl (dvd_st e₁ h)) (fun h => Or.inr (dvd_st e₁ h))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PIdemCover
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma idem_prod_one_sub {B : Type} [CommRing B] (s : Finset B)
    (hs : ∀ e ∈ s, IsIdempotentElem e) : IsIdempotentElem (∏ e ∈ s, (1 - e)) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e he => (hs e he).one_sub

private lemma one_sub_prod_mem {B : Type} [CommRing B] (I : Ideal B) (s : Finset B)
    (hs : ∀ e ∈ s, e ∈ I) : 1 - ∏ e ∈ s, (1 - e) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : a ∈ I := hs a (Finset.mem_insert_self a s)
    have h2 := ih fun e he => hs e (Finset.mem_insert_of_mem he)
    have : 1 - (1 - a) * ∏ e ∈ s, (1 - e) = (1 - ∏ e ∈ s, (1 - e)) + a * ∏ e ∈ s, (1 - e) := by ring
    rw [this]
    exact I.add_mem h2 (I.mul_mem_right _ h1)

private lemma cover_step {B : Type} [CommRing B] (Λ : Type) [Fintype Λ] (J : Λ → Ideal B)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ σ, ∃ e ∈ J σ, IsIdempotentElem e ∧ e ∉ 𝔪) :
    ∃ f : Λ → B, (∀ σ, IsIdempotentElem (f σ)) ∧ (∀ σ, f σ ∈ J σ) ∧ ∏ σ, (1 - f σ) = 0 := by
  classical
  let E : Set B := {e | IsIdempotentElem e ∧ ∃ σ, e ∈ J σ}
  have hE : Ideal.span E = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨σ, e, he, hi, hn⟩ := h 𝔪 hm
    exact hn (hle (Ideal.subset_span ⟨hi, σ, he⟩))
  obtain ⟨t, htE, ht⟩ := (Ideal.span_eq_top_iff_finite E).1 hE
  refine ⟨fun σ => 1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e), fun σ => ?_, fun σ => ?_, ?_⟩
  · exact (idem_prod_one_sub _ fun e he => (htE (Finset.mem_filter.1 he).1).1).one_sub
  · exact one_sub_prod_mem _ _ fun e he => (Finset.mem_filter.1 he).2
  · set g : B := ∏ σ, (1 - (1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e))) with hg
    have hkill : ∀ e ∈ t, e * g = 0 := by
      intro e he
      obtain ⟨hi, σ, hσ⟩ := htE he
      have hef : e ∈ t.filter (· ∈ J σ) := Finset.mem_filter.2 ⟨he, hσ⟩
      obtain ⟨c, hc⟩ : (1 - e) ∣ g := by
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ σ))
        rw [sub_sub_cancel]
        exact Finset.dvd_prod_of_mem _ hef
      have h0 : e * (1 - e) = 0 := by
        have : e * e = e := hi
        rw [mul_sub, mul_one, this, sub_self]
      rw [hc, ← mul_assoc, h0, zero_mul]
    have hall : ∀ x ∈ Ideal.span (t : Set B), x * g = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hkill x hx
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
    have := hall 1 (by rw [ht]; trivial)
    rwa [one_mul] at this

theorem UpperTheory.Gal.crystallineComparison.idemCover_of :
    IdemCover := by
  intro B _ Λ _ J h
  classical
  obtain ⟨f, hfi, hfJ, hf0⟩ := cover_step Λ J h
  letI : LinearOrder Λ := LinearOrder.lift' (Fintype.equivFin Λ) (Equiv.injective _)
  let P : Λ → B := fun σ => ∏ τ ∈ Finset.univ.filter (· < σ), (1 - f τ)
  have hP : ∀ σ, IsIdempotentElem (P σ) := by
    intro σ
    show P σ * P σ = P σ
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => (hfi τ).one_sub
  have hkill : ∀ σ τ, τ < σ → P σ * f τ = 0 := by
    intro σ τ hτ
    obtain ⟨c, hc⟩ : (1 - f τ) ∣ P σ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ τ, hτ⟩)
    have h0 : (1 - f τ) * f τ = 0 := by
      have : f τ * f τ = f τ := hfi τ
      rw [sub_mul, one_mul, this, sub_self]
    rw [hc, mul_comm (1 - f τ) c, mul_assoc, h0, mul_zero]
  have hlt : ∀ σ τ, τ < σ → (f σ * P σ) * (f τ * P τ) = 0 := by
    intro σ τ hτ
    have : (f σ * P σ) * (f τ * P τ) = f σ * (P σ * f τ) * P τ := by ring
    rw [this, hkill σ τ hτ, mul_zero, zero_mul]
  refine ⟨fun σ => f σ * P σ, ⟨⟨fun σ => (hfi σ).mul (hP σ), ?_⟩, ?_⟩, fun σ => (J σ).mul_mem_right _ (hfJ σ)⟩
  · intro σ τ hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · show (f σ * P σ) * (f τ * P τ) = 0
      rw [mul_comm]
      exact hlt τ σ hl
    · exact hlt σ τ hl
  · have := Finset.prod_one_sub_ordered (Finset.univ : Finset Λ) f
    rw [hf0] at this
    exact (sub_eq_zero.1 this.symm).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCountOut
noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem countOut_of : CountOut := by
  intro k H _ _ _ _ _ C hC E
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)
  have hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e := by
    intro s hs e
    exact LinearMap.congr_fun hs e
  let S := {s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}
  have hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E := by
    intro s
    constructor
    · intro hle
      haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC
      obtain ⟨c, hc⟩ := exists_ne (0 : C)
      obtain ⟨e, he⟩ := LinearMap.mem_range.1 (hle c.2)
      have h1 : C.mkQ (s.1 e) = e := hsec s.1 s.2 e
      have h2 : C.mkQ (c : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 c.2
      rw [he, h2] at h1
      have e0 : e = 0 := Subtype.ext h1.symm
      apply hc
      apply Subtype.ext
      rw [← he, e0, map_zero]
      rfl
    · rw [← LinearMap.range_comp, s.2, Submodule.range_subtype]
  let F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E} :=
    fun s => ⟨LinearMap.range s.1, hF s⟩
  have hFb : Function.Bijective F := by
    constructor
    · intro s t h
      have h' : LinearMap.range s.1 = LinearMap.range t.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply LinearMap.ext
      intro e
      have hm : s.1 e ∈ LinearMap.range t.1 := h' ▸ LinearMap.mem_range_self s.1 e
      obtain ⟨e', he'⟩ := LinearMap.mem_range.1 hm
      have h1 := hsec t.1 t.2 e'
      rw [he', hsec s.1 s.2 e] at h1
      have : e' = e := Subtype.ext h1.symm
      rw [← he', this]
    · rintro ⟨D, hnot, hmap⟩
      have hdisj : ∀ x ∈ D, x ∈ C → x = 0 := by
        intro x hxD hxC
        by_contra hx
        apply hnot
        intro y hy
        have hx' : (⟨x, hxC⟩ : C) ≠ 0 := fun h => hx (congrArg Subtype.val h)
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩
        have : a • x = y := congrArg Subtype.val ha
        rw [← this]
        exact D.smul_mem a hxD
      let f : D →ₗ[k] H ⧸ C := C.mkQ ∘ₗ D.subtype
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro d hd
        apply Subtype.ext
        exact hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)
      have hr : LinearMap.range f = E := by
        rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
      let φ : D ≃ₗ[k] E := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
      have hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d := fun d => rfl
      let s : E →ₗ[k] H := D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)
      have hs : C.mkQ ∘ₗ s = E.subtype := by
        apply LinearMap.ext
        intro e
        have h1 := hφ (φ.symm e)
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show LinearMap.range s = D
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]
  let G : (E →ₗ[k] C) → S := fun g =>
    ⟨s0 + C.subtype ∘ₗ g, by
      apply LinearMap.ext
      intro e
      have h1 := LinearMap.congr_fun hs0 e
      have h2 : C.mkQ (g e : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 (g e).2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _), Submodule.subtype_apply] at h1 ⊢
      rw [h2, add_zero, h1]⟩
  have hGb : Function.Bijective G := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      have := LinearMap.congr_fun (congrArg Subtype.val h) e
      simpa [G] using this
    · rintro ⟨s, hs⟩
      have hmem : ∀ e, s e - s0 e ∈ C := by
        intro e
        apply (Submodule.Quotient.mk_eq_zero C).1
        have h1 := hsec s hs e
        have h2 := hsec s0 hs0 e
        simp only [Submodule.mkQ_apply] at h1 h2
        rw [Submodule.Quotient.mk_sub, h1, h2, sub_self]
      refine ⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩
      apply LinearMap.ext
      intro e
      simp [G]
  have hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E := by
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k
    haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C),
      Module.finrank_linearMap k k E C, hC, mul_one]
  rw [← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]

end UpperTheory.Gal.crystallineComparison
end
end
