module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdComp
open Polynomial Matrix

private theorem comp_image {G : Type} [TopologicalSpace G] (e : G ≃ₜ G) {Z : Set G}
    (hZ : Z ∈ irreducibleComponents G) : e '' Z ∈ irreducibleComponents G := by
  refine ⟨hZ.1.image e e.continuous.continuousOn, fun y hy hsub => ?_⟩
  have h1 : Z ⊆ e.symm '' y := by
    intro z hz
    exact ⟨e z, hsub ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
  have h2 := hZ.2 (hy.image e.symm e.symm.continuous.continuousOn) h1
  intro w hw
  exact ⟨e.symm w, h2 ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩

private theorem exists_unique_pt {G : Type} [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G]
    (a : G) : ∃ x : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      x ∈ Z → x ∈ W → Z = W := by
  classical
  obtain ⟨Z, hZ, haZ⟩ : ∃ Z ∈ irreducibleComponents G, a ∈ Z :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent⟩
  have hfin : (irreducibleComponents G \ {Z}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff
  have hnot : ¬ Z ⊆ ⋃₀ (irreducibleComponents G \ {Z}) := by
    intro hsub
    obtain ⟨W, hW, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1) hfin.toFinset
      (fun W hW => isClosed_of_mem_irreducibleComponents W (hfin.mem_toFinset.1 hW).1)
      (by simpa using hsub)
    rw [hfin.mem_toFinset] at hW
    exact hW.2 (Set.mem_singleton_iff.2 (le_antisymm (hZ.2 hW.1.1 hZW) hZW))
  obtain ⟨x, hxZ, hxn⟩ := Set.not_subset.1 hnot
  have key : ∀ Y ∈ irreducibleComponents G, x ∈ Y → Y = Z := by
    intro Y hY hxY
    by_contra hne
    exact hxn ⟨Y, ⟨hY, hne⟩, hxY⟩
  refine ⟨x, fun Z' hZ' W' hW' hx1 hx2 => ?_⟩
  rw [key Z' hZ' hx1, key W' hW' hx2]

theorem UpperTheory.V.AlgebraTools.idComp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G],
      (∀ g : G, Continuous (fun x => g * x)) → (∀ g : G, Continuous (fun x => x * g)) →
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ IsClosed (N : Set G) ∧ IsIrreducible (N : Set G) ∧
        ∀ U : Subgroup G, U.FiniteIndex → (N : Set G) ⊆ closure ((U ⊓ N : Subgroup G) : Set G) := by
  intro G _ _ _ hL hR
  classical
  let hl : G → G ≃ₜ G := fun g =>
    { toFun := fun x => g * x, invFun := fun x => g⁻¹ * x,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hL g, continuous_invFun := hL g⁻¹ }
  let hr : G → G ≃ₜ G := fun g =>
    { toFun := fun x => x * g, invFun := fun x => x * g⁻¹,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hR g, continuous_invFun := hR g⁻¹ }
  obtain ⟨x, hx⟩ := exists_unique_pt (1 : G)
  have uniq : ∀ y : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      y ∈ Z → y ∈ W → Z = W := by
    intro y Z hZ W hW hyZ hyW
    have hxy : (hl (x * y⁻¹)) y = x := by
      show x * y⁻¹ * y = x
      simp
    have h := hx _ (comp_image (hl (x * y⁻¹)) hZ) _ (comp_image (hl (x * y⁻¹)) hW)
      ⟨y, hyZ, hxy⟩ ⟨y, hyW, hxy⟩
    exact Set.image_injective.2 (hl (x * y⁻¹)).injective h
  obtain ⟨C, hC, h1C⟩ : ∃ C ∈ irreducibleComponents G, (1 : G) ∈ C :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents 1, mem_irreducibleComponent⟩
  let N : Subgroup G :=
    { carrier := C
      one_mem' := h1C
      mul_mem' := fun {a b} ha hb => by
        have e1 : (hl a) '' C = C := uniq a _ (comp_image (hl a) hC) _ hC
          ⟨1, h1C, by show a * 1 = a; simp⟩ ha
        have h2 : a * b ∈ (hl a) '' C := ⟨b, hb, rfl⟩
        rwa [e1] at h2
      inv_mem' := fun {a} ha => by
        have e1 : (hl a⁻¹) '' C = C := uniq 1 _ (comp_image (hl a⁻¹) hC) _ hC
          ⟨a, ha, by show a⁻¹ * a = 1; simp⟩ h1C
        have h2 : a⁻¹ ∈ (hl a⁻¹) '' C := ⟨1, h1C, by show a⁻¹ * 1 = a⁻¹; simp⟩
        rwa [e1] at h2 }
  have hNC : ∀ y, y ∈ N ↔ y ∈ C := fun y => Iff.rfl
  have hfinQ : Finite (G ⧸ N) := by
    let F : G ⧸ N → irreducibleComponents G :=
      Quotient.lift (fun g => (⟨(hl g) '' C, comp_image (hl g) hC⟩ : irreducibleComponents G))
        (by
          intro a b hab
          have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
          apply Subtype.ext
          exact uniq b _ (comp_image (hl a) hC) _ (comp_image (hl b) hC)
            ⟨a⁻¹ * b, hab', by show a * (a⁻¹ * b) = b; simp⟩ ⟨1, h1C, by show b * 1 = b; simp⟩)
    have hFinj : Function.Injective F := by
      intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h := congrArg Subtype.val hpq
      change (hl a) '' C = (hl b) '' C at h
      have hb : b ∈ (hl a) '' C := by
        rw [h]
        exact ⟨1, h1C, by show b * 1 = b; simp⟩
      obtain ⟨c, hc, hcb⟩ := hb
      change a * c = b at hcb
      apply QuotientGroup.eq.2
      rw [← hcb, inv_mul_cancel_left]
      exact hc
    haveI : Finite (irreducibleComponents G) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Finite.of_injective F hFinj
  refine ⟨N, ⟨fun n hn g => ?_⟩, Subgroup.finiteIndex_of_finite_quotient,
    isClosed_of_mem_irreducibleComponents C hC, hC.1, fun U hU => ?_⟩
  · have e1 : ((hl g).trans (hr g⁻¹)) '' C = C := uniq 1 _ (comp_image _ hC) _ hC
      ⟨1, h1C, by show g * 1 * g⁻¹ = 1; simp⟩ h1C
    have h2 : g * n * g⁻¹ ∈ ((hl g).trans (hr g⁻¹)) '' C := ⟨n, hn, rfl⟩
    rw [e1] at h2
    exact h2
  · haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    haveI := Fintype.ofFinite (G ⧸ U)
    let S : G ⧸ U → Set G := fun q => {y | y ∈ C ∧ (y : G ⧸ U) = q}
    obtain ⟨z, hz, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1)
      (Finset.univ.image fun q => closure (S q)) (by simp [isClosed_closure]) (by
        intro y hy
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range,
          Set.mem_iUnion]
        exact ⟨(y : G ⧸ U), subset_closure ⟨hy, rfl⟩⟩)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨n, hnC, hnq⟩ : (S q).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, closure_empty] at hCz
      exact hCz h1C
    have hSsub : S q ⊆ (hl n) '' ((U ⊓ N : Subgroup G) : Set G) := by
      rintro y ⟨hyC, hyq⟩
      refine ⟨n⁻¹ * y, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by show n * (n⁻¹ * y) = y; simp⟩
      · exact QuotientGroup.eq.1 (hnq.trans hyq.symm)
      · exact N.mul_mem (N.inv_mem hnC) hyC
    intro y hy
    have h3 : n * y ∈ closure ((hl n) '' ((U ⊓ N : Subgroup G) : Set G)) :=
      closure_mono hSsub (hCz (N.mul_mem hnC hy))
    rw [← Homeomorph.image_closure] at h3
    obtain ⟨k, hk, hky⟩ := h3
    change n * k = n * y at hky
    rwa [mul_left_cancel hky] at hk
end

open Polynomial Matrix

private noncomputable def UpperTheory.V.AlgebraTools.icmPt {K ι : Type} [Field K] (A : Matrix ι ι K) :
    PrimeSpectrum (MvPolynomial (ι × ι) K) :=
  ⟨RingHom.ker (MvPolynomial.eval (fun p : ι × ι => A p.1 p.2)), RingHom.ker_isPrime _⟩

private theorem UpperTheory.V.AlgebraTools.icmPt_left {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (A * B) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (A * B) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

private theorem UpperTheory.V.AlgebraTools.icmPt_right {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (B * A) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (B * A) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

theorem UpperTheory.V.AlgebraTools.idCompMat :
    ∀ (K G ι : Type) [Field K] [Group G] [Fintype ι] [DecidableEq ι] (r : G →* Matrix ι ι K),
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧
        (∃ I : Set (MvPolynomial (ι × ι) K), ∀ g, g ∈ N ↔ ∀ f ∈ I, MvPolynomial.eval (fun p => r g p.1 p.2) f = 0) ∧
        ∀ (U : Subgroup G), U.FiniteIndex → ∀ (σ : G) (s : Finset (MvPolynomial (ι × ι) K)),
          (∀ f ∈ s, ∃ g ∈ N, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0) →
          ∃ g ∈ U ⊓ N, ∀ f ∈ s, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0 := by
  classical
  intro K G ι _ _ _ _ r
  let f : G → PrimeSpectrum (MvPolynomial (ι × ι) K) := fun g => UpperTheory.V.AlgebraTools.icmPt (r g)
  letI tG : TopologicalSpace G := TopologicalSpace.induced f inferInstance
  have hind : Topology.IsInducing f := ⟨rfl⟩
  haveI : TopologicalSpace.NoetherianSpace G := hind.noetherianSpace
  have hf : Continuous f := continuous_induced_dom
  have hL : ∀ g : G, Continuous fun x => g * x := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_left (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => g * x) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  have hR : ∀ g : G, Continuous fun x => x * g := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_right (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => x * g) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  obtain ⟨N, hNn, hNf, hNc, hNi, hNd⟩ := UpperTheory.V.AlgebraTools.idComp G hL hR
  have hmemZ : ∀ (S : Set (MvPolynomial (ι × ι) K)) (g : G),
      f g ∈ PrimeSpectrum.zeroLocus S ↔ ∀ q ∈ S, MvPolynomial.eval (fun p => r g p.1 p.2) q = 0 := by
    intro S g
    rw [PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro h q hq
      exact (RingHom.mem_ker).1 (h hq)
    · intro h q hq
      exact (RingHom.mem_ker).2 (h q hq)
  refine ⟨N, hNn, hNf, ?_, ?_⟩
  · obtain ⟨t, ht, hNt⟩ := isClosed_induced_iff.1 hNc
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
    refine ⟨S, fun g => ?_⟩
    rw [← hmemZ S g]
    constructor
    · intro hg
      have h' : g ∈ (N : Set G) := hg
      rw [← hNt] at h'
      exact h'
    · intro hg
      have h' : g ∈ f ⁻¹' PrimeSpectrum.zeroLocus S := hg
      rw [hNt] at h'
      exact h'
  · intro U hU σ s hs
    let W : MvPolynomial (ι × ι) K → Set G :=
      fun q => {g | MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) q ≠ 0}
    have hWo : ∀ q, IsOpen (W q) := by
      intro q
      have h1 : IsOpen (f ⁻¹' (PrimeSpectrum.basicOpen q : Set _)) :=
        (PrimeSpectrum.isOpen_basicOpen).preimage hf
      have h2 := h1.preimage (hL σ)
      convert h2 using 1
      ext g
      simp only [W, Set.mem_setOf_eq, Set.mem_preimage, f, SetLike.mem_coe,
        PrimeSpectrum.mem_basicOpen]
      show _ ↔ q ∉ RingHom.ker _
      rw [RingHom.mem_ker]
    obtain ⟨x, hxN, hxO⟩ := (isIrreducible_iff_sInter.1 hNi) (s.image W)
      (by
        intro u hu
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
        exact hWo q)
      (by
        intro u hu
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨g, hgN, hg⟩ := hs q hq
        exact ⟨g, hgN, hg⟩)
    have hOo : IsOpen (⋂₀ (↑(s.image W) : Set (Set G))) := by
      apply Set.Finite.isOpen_sInter (Finset.finite_toSet _)
      intro u hu
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      exact hWo q
    obtain ⟨g, hgO, hgUN⟩ := mem_closure_iff.1 (hNd U hU hxN) _ hOo hxO
    refine ⟨g, hgUN, fun q hq => ?_⟩
    have : g ∈ W q := hgO _ (Finset.mem_image_of_mem W hq)
    exact this
