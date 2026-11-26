module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
open CategoryTheory UpperTheory.V.KH

private theorem group_homology_long_exact (k G : Type) [CommRing k] [Group G] (A B C : Rep k G)
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) (j : ℕ) :
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  have h0 : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact hfg.apply_apply_eq_zero x
  let X : ShortComplex (Rep k G) := ShortComplex.mk f g h0
  have hex : X.Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful X (forget₂ (Rep k G) (ModuleCat k))]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
  have hX : X.ShortExact :=
    ShortComplex.ShortExact.mk' hex ((Rep.mono_iff_injective f).2 hf)
      ((Rep.epi_iff_surjective g).2 hg)
  have h2 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₂_exact hX j)
  have h3 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₃_exact hX (i := j + 1) (j := j) rfl)
  exact ⟨⟨(groupHomology.mapShortComplex₂ X j).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₂ X j).g.hom.toAddMonoidHom, h2⟩,
    ⟨(groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).g.hom.toAddMonoidHom, h3⟩⟩

theorem UpperTheory.V.KH.les :
    ∀ (G : Type) [Group G] (A B C : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ C),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom → ∀ j : ℕ,
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  intro G _ A B C f g hf hfg hg j
  exact group_homology_long_exact ℤ G A B C f g hf hfg hg j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.transport :
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N] (_ : M ≃+ N) (B : ℕ), TorsLe M B → TorsLe N B) ∧
    (∀ (M N : Type) (_ : M ≃ N) (B : ℕ), CardLe M B → CardLe N B) ∧
    (∀ (M : Type) [AddCommGroup M] (B B' : ℕ), B ≤ B' → TorsLe M B → TorsLe M B') ∧
    (∀ (M : Type) (B B' : ℕ), B ≤ B' → CardLe M B → CardLe M B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N _ _ e B h
    obtain ⟨hfin, hcard⟩ := h
    let f : AddCommGroup.torsion M ≃ AddCommGroup.torsion N :=
      (e : M ≃ N).subtypeEquiv fun x => by
        simp only [SetLike.mem_coe, AddCommGroup.mem_torsion, ← addOrderOf_pos_iff]
        simp
    exact ⟨Finite.of_equiv _ f, (Nat.card_congr f).symm ▸ hcard⟩
  · intro M N e B h
    obtain ⟨hfin, hcard⟩ := h
    exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm ▸ hcard⟩
  · intro M _ B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
  · intro M B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImageRep
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.imageRep :
    ∀ (G : Type) [Group G] (C B M : Rep ℤ G) (d : C ⟶ B) (e : B ⟶ M), Function.Exact d.hom e.hom →
      ∃ (K : Rep ℤ G) (p : C ⟶ K) (i : K ⟶ B), Function.Surjective p.hom ∧ Function.Injective i.hom ∧
        (∀ x, i.hom (p.hom x) = d.hom x) ∧ Function.Exact i.hom e.hom := by
  intro G _ C B M d e h
  have hs : Function.Surjective (Abelian.factorThruImage d).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (Abelian.image.ι d).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  have hc : ∀ x, (Abelian.image.ι d).hom ((Abelian.factorThruImage d).hom x) = d.hom x := by
    intro x
    have := congrArg (fun f : C ⟶ B => f.hom x) (Abelian.image.fac d)
    simpa using this
  refine ⟨Abelian.image d, Abelian.factorThruImage d, Abelian.image.ι d, hs, hi, hc, ?_⟩
  intro y
  rw [h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hc x⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (hc x).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.KerOrb
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kerOrb :
    ∀ (G X : Type) [Group G] [MulAction G X],
      LinearMap.ker (Finsupp.lmapDomain ℤ ℤ
        (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X)) =
      Representation.Coinvariants.ker (perm G X) := by
  intro G X _ _
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  set K := Representation.Coinvariants.ker (perm G X) with hK
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply] at hf
    let r : X → X := fun x => Quotient.out (q x)
    have hstep : ∀ f : X →₀ ℤ, f - Finsupp.mapDomain r f ∈ K := by
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [Finsupp.mapDomain_add]
        have := K.add_mem ha hb
        convert this using 1
        abel
      | single x c =>
        rw [Finsupp.mapDomain_single]
        have hx : (MulAction.orbitRel G X) (r x) x := Quotient.mk_out (s := MulAction.orbitRel G X) x
        obtain ⟨g, hg⟩ := hx
        have hg' : g • x = r x := hg
        have hmem := Representation.Coinvariants.mem_ker_of_eq (ρ := perm G X) g
          (Finsupp.single x c) _ rfl
        have hneg := K.neg_mem hmem
        convert hneg using 1
        rw [perm_single, hg']
        abel
    have h0 : Finsupp.mapDomain r f = 0 := by
      have : r = (fun c => Quotient.out c) ∘ q := rfl
      rw [this, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]
    have := hstep f
    rwa [h0, sub_zero] at this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change Finsupp.lmapDomain ℤ ℤ q ((perm G X) g v - v) = 0
    rw [map_sub, perm_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      ← Finsupp.mapDomain_comp]
    have : q ∘ (fun x => g • x) = q := by
      funext x
      exact Quotient.sound ⟨g, rfl⟩
    rw [this, sub_self]
end

open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.quotients_equiv_of_ker_eq {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (a : A →+ B) (b : A →+ C) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (h : a.ker = b.ker) : Nonempty (B ≃+ C) :=
  ⟨(QuotientAddGroup.quotientKerEquivOfSurjective a ha).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq h).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective b hb))⟩

private theorem UpperTheory.V.KH.hZero_push {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M) (x : N)
    (hx : x ∈ Representation.Coinvariants.ker N.ρ) :
    e.hom x ∈ Representation.Coinvariants.ker M.ρ := by
  have := (Representation.Coinvariants.mk_eq_zero N.ρ).2 hx
  rw [← Representation.Coinvariants.mk_eq_zero, ← Representation.Coinvariants.map_mk, this,
    map_zero]

private theorem UpperTheory.V.KH.hZero_lift {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G) (e : N ⟶ M)
    (he : Function.Surjective e.hom) (y : M)
    (hy : y ∈ Representation.Coinvariants.ker M.ρ) :
    ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom x = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hy
    obtain ⟨u, rfl⟩ := he v
    exact ⟨N.ρ g u - u, Representation.Coinvariants.sub_mem_ker g u, by
      rw [map_sub, Rep.hom_comm_apply]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    exact ⟨u + v, Submodule.add_mem _ hu hv, map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    exact ⟨_, Submodule.smul_mem _ c hu, map_smul e.hom c u⟩

private theorem UpperTheory.V.KH.hZero_gen {R G : Type} [CommRing R] [Group G] (N M : Rep.{0} R G)
    (e : N ⟶ M) (he : Function.Surjective e.hom) :
    ∃ a : N →+ groupHomology M 0, Function.Surjective a ∧
      ∀ f, a f = 0 ↔ ∃ x ∈ Representation.Coinvariants.ker N.ρ, e.hom (f - x) = 0 := by
  let ψ : groupHomology M 0 ≃ₗ[R] M.ρ.Coinvariants := (groupHomology.H0Iso M).toLinearEquiv
  let a : N →ₗ[R] groupHomology M 0 :=
    ψ.symm.toLinearMap ∘ₗ Representation.Coinvariants.mk M.ρ ∘ₗ e.hom.toLinearMap
  refine ⟨a.toAddMonoidHom, ψ.symm.surjective.comp
    ((Representation.Coinvariants.mk_surjective M.ρ).comp he), fun f => ?_⟩
  have h1 : a.toAddMonoidHom f = 0 ↔ e.hom f ∈ Representation.Coinvariants.ker M.ρ :=
    ψ.symm.map_eq_zero_iff.trans (Representation.Coinvariants.mk_eq_zero M.ρ)
  rw [h1]
  constructor
  · intro h
    obtain ⟨k, hk, hkf⟩ := hZero_lift N M e he _ h
    exact ⟨k, hk, by rw [map_sub, hkf, sub_self]⟩
  · rintro ⟨x, hx, h⟩
    rw [map_sub, sub_eq_zero] at h
    rw [h]
    exact hZero_push N M e x hx

theorem UpperTheory.V.KH.hZero :
    ∀ (G X : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M) (S : Set (X →₀ ℤ)),
      Function.Surjective e.hom → (∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S) →
      Nonempty (groupHomology M 0 ≃+ ((MulAction.orbitRel.Quotient G X →₀ ℤ) ⧸
        Submodule.span ℤ (Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X) '' S))) := by
  intro G X _ _ M e S he hS
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  let L : (X →₀ ℤ) →ₗ[ℤ] (MulAction.orbitRel.Quotient G X →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ q
  have hL : LinearMap.ker L = Representation.Coinvariants.ker (perm G X) := kerOrb G X
  have hsp : Submodule.span ℤ (Finsupp.mapDomain q '' S) = (Submodule.span ℤ S).map L :=
    (Submodule.map_span L S).symm
  rw [hsp]
  obtain ⟨a, ha, hak⟩ := hZero_gen (permRep G X) M e he
  let a' : (X →₀ ℤ) →+ groupHomology M 0 := a
  have hak' : ∀ f : X →₀ ℤ, a' f = 0 ↔
      ∃ x ∈ LinearMap.ker L, f - x ∈ Submodule.span ℤ S := by
    intro f
    rw [hL]
    simp only [← hS]
    exact hak f
  let b : (X →₀ ℤ) →+ (_ ⧸ (Submodule.span ℤ S).map L) :=
    (((Submodule.span ℤ S).map L).mkQ ∘ₗ L).toAddMonoidHom
  have hb : Function.Surjective b :=
    (Submodule.mkQ_surjective _).comp (Finsupp.mapDomain_surjective Quotient.mk_surjective)
  have hab : a'.ker = b.ker := by
    ext f
    have h2 : f ∈ b.ker ↔ L f ∈ (Submodule.span ℤ S).map L :=
      Submodule.Quotient.mk_eq_zero _
    rw [AddMonoidHom.mem_ker, hak', h2]
    constructor
    · rintro ⟨k, hk, h⟩
      exact ⟨f - k, h, by rw [map_sub, LinearMap.mem_ker.1 hk, sub_zero]⟩
    · rintro ⟨s, hs, hsf⟩
      exact ⟨f - s, by rw [LinearMap.mem_ker, map_sub, hsf, sub_self],
        by rwa [sub_sub_cancel]⟩
  obtain ⟨φ⟩ := quotients_equiv_of_ker_eq a' b ha hb hab
  exact ⟨φ⟩
end
