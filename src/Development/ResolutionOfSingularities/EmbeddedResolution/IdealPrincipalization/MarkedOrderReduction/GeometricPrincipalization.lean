module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentsInSupport
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_basicOpen_iff_notMem_asIdeal_primeIdealOf {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {x : ↥X} (hx : x ∈ V) (f : Γ(X, V)) :
    x ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : (hV.primeIdealOf ⟨x, hx⟩) ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [h1]
  rw [← h2, hV.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen f _

private theorem mem_support_iff_ideal_le_asIdeal_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hx, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    by_contra hfP
    exact h f hf ((mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f).mpr hfP)
  · intro h f hf hb
    exact (mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f).mp hb (h (SetLike.mem_coe.mp hf))

private theorem mem_of_mul_pow_mem {R : Type u} [CommRing R] (I : Ideal R) (g : R)
    (hnzd : ∀ x : R, g * x ∈ I → x ∈ I) :
    ∀ (n : ℕ) (u : R), u * g ^ n ∈ I → u ∈ I := by
  intro n
  induction n with
  | zero =>
      intro u h
      simpa using h
  | succ n ih =>
      intro u h
      refine ih u (hnzd _ ?_)
      have e : g * (u * g ^ n) = u * g ^ (n + 1) := by ring
      rw [e]
      exact h

private theorem exists_isPrime_between_notMem_of_mul_mem {R : Type u} [CommRing R] (I : Ideal R) (g : R)
    (hnzd : ∀ x : R, g * x ∈ I → x ∈ I)
    (P : Ideal R) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q : Ideal R, Q.IsPrime ∧ I ≤ Q ∧ Q ≤ P ∧ g ∉ Q := by
  classical
  have h1P : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  let M : Submonoid R :=
    { carrier := {x : R | ∃ (u : R) (n : ℕ), u ∉ P ∧ x = u * g ^ n}
      mul_mem' := by
        rintro x y ⟨u, n, hu, rfl⟩ ⟨v, l, hv, rfl⟩
        refine ⟨u * v, n + l, ?_, by ring⟩
        intro h
        rcases hP.mem_or_mem h with h' | h'
        · exact hu h'
        · exact hv h'
      one_mem' := ⟨1, 0, h1P, by ring⟩ }
  have hdisj : Disjoint (I : Set R) (M : Set R) := by
    rw [Set.disjoint_left]
    rintro x hxI ⟨u, n, hu, rfl⟩
    exact hu (hIP (mem_of_mul_pow_mem I g hnzd n u hxI))
  obtain ⟨Q, hQ, hIQ, hQdisj⟩ := Ideal.exists_le_prime_disjoint I M hdisj
  refine ⟨Q, hQ, hIQ, ?_, ?_⟩
  · intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hQdisj hx ⟨x, 0, hxP, by ring⟩
  · intro hg
    exact Set.disjoint_left.mp hQdisj hg ⟨1, 1, h1P, by ring⟩

private theorem mem_map_of_mul_mem_of_etale_of_isSMulRegular {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hy : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hsm : ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = (0 : A ⧸ Ideal.map f I) := by
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    exact hy
  have hreg0 : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := fun a b h => hw a b h
  have hreg : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg0.of_flat
  have hzero : (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    refine hreg ?_
    show ((Ideal.Quotient.mk I) w) • ((Ideal.Quotient.mk (Ideal.map f I)) x)
      = ((Ideal.Quotient.mk I) w) • (0 : A ⧸ Ideal.map f I)
    rw [smul_zero]
    exact hsm
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

private theorem mem_mvPolynomialCoordIdeal_of_X_mul_mem (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) {s : Fin m} (hs : s ∉ S) (r : MvPolynomial (ULift.{u} (Fin m)) k)
    (h : MvPolynomial.X (ULift.up.{u} s) * r ∈ mvPolynomialCoordIdeal k m S) :
    r ∈ mvPolynomialCoordIdeal k m S := by
  classical
  obtain ⟨ψ, hψC, hψX⟩ :
      ∃ ψ : MvPolynomial (ULift.{u} (Fin m)) k →+* MvPolynomial (ULift.{u} (Fin m)) k,
        (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        (∀ j : Fin m, ψ (MvPolynomial.X (ULift.up.{u} j))
          = if j ∈ S then 0 else MvPolynomial.X (ULift.up.{u} j)) := by
    refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : ULift.{u} (Fin m) =>
        if i.down ∈ S then (0 : MvPolynomial (ULift.{u} (Fin m)) k)
        else MvPolynomial.X i), ?_, ?_⟩
    · intro a
      simp
    · intro j
      simp
  have hker : mvPolynomialCoordIdeal k m S ≤ RingHom.ker ψ := by
    rw [mvPolynomialCoordIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hz : ψ (MvPolynomial.X (ULift.up.{u} j)) = 0 := by
      rw [hψX j]
      exact if_pos (Finset.mem_coe.mp hj)
    exact SetLike.mem_coe.mpr (RingHom.mem_ker.mpr hz)
  have key : (Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp ψ
      = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      obtain ⟨j⟩ := i
      rw [RingHom.comp_apply, hψX j]
      by_cases hi : j ∈ S
      · rw [if_pos hi, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (X_mem_mvPolynomialCoordIdeal k m S hi)).symm
      · rw [if_neg hi]
  have h0 : ψ (MvPolynomial.X (ULift.up.{u} s) * r) = 0 :=
    RingHom.mem_ker.mp (hker h)
  rw [map_mul, hψX s, if_neg hs] at h0
  have hXne : (MvPolynomial.X (ULift.up.{u} s) : MvPolynomial (ULift.{u} (Fin m)) k) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hXne
    · exact h1
  have hfin := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfin.symm

private theorem false_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart p V m) (Z D : X.IdealSheafData) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∉ S) (hZ : restrictIdeal Z V = c.coordIdeal S)
    (hD : restrictIdeal D V = c.coordIdeal {s})
    (ξ : ↥X) (hξV : ξ ∈ V) (hξZ : ξ ∈ Z.support) (_hξD : ξ ∈ D.support)
    (hmin : ∀ η : ↥X, η ∈ Z.support → ξ ∈ closure ({η} : Set ↥X) → η ∈ D.support) : False := by
  classical
  have hIZ : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV Z S hZ
  have hID : Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m {s}) = D.ideal ⟨V, hV⟩ :=
    c.map_mvPolynomialCoordIdeal_eq_ideal hV D {s} hD
  have hDspan : D.ideal ⟨V, hV⟩ = Ideal.span {c.coord s} := by
    rw [← hID, mvPolynomialCoordIdeal_eq_span, Finset.coe_singleton, Set.image_singleton, Ideal.map_span,
      Set.image_singleton, c.coordRingHom_X]
  have hnzd : ∀ x : Γ(X, V), c.coord s * x ∈ Z.ideal ⟨V, hV⟩ → x ∈ Z.ideal ⟨V, hV⟩ := by
    intro x hx
    rw [← hIZ] at hx ⊢
    refine mem_map_of_mul_mem_of_etale_of_isSMulRegular (c.coordRingHom_etale hV) (mvPolynomialCoordIdeal k m S)
      (MvPolynomial.X (ULift.up.{u} s)) ?_ x ?_
    · intro A B hAB
      obtain ⟨A', rfl⟩ := Ideal.Quotient.mk_surjective A
      obtain ⟨B', rfl⟩ := Ideal.Quotient.mk_surjective B
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hAB
      exact Ideal.Quotient.eq.mpr (mem_mvPolynomialCoordIdeal_of_X_mul_mem k m S hs (A' - B') hAB)
    · rw [c.coordRingHom_X]
      exact hx
  have hIP : Z.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal :=
    (mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hξV).mp hξZ
  obtain ⟨Q, hQp, hIQ, hQP, hgQ⟩ :=
    exists_isPrime_between_notMem_of_mul_mem (Z.ideal ⟨V, hV⟩) (c.coord s) hnzd
      (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal (hV.primeIdealOf ⟨ξ, hξV⟩).isPrime hIP
  obtain ⟨q, hqQ⟩ : ∃ q : PrimeSpectrum Γ(X, V), q.asIdeal = Q := ⟨⟨Q, hQp⟩, rfl⟩
  have hrange : hV.fromSpec.base q ∈ V := by
    have h0 : hV.fromSpec.base q ∈ Set.range ⇑hV.fromSpec.base := ⟨q, rfl⟩
    rw [hV.range_fromSpec] at h0
    exact h0
  have hQeq : hV.primeIdealOf ⟨hV.fromSpec.base q, hrange⟩ = q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
  have hηZ : hV.fromSpec.base q ∈ Z.support := by
    rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hrange, hQeq, hqQ]
    exact hIQ
  have hspec : ξ ∈ closure ({hV.fromSpec.base q} : Set ↥X) := by
    have hle : q.asIdeal ≤ (hV.primeIdealOf ⟨ξ, hξV⟩).asIdeal := by
      rw [hqQ]
      exact hQP
    have h1 : q ⤳ hV.primeIdealOf ⟨ξ, hξV⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map hV.fromSpec.base.hom.continuous
    rw [hV.fromSpec_primeIdealOf] at h2
    exact specializes_iff_mem_closure.mp h2
  have hηD := hmin _ hηZ hspec
  rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf D hV hrange, hQeq, hDspan, hqQ] at hηD
  exact hgQ (hηD (Ideal.mem_span_singleton_self _))

private theorem not_subset_boundary_support_of_notMem (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) (hi : i ∉ J)
    (hsub : C ⊆ ((T.boundary.get i).support : Set ↥T.scheme)) : False := by
  classical
  obtain ⟨hirr, hCsub, hmax⟩ := hC
  have hirr' : IsIrreducible C := hirr
  have hclosed : IsClosed C :=
    isClosed_of_maximal_irreducible_subset_support (intersectionIdeal T.boundary J) hirr' hCsub hmax
  have hgen : closure ({hirr'.genericPoint} : Set ↥T.scheme) = C := by
    have h : closure ({hirr'.genericPoint} : Set ↥T.scheme) = closure C :=
      hirr'.genericPoint_closure_eq
    rw [h, hclosed.closure_eq]
  have hxiC : hirr'.genericPoint ∈ C := IsGenericPoint.mem hgen
  have hxiZ : hirr'.genericPoint ∈ (intersectionIdeal T.boundary J).support := hCsub hxiC
  have hxiD : hirr'.genericPoint ∈ (T.boundary.get i).support := hsub hxiC
  obtain ⟨U, hxiU, m, c, a, hinj, hnone, hsome⟩ := hT.snc.2 hirr'.genericPoint
  obtain ⟨V, hVaff, hxiV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxiU
  have hV : IsAffineOpen V := hVaff
  let cV : EtaleChart T.structMap V m := {
    map := T.scheme.homOfLE hVU ≫ c.map
    comp_struct := by simp [Category.assoc, c.comp_struct]
    isEtale := by
      letI := c.isEtale
      infer_instance }
  have hrestrict (Z : T.scheme.IdealSheafData) (S : Finset (Fin m))
      (h : restrictIdeal Z U = c.coordIdeal S) :
      restrictIdeal Z V = cV.coordIdeal S := by
    have h' : Z.comap U.ι = (coordSubspaceIdeal T.base m S).comap c.map := by
      rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    change Z.comap ((show T.scheme.Opens from V).ι) = (coordSubspaceIdeal _ m S).comap (T.scheme.homOfLE hVU ≫ c.map)
    rw [Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
      Scheme.homOfLE_ι]
  have key : ∀ j : Fin T.boundary.length, hirr'.genericPoint ∈ (T.boundary.get j).support →
      ∃ t : Fin m, a (j : ℕ) = some t ∧
        restrictIdeal (T.boundary.get j) V = cV.coordIdeal {t} := by
    intro j hj
    cases hA : a (j : ℕ) with
    | none =>
        exfalso
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = ⊤ := hnone (j : ℕ) j.isLt hA
        have h2 : restrictIdeal (T.boundary.get j) U = ⊤ := by
          rw [List.get_eq_getElem]
          exact h1
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top (T.boundary.get j) U h2
          hirr'.genericPoint hxiU hj
    | some t =>
        refine ⟨t, rfl, ?_⟩
        have h1 : restrictIdeal (T.boundary[(j : ℕ)]'j.isLt) U = c.coordIdeal {t} :=
          hsome (j : ℕ) j.isLt t hA
        have h2 : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
          rw [List.get_eq_getElem]
          exact h1
        exact hrestrict (T.boundary.get j) {t} h2
  have hmemJ : ∀ j ∈ J, hirr'.genericPoint ∈ (T.boundary.get j).support := by
    intro j hj
    refine Scheme.IdealSheafData.support_antitone ?_ hxiZ
    rw [intersectionIdeal_eq_iSup]
    exact le_biSup T.boundary.get hj
  obtain ⟨si, hsi, hDi⟩ := key i hxiD
  obtain ⟨S, hmemS⟩ :
      ∃ S : Finset (Fin m), ∀ t : Fin m, t ∈ S ↔ ∃ j ∈ J, a (j : ℕ) = some t :=
    ⟨Finset.univ.filter (fun t : Fin m => ∃ j ∈ J, a (j : ℕ) = some t), by
      intro t
      simp⟩
  have hsiS : si ∉ S := by
    intro hmem
    obtain ⟨j, hj, haj⟩ := (hmemS si).mp hmem
    have hval : (i : ℕ) = (j : ℕ) := hinj (i : ℕ) i.isLt (j : ℕ) j.isLt si hsi haj
    have hij : i = j := Fin.eq_of_val_eq hval
    exact hi (by rw [hij]; exact hj)
  have hZV : restrictIdeal (intersectionIdeal T.boundary J) V = cV.coordIdeal S := by
    have hbi : restrictIdeal (intersectionIdeal T.boundary J) V
        = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) V := by
      rw [intersectionIdeal_eq_iSup]
      exact MonomialChart.restrictIdeal_biSup_finset V T.boundary.get J
    have hcb : cV.coordIdeal S = ⨆ t ∈ S, cV.coordIdeal {t} :=
      MonomialChart.coordIdeal_eq_biSup_singleton T.structMap V m cV S
    rw [hbi, hcb]
    refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun t ht => ?_)
    · obtain ⟨t, hat, hres⟩ := key j (hmemJ j hj)
      rw [hres]
      exact le_biSup (fun t : Fin m => cV.coordIdeal {t})
        ((hmemS t).mpr ⟨j, hj, hat⟩)
    · obtain ⟨j, hj, hat⟩ := (hmemS t).mp ht
      obtain ⟨t', hat', hres⟩ := key j (hmemJ j hj)
      have htt : t = t' := Option.some.inj (hat.symm.trans hat')
      rw [htt, ← hres]
      exact le_biSup (fun j : Fin T.boundary.length => restrictIdeal (T.boundary.get j) V) hj
  refine false_of_restrictIdeal_eq_coordIdeal hV cV (intersectionIdeal T.boundary J) (T.boundary.get i)
    S si hsiS hZV hDi hirr'.genericPoint hxiV hxiZ hxiD ?_
  intro η hηZ hηxi
  have hirr2 : IsIrreducible (closure ({η} : Set ↥T.scheme)) := isIrreducible_singleton.closure
  have hs1 : C ⊆ closure ({η} : Set ↥T.scheme) := by
    rw [← hgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηxi) isClosed_closure
  have hs2 : closure ({η} : Set ↥T.scheme)
      ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hηZ)
      (intersectionIdeal T.boundary J).support.2
  have heq : closure ({η} : Set ↥T.scheme) = C := hmax _ hirr2 hs1 hs2
  have hηC : η ∈ C := by
    rw [← heq]
    exact subset_closure (Set.mem_singleton η)
  exact hsub hηC

theorem intersectionComponents_subset_support_iff : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ C ∈ intersectionComponents T.boundary J,
        ∀ (i : Fin T.boundary.length),
          C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J := by
  intro T hT J C hC i
  constructor
  · intro hsub
    by_contra hi
    exact not_subset_boundary_support_of_notMem T hT J C hC i hi hsub
  · intro hi x hx
    have hle : T.boundary.get i ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_biSup T.boundary.get hi
    exact Scheme.IdealSheafData.support_antitone hle (hC.2.1 hx)

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentCodimension
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

private theorem nontrivial_sections_of_mem (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have := hs
  have h1 : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Subsingleton.elim (1 : Γ(X, U)) 0]
    exact Ideal.zero_mem _
  exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem ideal_le_primeIdealOf_of_mem_support (I : X.IdealSheafData)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxI : x ∈ I.support) :
    I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx).mp hxI
  rw [Scheme.mem_zeroLocus_iff] at h1
  intro f hf
  rw [← germ_mem_maximalIdeal_iff hU x hx f, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact h1 f hf ((X.mem_basicOpen f x hx).mpr hu)

private theorem coord_injective (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) : Function.Injective c.coord := by
  let inst : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra_etale hU
  have : Nontrivial Γ(X, U) := nontrivial_sections_of_mem hU x hx
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := inferInstance
  have := Module.Flat.isTorsionFree (R := MvPolynomial (ULift.{u} (Fin m)) k) (M := Γ(X, U))
  have hinj0 : Function.Injective
      (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective ⇑c.coordRingHom := hinj0
  intro a b hab
  have h1 : (MvPolynomial.X (ULift.up a) : MvPolynomial (ULift.{u} (Fin m)) k)
      = MvPolynomial.X (ULift.up b) := by
    apply hinj
    rw [EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X, hab]
  have h2 : (ULift.up a : ULift.{u} (Fin m)) = ULift.up b := MvPolynomial.X_injective h1
  exact congrArg ULift.down h2

theorem card_le_ringKrullDim_stalk (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ j hj))
  rw [← hd]
  rcases Finset.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Finset.card_empty]
    exact_mod_cast Nat.zero_le d
  · obtain ⟨j₀, hj₀⟩ := hJne
    obtain ⟨i₀, -⟩ := hf2 j₀ hj₀
    have hch : ∀ j : Fin m, ∃ i : Fin d, j ∈ J → f i = c.coord j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨i, hi⟩ := hf2 j hj
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hj⟩
    choose g hg using hch
    have hmap : ∀ a ∈ J, g a ∈ (Finset.univ : Finset (Fin d)) := fun a _ => Finset.mem_univ _
    have hinjOn : Set.InjOn g (J : Set (Fin m)) := by
      intro a ha b hb hab
      have h1 : c.coord a = c.coord b := by
        rw [← hg a (Finset.mem_coe.mp ha), ← hg b (Finset.mem_coe.mp hb), hab]
      exact coord_injective hU c x hx h1
    have hcard : J.card ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card_of_injOn g hmap hinjOn
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact_mod_cast hcard

theorem coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ U) (hxD : x ∈ D.support) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) :=
    EtaleChart.ideal_eq_span_coord c hU D {j} hD
  have h2 : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf_of_mem_support D hU hx hxD
  refine h2 ?_
  rw [h1]
  exact Ideal.subset_span ⟨j, by simp, rfl⟩

end FunctorialResolution.EmbeddedResolution
end
end

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  let d : EtaleChart T.structMap V m := {
    map := T.scheme.homOfLE hVU ≫ c.map
    comp_struct := by rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]
    isEtale := by
      have := c.isEtale
      infer_instance }
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      d.coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' : restrictIdeal T.boundary[p.1.val] V = d.coordIdeal {t} := by
      have h' : T.boundary[p.1.val].comap U.ι =
          (coordSubspaceIdeal _ m {t}).comap c.map := by
        rw [← restrictIdeal_eq_comap_ι, hU', EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      change _ = (coordSubspaceIdeal _ m {t}).comap (T.scheme.homOfLE hVU ≫ c.map)
      rw [Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      d t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV d x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialCenterHypotheses
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenterCase

structure MonomialCenterHypotheses : Prop where
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            AlgebraicGeometry.Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ x' : ↥X',
                  ∃ (U' : X'.Opens) (ε : ℕ),
                    x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                        (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)
                          ⊆ (D.support : Set ↥T.scheme)) ∧
                      (D.comap π).comap U'.ι =
                        (Blowup.strictTransform π Z D).comap U'.ι *
                          (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ i : Fin T.boundary.length,
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ

theorem monomialCaseHypotheses_of_monomialCenterHypotheses (h : MonomialCenterHypotheses.{u}) :
    MonomialCaseHypotheses.{u} := by
  exact {
    card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
    center_smooth := h.center_smooth
    center_snc := h.center_snc
    blowup_total_transform := h.blowup_total_transform
    components_subset_divisor_iff := h.components_subset_divisor_iff
    transformed_components := h.transformed_components
    stratum_smooth := MonomialChart.smooth_intersectionIdeal_subscheme
    orderAt_comap_off_exceptional := fun T hT X' π Z hπ x' hx' A =>
      orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A
    orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one }

end MonomialCenterCase

namespace StrictTransformCase

structure StrictTransformHypotheses : Prop extends MonomialCenterCase.MonomialCenterHypotheses.{u} where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_residualHypotheses (h : StrictTransformHypotheses.{u}) :
    StrictTransformAndMonomialCaseHypotheses.{u} := by
  exact {
    strictTransform_components := h.strictTransform_components
    monomial := MonomialCenterCase.monomialCaseHypotheses_of_monomialCenterHypotheses
      h.toMonomialCenterHypotheses }

end StrictTransformCase

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.TransformedComponentHypotheses
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialStrictTransformComponents

structure TransformedComponentHypotheses : Prop where
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_transformedComponents (h : TransformedComponentHypotheses.{u}) :
    StrictTransformCase.StrictTransformHypotheses.{u} := by
  exact {
    toMonomialCenterHypotheses := {
      center_smooth := MonomialCenterGeometry.smooth_componentUnionIdeal
      center_snc := MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal
      blowup_total_transform := comap_eq_strictTransform_mul_exceptionalIdeal_pow
      components_subset_divisor_iff := intersectionComponents_subset_support_iff
      transformed_components := h.transformed_components }
    strictTransform_components := h.strictTransform_components }

end MonomialStrictTransformComponents

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem MonomialStrictTransformComponents.transformedComponentHypotheses :
    MonomialStrictTransformComponents.TransformedComponentHypotheses.{u} := by
  exact {
    transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
    strictTransform_components := exists_eq_closure_of_isIrreducibleComponentOf_strictTransform }

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses.{u} := by
  have h := StrictTransformCase.strictTransformHypotheses_of_residualHypotheses
    (MonomialStrictTransformComponents.strictTransformHypotheses_of_transformedComponents
      MonomialStrictTransformComponents.transformedComponentHypotheses)
  have hOrder : OrderReductionHypotheses.{u} := {
    controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
    strictTransform_components := h.strictTransform_components
    monomial := h.monomial }
  exact geometricHypotheses_of_orderReductionHypotheses hOrder

end FunctorialResolution.EmbeddedResolution

end
