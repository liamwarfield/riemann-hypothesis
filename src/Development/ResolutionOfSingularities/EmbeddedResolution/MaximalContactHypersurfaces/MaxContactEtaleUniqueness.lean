module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianChartChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsChartNormalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.EtaleMaxContactComparison
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactChartUniqueness

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCommonCharts
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] [AlgebraicGeometry.Smooth p]

private theorem presheaf_map_mem_ideal_of_mem (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (D : X.IdealSheafData)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {y : Γ(X, U)} (hy : y ∈ D.ideal ⟨U, hU⟩) :
    (X.presheaf.map (homOfLE h).op).hom y ∈ D.ideal ⟨V, hV⟩ := by
  have hcomap : D.ideal ⟨U, hU⟩
      ≤ (D.ideal ⟨V, hV⟩).comap (X.presheaf.map (homOfLE h).op).hom :=
    D.ideal_le_comap_ideal h
  exact hcomap hy

private theorem ideal_le_of_ideal_le_of_le (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (D E : X.IdealSheafData)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (hDleE : D.ideal ⟨U, hU⟩ ≤ E.ideal ⟨U, hU⟩) : D.ideal ⟨V, hV⟩ ≤ E.ideal ⟨V, hV⟩ := by
  let _ : Algebra k Γ(X, U) := sectionsAlgebra k p U
  have : IsNoetherianRing Γ(X, U) :=
    isNoetherianRing_sections k p ⟨U, hU⟩ (algebraMap_sectionsAlgebra k p U)
  obtain ⟨s, hs⟩ : (D.ideal ⟨U, hU⟩).FG := IsNoetherian.noetherian _
  have hs' : Ideal.span (↑s : Set Γ(X, U)) = D.ideal ⟨U, hU⟩ := hs
  have hspan : D.ideal ⟨V, hV⟩
      = Ideal.span ((X.presheaf.map (homOfLE h).op).hom '' (↑s : Set Γ(X, U))) :=
    ideal_eq_span_image_map_of_le D hU hV h (↑s : Set Γ(X, U)) hs'.symm
  rw [hspan, Ideal.span_le]
  rintro _ ⟨y, hy, rfl⟩
  have hyD : y ∈ D.ideal ⟨U, hU⟩ := by
    rw [← hs']
    exact Ideal.subset_span hy
  exact presheaf_map_mem_ideal_of_mem k p E hU hV h (hDleE hyD)

private theorem restrictIdeal_eq_coordIdeal_of_coord_eq {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c c' : EtaleChart p V n) (j : Fin n) (hcoord : c'.coord j = c.coord j)
    (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal {j}) :
    restrictIdeal D V = c'.coordIdeal {j} := by
  have h1 : D.ideal ⟨V, hV⟩
      = Ideal.span (c.coord '' ((({j} : Finset (Fin n))) : Set (Fin n))) :=
    c.ideal_eq_span_coord hV D {j} hD
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c' D {j} ?_
  rw [h1, Finset.coe_singleton, Set.image_singleton, Set.image_singleton, hcoord]

theorem exists_common_charts_of_isMaxContactHypersurface (A : X.IdealSheafData) {μ : ℕ}
    (hμ : 1 ≤ μ) (N : List X.IdealSheafData) (H₁ H₂ : X.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂)
    (x : X) (hx : x ∈ orderAtLeastLocus A μ) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hxV : x ∈ V) (n : ℕ) (c₁ : EtaleChart p V n)
      (c₂ : EtaleChart p V n) (γ : ℕ → Option (Fin n)) (j₀ : Fin n),
      restrictIdeal H₁ V = c₁.coordIdeal {j₀} ∧
      restrictIdeal H₂ V = c₂.coordIdeal {j₀} ∧
      IsMaxContactCoord k p A μ c₁ j₀ ∧
      IsMaxContactCoord k p A μ c₂ j₀ ∧
      (X.presheaf.germ V x hxV).hom (c₁.coord j₀) ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
      (X.presheaf.germ V x hxV).hom (c₂.coord j₀) ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ∧
      (∀ j : Fin n, j ≠ j₀ → c₂.coord j = c₁.coord j) ∧
      (∀ i : ℕ, ∀ hi : i < N.length,
        (γ i = none → restrictIdeal (N[i]'hi) V = ⊤) ∧
          ∀ j : Fin n, γ i = some j → restrictIdeal (N[i]'hi) V = c₁.coordIdeal {j}) ∧
      (∀ i i' : ℕ, i < N.length → i' < N.length → ∀ j : Fin n,
        γ i = some j → γ i' = some j → i = i') ∧
      (∀ i : ℕ, γ i ≠ some j₀) := by
  classical
  have hxH₁ : x ∈ H₁.support := hadm₁.orderAtLeastLocus_subset_support hμ hx
  have hxH₂ : x ∈ H₂.support := hadm₂.orderAtLeastLocus_subset_support hμ hx
  obtain ⟨U₁, hU₁, hxU₁, hcase₁⟩ := (isMaxContactHypersurface_iff k p A μ H₁).mp hadm₁ x
  obtain ⟨n₁, d₁, i₁, hH₁U₁, hmc₁⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U₁ n) (j : Fin n),
        restrictIdeal H₁ U₁ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A μ c j := by
    rcases hcase₁ with ⟨hdisj, -⟩ | hc
    · exact absurd hxU₁ (Set.disjoint_left.mp hdisj hx)
    · exact hc
  obtain ⟨U₂, hU₂, hxU₂, hcase₂⟩ := (isMaxContactHypersurface_iff k p A μ H₂).mp hadm₂ x
  obtain ⟨n₂, d₂, i₂, hH₂U₂, hmc₂⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U₂ n) (j : Fin n),
        restrictIdeal H₂ U₂ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A μ c j := by
    rcases hcase₂ with ⟨hdisj, -⟩ | hc
    · exact absurd hxU₂ (Set.disjoint_left.mp hdisj hx)
    · exact hc
  have hM₁ : H₁.ideal ⟨U₁, hU₁⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨U₁, hU₁⟩ := by
    have h1 : H₁.ideal ⟨U₁, hU₁⟩
        = Ideal.span (d₁.coord '' ((({i₁} : Finset (Fin n₁))) : Set (Fin n₁))) :=
      d₁.ideal_eq_span_coord hU₁ H₁ {i₁} hH₁U₁
    rw [h1, Finset.coe_singleton, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A μ hU₁ d₁ i₁).mp hmc₁
  have hM₂ : H₂.ideal ⟨U₂, hU₂⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨U₂, hU₂⟩ := by
    have h1 : H₂.ideal ⟨U₂, hU₂⟩
        = Ideal.span (d₂.coord '' ((({i₂} : Finset (Fin n₂))) : Set (Fin n₂))) :=
      d₂.ideal_eq_span_coord hU₂ H₂ {i₂} hH₂U₂
    rw [h1, Finset.coe_singleton, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A μ hU₂ d₂ i₂).mp hmc₂
  have hsnc₁' := (inStrictNormalCrossingPosition_iff p (H₁ :: N)).mp hsnc₁
  have hsnc₂' := (inStrictNormalCrossingPosition_iff p (H₂ :: N)).mp hsnc₂
  have hcart₂ : Blowup.IsLocallyGeneratedByNonZeroDivisor H₂ :=
    ((isSmoothDivisor_iff p H₂).mp (hsnc₂'.1 H₂ (by simp))).1
  obtain ⟨⟨W₂, hW₂⟩, f₂, hxW₂, -, hf₂span⟩ := hcart₂ x
  obtain ⟨W, hxW, m₀, c₀, a, hainj, hanone, hasome⟩ := (hsnc₁'.2 x).exists_etaleChart
  obtain ⟨V₀, hV₀b, hxV₀, hV₀W⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  have hV₀ : IsAffineOpen V₀ := hV₀b
  have hdesc0 : ∀ i : ℕ, ∀ hi : i < (H₁ :: N).length,
      (a i = none → restrictIdeal ((H₁ :: N)[i]'hi) V₀ = ⊤) ∧
        ∀ j : Fin m₀, a i = some j →
          restrictIdeal ((H₁ :: N)[i]'hi) V₀ = (c₀.restrict hV₀W).coordIdeal {j} := by
    intro i hi
    refine ⟨fun hn => restrictIdeal_eq_top_of_le _ hV₀W (hanone i hi hn), ?_⟩
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV₀W c₀ _ {j} (hasome i hi j hj)
  have hinj0 : ∀ i i' : ℕ, i < (H₁ :: N).length → i' < (H₁ :: N).length →
      ∀ j : Fin m₀, a i = some j → a i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    exact hainj i hi i' hi' j h1 h2
  obtain ⟨U', hU', hxU', n', c', a', hdesc', hinj', hprime'⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf (H₁ :: N) x V₀ hV₀ hxV₀ (c₀.restrict hV₀W) a hdesc0 hinj0
  have hlt0 : 0 < (H₁ :: N).length := by simp
  obtain ⟨j₀, hj₀⟩ : ∃ t : Fin n', a' 0 = some t := by
    cases h0 : a' 0 with
    | none =>
      exfalso
      have htop := (hdesc' 0 hlt0).1 h0
      simp only [List.getElem_cons_zero] at htop
      exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H₁ U' htop x hxU' hxH₁
    | some t => exact ⟨t, rfl⟩
  have hH₁U' : restrictIdeal H₁ U' = c'.coordIdeal {j₀} := by
    have h1 := (hdesc' 0 hlt0).2 j₀ hj₀
    simpa only [List.getElem_cons_zero] using h1
  obtain ⟨γ, hγval, hγnone⟩ :
      ∃ γ : ℕ → Option (Fin n'),
        (∀ i : ℕ, i < N.length → γ i = a' (i + 1)) ∧
        (∀ i : ℕ, ¬ i < N.length → γ i = none) :=
    ⟨fun i => if i < N.length then a' (i + 1) else none, fun i hi => if_pos hi,
      fun i hi => if_neg hi⟩
  have hγinj : LabelingInjective γ N.length := by
    intro i i' hi hi' j hj hj'
    rw [hγval i hi] at hj
    rw [hγval i' hi'] at hj'
    have h1 : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have h2 : i' + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have h3 := hinj' (i + 1) (i' + 1) h1 h2 j hj hj'
    omega
  have hγj₀ : ∀ i : ℕ, γ i ≠ some j₀ := by
    intro i hcon
    by_cases hi : i < N.length
    · rw [hγval i hi] at hcon
      have h1 : i + 1 < (H₁ :: N).length := by
        simp only [List.length_cons]
        omega
      have h3 := hinj' (i + 1) 0 h1 hlt0 j₀ hcon hj₀
      omega
    · rw [hγnone i hi] at hcon
      exact Option.some_ne_none j₀ hcon.symm
  have hlabU' : IsCoordLabeling c' γ N := by
    intro i hi
    have hiE : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have hget : (H₁ :: N)[i + 1]'hiE = N[i]'hi := by simp
    refine ⟨?_, ?_⟩
    · intro hnone
      have ha' : a' (i + 1) = none := by
        rw [← hγval i hi]
        exact hnone
      have htop := (hdesc' (i + 1) hiE).1 ha'
      rw [hget] at htop
      exact htop
    · intro j hj
      have ha' : a' (i + 1) = some j := by
        rw [← hγval i hi]
        exact hj
      have h2 := (hdesc' (i + 1) hiE).2 j ha'
      rw [hget] at h2
      exact h2
  have hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n',
      γ i = some j → x ∈ (N[i]'hi).support := by
    intro i hi j hj
    have hiE : i + 1 < (H₁ :: N).length := by
      simp only [List.length_cons]
      omega
    have ha' : a' (i + 1) = some j := by
      rw [← hγval i hi]
      exact hj
    have h2 := (hlabU' i hi).2 j hj
    have hideal : (N[i]'hi).ideal ⟨U', hU'⟩ = Ideal.span {c'.coord j} := by
      have h3 := c'.ideal_eq_span_coord hU' (N[i]'hi) {j} h2
      rwa [Finset.coe_singleton, Set.image_singleton] at h3
    refine mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU' hxU' ?_
    rw [hideal, Ideal.span_le, Set.singleton_subset_iff]
    exact hprime' (i + 1) hiE j ha'
  obtain ⟨V, hVb, hxV, hVΩ⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U' ⊓ U₁ ⊓ U₂ ⊓ W₂ from ⟨⟨⟨hxU', hxU₁⟩, hxU₂⟩, hxW₂⟩)
  have hV : IsAffineOpen V := hVb
  have hVU' : V ≤ U' := le_trans hVΩ (le_trans inf_le_left (le_trans inf_le_left inf_le_left))
  have hVU₁ : V ≤ U₁ := le_trans hVΩ (le_trans inf_le_left (le_trans inf_le_left inf_le_right))
  have hVU₂ : V ≤ U₂ := le_trans hVΩ (le_trans inf_le_left inf_le_right)
  have hVW₂ : V ≤ W₂ := le_trans hVΩ inf_le_right
  have hH₁V : restrictIdeal H₁ V = (c'.restrict hVU').coordIdeal {j₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' H₁ {j₀} hH₁U'
  have hlab : IsCoordLabeling (c'.restrict hVU') γ N := by
    intro i hi
    refine ⟨?_, ?_⟩
    · intro hnone
      exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU' ((hlabU' i hi).1 hnone)
    · intro j hj
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' (N[i]'hi) {j} ((hlabU' i hi).2 j hj)
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, V), H₂.ideal ⟨V, hV⟩ = Ideal.span {g} := by
    refine ⟨(X.presheaf.map (homOfLE hVW₂).op).hom f₂, ?_⟩
    have h2 := ideal_eq_span_image_map_of_le H₂ hW₂ hV hVW₂ ({f₂} : Set Γ(X, W₂)) hf₂span
    rwa [Set.image_singleton] at h2
  obtain ⟨jd, hjdlab, hjdpd⟩ : ∃ j : Fin n',
      (∀ i : ℕ, i < N.length → γ i ≠ some j) ∧
      chartPartialDeriv hV (c'.restrict hVU') j g ∉
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    exists_unlabeled_index_partialDeriv_notMem_primeIdealOf hV (c'.restrict hVU') hxV N γ
      H₂ g hlab hγinj (hsnc₂'.2 x) hg hxH₂ hxN
  have hjdpd' :
      chartPartialDeriv hV (c'.restrict hVU') jd g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hjdpd
  obtain ⟨c'', hcj₀, hclab, hpd⟩ : ∃ c'' : EtaleChart p V n',
      c''.coord j₀ = (c'.restrict hVU').coord j₀ ∧
      (∀ j : Fin n', (∃ i : ℕ, i < N.length ∧ γ i = some j) →
        c''.coord j = (c'.restrict hVU').coord j) ∧
      chartPartialDeriv hV c'' j₀ g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    by_cases h0 : chartPartialDeriv hV (c'.restrict hVU') j₀ g ∈
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    · have hne : j₀ ≠ jd := by
        intro hh
        rw [hh] at h0
        exact hjdpd' h0
      obtain ⟨c'', -, hcother, hderiv, -⟩ :=
        exists_etaleChart_coord_add_smul_chartPartialDeriv hV (c'.restrict hVU') j₀ jd hne (1 : k)
      refine ⟨c'', hcother j₀ hne, ?_, ?_⟩
      · rintro j ⟨i, hi, hγi⟩
        refine hcother j ?_
        intro hjd
        exact hjdlab i hi (by rw [hγi, hjd])
      · rw [hderiv g, map_one, one_mul]
        intro hmem
        apply hjdpd'
        have heq : chartPartialDeriv hV (c'.restrict hVU') jd g
            = chartPartialDeriv hV (c'.restrict hVU') j₀ g
              - (chartPartialDeriv hV (c'.restrict hVU') j₀ g
                 - chartPartialDeriv hV (c'.restrict hVU') jd g) := by ring
        rw [heq]
        exact Submodule.sub_mem _ h0 hmem
    · exact ⟨c'.restrict hVU', rfl, fun j _ => rfl, h0⟩
  have hH₁V'' : restrictIdeal H₁ V = c''.coordIdeal {j₀} :=
    restrictIdeal_eq_coordIdeal_of_coord_eq hV (c'.restrict hVU') c'' j₀ hcj₀ H₁ hH₁V
  have hlab'' : IsCoordLabeling c'' γ N := by
    intro i hi
    refine ⟨(hlab i hi).1, ?_⟩
    intro j hj
    exact restrictIdeal_eq_coordIdeal_of_coord_eq hV (c'.restrict hVU') c'' j
      (hclab j ⟨i, hi, hj⟩) (N[i]'hi) ((hlab i hi).2 j hj)
  obtain ⟨V', hV', hV'V, hxV', c₂, hc₂j₀, hc₂other⟩ :=
    exists_etaleChart_update_coord_of_partialDeriv_notMem hV c'' hxV j₀ g hpd
  have hH₁V' : restrictIdeal H₁ V' = (c''.restrict hV'V).coordIdeal {j₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' H₁ {j₀} hH₁V''
  have hH₁id : H₁.ideal ⟨V', hV'⟩ = Ideal.span {(c''.restrict hV'V).coord j₀} := by
    have h1 := (c''.restrict hV'V).ideal_eq_span_coord hV' H₁ {j₀} hH₁V'
    rwa [Finset.coe_singleton, Set.image_singleton] at h1
  have hgV' : H₂.ideal ⟨V', hV'⟩ = Ideal.span {c₂.coord j₀} := by
    have h2 := ideal_eq_span_image_map_of_le H₂ hV hV' hV'V ({g} : Set Γ(X, V)) hg
    rw [Set.image_singleton] at h2
    rw [h2, hc₂j₀]
  have hH₂V' : restrictIdeal H₂ V' = c₂.coordIdeal {j₀} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV' c₂ H₂ {j₀} ?_
    rw [hgV', Finset.coe_singleton, Set.image_singleton]
  have hmcc₁ : IsMaxContactCoord k p A μ (c''.restrict hV'V) j₀ := by
    rw [isMaxContactCoord_iff_coord_mem k p A μ hV' (c''.restrict hV'V) j₀]
    have h1 : H₁.ideal ⟨V', hV'⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨V', hV'⟩ :=
      ideal_le_of_ideal_le_of_le k p H₁ (maxContactIdeal k p A μ) hU₁ hV'
        (le_trans hV'V hVU₁) hM₁
    refine h1 ?_
    rw [hH₁id]
    exact Ideal.mem_span_singleton_self _
  have hmcc₂ : IsMaxContactCoord k p A μ c₂ j₀ := by
    rw [isMaxContactCoord_iff_coord_mem k p A μ hV' c₂ j₀]
    have h1 : H₂.ideal ⟨V', hV'⟩ ≤ (maxContactIdeal k p A μ).ideal ⟨V', hV'⟩ :=
      ideal_le_of_ideal_le_of_le k p H₂ (maxContactIdeal k p A μ) hU₂ hV'
        (le_trans hV'V hVU₂) hM₂
    refine h1 ?_
    rw [hgV']
    exact Ideal.mem_span_singleton_self _
  have hgerm₁ : (X.presheaf.germ V' x hxV').hom ((c''.restrict hV'V).coord j₀)
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    have hmem : (c''.restrict hV'V).coord j₀ ∈ H₁.ideal ⟨V', hV'⟩ := by
      rw [hH₁id]
      exact Ideal.mem_span_singleton_self _
    have h2 := germ_mem_stalkIdeal H₁ x ⟨V', hV'⟩ hxV' hmem
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H₁ x).mp hxH₁ h2
  have hgerm₂ : (X.presheaf.germ V' x hxV').hom (c₂.coord j₀)
      ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
    have hmem : c₂.coord j₀ ∈ H₂.ideal ⟨V', hV'⟩ := by
      rw [hgV']
      exact Ideal.mem_span_singleton_self _
    have h2 := germ_mem_stalkIdeal H₂ x ⟨V', hV'⟩ hxV' hmem
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H₂ x).mp hxH₂ h2
  have hcoords : ∀ j : Fin n', j ≠ j₀ → c₂.coord j = (c''.restrict hV'V).coord j := by
    intro j hj
    rw [hc₂other j hj]
    change (X.presheaf.map (homOfLE hV'V).op).hom (c''.coord j) =
      (c''.restrictCompat hV'V).coord j
    exact (EtaleChart.coord_restrict c'' hV'V j).symm
  have hlabV' : ∀ i : ℕ, ∀ hi : i < N.length,
      (γ i = none → restrictIdeal (N[i]'hi) V' = ⊤) ∧
        ∀ j : Fin n', γ i = some j →
          restrictIdeal (N[i]'hi) V' = (c''.restrict hV'V).coordIdeal {j} := by
    intro i hi
    refine ⟨fun hn => restrictIdeal_eq_top_of_le (N[i]'hi) hV'V ((hlab'' i hi).1 hn), ?_⟩
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' (N[i]'hi) {j} ((hlab'' i hi).2 j hj)
  exact ⟨V', hV', hxV', n', c''.restrict hV'V, c₂, γ, j₀, hH₁V', hH₂V', hmcc₁, hmcc₂,
    hgerm₁, hgerm₂, hcoords, hlabV', hγinj, hγj₀⟩

end

end FunctorialResolution.EmbeddedResolution
end
end

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_comp_eq_of_comap_comap_eq {A B C : Scheme.{u}} (ι : A ⟶ B) (F G : B ⟶ C)
    (I J : C.IdealSheafData) (h : (I.comap F).comap ι = (J.comap G).comap ι) :
    I.comap (ι ≫ F) = J.comap (ι ≫ G) := by
  have hF : I.comap (ι ≫ F) = (I.comap F).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  have hG : J.comap (ι ≫ G) = (J.comap G).comap ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [hF, hG]
  exact h

private theorem comap_comp_ι_eq_comap_restrictIdeal {Y Z : Scheme.{u}} (J : Y.IdealSheafData)
    (U : Y.Opens) (g : Z ⟶ U.toScheme) : J.comap (g ≫ U.ι) = (restrictIdeal J U).comap g := by
  show J.comap (g ≫ U.ι) = (J.comap U.ι).comap g
  simp [Scheme.IdealSheafData.comap_comp]

private theorem exists_subscheme_comap_lift {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    ∃ θ : (I.comap f).subscheme ⟶ I.subscheme,
      θ ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  have h2 : Scheme.Hom.ker I.subschemeι ≤
      Scheme.Hom.ker ((I.comap f).subschemeι ≫ f) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.IdealSheafData.le_map_comap I f
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι _ h2,
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι _ h2⟩

private theorem range_base_subset_range_preimage_ι {T W Z S : Scheme.{u}} (tι : T ⟶ W) (ιZ : W ⟶ Z)
    (θ : T ⟶ S) (σ : S ⟶ Z) (hθ : θ ≫ σ = tι ≫ ιZ) (Wop : Z.Opens)
    (hsub : Set.range ⇑ιZ.base ⊆ (Wop : Set ↥Z)) :
    Set.range ⇑θ.base ⊆ Set.range ⇑((σ ⁻¹ᵁ Wop).ι).base := by
  rw [Scheme.Opens.range_ι]
  rintro z ⟨y, rfl⟩
  show σ.base (θ.base y) ∈ Wop
  have hb : (θ ≫ σ).base y = (tι ≫ ιZ).base y := by rw [hθ]
  have hb2 : σ.base (θ.base y) = ιZ.base (tι.base y) := hb
  rw [hb2]
  exact hsub ⟨tι.base y, rfl⟩

private theorem comp_eq_of_lift_comp_eq {T W Z S S' Q : Scheme.{u}}
    (tι : T ⟶ W) (ιZ : W ⟶ Z) (σ : S ⟶ Z) (j : S' ⟶ S) (θ : T ⟶ S) (δ : T ⟶ S')
    (F G : Z ⟶ Q) (hθ : θ ≫ σ = tι ≫ ιZ) (hδ : δ ≫ j = θ)
    (heq : j ≫ σ ≫ F = j ≫ σ ≫ G) :
    tι ≫ ιZ ≫ F = tι ≫ ιZ ≫ G := by
  have h1 : tι ≫ ιZ ≫ F = δ ≫ j ≫ σ ≫ F := by
    rw [← Category.assoc tι ιZ F, ← hθ, ← hδ]
    simp only [Category.assoc]
  have h2 : tι ≫ ιZ ≫ G = δ ≫ j ≫ σ ≫ G := by
    rw [← Category.assoc tι ιZ G, ← hθ, ← hδ]
    simp only [Category.assoc]
  rw [h1, h2, heq]

theorem nonempty_etaleMaxContactComparison (k : Type u) [Field k] [CharZero k] {P : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂)
    (pt : P) (hpt : pt ∈ orderAtLeastLocus A μ) :
    Nonempty (EtaleMaxContactComparison k p A μ N H₁ H₂ pt) := by
  obtain ⟨V, hVaff, hptV, n, c₁, c₂, γ, j₀, hH₁, hH₂, hmc₁, hmc₂, hgm₁, hgm₂, hco, hNγ,
      _, hγne⟩ :=
    exists_common_charts_of_isMaxContactHypersurface A hμ N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt
  have hlftF : LocallyOfFiniteType (chartPullbackFst c₁ c₂ ≫ p) := inferInstance
  have hln1 : IsLocallyNoetherian (chartPullback c₁ c₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (f := chartPullbackFst c₁ c₂ ≫ p)
  have hln2 : IsLocallyNoetherian
      ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subscheme := by
    have : LocallyOfFiniteType
        (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          (chartPullbackFst c₁ c₂ ≫ p)) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian
      (f := ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
        (chartPullbackFst c₁ c₂ ≫ p))
  obtain ⟨hagree, Wop, hptW, hstalk, _, heqmor, hHcomap, hcoordS⟩ :=
    exists_opens_chartPullback_eq_of_mem_maxContactIdeal k p A hμ hinv hVaff c₁ c₂ j₀
      (fun i hi => (hco i hi).symm) pt hptV
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₁ j₀).mp hmc₁)
      ((isMaxContactCoord_iff_coord_mem k p A μ hVaff c₂ j₀).mp hmc₂)
      hgm₁ hgm₂ (mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hμ hpt)
  obtain ⟨U0, hU0⟩ : ∃ U0 : (chartPullback c₁ c₂).affineOpens,
      chartPullbackPoint c₁ c₂ pt hptV hagree ∈ U0.1 := by
    have hx : chartPullbackPoint c₁ c₂ pt hptV hagree ∈
        (⨆ U : (chartPullback c₁ c₂).affineOpens, (U : (chartPullback c₁ c₂).Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top (chartPullback c₁ c₂)]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, hU⟩
  obtain ⟨g, hgle, hw0W'⟩ :=
    U0.2.exists_basicOpen_le (⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hptW⟩ : Wop) hU0
  have hW'aff : IsAffineOpen ((chartPullback c₁ c₂).basicOpen g) :=
    ((chartPullback c₁ c₂).affineBasicOpen g).2
  have hetale1 : AlgebraicGeometry.Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hetale2 : AlgebraicGeometry.Etale
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂) := inferInstance
  have hsmooth1 : AlgebraicGeometry.Smooth
      (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) := inferInstance
  have hlft1 : LocallyOfFiniteType
      ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p) := inferInstance
  have e1 : H₁.comap (chartPullbackFst c₁ c₂)
      = (c₁.coordIdeal {j₀}).comap (Limits.pullback.fst c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal H₁ V (Limits.pullback.fst c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.fst c₁.map c₂.map)) hH₁)
  have e2 : H₂.comap (chartPullbackSnd c₁ c₂)
      = (c₂.coordIdeal {j₀}).comap (Limits.pullback.snd c₁.map c₂.map) :=
    (comap_comp_ι_eq_comap_restrictIdeal H₂ V (Limits.pullback.snd c₁.map c₂.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        K.comap (Limits.pullback.snd c₁.map c₂.map)) hH₂)
  have e3 : H₁.comap (chartPullbackFst c₁ c₂) = H₂.comap (chartPullbackSnd c₁ c₂) :=
    e1.trans (hHcomap.trans e2.symm)
  refine ⟨{ W := ((chartPullback c₁ c₂).basicOpen g).toScheme
          , f₁ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂
          , f₂ := ((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackSnd c₁ c₂
          , w := ⟨chartPullbackPoint c₁ c₂ pt hptV hagree, hw0W'⟩
          , isAffine := hW'aff
          , etale_f₁ := hetale1
          , etale_f₂ := hetale2
          , lft_f₁ := hlft1
          , base_f₁ := ?_
          , base_f₂ := ?_
          , comap_A := ?_
          , comap_H := ?_
          , comap_N := ?_
          , comp_p := ?_
          , maxContact_comp := ?_ }⟩
  · exact chartPullbackFst_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · exact chartPullbackSnd_base_chartPullbackPoint c₁ c₂ pt hptV hagree
  · refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) A A ?_
    exact restrictIdeal_eq_of_stalkIdeal_eq _ _ ((chartPullback c₁ c₂).basicOpen g)
      (fun y hy => hstalk y (hgle hy))
  · refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) H₁ H₂ ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) e3
  · intro J hJ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hJ
    have key : (N[i]'hi).comap (chartPullbackFst c₁ c₂) = (N[i]'hi).comap (chartPullbackSnd c₁ c₂) := by
      obtain ⟨hnone, hsome⟩ := hNγ i hi
      have h0F : (N[i]'hi).comap (chartPullbackFst c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.fst c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal _ V _
      have h0G : (N[i]'hi).comap (chartPullbackSnd c₁ c₂)
          = (restrictIdeal (N[i]'hi) V).comap (Limits.pullback.snd c₁.map c₂.map) :=
        comap_comp_ι_eq_comap_restrictIdeal _ V _
      rw [h0F, h0G]
      cases hγ : γ i with
      | none =>
        rw [hnone hγ, Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.comap_top]
      | some jj =>
        have hjj : jj ≠ j₀ := by
          intro h
          exact hγne i (by rw [hγ, h])
        have hnotmem : j₀ ∉ ({jj} : Finset (Fin n)) := by
          simp only [Finset.mem_singleton]
          exact fun h => hjj h.symm
        rw [hsome jj hγ, chartPullback_comap_coordIdeal_eq c₁ c₂ {jj}, hcoordS {jj} hnotmem]
    refine comap_comp_eq_of_comap_comap_eq ((chartPullback c₁ c₂).basicOpen g).ι (chartPullbackFst c₁ c₂)
      (chartPullbackSnd c₁ c₂) (N[i]'hi) (N[i]'hi) ?_
    exact congrArg (fun J : (chartPullback c₁ c₂).IdealSheafData =>
      J.comap ((chartPullback c₁ c₂).basicOpen g).ι) key
  · have hcs := chartPullbackFst_comp_eq_chartPullbackSnd_comp c₁ c₂
    simp only [Category.assoc] at hcs ⊢
    rw [hcs]
  · have hNeq : maxContactIdeal k
          ((((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) ≫ p)
          (A.comap (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂)) μ
        = ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
            ((chartPullback c₁ c₂).basicOpen g).ι := by
      simp only [maxContactIdeal_eq_derivIdealSheafIterate]
      rw [derivIdealSheafIterate_comap k p
        (((chartPullback c₁ c₂).basicOpen g).ι ≫ chartPullbackFst c₁ c₂) (μ - 1) A]
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hNeq]
    obtain ⟨θ, hθ⟩ :=
      exists_subscheme_comap_lift ((chartPullback c₁ c₂).basicOpen g).ι
        ((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂))
    have hsub : Set.range ⇑(((chartPullback c₁ c₂).basicOpen g).ι).base ⊆
        (Wop : Set ↥(chartPullback c₁ c₂)) := by
      rw [Scheme.Opens.range_ι]
      intro z hz
      exact hgle hz
    have hrange := range_base_subset_range_preimage_ι
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).comap
        ((chartPullback c₁ c₂).basicOpen g).ι).subschemeι)
      ((chartPullback c₁ c₂).basicOpen g).ι θ
      (((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι) hθ Wop hsub
    exact comp_eq_of_lift_comp_eq _ _ _
      ((((maxContactIdeal k p A μ).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ Wop).ι)
      θ (IsOpenImmersion.lift _ θ hrange) (chartPullbackFst c₁ c₂) (chartPullbackSnd c₁ c₂)
      hθ (IsOpenImmersion.lift_fac _ θ hrange) heqmor

theorem exists_etale_equalizing_isMaxContactHypersurface (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (A : P.IdealSheafData) {μ : ℕ} (hμ : 1 ≤ μ) (hinv : IsMaxContactInvariant k p A μ)
    (_horder : ∀ x : P, orderAt A x ≤ (μ : ℕ∞))
    (N : List P.IdealSheafData) (H₁ H₂ : P.IdealSheafData)
    (hsnc₁ : InStrictNormalCrossingPosition p (H₁ :: N)) (hsnc₂ : InStrictNormalCrossingPosition p (H₂ :: N))
    (hadm₁ : IsMaxContactHypersurface k p A μ H₁)
    (hadm₂ : IsMaxContactHypersurface k p A μ H₂) :
    ∃ (V : Scheme.{u}) (g₁ : V ⟶ P) (g₂ : V ⟶ P) (_ : Etale g₁) (_ : Etale g₂)
      (_ : QuasiCompact (g₁ ≫ p)) (hlft : LocallyOfFiniteType (g₁ ≫ p)),
      g₁ ≫ p = g₂ ≫ p ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₁.base ∧
      orderAtLeastLocus A μ ⊆ Set.range ⇑g₂.base ∧
      A.comap g₁ = A.comap g₂ ∧
      H₁.comap g₁ = H₂.comap g₂ ∧
      N.map (fun J => J.comap g₁) = N.map (fun J => J.comap g₂) ∧
      (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₁ =
        (@maxContactIdeal k _ _ V (g₁ ≫ p) hlft (A.comap g₁) μ).subschemeι ≫ g₂ :=
  exists_etale_maxContactIdeal_comparison k p A μ N H₁ H₂
    (fun pt hpt =>
      nonempty_etaleMaxContactComparison k p A hμ hinv N H₁ H₂ hsnc₁ hsnc₂ hadm₁ hadm₂ pt hpt)

end FunctorialResolution.EmbeddedResolution
