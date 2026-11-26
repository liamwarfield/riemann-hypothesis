module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensors
open Classical MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.FrobProd

theorem exists_compact_clopen {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {u : Set X} (hu : IsOpen u) (hx : x ∈ u) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ u := by
  obtain ⟨K, hK, hxK, hKu⟩ := exists_compact_subset hu hx
  obtain ⟨V, hV, hxV, hVK⟩ := (isTopologicalBasis_isClopen (X := X)).exists_subset_of_mem_open
    hxK isOpen_interior
  have hVK' : V ⊆ K := hVK.trans interior_subset
  exact ⟨V, hK.of_isClosed_subset hV.isClosed hVK', hV, hxV, hVK'.trans hKu⟩


open Classical in
theorem fiber_ind_mem {X S : Type} [TopologicalSpace X] [T2Space X] {ξ : X → S}
    (hξ : IsLocallyConstant ξ) (s : S) (hs : IsCompact (ξ ⁻¹' {s})) :
    (fun x => if ξ x = s then (1 : ℂ) else 0) ∈ SB X := by
  refine mem_SB_iff.2 ⟨hξ.comp (fun t => if t = s then (1 : ℂ) else 0), ?_⟩
  refine HasCompactSupport.intro hs fun x hx => ?_
  have : ξ x ≠ s := hx
  simp [this]


open Classical in
theorem isLocallyConstant_pattern {X ι : Type} [TopologicalSpace X] [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsClopen (U i)) :
    IsLocallyConstant (fun x => Finset.univ.filter (fun i => x ∈ U i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ i, (y ∈ U i ↔ x ∈ U i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hx : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds hx] with y hy
      exact iff_of_true hy hx
    · filter_upwards [(hU i).compl.isOpen.mem_nhds hx] with y hy
      exact iff_of_false hy hx
  filter_upwards [h] with y hy
  ext i
  simp [hy i]


open Classical in
theorem isCompact_pattern_fiber {X ι : Type} [TopologicalSpace X] [T2Space X] [Fintype ι]
    {U : ι → Set X} (hU : ∀ i, IsClopen (U i)) (hc : ∀ i, IsCompact (U i)) (s : Finset ι)
    (hs : s ≠ ∅) :
    IsCompact ((fun x => Finset.univ.filter (fun i => x ∈ U i)) ⁻¹' {s}) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
  refine (hc i).of_isClosed_subset ((isLocallyConstant_pattern hU).isClosed_fiber s) ?_
  intro x hx
  have hx' : Finset.univ.filter (fun i => x ∈ U i) = s := hx
  rw [← hx'] at hi
  simpa using hi


open Classical in
theorem span_of_factor {A B S T : Type} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    [T2Space B] [Fintype S] [Fintype T] {ξ : A → S} {η : B → T}
    (hξ : IsLocallyConstant ξ) (hη : IsLocallyConstant η) (s0 : S) (t0 : T)
    (hcs : ∀ s, s ≠ s0 → IsCompact (ξ ⁻¹' {s})) (hct : ∀ t, t ≠ t0 → IsCompact (η ⁻¹' {t}))
    (f : SB (A × B))
    (hΦ : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q')
    (h0 : ∀ q : A × B, ξ q.1 = s0 → (f : A × B → ℂ) q = 0)
    (h0' : ∀ q : A × B, η q.2 = t0 → (f : A × B → ℂ) q = 0) :
    (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B,
      (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧
        F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  have hsum : (f : A × B → ℂ) =
      ∑ p : S × T, fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0 := by
    funext q
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ q.1, η q.2)]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1.symm h2.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine Eq.mpr (congrArg (· ∈ _) hsum) (Submodule.sum_mem _ fun p _ => ?_)
  by_cases hex : ∃ q0 : A × B, ξ q0.1 = p.1 ∧ η q0.2 = p.2 ∧ (f : A × B → ℂ) q0 ≠ 0
  · obtain ⟨q0, h1, h2, h3⟩ := hex
    have hs : p.1 ≠ s0 := fun h => h3 (h0 q0 (h1.trans h))
    have ht : p.2 ≠ t0 := fun h => h3 (h0' q0 (h2.trans h))
    let ia : SB A := ⟨_, fiber_ind_mem hξ p.1 (hcs _ hs)⟩
    let ib : SB B := ⟨_, fiber_ind_mem hη p.2 (hct _ ht)⟩
    have hia : ∀ x, (ia : A → ℂ) x = if ξ x = p.1 then 1 else 0 := fun _ => rfl
    have hib : ∀ x, (ib : B → ℂ) x = if η x = p.2 then 1 else 0 := fun _ => rfl
    refine Submodule.subset_span ⟨(f : A × B → ℂ) q0 • ia, ib, ?_, ?_⟩
    · intro q ha hb
      have e1 : ξ q.1 = p.1 := by
        by_contra h
        apply ha
        simp [hia, h]
      have e2 : η q.2 = p.2 := by
        by_contra h
        apply hb
        simp [hib, h]
      rw [hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
      exact h3
    · funext q
      by_cases e1 : ξ q.1 = p.1
      · by_cases e2 : η q.2 = p.2
        · simp [hia, hib, e1, e2, hΦ q q0 (e1.trans h1.symm) (e2.trans h2.symm)]
        · simp [hia, hib, e2]
      · simp [hia, e1]
  · have hz : (fun q : A × B => if ξ q.1 = p.1 ∧ η q.2 = p.2 then (f : A × B → ℂ) q else 0) = 0 := by
      funext q
      by_cases e : ξ q.1 = p.1 ∧ η q.2 = p.2
      · rw [if_pos e]
        by_contra h
        exact hex ⟨q, e.1, e.2, h⟩
      · rw [if_neg e]
        rfl
    rw [hz]
    exact Submodule.zero_mem _


open Classical in
theorem span_box : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  intro A B _ _ _ _ _ _ _ _ f
  have hlc : IsLocallyConstant (f : A × B → ℂ) := (mem_SB_iff.1 f.2).1
  have hcs : HasCompactSupport (f : A × B → ℂ) := (mem_SB_iff.1 f.2).2
  have hbox : ∀ q : A × B, ∃ U : Set A, ∃ V : Set B, IsCompact U ∧ IsClopen U ∧ IsCompact V ∧
      IsClopen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧
      ∀ q' : A × B, q'.1 ∈ U → q'.2 ∈ V → (f : A × B → ℂ) q' = (f : A × B → ℂ) q := by
    intro q
    obtain ⟨u, v, hu, hv, hqu, hqv, huv⟩ := isOpen_prod_iff.1
      (hlc.isOpen_fiber ((f : A × B → ℂ) q)) q.1 q.2 rfl
    obtain ⟨U, hUc, hUo, hqU, hUu⟩ := exists_compact_clopen hu hqu
    obtain ⟨V, hVc, hVo, hqV, hVv⟩ := exists_compact_clopen hv hqv
    exact ⟨U, V, hUc, hUo, hVc, hVo, hqU, hqV, fun q' h1 h2 => huv ⟨hUu h1, hVv h2⟩⟩
  choose U V hUc hUo hVc hVo hqU hqV hUV using hbox
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover (fun q => U q ×ˢ V q)
    (fun q _ => ((hUo q).isOpen.prod (hVo q).isOpen).mem_nhds ⟨hqU q, hqV q⟩)
  have hcov : ∀ q : A × B, (f : A × B → ℂ) q ≠ 0 → ∃ i : t, q.1 ∈ U i ∧ q.2 ∈ V i := by
    intro q hq
    have := ht (subset_tsupport _ hq)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h.1, h.2⟩
  let ξ : A → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ U i)
  let η : B → Finset t := fun x => Finset.univ.filter (fun i : t => x ∈ V i)
  have hξm : ∀ x i, i ∈ ξ x ↔ x ∈ U i := fun x i => by simp [ξ]
  have hηm : ∀ x i, i ∈ η x ↔ x ∈ V i := fun x i => by simp [η]
  have hstep : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 → (f : A × B → ℂ) q ≠ 0 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q' := by
    intro q q' e1 e2 hq
    obtain ⟨i, h1, h2⟩ := hcov q hq
    have h1' : q'.1 ∈ U i := (hξm _ _).1 (e1 ▸ (hξm _ _).2 h1)
    have h2' : q'.2 ∈ V i := (hηm _ _).1 (e2 ▸ (hηm _ _).2 h2)
    rw [hUV i q h1 h2, hUV i q' h1' h2']
  refine span_of_factor (ξ := ξ) (η := η)
    (isLocallyConstant_pattern (U := fun i : t => U i) fun i => hUo i)
    (isLocallyConstant_pattern (U := fun i : t => V i) fun i => hVo i) ∅ ∅
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => U i) (fun i => hUo i) (fun i => hUc i) s hs)
    (fun s hs => isCompact_pattern_fiber (U := fun i : t => V i) (fun i => hVo i) (fun i => hVc i) s hs)
    f ?_ ?_ ?_
  · intro q q' e1 e2
    by_cases hq : (f : A × B → ℂ) q = 0
    · by_cases hq' : (f : A × B → ℂ) q' = 0
      · rw [hq, hq']
      · exact (hstep q' q e1.symm e2.symm hq').symm
    · exact hstep q q' e1 e2 hq
  · intro q hq
    by_contra h
    obtain ⟨i, h1, -⟩ := hcov q h
    have : i ∈ ξ q.1 := (hξm _ _).2 h1
    rw [hq] at this
    simp at this
  · intro q hq
    by_contra h
    obtain ⟨i, -, h2⟩ := hcov q h
    have : i ∈ η q.2 := (hηm _ _).2 h2
    rw [hq] at this
    simp at this

end GlobalTheory.CompanionTheory.FrobProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensorsStatement
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_prod_span_tensors : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  first | exact @GlobalTheory.CompanionTheory.FrobProd.span_box | exact GlobalTheory.CompanionTheory.FrobProd.span_box | (intros; apply GlobalTheory.CompanionTheory.FrobProd.span_box <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultiple
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultiple
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

noncomputable section

namespace GlobalTheory.CompanionTheory.FrobHaarR

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_open_left_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x, F (k * x) = F x := by
  let K : Subgroup G :=
    { carrier := {k | ∀ g, F (k * g) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha g
        have := ha (a⁻¹ * g)
        simpa using this.symm }
  have h1 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k * g) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.1 * z.2)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, one_mul]
  have h2 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k⁻¹ * g) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  have hK : IsOpen (K : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds K (g := 1)
    filter_upwards [h1, h2] with k hk1 hk2
    intro g
    by_cases hg : g ∈ tsupport F
    · exact hk1 g hg
    · by_cases hg' : k * g ∈ tsupport F
      · simpa using (hk2 _ hg').symm
      · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
  exact ⟨⟨K, hK⟩, fun k hk x => hk x⟩

theorem ind_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Set.indicator (K : Set G) (fun _ => (1 : ℂ)) ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (K : Set G)
  · exact ⟨K, K.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set G)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨_, ind_mem K hK⟩

theorem ind_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (ind K hK : G → ℂ) x = Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x :=
  rfl

theorem ind_left (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (x : G) :
    (ind K hK : G → ℂ) (k * x) = (ind K hK : G → ℂ) x := by
  have h : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) :=
    Subgroup.mul_mem_cancel_left K.toSubgroup hk
  by_cases hx : x ∈ (K : Set G)
  · rw [ind_apply, ind_apply, Set.indicator_of_mem (h.2 hx), Set.indicator_of_mem hx]
  · rw [ind_apply, ind_apply, Set.indicator_of_notMem (fun h' => hx (h.1 h')),
      Set.indicator_of_notMem hx]

theorem exists_decomp (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ (S : Finset G) (a : G → ℂ),
      f = ∑ t ∈ S, a t • pullHomeo (Homeomorph.mulRight t) (ind K hK) := by
  classical
  have hdisc : DiscreteTopology (G ⧸ (K : Subgroup G)) :=
    QuotientGroup.discreteTopology K.isOpen
  let π : G → G ⧸ (K : Subgroup G) := fun x => ((x⁻¹ : G) : G ⧸ (K : Subgroup G))
  have hπ : Continuous π := QuotientGroup.continuous_mk.comp continuous_inv
  have hfin : (π '' tsupport (f : G → ℂ)).Finite :=
    ((show IsCompact (tsupport (f : G → ℂ)) from f.2.2).image hπ).finite_of_discrete
  have key : ∀ (x : G) (q : G ⧸ (K : Subgroup G)), x * q.out ∈ K ↔ π x = q := by
    intro x q
    have h := QuotientGroup.eq (s := (K : Subgroup G)) (a := x⁻¹) (b := q.out)
    rw [inv_inv, QuotientGroup.out_eq'] at h
    exact h.symm
  have hinj : Set.InjOn (fun q : G ⧸ (K : Subgroup G) => q.out) (hfin.toFinset : Set _) :=
    fun a _ b _ h => Quotient.out_injective h
  refine ⟨hfin.toFinset.image (fun q => q.out), fun t => (f : G → ℂ) t⁻¹, ?_⟩
  rw [Finset.sum_image hinj]
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ hfin.toFinset,
      ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) : G → ℂ) x
        = if π x = q then (f : G → ℂ) x else 0 := by
    intro q _
    have e : ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) :
        G → ℂ) x = (f : G → ℂ) q.out⁻¹ * (ind K hK : G → ℂ) (x * q.out) := rfl
    rw [e, ind_apply]
    by_cases h : π x = q
    · have hm : x * q.out ∈ K := (key x q).2 h
      rw [if_pos h, Set.indicator_of_mem (show x * q.out ∈ (K : Set G) from hm), mul_one]
      have := hf _ hm q.out⁻¹
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [if_neg h, Set.indicator_of_notMem
        (show x * q.out ∉ (K : Set G) from fun hm => h ((key x q).1 hm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h0
    exact h (hfin.mem_toFinset.2 ⟨x, subset_tsupport _ h0, rfl⟩)

theorem exists_coeff (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ s : ℂ, ∀ M : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), M (pullHomeo (Homeomorph.mulRight g) α) = M α) →
        M f = s * M (ind K hK) := by
  obtain ⟨S, a, h⟩ := exists_decomp K hK f hf
  refine ⟨∑ t ∈ S, a t, fun M hM => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, _root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hM, smul_eq_mul]

end Abstract

section Integral

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem integrable_sb (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    Integrable (α : G → ℂ) μ :=
  α.2.1.continuous.integrable_of_hasCompactSupport α.2.2

def haarForm (μ : Measure G) [IsFiniteMeasureOnCompacts μ] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (integrable_sb μ α) (integrable_sb μ β)
  map_smul' c α := integral_const_mul c (α : G → ℂ)

theorem haarForm_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    haarForm μ α = ∫ x, (α : G → ℂ) x ∂μ :=
  rfl

variable [LocallyCompactSpace G]

theorem integral_mul_right_real (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G)
    {u : G → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) :
    ∫ x, u (x * g) ∂μ = ∫ x, u x ∂μ := by
  have h := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (map (· * g) μ) μ hu hcu
  have h1 : modularCharacterFun g = 1 := hU g
  rw [integral_smul_nnreal_measure, ← modularCharacterFun_eq_haarScalarFactor μ g, h1, one_smul,
    integral_map (AEMeasurable.mul_const aemeasurable_id' _) hu.aestronglyMeasurable] at h
  exact h

theorem haarForm_right (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    haarForm μ (pullHomeo (Homeomorph.mulRight g) α) = haarForm μ α := by
  have hc : Continuous (α : G → ℂ) := α.2.1.continuous
  have hcs : HasCompactSupport (α : G → ℂ) := α.2.2
  have hre := integral_mul_right_real hU μ g (u := fun x => RCLike.re ((α : G → ℂ) x))
    (RCLike.continuous_re.comp hc) (hcs.comp_left (g := RCLike.re) (map_zero _))
  have him := integral_mul_right_real hU μ g (u := fun x => RCLike.im ((α : G → ℂ) x))
    (RCLike.continuous_im.comp hc) (hcs.comp_left (g := RCLike.im) (map_zero _))
  rw [haarForm_apply, haarForm_apply,
    ← integral_re_add_im (integrable_sb μ (pullHomeo (Homeomorph.mulRight g) α)),
    ← integral_re_add_im (integrable_sb μ α)]
  simp only [pullHomeo_apply, Homeomorph.coe_mulRight]
  rw [hre, him]

theorem haarForm_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : haarForm μ (ind K hK) ≠ 0 := by
  have e : haarForm μ (ind K hK) = ∫ x, Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x ∂μ := rfl
  rw [e, integral_indicator_const (1 : ℂ) K.isOpen.measurableSet]
  have h0 : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have h1 : μ.real (K : Set G) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨h0, hK.measure_lt_top.ne⟩
  simpa using h1

end Integral

theorem exists_eq_mul_integral :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G],
      IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ),
      (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  intro G _ _ _ _ _ _ _ _ hU μ _ L hL
  obtain ⟨K₀, hK₀⟩ := GroundTheory.Automorphic.exists_compactOpenSubgroup (G := G)
  have hI := haarForm_right hU μ
  refine ⟨L (ind K₀ hK₀) / haarForm μ (ind K₀ hK₀), fun α => ?_⟩
  rw [← haarForm_apply]
  obtain ⟨K', hK'⟩ := exists_open_left_stab α.2
  have hKc : IsCompact ((K₀ ⊓ K' : OpenSubgroup G) : Set G) :=
    GroundTheory.Automorphic.isCompact_inf_left hK₀
  obtain ⟨s, hs⟩ := exists_coeff (K₀ ⊓ K') hKc α (fun k hk x => hK' k hk.2 x)
  obtain ⟨s₀, hs₀⟩ := exists_coeff (K₀ ⊓ K') hKc (ind K₀ hK₀)
    (fun k hk x => ind_left K₀ hK₀ hk.1 x)
  have hne := haarForm_ind_ne_zero μ (K₀ ⊓ K') hKc
  have hne₀ := haarForm_ind_ne_zero μ K₀ hK₀
  have h1 := hs L hL
  have h2 := hs _ hI
  have h3 := hs₀ L hL
  have h4 := hs₀ _ hI
  rw [h1, h2, h3, h4]
  have hs₀0 : s₀ ≠ 0 := fun h => hne₀ (by rw [h4, h, zero_mul])
  field_simp

end GlobalTheory.CompanionTheory.FrobHaarR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultipleStatement
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_functional_eq_haar_multiple : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ), (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) → ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | exact GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral | (intros; apply GlobalTheory.CompanionTheory.FrobHaarR.exists_eq_mul_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhat
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.TestFunctionFibreIntegral

theorem eventually_slice_eq {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (F : SB (A × B)) (a₀ : A) :
    ∀ᶠ a in nhds a₀, ∀ b, (F : A × B → ℂ) (a, b) = (F : A × B → ℂ) (a₀, b) := by
  obtain ⟨hF, hc⟩ := mem_SB_iff.1 F.2
  have hK : IsCompact (Prod.snd '' tsupport (F : A × B → ℂ)) := hc.isCompact.image continuous_snd
  have hopen : IsOpen {p : A × B | (F : A × B → ℂ) p = (F : A × B → ℂ) (a₀, p.2)} := by
    have h2 : IsLocallyConstant
        (fun p : A × B => (F : A × B → ℂ) p - (F : A × B → ℂ) (a₀, p.2)) :=
      hF.sub (hF.comp_continuous (by fun_prop))
    have h3 := h2.isOpen_fiber 0
    simpa [Set.preimage, sub_eq_zero] using h3
  obtain ⟨U, V, hU, -, haU, hKV, hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := a₀)) hK
    hopen (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = a₀ := ha
      subst ha'
      rfl)
  filter_upwards [hU.mem_nhds (haU rfl)] with a ha b
  by_cases hb : b ∈ Prod.snd '' tsupport (F : A × B → ℂ)
  · exact hUV (Set.mk_mem_prod ha (hKV hb))
  · have h1 : (a, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    have h2 : (a₀, b) ∉ tsupport (F : A × B → ℂ) := fun h => hb ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem integral_mem_SB : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
    [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B)
    [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B),
    (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  intro A B _ _ _ _ _ _ _ _ _ _ μ _ w _ F
  obtain ⟨-, hc⟩ := mem_SB_iff.1 F.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    filter_upwards [eventually_slice_eq F a₀] with a ha
    simp only [ha]
  · refine HasCompactSupport.intro (hc.isCompact.image continuous_fst) ?_
    intro a ha
    have h0 : ∀ b, (F : A × B → ℂ) (a, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
    simp only [h0, zero_mul, integral_zero]

end GlobalTheory.CompanionTheory.TestFunctionFibreIntegral
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhatStatement
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_integral_mem_schwartzBruhat : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B), (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  first | exact @GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | exact GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | (intros; apply GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.TensInduction
noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

section Tens

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]

theorem tens_mem (a : SB A) (b : SB B) :
    (fun q : A × B => (a : A → ℂ) q.1 * (b : B → ℂ) q.2) ∈ SB (A × B) := by
  have ha := mem_SB_iff.1 a.2
  have hb := mem_SB_iff.1 b.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · exact (ha.1.comp_continuous continuous_fst).mul (hb.1.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro (IsCompact.prod ha.2 hb.2) ?_
    intro q hq
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

def tens (a : SB A) (b : SB B) : SB (A × B) :=
  ⟨_, tens_mem a b⟩

@[simp]
theorem tens_apply (a : SB A) (b : SB B) (q : A × B) :
    ((tens a b : SB (A × B)) : A × B → ℂ) q = (a : A → ℂ) q.1 * (b : B → ℂ) q.2 :=
  rfl

def tensL (b : SB B) : SB A →ₗ[ℂ] SB (A × B) where
  toFun a := tens a b
  map_add' a a' := Subtype.ext (funext fun q => by
    show ((a : A → ℂ) q.1 + (a' : A → ℂ) q.1) * (b : B → ℂ) q.2 = _
    rw [add_mul]; rfl)
  map_smul' c a := Subtype.ext (funext fun q => by
    show (c * (a : A → ℂ) q.1) * (b : B → ℂ) q.2 = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    rw [mul_assoc])

@[simp]
theorem tensL_apply (a : SB A) (b : SB B) : tensL b a = tens a b :=
  rfl

def tensR (a : SB A) : SB B →ₗ[ℂ] SB (A × B) where
  toFun b := tens a b
  map_add' b b' := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * ((b : B → ℂ) q.2 + (b' : B → ℂ) q.2) = _
    rw [mul_add]; rfl)
  map_smul' c b := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * (c * (b : B → ℂ) q.2) = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    ring)

end Tens

theorem span_transfer {A : Type*} [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : SB A →ₗ[ℂ] M) {S : Set (A → ℂ)} (hS : S ⊆ SB A) (N : Submodule ℂ M)
    (hT : ∀ F (hF : F ∈ S), T ⟨F, hS hF⟩ ∈ N) (f : SB A)
    (hf : (f : A → ℂ) ∈ Submodule.span ℂ S) : T f ∈ N := by
  have key : Submodule.span ℂ S ≤ (N.comap T).map (SB A).subtype := by
    rw [Submodule.span_le]
    intro F hF
    exact Submodule.mem_map.2 ⟨⟨F, hS hF⟩, hT F hF, rfl⟩
  obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 (key hf)
  have e' : f' = f := Subtype.ext e
  subst e'
  exact hf'

section Prod

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]

theorem tens_induction {M : Type*} [AddCommGroup M] [Module ℂ M] (T : SB (A × B) →ₗ[ℂ] M)
    (N : Submodule ℂ M) (f : SB (A × B))
    (h : ∀ (a : SB A) (b : SB B), (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 →
      (f : A × B → ℂ) q ≠ 0) → T (tens a b) ∈ N) : T f ∈ N := by
  refine span_transfer T ?_ N ?_ f (GlobalTheory.T.schwartzBruhat_prod_span_tensors A B f)
  · rintro F ⟨a, b, -, rfl⟩
    exact tens_mem a b
  · rintro F ⟨a, b, hab, rfl⟩
    exact h a b hab

end Prod

section Fint

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]

theorem fib_integrable (F : SB (A × B)) (a : A) {w : B → ℂ} (hw : Continuous w) :
    Integrable (fun b => (F : A × B → ℂ) (a, b) * w b) μ := by
  have hF := mem_SB_iff.1 F.2
  refine Continuous.integrable_of_hasCompactSupport
    ((hF.1.continuous.comp (Continuous.prodMk_right a)).mul hw) ?_
  refine HasCompactSupport.mul_right (f' := w) ?_
  refine HasCompactSupport.intro (IsCompact.image hF.2 continuous_snd) ?_
  intro b hb
  by_contra h
  exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩

def intB (w : B → ℂ) (hw : Continuous w) : SB (A × B) →ₗ[ℂ] SB A where
  toFun F := ⟨fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ, GlobalTheory.T.partial_integral_mem_schwartzBruhat A B μ w hw F⟩
  map_add' F F' := Subtype.ext (funext fun a => by
    show ∫ b, ((F : A × B → ℂ) (a, b) + (F' : A × B → ℂ) (a, b)) * w b ∂μ =
      (∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) + ∫ b, (F' : A × B → ℂ) (a, b) * w b ∂μ
    simp only [add_mul]
    exact integral_add (fib_integrable μ F a hw) (fib_integrable μ F' a hw))
  map_smul' c F := Subtype.ext (funext fun a => by
    show ∫ b, (c * (F : A × B → ℂ) (a, b)) * w b ∂μ = c * ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _)

theorem intB_tens (w : B → ℂ) (hw : Continuous w) (a : SB A) (b : SB B) :
    intB μ w hw (tens a b) = (∫ y, (b : B → ℂ) y * w y ∂μ) • a := by
  apply Subtype.ext
  funext x
  show ∫ y, ((a : A → ℂ) x * (b : B → ℂ) y) * w y ∂μ = (∫ y, (b : B → ℂ) y * w y ∂μ) * (a : A → ℂ) x
  simp only [mul_assoc]
  rw [integral_const_mul, mul_comm]

end Fint

section Factor

variable {A : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A]
  {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

def rtr (k : K) : SB (A × K) →ₗ[ℂ] SB (A × K) :=
  pullHomeo ((Homeomorph.refl A).prodCongr (Homeomorph.mulRight k))

theorem factor_intB (uK : IsUnimod K) (b0 : SB K) (hb0 : ∫ y, (b0 : K → ℂ) y ∂μ = 1)
    (M : SB (A × K) →ₗ[ℂ] ℂ) (hM : ∀ (k : K) (F : SB (A × K)), M (rtr k F) = M F)
    (F : SB (A × K)) :
    M F = M (tens (intB μ (fun _ => (1 : ℂ)) continuous_const F) b0) := by
  have hc : ∀ a : SB A, ∃ c : ℂ, ∀ b : SB K, M (tens a b) = c * ∫ y, (b : K → ℂ) y ∂μ := by
    intro a
    refine GlobalTheory.T.invariant_functional_eq_haar_multiple K uK μ (M ∘ₗ tensR a) ?_
    intro k b
    have e : tens a (pullHomeo (Homeomorph.mulRight k) b) = rtr k (tens a b) := rfl
    show M (tens a (pullHomeo (Homeomorph.mulRight k) b)) = M (tens a b)
    rw [e, hM]
  choose c hc using hc
  let T : SB (A × K) →ₗ[ℂ] ℂ :=
    M - M ∘ₗ tensL b0 ∘ₗ intB μ (fun _ => (1 : ℂ)) continuous_const
  have key : T F ∈ (⊥ : Submodule ℂ ℂ) := by
    refine tens_induction T ⊥ F (fun a b _ => ?_)
    rw [Submodule.mem_bot]
    show M (tens a b) - M (tensL b0 (intB μ (fun _ => (1 : ℂ)) continuous_const (tens a b))) = 0
    rw [intB_tens, LinearMap.map_smul, tensL_apply, LinearMap.map_smul, hc, hc, hb0]
    simp only [mul_one, smul_eq_mul]
    ring
  rw [Submodule.mem_bot] at key
  exact sub_eq_zero.1 key

end Factor

end PositivityTheory.PfBern.Frob
end
end

noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

structure Sec {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) where

  s : G ⧸ H → G
  cont : Continuous s
  sec : ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H}

theorem Sec.inv_smul (σ : Sec H) (c : G ⧸ H) : (σ.s c)⁻¹ • c = ((1 : G) : G ⧸ H) := by
  have hc := σ.sec c
  calc (σ.s c)⁻¹ • c = (σ.s c)⁻¹ • ((σ.s c : G) : G ⧸ H) := by rw [hc]
    _ = ((1 : G) : G ⧸ H) := by rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]

theorem Sec.inv_mul_mem (σ : Sec H) (g : G) : (σ.s (g : G ⧸ H))⁻¹ * g ∈ H := by
  have hg := σ.sec (g : G ⧸ H)
  rwa [QuotientGroup.eq] at hg

variable (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)

def zpart (x : X) : Fib p :=
  ⟨(σ.s (p x))⁻¹ • x, by rw [hp]; exact σ.inv_smul (p x)⟩

include hp in
theorem p_smul_fib (g : G) (z : Fib p) : p (g • z.1) = (g : G ⧸ H) := by
  have hz : p z.1 = ((1 : G) : G ⧸ H) := z.2
  rw [hp, hz, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

variable (hpc : Continuous p)

def triv : X × H ≃ₜ G × Fib p where
  toFun q := (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1))
  invFun r := (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩)
  left_inv q := by
    obtain ⟨x, h⟩ := q
    have e1 : ((σ.s (p x) * h : G) : G ⧸ H) = p x := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, σ.sec]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (σ.s (p x) * h) • (((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x)) = x
      rw [smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
    · show (σ.s ((σ.s (p x) * h : G) : G ⧸ H))⁻¹ * (σ.s (p x) * h) = h
      rw [e1, inv_mul_cancel_left]
  right_inv r := by
    obtain ⟨g, z⟩ := r
    have e2 := p_smul_fib hp g z
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show σ.s (p (g • z.1)) * ((σ.s (g : G ⧸ H))⁻¹ * g) = g
      rw [e2, mul_inv_cancel_left]
    · show (((⟨(σ.s (g : G ⧸ H))⁻¹ * g, σ.inv_mul_mem g⟩ : H)⁻¹ : H) : G) •
          ((σ.s (p (g • z.1)))⁻¹ • (g • z.1)) = z.1
      rw [e2, smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.prodMk
      ((σ.cont.comp (hpc.comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd.inv).smul
      (((σ.cont.comp (hpc.comp continuous_fst)).inv).smul continuous_fst)) _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk
      (((σ.cont.comp (QuotientGroup.continuous_mk.comp continuous_fst)).inv).mul continuous_fst) _

@[simp]
theorem triv_symm_apply (r : G × Fib p) :
    (triv hp σ hpc).symm r = (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩) := rfl

end Triv

section Fap

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure]

def avg [LocallyCompactSpace (Fib p)] : SB (G × Fib p) →ₗ[ℂ] SB X :=
  intB μH (fun _ => (1 : ℂ)) continuous_const ∘ₗ pullHomeo (triv hp σ hpc)

def fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) : SB X :=
  avg hp σ hpc μH (tens α φ)

theorem fap_apply [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (x : X) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) x = ∫ h, (α : G → ℂ) (σ.s (p x) * (h : G)) *
      (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) ∂μH := by
  simp [fap, avg, intB, pullHomeo, tens, triv]

theorem fap_smul [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (g : G) (z : Fib p) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH := by
  rw [fap_apply, p_smul_fib hp g z]
  set s0 := σ.s (g : G ⧸ H)
  set k : H := ⟨s0⁻¹ * g, σ.inv_mul_mem g⟩
  conv_lhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have e1 : s0 * ((k * h : H) : G) = g * h := by
    simp [k, mul_assoc]
  have e2 : fibSmul hp (k * h)⁻¹ (zpart hp σ (g • z.1)) = fibSmul hp h⁻¹ z := by
    apply Subtype.ext
    simp [fibSmul, zpart, k, s0, smul_smul, mul_assoc, p_smul_fib hp g z]
  simp only [e1, e2]

theorem eq_fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (f : SB X)
    (hf : ∀ (g : G) (z : Fib p), (f : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH) :
    f = fap hp σ hpc μH α φ := by
  apply Subtype.ext
  funext x
  have hx : x = σ.s (p x) • (zpart hp σ x).1 := by simp [zpart, ← smul_smul]
  rw [hx, hf, fap_smul]

end Fap

end PositivityTheory.PfBern.Frob
