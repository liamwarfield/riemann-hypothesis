module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleDiscrete

theorem exists_nhds_zero_principal_eq_zero : ∀ (F : Type) [Field F] [NumberField F], ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F), ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by
  intro F _ _
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos,
    fun v => zero_mem _⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h := h2 v
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1 := fun w => by
    have h := h1 w trivial
    rw [mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe] at h
    exact h
  by_contra h0
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

end GlobalTheory.AdeleDiscrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise

namespace GlobalTheory

open Pointwise in
theorem integrableOn_fundamentalDomain_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  intro G _ _ _ _ _ Γ _ K hK hcov μ hμ 𝓕 h𝓕 f hf hinv
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ g, ‖f g‖ ≤ C := by
    intro g
    obtain ⟨γ, hγ, hγg⟩ := hcov g
    rw [← hinv γ hγ g]
    exact hC _ hγg
  have hcover : 𝓕 ⊆ ⋃ γ : Γ, (γ • K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    refine Set.mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hγx
  have hle : μ 𝓕 ≤ μ K :=
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, (γ • K ∩ 𝓕)) := measure_mono hcover
      _ ≤ ∑' γ : Γ, μ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ K := (h𝓕.measure_eq_tsum K).symm
  exact Measure.integrableOn_of_bounded (hle.trans_lt hK.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) (ae_of_all _ hbound)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompactStatement
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  first | exact @GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | exact GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | (intros; apply GlobalTheory.integrableOn_fundamentalDomain_of_cocompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory

theorem exists_isAddHaarMeasure_isAddFundamentalDomain_preimage :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H), Continuous e → Continuous e.symm → ∀ (Γ : AddSubgroup G) (Λ : AddSubgroup H), (∀ x, e x ∈ Λ ↔ x ∈ Γ) → ∀ (μ : Measure H) (𝓕 : Set H), μ.IsAddHaarMeasure → IsAddFundamentalDomain Λ 𝓕 μ → ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧ ∀ φ : H → ℝ, ∫ w in e ⁻¹' 𝓕, φ (e w) ∂ν = ∫ w in 𝓕, φ w ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ e he hes Γ Λ hΓ μ 𝓕 hμ h𝓕
  let m : G ≃ᵐ H :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  refine ⟨μ.map e.symm, AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he), ?_, ?_⟩
  · let f : Λ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro φ
    exact hmp.setIntegral_preimage_emb m.measurableEmbedding φ 𝓕

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHyperbolicCompletion
namespace GlobalTheory

open Module

theorem _root_.GlobalTheory.exists_hyperbolic_completion :
    ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by
  intro E V _ _ _ _ _ _ h hs hn W hW i e he hee heW hdim
  set m := finrank E W with hm
  let b := Module.finBasis E W
  let w : Fin m → V := fun j => (b j : V)
  have hwW : ∀ j, w j ∈ W := fun j => (b j).2
  let u : Fin i ⊕ Fin m → V := Sum.elim e w
  have hw : LinearIndependent E w := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hu : LinearIndependent E u := by
    refine he.sum_type hw ?_
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hxW : x ∈ W := (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwW j)) hx2
    refine hW x hxW fun y hy => ?_
    have hle : Submodule.span E (Set.range e) ≤ LinearMap.ker (h y) :=
      Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact heW a y hy)
    rw [← hs.eq, show h y x = 0 from hle hx1, map_zero]
  let L : V →ₗ[E] (Fin i ⊕ Fin m → E) := LinearMap.pi fun k => h (u k)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨μ, hμ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hz : ∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k = 0 := by
      refine hn.1 _ fun y => ?_
      have h0 : μ (L y) = 0 := hle (LinearMap.mem_range_self L y)
      rw [LinearMap.pi_apply_eq_sum_univ] at h0
      have h1 : h (∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k) y = ∑ k, L y k • μ fun j => if k = j then (1 : E) else 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, L, LinearMap.pi_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1, h0]
    have hc0 : ∀ k, μ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
      have := Fintype.linearIndependent_iff.mp hu _ hz k
      simpa using this
    apply hμ
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [hc0, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]
  choose g hg using fun a : Fin i => hL fun k => if k = Sum.inl a then (1 : E) else 0
  have hge : ∀ a b, h (e b) (g a) = if b = a then 1 else 0 := fun a b => by
    have := congrFun (hg a) (Sum.inl b)
    simpa [L, u] using this
  have hgw : ∀ a j, h (w j) (g a) = 0 := fun a j => by
    have := congrFun (hg a) (Sum.inr j)
    simpa [L, u] using this
  have hgW : ∀ a, ∀ x ∈ W, h x (g a) = 0 := by
    intro a x hx
    have hx' : x = ∑ j, b.repr ⟨x, hx⟩ j • w j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hgw]
  set f : Fin i → V := fun a => g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c with hf
  have hfa : ∀ a, f a = g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c := fun a => rfl
  have hfe : ∀ a b, h (e b) (f a) = if b = a then 1 else 0 := by
    intro a b
    rw [hfa]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hee, hge]
  have hfe' : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs.eq, hfe]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hfW : ∀ a, ∀ x ∈ W, h x (f a) = 0 := by
    intro a x hx
    rw [hfa]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hgW a x hx, heW _ x hx]
  have hff : ∀ a b, h (f a) (f b) = 0 := by
    intro a b
    have hs' : starRingEnd E (h (g b) (g a)) = h (g a) (g b) := hs.eq (g b) (g a)
    have h1 : h (f a) (f b) = h (f a) (g b) - 2⁻¹ * h (g a) (g b) := by
      conv_lhs => rw [hfa b]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sub, map_sum, hfe']
    rw [h1, hfa a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hge, hs', map_ofNat]
    ring
  let v : Fin i ⊕ (Fin i ⊕ Fin m) → V := Sum.elim f u
  have hu0 : ∀ c k, h (e c) (u k) = 0 := by
    intro c k
    rcases k with d | j
    · exact hee c d
    · show h (e c) (w j) = 0
      rw [← hs.eq, heW c _ (hwW j)]
      simp
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro γ hγ
    simp only [v] at hγ
    rw [Fintype.sum_sum_type] at hγ
    simp only [Sum.elim_inl, Sum.elim_inr] at hγ
    have hfst : ∀ a, γ (Sum.inl a) = 0 := by
      intro a
      have := congrArg (h (e a)) hγ
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_add (f := _), map_sum, hfe, hu0] using this
    have hrest : ∑ k, γ (Sum.inr k) • u k = 0 := by simpa [hfst] using hγ
    intro k
    rcases k with a | k
    · exact hfst a
    · exact Fintype.linearIndependent_iff.mp hu _ hrest k
  have hspan : Submodule.span E (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp; omega)
  refine ⟨f, hff, hfe', hfW, ?_⟩
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases k with a | c | j
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨c, rfl⟩))
  · exact Submodule.mem_sup_left (hwW j)

end GlobalTheory
end
