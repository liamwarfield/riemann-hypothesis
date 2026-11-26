module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivA
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace KTypeIsomorphism

variable {ι : Type*} {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem inner_lc (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f f' : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ y₂ f) (Finsupp.linearCombination ℂ y₂ f') =
      inner ℂ (Finsupp.linearCombination ℂ y₁ f) (Finsupp.linearCombination ℂ y₁ f') := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hI]

theorem norm_lc (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ y₂ f‖ = ‖Finsupp.linearCombination ℂ y₁ f‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_lc y₁ y₂ hI]

theorem lc_mem (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) (f : ι →₀ ℂ) :
    Finsupp.linearCombination ℂ y₁ f ∈ C₁ := by
  have h : Finsupp.linearCombination ℂ y₁ f ∈ Submodule.span ℂ (Set.range y₁) := by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ f
  exact Submodule.span_le.2 (Set.range_subset_iff.2 h₁) h

def lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) : (ι →₀ ℂ) →ₗ[ℂ] C₁ :=
  (Finsupp.linearCombination ℂ y₁).codRestrict C₁ (lc_mem y₁ C₁ h₁)

theorem dense_lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure) : DenseRange (lcC y₁ C₁ h₁) := by
  intro x
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  show (x : H₁) ∈ closure (Subtype.val '' Set.range (lcC y₁ C₁ h₁))
  have he : Subtype.val '' Set.range (lcC y₁ C₁ h₁) = (Submodule.span ℂ (Set.range y₁) : Set H₁) := by
    rw [← Set.range_comp, ← Finsupp.range_linearCombination, LinearMap.coe_range]
    rfl
  rw [he, ← Submodule.topologicalClosure_coe]
  exact hd₁ x.2

variable [CompleteSpace H₁] [CompleteSpace H₂]

theorem gns_extend (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j))
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (hC₁ : IsClosed (C₁ : Set H₁)) (hC₂ : IsClosed (C₂ : Set H₂))
    (h₁ : ∀ i, y₁ i ∈ C₁) (h₂ : ∀ i, y₂ i ∈ C₂)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (hd₂ : C₂ ≤ (Submodule.span ℂ (Set.range y₂)).topologicalClosure) :
    ∃ U : C₁ ≃ₗᵢ[ℂ] C₂, ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f := by
  have : CompleteSpace C₁ := hC₁.completeSpace_coe
  have : CompleteSpace C₂ := hC₂.completeSpace_coe
  have hn : ∀ f, ‖lcC y₂ C₂ h₂ ((LinearEquiv.refl ℂ (ι →₀ ℂ)) f)‖ = ‖lcC y₁ C₁ h₁ f‖ := by
    intro f
    show ‖(lcC y₂ C₂ h₂ f : H₂)‖ = ‖(lcC y₁ C₁ h₁ f : H₁)‖
    exact norm_lc y₁ y₂ hI f
  refine ⟨(LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry (lcC y₁ C₁ h₁) (lcC y₂ C₂ h₂)
    (dense_lcC y₁ C₁ h₁ hd₁) (dense_lcC y₂ C₂ h₂ hd₂) hn, ?_⟩
  intro f x hx
  have hx' : x = lcC y₁ C₁ h₁ f := Subtype.ext hx
  subst hx'
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

theorem gns_intertwine (y₁ : ι → H₁) (y₂ : ι → H₂)
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (U : C₁ ≃ₗᵢ[ℂ] C₂) (hU : ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f)
    (T₁ : H₁ →L[ℂ] H₁) (T₂ : H₂ →L[ℂ] H₂) (τ : ι → ι) (hT₁ : ∀ i, T₁ (y₁ i) = y₁ (τ i))
    (hT₂ : ∀ i, T₂ (y₂ i) = y₂ (τ i)) (hTC : ∀ x ∈ C₁, T₁ x ∈ C₁) :
    ∀ x y : C₁, (x : H₁) = T₁ (y : H₁) → ((U x : C₂) : H₂) = T₂ ((U y : C₂) : H₂) := by
  let R : C₁ →L[ℂ] C₁ := (T₁.comp C₁.subtypeL).codRestrict C₁ (fun y => hTC _ y.2)
  let A : C₁ →L[ℂ] H₂ := C₂.subtypeL.comp (U.toLinearIsometry.toContinuousLinearMap.comp R)
  let B : C₁ →L[ℂ] H₂ := T₂.comp (C₂.subtypeL.comp U.toLinearIsometry.toContinuousLinearMap)
  have hAB : (A : C₁ → H₂) = B := by
    refine (dense_lcC y₁ C₁ h₁ hd₁).equalizer A.continuous B.continuous (funext fun f => ?_)
    show ((U (R (lcC y₁ C₁ h₁ f)) : C₂) : H₂) = T₂ ((U (lcC y₁ C₁ h₁ f) : C₂) : H₂)
    have hR : ((R (lcC y₁ C₁ h₁ f) : C₁) : H₁) =
        Finsupp.linearCombination ℂ y₁ (Finsupp.mapDomain τ f) := by
      show T₁ (Finsupp.linearCombination ℂ y₁ f) = _
      rw [Finsupp.linearCombination_mapDomain]
      have := Finsupp.apply_linearCombination ℂ T₁.toLinearMap y₁ f
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, show (⇑T₁ ∘ y₁) = y₁ ∘ τ from funext hT₁]
    rw [hU _ _ hR, hU f _ rfl, Finsupp.linearCombination_mapDomain]
    have := Finsupp.apply_linearCombination ℂ T₂.toLinearMap y₂ f
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, show (⇑T₂ ∘ y₂) = y₂ ∘ τ from funext hT₂]
  intro x y hxy
  have hx : x = R y := Subtype.ext hxy
  subst hx
  exact congrFun hAB y

end KTypeIsomorphism

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

namespace KTypeIsomorphism

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem closGen_le_span (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {ι : Type*} (y : ι → H)
    (hy : ∀ i, y i ∈ closGen E V) (hst : ∀ g ∈ UJset ε, ∀ i, ∃ j, σ g (y i) = y j)
    (hne : ∃ i, y i ≠ 0) :
    closGen E V ≤ (Submodule.span ℂ (Set.range y)).topologicalClosure := by
  have hSc : IsClosed ((Submodule.span ℂ (Set.range y)).topologicalClosure : Set H) :=
    Submodule.isClosed_topologicalClosure _
  have hcl : IsClosed (closGen E V : Set H) := Submodule.isClosed_topologicalClosure _
  have hspan : Submodule.span ℂ (Set.range y) ≤ closGen E V :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hy)
  have hS : (Submodule.span ℂ (Set.range y)).topologicalClosure ≤ closGen E V :=
    Submodule.topologicalClosure_minimal _ hspan hcl
  have hSG : ∀ g ∈ UJset ε, ∀ x ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure,
      σ g x ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure := by
    intro g hg
    have hle : Submodule.span ℂ (Set.range y) ≤
        ((Submodule.span ℂ (Set.range y)).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hst g hg i
      show σ g (y i) ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure
      rw [hj]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩)
    have hc' : IsClosed ((((Submodule.span ℂ (Set.range y)).topologicalClosure).comap
        (σ g : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      hSc.preimage (σ g).continuous
    exact fun x hx => Submodule.topologicalClosure_minimal _ hle hc' hx
  rcases rigid_irred hgap hσ hD hV hc hVK _ hS hSc hSG with h | h
  · exfalso
    obtain ⟨i, hi⟩ := hne
    have : y i ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [h, Submodule.mem_bot] at this
    exact hi this
  · exact h.symm.le

end Gen

section Phi

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem exists_phi {Λ : Fin n → ℝ} (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁)
    (hV₁ : IsKIrrHW ε E₁ Λ V₁) (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    (hV₂ : IsKIrrHW ε E₂ Λ V₂) :
    ∃ φ : V₁ →ₗ[ℂ] V₂,
      (∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
        (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂)) ∧
      (∀ v v' : V₁, inner ℂ (((φ v' : V₂) : D₂) : H₂) (((φ v : V₂) : D₂) : H₂) =
        inner ℂ ((v' : D₁) : H₁) ((v : D₁) : H₁)) := by
  have := hV₁.1
  have := hV₂.1
  obtain ⟨w₁, hw₁V, hw₁0, hw₁⟩ := hV₁.2.2.2
  obtain ⟨w₂, hw₂V, hw₂0, hw₂⟩ := hV₂.2.2.2
  have hu₁ : (⟨w₁, hw₁V⟩ : V₁) ≠ 0 := fun h => hw₁0 (congrArg Subtype.val h)
  have hu₂ : (⟨w₂, hw₂V⟩ : V₂) ≠ 0 := fun h => hw₂0 (congrArg Subtype.val h)
  have hn₁ := norm_smul_inv_norm (𝕜 := ℂ) hu₁
  have hn₂ := norm_smul_inv_norm (𝕜 := ℂ) hu₂
  have hx₁ : ∀ x : V₁, ‖x‖ = 1 → x ≠ 0 := fun x hx h => by
    rw [h, norm_zero] at hx; exact zero_ne_one hx
  have hx₂ : ∀ x : V₂, ‖x‖ = 1 → x ≠ 0 := fun x hx h => by
    rw [h, norm_zero] at hx; exact zero_ne_one hx
  obtain ⟨ψ, hψ⟩ := exists_kIso ε (resE E₁ V₁ hV₁.2.1) (resE E₂ V₂ hV₂.2.1) Λ
    _ _
    (kRel_resE hD₁.glRep) (kRel_resE hD₂.glRep)
    (kUnit_resE (isInfUnitary_of_isDerivedOn hσ₁ hD₁)) (kUnit_resE (isInfUnitary_of_isDerivedOn hσ₂ hD₂))
    (kHighest_smul (kHighest_resE hw₁V hw₁) _) (kHighest_smul (kHighest_resE hw₂V hw₂) _) hn₁ hn₂
    (kSpan_resE_top hV₁.2.2.1 (hx₁ _ hn₁)) (kSpan_resE_top hV₂.2.2.1 (hx₂ _ hn₂))
  exact ⟨ψ.toLinearMap, phi_K hσ₁ hD₁ hV₁.1 hV₁.2.1 hσ₂ hD₂ hV₂.1 hV₂.2.1 ψ.toLinearMap hψ,
    fun v v' => ψ.inner_map_map v' v⟩

end Phi

end KTypeIsomorphism

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem data_unitary_equiv (hgap : StdGap ε lam)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (hV₁0 : V₁ ≠ ⊥)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v) (hV₂0 : V₂ ≠ ⊥) :
    ∃ U : closGen E₁ V₁ ≃ₗᵢ[ℂ] closGen E₂ V₂, ∀ g ∈ UJset ε, ∀ x y : closGen E₁ V₁,
      (x : H₁) = σ₁ g (y : H₁) → ((U x : closGen E₂ V₂) : H₂) = σ₂ g ((U y : closGen E₂ V₂) : H₂) := by
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ₁ hD₁ hV₁ hσ₂ hD₂ hV₂
  have huniv := rigid_universal hσ₁ hD₁ hV₁ hc₁ hVK₁ hσ₂ hD₂ hV₂ hc₂ hVK₂ hgap φ hφK hφI
  let y₁ : ↥(UJset ε) × ↥V₁ → H₁ := fun p => σ₁ p.1.1 ((p.2 : D₁) : H₁)
  let y₂ : ↥(UJset ε) × ↥V₁ → H₂ := fun p => σ₂ p.1.1 (((φ p.2 : V₂) : D₂) : H₂)
  have split : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ∃ h ∈ UJset ε,
      σ₁ g' = (σ₁ g).comp (σ₁ h) ∧ σ₂ g' = (σ₂ g).comp (σ₂ h) := by
    intro g hg g' hg'
    obtain ⟨gi, hgi, hggi⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    have hm : gi * g' ∈ UJset ε := mul_mem_unitaryJ hgi hg'
    have e1 : g * (gi * g') = g' := by rw [← Matrix.mul_assoc, hggi, Matrix.one_mul]
    exact ⟨gi * g', hm, by rw [← hσ₁.1.2 g hg _ hm, e1], by rw [← hσ₂.1.2 g hg _ hm, e1]⟩
  have hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j) := by
    rintro ⟨⟨g, hg⟩, v⟩ ⟨⟨g', hg'⟩, v'⟩
    obtain ⟨h, hh, e₁, e₂⟩ := split g hg g' hg'
    show inner ℂ (σ₂ g (((φ v : V₂) : D₂) : H₂)) (σ₂ g' (((φ v' : V₂) : D₂) : H₂)) =
      inner ℂ (σ₁ g ((v : D₁) : H₁)) (σ₁ g' ((v' : D₁) : H₁))
    rw [e₁, e₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      UnitaryGroupOfForm.inner_map_map' hσ₂ hg, UnitaryGroupOfForm.inner_map_map' hσ₁ hg]
    exact huniv h hh v' v
  have h₁ : ∀ i, y₁ i ∈ closGen E₁ V₁ := fun p =>
    closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ p.1.1 p.1.2 _ (UnitaryGroupOfForm.mem_closGen V₁ (p.2 : D₁) p.2.2)
  have h₂ : ∀ i, y₂ i ∈ closGen E₂ V₂ := fun p =>
    closGen_stable hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ p.1.1 p.1.2 _
      (UnitaryGroupOfForm.mem_closGen V₂ ((φ p.2 : V₂) : D₂) (φ p.2).2)
  have hτ₁ : ∀ g (hg : g ∈ UJset ε) (p : ↥(UJset ε) × ↥V₁),
      σ₁ g (y₁ p) = y₁ (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2) := by
    intro g hg p
    show σ₁ g (σ₁ p.1.1 _) = σ₁ (g * p.1.1) _
    rw [hσ₁.1.2 g hg _ p.1.2]
    rfl
  have hτ₂ : ∀ g (hg : g ∈ UJset ε) (p : ↥(UJset ε) × ↥V₁),
      σ₂ g (y₂ p) = y₂ (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2) := by
    intro g hg p
    show σ₂ g (σ₂ p.1.1 _) = σ₂ (g * p.1.1) _
    rw [hσ₂.1.2 g hg _ p.1.2]
    rfl
  obtain ⟨v₀, hv₀V, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₁0
  have hne₁ : ∃ i, y₁ i ≠ 0 := by
    refine ⟨(⟨1, one_mem_unitaryJ ε⟩, ⟨v₀, hv₀V⟩), ?_⟩
    show σ₁ 1 ((v₀ : D₁) : H₁) ≠ 0
    rw [hσ₁.1.1]
    intro h
    have h' : ((v₀ : D₁) : H₁) = 0 := h
    exact hv₀ (Subtype.ext h')
  have hne₂ : ∃ i, y₂ i ≠ 0 := by
    refine ⟨(⟨1, one_mem_unitaryJ ε⟩, ⟨v₀, hv₀V⟩), ?_⟩
    show σ₂ 1 (((φ ⟨v₀, hv₀V⟩ : V₂) : D₂) : H₂) ≠ 0
    rw [hσ₂.1.1]
    intro h
    have h' : (((φ ⟨v₀, hv₀V⟩ : V₂) : D₂) : H₂) = 0 := h
    have hh := hφI ⟨v₀, hv₀V⟩ ⟨v₀, hv₀V⟩
    rw [h', inner_zero_left] at hh
    exact hv₀ (Subtype.ext (inner_self_eq_zero.1 hh.symm))
  have hd₁ := KTypeIsomorphism.closGen_le_span hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ y₁ h₁
    (fun g hg i => ⟨_, hτ₁ g hg i⟩) hne₁
  have hd₂ := KTypeIsomorphism.closGen_le_span hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ y₂ h₂
    (fun g hg i => ⟨_, hτ₂ g hg i⟩) hne₂
  obtain ⟨U, hU⟩ := KTypeIsomorphism.gns_extend y₁ y₂ hI (closGen E₁ V₁) (closGen E₂ V₂)
    (Submodule.isClosed_topologicalClosure _) (Submodule.isClosed_topologicalClosure _) h₁ h₂ hd₁ hd₂
  refine ⟨U, fun g hg x y hxy => ?_⟩
  exact KTypeIsomorphism.gns_intertwine y₁ y₂ _ _ h₁ hd₁ U hU (σ₁ g) (σ₂ g)
    (fun p => (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2)) (hτ₁ g hg) (hτ₂ g hg)
    (closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ g hg) x y hxy

end ReciprocityTheory.ChartRestriction.DS
