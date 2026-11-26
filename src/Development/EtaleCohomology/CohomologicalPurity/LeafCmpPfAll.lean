module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPf
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

def LeafCmpNb : Prop := ∀ (X : Scheme.{0}) (B B₀ : Type) [CommRing B] [CommRing B₀] (w : Spec (CommRingCat.of B) ⟶ X)
  (w₀ : Spec (CommRingCat.of B₀) ⟶ X), IsOpenImmersion w₀ → ∀ y, w y ∈ Set.range w₀ →
  ∃ (C : Type) (_ : CommRing C) (φ : B →+* C) (ψ : B₀ →+* C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ w = Spec.map (CommRingCat.ofHom ψ) ≫ w₀

def LeafCmpId : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C),
  Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w → F.I.map φ = F₀.I.map ψ

theorem spec_comp_ofHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

theorem LeafCmp_of (hMat : LeafMat) (hNb : LeafCmpNb) (hId : LeafCmpId) : LeafCmp := by
  intro d P F F₀ h₀ y hy
  obtain ⟨C, _, φ, ψ, ho, ⟨z, rfl⟩, e⟩ := hNb P.X F.B F₀.B F.w F₀.w h₀ y hy
  have hI := hId d P F F₀ C φ ψ e
  obtain ⟨M, hdet, hM⟩ := hMat d C (ψ ∘ F₀.x) (φ ∘ F.x)
    (by rw [span_comp, span_comp, F.hx, F₀.hx, hI]) z
  let g : C := M.det
  let l : C →+* Localization.Away g := algebraMap C (Localization.Away g)
  have hl : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) g
  refine ⟨Localization.Away g, inferInstance, l.comp φ, l.comp ψ, M.map l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_comp_ofHom φ l]; infer_instance
  · have hr : z ∈ Set.range (PrimeSpectrum.comap l) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hdet
    obtain ⟨z', hz'⟩ := hr
    refine ⟨show Spec (CommRingCat.of (Localization.Away g)) from z', ?_⟩
    rw [spec_comp_ofHom φ l]
    show (Spec.map (CommRingCat.ofHom φ)) ((Spec.map (CommRingCat.ofHom l)) z') = _
    exact congrArg (Spec.map (CommRingCat.ofHom φ)) hz'
  · rw [spec_comp_ofHom φ l, spec_comp_ofHom ψ l, Category.assoc, Category.assoc, e]
  · rw [← Ideal.map_map, ← Ideal.map_map, hI]
  · change IsUnit (l.mapMatrix M).det
    rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit g
  · funext j
    change l (φ (F.x j)) = _
    rw [show φ (F.x j) = (φ ∘ F.x) j from rfl, hM, RingHom.map_mulVec]
    rfl

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfId
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_map_of {d : ℕ} {P : SP d} (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C)
    (e : Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w) : F.I.map φ ≤ F₀.I.map ψ := by
  let J := F₀.I.map ψ
  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  let ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J := Ideal.Quotient.lift F₀.I (π.comp ψ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))
  have hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ := RingHom.ext fun a => rfl
  have hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w =
      (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι := by
    rw [Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc,
      ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]
  let t := F.cart.lift _ _ hw
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) =
      Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) := F.cart.lift_fst _ _ _
  let τ : F.B ⧸ F.I →+* C ⧸ J := (Spec.preimage t).hom
  have h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) =
      Spec.map (CommRingCat.ofHom (π.comp φ)) := by
    rw [spec_comp_ofHom, spec_comp_ofHom, ← ht]
    congr 1
    exact Spec.map_preimage t
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (π.comp φ) a = 0
  rw [← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem LeafCmpId_pf : LeafCmpId := fun _ _ F F₀ C _ φ ψ e =>
  le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfNb
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmpNb_pf : LeafCmpNb := by
  intro X B B₀ _ _ w w₀ h₀ y hy
  let W : (Spec (CommRingCat.of B)).Opens := w ⁻¹ᵁ w₀.opensRange
  have hs : IsOpen (X := PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2
  have hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B))) := hy
  obtain ⟨_, ⟨g, rfl⟩, hyg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs
  let l : B →+* Localization.Away g := algebraMap B (Localization.Away g)
  have hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀ := by
    rintro _ ⟨t, rfl⟩
    have : (Spec.map (CommRingCat.ofHom l)) t ∈ W :=
      hsub (by
        have h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l) := ⟨t, rfl⟩
        rw [hr] at h1; exact h1)
    exact this
  let u := IsOpenImmersion.lift w₀ _ H
  refine ⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩
  · exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g
  · have h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l) := by rw [hr]; exact hyg
    obtain ⟨t, ht⟩ := h2
    exact ⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac w₀ _ H).symm

end LateralTheory.CohomologicalPurity.Cl
end
end

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
