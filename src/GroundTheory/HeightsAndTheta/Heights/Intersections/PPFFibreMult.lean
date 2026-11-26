module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFFibreMultProof

theorem length_quot_map_of_surjective {L L' : Type*} [CommRing L] [CommRing L'] (θ : L →+* L')
    (hθ : Function.Surjective θ) (I : Ideal L) (hker : RingHom.ker θ ≤ I) :
    Module.length L' (L' ⧸ I.map θ) = Module.length L (L ⧸ I) := by
  have hk : RingHom.ker ((Ideal.Quotient.mk (I.map θ)).comp θ) = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hθ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker
  let τ : L ⧸ I ≃+* L' ⧸ I.map θ := (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hθ))
  have e1 : Module.length L (L ⧸ I) = Module.length (L ⧸ I) (L ⧸ I) :=
    Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
  have e2 : Module.length L' (L' ⧸ I.map θ) = Module.length (L' ⧸ I.map θ) (L' ⧸ I.map θ) :=
    Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
  rw [e1, e2, ObjectsChow.VerticalPartMultiplicity.length_self_eq_of_ringEquiv τ]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') (t : MRing ι) :
    baseSubst κ G (rename v t) = C (aeval G.x t) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dite_eq_left h1, dite_eq_left h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h t


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem baseSubst_X_fib (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dite_eq_right q.1.2]


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem exists_baseSubst_mul (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (t : MRing ι) (f : MRing ι'), aeval G.x t ≠ 0 ∧ baseSubst κ G (rename v t) * g = baseSubst κ G f := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨f, t, ht, rfl⟩ := G.gen c
    refine ⟨t, rename v f, ht, ?_⟩
    rw [baseSubst_rename hv, baseSubst_rename hv, ← C_mul]
    congr 1
    field_simp
  | add g₁ g₂ h₁ h₂ =>
    obtain ⟨t₁, f₁, ht₁, e₁⟩ := h₁
    obtain ⟨t₂, f₂, ht₂, e₂⟩ := h₂
    refine ⟨t₁ * t₂, f₁ * rename v t₂ + rename v t₁ * f₂, by rw [map_mul]; exact mul_ne_zero ht₁ ht₂, ?_⟩
    rw [map_mul, map_mul, map_add (f := _), map_mul, map_mul, ← e₁, ← e₂]
    ring
  | mul_X g q h =>
    obtain ⟨t, f, ht, e⟩ := h
    refine ⟨t, f * X ⟨q.1.1, q.2⟩, ht, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fib]
    ring


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isUnit_baseSubst_rename (hv : IsBlockMap κ v) (G : GenFibre v P') {t : MRing ι} (ht : aeval G.x t ≠ 0) :
    IsUnit (baseSubst κ G (rename v t)) := by
  rw [baseSubst_rename hv]
  exact (isUnit_iff_ne_zero.mpr ht).map C


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem ker_baseSubst_le (hv : IsBlockMap κ v) (G : GenFibre v P') : RingHom.ker (baseSubst κ G) ≤ P' := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ha, map_zero]


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem fibreIdeal_eq_map (hv : IsBlockMap κ v) (G : GenFibre v P') :
    ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G = P'.map (baseSubst κ G) := by
  apply le_antisymm
  · intro g hg
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker] at hg
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    have hf : f ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ← e, map_mul, hg, mul_zero]
    rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht), e]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
    exact ha


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem exists_of_mem_map (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι'))
    {g : MRingOver G.Φ (fibreIdx ι' κ)} (hg : g ∈ W.map (baseSubst κ G)) :
    ∃ (t : MRing ι) (w : MRing ι'), aeval G.x t ≠ 0 ∧ w ∈ W ∧
      baseSubst κ G (rename v t) * g = baseSubst κ G w := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨1, w, by simp, hw, by simp⟩
  | zero => exact ⟨1, 0, by simp, W.zero_mem, by simp⟩
  | add g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨t₁, w₁, ht₁, hw₁, e₁⟩ := h₁
    obtain ⟨t₂, w₂, ht₂, hw₂, e₂⟩ := h₂
    refine ⟨t₁ * t₂, w₁ * rename v t₂ + rename v t₁ * w₂, by rw [map_mul]; exact mul_ne_zero ht₁ ht₂,
      W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_left _ hw₂), ?_⟩
    rw [map_mul, map_mul, map_add (f := _), map_mul, map_mul, ← e₁, ← e₂]
    ring
  | smul c g _ h =>
    obtain ⟨t, w, ht, hw, e⟩ := h
    obtain ⟨t', f, ht', e'⟩ := exists_baseSubst_mul hv G c
    refine ⟨t' * t, f * w, by rw [map_mul]; exact mul_ne_zero ht' ht, W.mul_mem_left _ hw, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem comap_fibreOf_and_isPrime (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime]
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') :
    (fibreOf κ G W).comap (baseSubst κ G) = W ∧ (fibreOf κ G W).IsPrime := by
  have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
    intro t ht h
    have h' : t ∈ imageZ v W := h
    rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
    exact ht h'
  have hc : (fibreOf κ G W).comap (baseSubst κ G) = W := by
    refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
    obtain ⟨t, w, ht, hw, e⟩ := exists_of_mem_map hv G W ha
    have hk : rename v t * a - w ∈ W := by
      apply hPW
      apply ker_baseSubst_le hv G
      rw [RingHom.mem_ker, map_sub, map_mul, e, sub_self]
    have hta : rename v t * a ∈ W := by simpa using W.add_mem hk hw
    exact ((Ideal.IsPrime.mem_or_mem ‹_› hta).resolve_left (htW t ht))
  refine ⟨hc, Ideal.isPrime_iff.mpr ⟨fun h => ?_, fun {g₁ g₂} h => ?_⟩⟩
  · have h1 : (1 : MRing ι') ∈ W := by
      rw [← hc, Ideal.mem_comap, map_one, h]
      exact Submodule.mem_top
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one W).mpr h1)
  · obtain ⟨t₁, f₁, ht₁, e₁⟩ := exists_baseSubst_mul hv G g₁
    obtain ⟨t₂, f₂, ht₂, e₂⟩ := exists_baseSubst_mul hv G g₂
    have hf : f₁ * f₂ ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e₁, ← e₂,
        show baseSubst κ G (rename v t₁) * g₁ * (baseSubst κ G (rename v t₂) * g₂) =
          baseSubst κ G (rename v t₁) * baseSubst κ G (rename v t₂) * (g₁ * g₂) by ring]
      exact Ideal.mul_mem_left _ _ h
    rcases Ideal.IsPrime.mem_or_mem ‹_› hf with hf | hf
    · left
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₁), e₁, ← Ideal.mem_comap, hc]
      exact hf
    · right
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₂), e₂, ← Ideal.mem_comap, hc]
      exact hf

end PFFibreMultProof

open PFFibreMultProof

theorem PFFibreMult.proof : PFFibreMult.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s W hv hP' hP hW hH hI
  classical
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨hc, hQ⟩ := comap_fibreOf_and_isPrime hv G W hPW hI
  have := hQ
  set φ := baseSubst κ G with hφ
  have hWQ : W = (fibreOf κ G W).comap φ := hc.symm
  let θ := Localization.localRingHom W (fibreOf κ G W) φ hWQ
  have hcomp : θ.comp (algebraMap (MRing ι') (Localization.AtPrime W)) =
      (algebraMap _ (Localization.AtPrime (fibreOf κ G W))).comp φ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWQ z
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨⟨g, h⟩, rfl⟩ := IsLocalization.mk'_surjective (fibreOf κ G W).primeCompl y
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    obtain ⟨t', f', ht', e'⟩ := exists_baseSubst_mul hv G (h : MRingOver G.Φ (fibreIdx ι' κ))
    have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
      intro t ht h
      have h' : t ∈ imageZ v W := h
      rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
      exact ht h'
    have hf' : f' ∉ W := by
      intro hf'
      apply h.2
      have h1 : φ f' ∈ fibreOf κ G W := by rw [← Ideal.mem_comap, hc]; exact hf'
      rwa [← e', Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht')] at h1
    have hden : rename v t * f' ∈ W.primeCompl := fun hm =>
      (Ideal.IsPrime.mem_or_mem hWp hm).elim (htW t ht) hf'
    refine ⟨IsLocalization.mk' _ (f * rename v t') ⟨rename v t * f', hden⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    rw [← e, ← e']
    ring
  have hker : RingHom.ker θ ≤ (P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W)) := by
    intro z hz
    obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨c, hc'⟩, hc0⟩ := hz
    have hcne : c ≠ 0 := fun h0 => hc' (h0 ▸ (fibreOf κ G W).zero_mem)
    have ha : φ a = 0 := (mul_eq_zero.mp hc0).resolve_left hcne
    have haJ : a ∈ P' ⊔ Ideal.span {s} := Ideal.mem_sup_left (ker_baseSubst_le hv G (RingHom.mem_ker.mpr ha))
    change IsLocalization.mk' (Localization.AtPrime W) a w ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haJ)
  have hJ : (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ⊔ Ideal.span {φ s}).map (algebraMap _ (Localization.AtPrime (fibreOf κ G W))) =
      ((P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W))).map θ := by
    have hJ0 : ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ⊔ Ideal.span {φ s} = (P' ⊔ Ideal.span {s}).map φ := by
      rw [fibreIdeal_eq_map hv G, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rw [hJ0, Ideal.map_map, Ideal.map_map, hcomp]
  unfold multAt
  rw [dite_eq_left hQ, dite_eq_left hWp, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, hJ,
    length_quot_map_of_surjective θ hsurj _ hker]

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurther
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PullbackVanishingOfNullCycle.proof (hElim : PullbackEliminationOfVariable.Statement) : PullbackVanishingOfNullCycle.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' J' n Ψ hv hP' hP hΨ hJ hJP
  obtain ⟨h, a, hha, hhP, hvan⟩ := hElim K ι K' ι' κ v P' J' n hv hP' hP hJ hJP
  have hJh : IsMultiHomogIdeal (Ideal.span {h}) :=
    ⟨{h}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hha⟩, rfl⟩
  have hJhP : ¬ Ideal.span {h} ≤ imageZ v P' := fun hle => hhP (hle (Ideal.subset_span rfl))
  refine measure_mono_null ?_ (projB_null Ψ hP hΨ hJh hJhP)
  rintro y ⟨z', hz'P, hz'J, -, -, -, hΨy⟩
  set w : (Σ k, ι k) → ℂ := fun p => z' (v p) with hw
  have hw1 : (Ψ (segre w) 0)⁻¹ * Ψ (segre w) 0 = 1 := by
    have := congrFun hΨy 0
    simpa [map_smul] using this
  have h0 : Ψ (segre w) 0 ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre w) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre w) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hwP : w ∈ mcPts (imageZ v P') := IntersectionWithSection.comp_mem_mcPts hv hz'P
  have hwh : w ∈ mcPts (Ideal.span {h}) := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hvan z' hz'P hz'J, mul_zero]
  refine ⟨fun p => c p.1 * w p, mcPts_smul hP.2.1.2.1 c hc hwP, mcPts_smul hJh c hc hwh, ?_⟩
  rw [segre_smul, hpc]
  exact hΨy

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem semiLocRing_le_empty {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by
  unfold semiLocRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, fun _ h => h.elim, hu, hwa, rfl⟩

theorem SemilocFinite.proof (h₁ : SemilocIntegral.Statement) (h₂ : LocRingIntClosureFinite.Statement)
    (h₃ : LocRingDimOne.Statement) : SemilocFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  have := hP'.2.1.1
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hN : IsNoetherianRing (locRing (imageZ v P') W) := (h₃ K ι (imageZ v P') s α W hQ.2.1 hs hsQ hW).1
  have hint := h₁ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
  refine ⟨?_, ?_⟩
  · let _ := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    let _ : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    obtain ⟨t, ht⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
    let g : semiLocRing P' (fibreOver v P' W) →ₗ[locRing (imageZ v P') W] FractionRing (MRing ι' ⧸ P') :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : ∀ b, g b ∈ Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P'))) :=
      fun b => ht _ (semiLocRing_le_empty P' _ b.2)
        ((hint.isIntegral b).map_of_comp_eq (RingHom.id (locRing (imageZ v P') W)) (semiLocRing P' (fibreOver v P' W)).subtype
          (RingHom.ext fun _ => rfl))
    have : IsNoetherian (locRing (imageZ v P') W)
        (Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P')))) :=
      isNoetherian_span_of_finite _ t.finite_toSet
    exact Module.Finite.of_injective (g.codRestrict _ hg)
      fun b c hbc => by
        have h := congrArg Subtype.val hbc
        exact Subtype.ext h
  · have := imageZ_isPrime_of_prime v P'
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.val_injective ((fracMapZ v P').injective (congrArg Subtype.val hab))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingIntClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter


open Classical in
theorem subfield_closure_coords_eq_top {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι' ⧸ P') x
  have h : ∀ f : MRing ι', algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' f) ∈
      Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
        algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
          Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eq_intCast C r, map_intCast, map_intCast]; exact intCast_mem _ r
    | add f g hf hg =>
      rw [(Ideal.Quotient.mk P').map_add, (algebraMap _ _).map_add]
      exact add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact mul_mem hf (Subfield.subset_closure (by simp))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (h f) (h g)

theorem LocRingIntClosureFinite.proof (h₁ : LocRingChartLoc.Statement) (h₂ : IntClosureLocFinite.Statement) :
    LocRingIntClosureFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W _hv hP' _hQ _hs _hsQ hW
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  obtain ⟨T, hTA, hloc⟩ := h₁ K ι (imageZ v P') W hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
  obtain ⟨t, ht⟩ := h₂ _ _ (fracMapZ v P') _ (subfield_closure_coords_eq_top P') _ T hTA hloc
  exact ⟨t, fun x _ hx => ht x hx⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenericPointsCount.proof (hGood : GenericPointsAvoidBadLocus.Statement) : GenericPointsCount.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n G i Ψ hv hP' hP hΨ hi
  obtain ⟨D, a, hDa, hDP, hcount⟩ := hGood K ι K' ι' κ v P' n G i hv hP' hP hi
  have hJ : IsMultiHomogIdeal (Ideal.span {D}) :=
    ⟨{D}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hDa⟩, rfl⟩
  have hJP : ¬ Ideal.span {D} ≤ imageZ v P' := fun hle => hDP (hle (Ideal.subset_span rfl))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (projB_null Ψ hP hΨ hJ hJP)] with y hy
  rintro w ⟨z, hz, rfl, hΨz⟩
  have hD : eval z (map (Int.castRingHom ℂ) D) ≠ 0 := by
    intro h0
    refine hy ⟨z, hz, ⟨hz.1, fun f hf => ?_⟩, hΨz⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero]
  have hΨ0 : Ψ (segre z) 0 = 1 := by
    have := congrFun hΨz 0
    simpa using this
  rw [← hcount z hz hD]
  congr 1
  ext O
  constructor
  · rintro ⟨z', hz', rfl, hw⟩
    refine ⟨z', hz', rfl, ?_⟩
    have hμ : Ψ (segre fun p => z' (v p)) 0 ≠ 0 := by
      intro h0
      rw [h0, inv_zero, zero_smul] at hw
      rw [← hw, map_zero] at hΨ0
      exact zero_ne_one hΨ0
    refine sameOrbit_of_segre hz.1 (Ψ (segre fun p => z' (v p)) 0) hμ ?_
    rw [← hw, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · rintro ⟨z', hz', rfl, hs⟩
    refine ⟨z', hz', rfl, ?_⟩
    obtain ⟨c, hc, hcz⟩ := hs
    have hμ : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
    rw [hcz, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, hΨ0, mul_one, smul_smul, inv_mul_cancel₀ hμ,
      one_smul]

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBis
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ArithmeticIntersectionDivisorPushforward.proof (hDeh : regularityDehomogenization_holds.Statement) (hLoc : LocRingDimOne.Statement)
    (hFin : SemilocFinite.Statement) (hRank : SemilocRank.Statement) (hLen : SemilocLength.Statement) :
    ArithmeticIntersectionDivisorPushforward.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE
  have : P'.IsPrime := hP'.2.1.1
  have : (imageZ v P').IsPrime := hP.2.1.1

  obtain ⟨t, ht, htW⟩ := exists_form_notMem hW.2 hW.1.1.1 α
  have ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P'))
      (Ideal.Quotient.mk _ t) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))
  set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) /
    algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy
  have hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) := div_mul_cancel₀ _ ht0
  obtain ⟨hyA, hm⟩ := hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt
  obtain ⟨hNoeth, hLocal, hDim⟩ := hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW
  let _ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) := (locToSemiloc hv P' W).toAlgebra
  obtain ⟨hBf, hBt⟩ := hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW
  have hrk := hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW
  obtain ⟨N, hlen, hN⟩ := hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE
  have hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0 := fun h => by
    have h' : y = 0 := congrArg Subtype.val h
    rw [hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact h'.elim hsP ht0

  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim
  have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0
  have hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ =
      (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞) := by
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)
    rw [hm, locIdeal_eq_span hyA]
    exact (ENat.natCast_toNat hfin).symm
  rw [hlen, hord] at key
  have hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) *
      multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    exact_mod_cast key
  rw [← hN, hNat, ← hrk]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingDimOne.proof (hF : LocRingFrac.Statement) (hN : LocRingNoeth.Statement)
    (hL : LocRingLocal.Statement) (hPow : LocRingPow.Statement) : LocRingDimOne.Statement := by
  classical
  intro K _ ι _ P s a W hP hs hsP hW
  obtain ⟨hPp, hPh, -⟩ := hP
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hNoeth := hN K ι P W hPp hWp hPW hW.2
  refine ⟨hNoeth, hloc, ?_⟩

  choose c hc using hW.2
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) c a
  have htW := AvoidRing.coordProd_not_mem hWp c hc a
  set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
  have htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩
  have hxA : x ∈ locRing P W := Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩
  have hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x' : locRing P W := ⟨x, hxA⟩
  have hxu : ¬ IsUnit x' := fun h => (hunit x' s t a hs ht htW hx).mp h hsW
  have hx0 : x' ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hsP hx

  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyn⟩ :=
      hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv
    have hyn' : y ^ n = x' * ⟨z, hz⟩ := Subtype.ext (by simpa using hyn)
    have hyQ : y ^ n ∈ Q := hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))
    exact hQ.1.mem_of_pow_mem n hyQ
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥ := fun h =>
    hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)
  have h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ChartCongr
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegreeAfterAdjoining.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem VerticalDegreeAfterAdjoining.proof (hA : RankAdjoinFrac.Statement) (hB : FnDegAdjoin.Statement)
    (hT : ChartScalingIndep.Statement) (hC : AdjoinIndepRelfinrank.Statement)
    (hD : FinrankAdjoinRange.Statement) : VerticalDegreeAfterAdjoining.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW _ hc G'

  have hpΩ : ((p : ℕ) : G'.Φ') = 0 := by
    have h : ((p : ℕ) : MRing ι') ∈ RingHom.ker (aeval G'.x' : MRing ι' →ₐ[ℤ] G'.Φ') := G'.genericFibre_ker_target.symm ▸ hp
    rwa [RingHom.mem_ker, map_natCast] at h
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have : CharP G'.Φ p := ((algebraMap G'.Φ G'.Φ').charP_iff_charP p).2 inferInstance
  let : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  let : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

  have hker : RingHom.ker (aeval G'.x' : MRingOver (ZMod p) ι' →ₐ[ZMod p] G'.Φ') =
      W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
    ext g
    obtain ⟨f, rfl⟩ := PointVertical.red_surjective (ι := ι') p g
    have e : aeval G'.x' (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = aeval G'.x' f := by
      rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
    rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, e, ← RingHom.mem_ker, G'.genericFibre_ker_target]
  rw [← hker] at hW hc ⊢
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hc k' (by rw [RingHom.mem_ker, aeval_X, h])
  have hmh := hW.1.2.1

  let y' : (Σ k', ι' k') → G'.Φ' := fun q => G'.x' q / G'.x' ⟨q.1, i' q.1⟩
  let t : K → G'.Φ' := fun k => G'.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ').fieldRange
  let L₀ := IntermediateField.adjoin (ZMod p) (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin (ZMod p) (Set.range y')
  let E := IntermediateField.adjoin (ZMod p) (Set.range t)
  have mono : ∀ {A B : Set G'.Φ'}, A ⊆ B → IntermediateField.adjoin (ZMod p) A ≤ IntermediateField.adjoin (ZMod p) B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G'.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => VerticalDegreeAfterAdjoining.chart_congr G'.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G'.Φ G'.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G'.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G'.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G'.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G'.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G'.compat]
          refine mul_mem hf ?_
          have hq : G'.x' (v q) = y' (v q) * t q.1 := by
            show _ = G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ' (aeval G'.x f / aeval G'.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin (ZMod p)
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩) := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_)
      (((le_sup_right : E ≤ L₀ ⊔ E).trans hL₀E.le).trans le_sup_left)) (sup_le ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hv.2.2.2 q hq
        exact (le_sup_left : Φ₁ ≤ _) (hyv r)
      · exact (le_sup_right : IntermediateField.adjoin _ _ ≤ _)
          (IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩)
    · rw [← hL₀E]
      exact sup_le_sup_right (mono (Set.range_comp_subset_range v y')) E
    · refine (mono ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨q.1.1, q.2⟩, rfl⟩

  have hindep : AlgebraicIndependent L t := (hT (ZMod p) G'.Φ' K' ι' G'.x' i' hx hmh).comp κ hv.1
  refine Eq.trans (hB (ZMod p) G'.Φ' K ι K' ι' v G'.x' i' hx hmh)
    (Eq.trans (hA (ZMod p) G'.Φ' _ _ (Set.range_comp_subset_range v y')) ?_)
  rw [← hC (ZMod p) G'.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep, hD (ZMod p) G'.Φ G'.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

end GroundTheory.Heights₂.Heights.Inter
end
end
