module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimT
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimT
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LinearCodimTwo

open GlobalTheory.ProjSpace GlobalTheory.Adelic

theorem exists_linear_closedImmersion_two_le_ringKrullDim_stalk :
    ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧
      ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧
      ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  intro F _ N
  have h1 : Function.Injective (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := Fin.castSucc_injective _
  have h2 : Function.Injective (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := Fin.castSucc_injective _
  let ℓ₁ : PSpace F N ⟶ PSpace F (N + 1) := linearι F h1
  let ℓ₂ : PSpace F (N + 1) ⟶ PSpace F (N + 2) := linearι F h2
  have linear_str (A B : ℕ) {e : Fin (A + 1) → Fin (B + 1)}
      (he : Function.Injective e) : linearι F he ≫ PSpace.str F B = PSpace.str F A := by
    refine (Proj.mapAffineOpenCover (killHom F he)
      (irrelevant_le_map_of_surjective _ (killHom_surjective F he))).openCover.hom_ext _ _ fun s => ?_
    have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin (B + 1)) F) (hs : s ∈ grading F B d),
        Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ linearι F he ≫ PSpace.str F B =
          Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ PSpace.str F A := by
      intro d hd s hs
      rw [linearι, Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, PSpace.str, Proj.awayι_toSpecZero_assoc,
        Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
      refine (congrArg HomogeneousLocalization.val (HomogeneousLocalization.Away.map_mk (killHom F he) s hs 0 (MvPolynomial.C r)
        ((zero_smul ℕ d).symm ▸ MvPolynomial.isHomogeneous_C _ r))).trans ?_
      rw [HomogeneousLocalization.Away.val_mk]
      exact congrArg (Localization.mk · _) (MvPolynomial.killCompl_C he r)
    exact key _ s.1.2 _ s.2.2
  refine ⟨ℓ₁ ≫ ℓ₂, inferInstance, by rw [Category.assoc, linear_str _ _ h2, linear_str _ _ h1], fun y => ?_⟩
  have last1 : Fin.last (N + 1) ∉ Set.range (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have last2 : Fin.last (N + 2) ∉ Set.range (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have n1 : ℓ₁ y ∉ chart F (N + 1) (Fin.last (N + 1)) := fun h => by
    have : y ∈ ℓ₁ ⁻¹ᵁ chart F (N + 1) (Fin.last (N + 1)) := h
    rw [linearι_preimage_chart_of_notMem F h1 last1] at this
    exact this
  have n2 (z : PSpace F (N + 1)) : ℓ₂ z ∉ chart F (N + 2) (Fin.last (N + 2)) := fun h => by
    have : z ∈ ℓ₂ ⁻¹ᵁ chart F (N + 2) (Fin.last (N + 2)) := h
    rw [linearι_preimage_chart_of_notMem F h2 last2] at this
    exact this
  have s1 : projSys.gen F (N + 1) ⤳ ℓ₁ y :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₁ y).asHomogeneousIdeal from bot_le))
  have s2 : projSys.gen F (N + 2) ⤳ ℓ₂ (projSys.gen F (N + 1)) :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₂ (projSys.gen F (N + 1))).asHomogeneousIdeal from bot_le))
  have lt1 : ℓ₂ (ℓ₁ y) < ℓ₂ (projSys.gen F (N + 1)) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 (s1.map ℓ₂.continuous)) fun h => ?_
    have := ℓ₂.isClosedEmbedding.injective ((Scheme.le_iff_specializes.1 h).antisymm (s1.map ℓ₂.continuous)).eq
    exact n1 (this ▸ projSys.gen_mem F (N + 1) (Fin.last (N + 1)))
  have lt2 : ℓ₂ (projSys.gen F (N + 1)) < projSys.gen F (N + 2) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 s2) fun h => ?_
    have e : ℓ₂ (projSys.gen F (N + 1)) = projSys.gen F (N + 2) := ((Scheme.le_iff_specializes.1 h).antisymm s2).eq
    exact n2 _ (by rw [e]; exact projSys.gen_mem F (N + 2) (Fin.last (N + 2)))
  have hc : (2 : ℕ∞) ≤ Order.coheight (ℓ₂ (ℓ₁ y)) := by
    have a := Order.coheight_add_one_le lt1
    have b := Order.coheight_add_one_le lt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (projSys.gen F (N + 2)) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight (ℓ₂ (projSys.gen F (N + 1))) + 1 := by gcongr
      _ ≤ _ := a
  rw [Scheme.Hom.comp_apply, ringKrullDim_stalk_eq_coheight]
  have := WithBot.coe_le_coe.2 hc
  simpa using this

end GlobalTheory.LinearCodimTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimTStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo : ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧ ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧ ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  first | exact @GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | exact GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | (intros; apply GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartier
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

noncomputable section
namespace GlobalTheory.NotCartier

theorem ringKrullDim_stalk_le_one {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  haveI := IsLocallyNoetherian.component_noetherian V
  have hV : IsAffineOpen V.1 := V.2
  let p := hV.primeIdealOf ⟨x, hxV⟩
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal := by
    intro q
    have hqV : hV.fromSpec q ∈ V.1 := (Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hqV]
    change q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _
    rw [hV.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes := by
    refine ⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩
    let y : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hsp : hV.fromSpec y ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous
      rwa [hp] at this
    have hyx : hV.fromSpec y = hV.fromSpec p := (hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm
    have := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)
    exact le_of_eq this.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem

end GlobalTheory.NotCartier

namespace GlobalTheory.NotCartier

theorem ker_ne_bot_and_not_effCartier : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  intro W Y _ _ i _ hdim
  set y := i (genericPoint W) with hy
  have hsub : (i.ker.support : Set Y) ⊆ closure {y} := by
    rw [Scheme.Hom.support_ker]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure {genericPoint W} := by
      rw [(genericPoint_spec W).def]; trivial
    exact specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)
  have hyS : y ∈ i.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure ⟨_, rfl⟩
  have hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y := fun z hz hzy =>
    (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq
  have hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1 := fun h => by
    have := hdim.trans h
    exact absurd this (by decide)
  refine ⟨fun hbot => ?_, fun U hyU hC => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)
    rw [hbot, Scheme.IdealSheafData.ideal_bot]
    exact bot_isPrincipal
  · let x : U.toScheme := ⟨y, hyU⟩
    obtain ⟨V, f, hxV, -, hf⟩ := hC x
    have hxS : x ∈ (i.ker.comap U.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hyS
    have hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x := by
      intro z hz hzx
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))
    have h1 := ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv] at h1
    exact hlt h1

end GlobalTheory.NotCartier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartierStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  first | exact @GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | exact GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | (intros; apply GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGeneric
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem isIso_restrict_of_closedImmersion_near_generic :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  intro W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw
  obtain ⟨w', hw'⟩ := hw
  refine ⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩
  have hi : IsClosedImmersion (i ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U
  have hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _
  have h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U) := by
    rw [morphismRestrict_comp]
    have hs : IsClosedImmersion (s₁ ∣_ U) := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hc hs
  have h2 : IsClosedImmersion ((h ≫ i) ∣_ U) := by
    rw [hcomm]; exact h1
  rw [morphismRestrict_comp] at h2
  have h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U)) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2
  have hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    show h w' ∈ i ⁻¹ᵁ U
    rw [hw']; exact hη
  have h4 : Surjective (h ∣_ (i ⁻¹ᵁ U)) := by
    constructor
    intro x
    have hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U))) := (h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range
    let p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme) := ⟨w', hw'U⟩
    have hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W := by
      rw [morphismRestrict_base_coe]; exact hw'
    have hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x := by
      rw [← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]
      have : (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W := hp
      rw [this]
      exact (genericPoint_spec W).specializes (Set.mem_univ _)
    exact hsp.mem_closed hcl ⟨p, rfl⟩
  exact isIso_of_isClosedImmersion_of_surjective _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGenericStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem : ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W) (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ → i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) → ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  first | exact @GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | exact GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | (intros; apply GlobalTheory.isIso_restrict_of_closedImmersion_near_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeets
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SeqFirst

theorem isIso_restrict_of_le {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1

theorem exists_preimage {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {y : Y} (hy : y ∈ U) :
    ∃ x ∈ s ⁻¹ᵁ U, s x = y := by
  obtain ⟨z, hz⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨z.1, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [← morphismRestrict_base_coe]
  exact this

theorem injOn {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {a b : X}
    (ha : a ∈ s ⁻¹ᵁ U) (hb : b ∈ s ⁻¹ᵁ U) (h : s a = s b) : a = b := by
  obtain ⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b := ⟨⟨b, hb⟩, rfl⟩
  have : (s ∣_ U) za = (s ∣_ U) zb :=
    Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))
  exact congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)

theorem isOpen_image {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {A : Set X}
    (hA : IsOpen A) : IsOpen (s '' (A ∩ s ⁻¹ᵁ U)) := by
  have h1 : IsOpenMap (fun z : (s ⁻¹ᵁ U) => s z.1) := by
    have : (fun z : (s ⁻¹ᵁ U) => s z.1) = (fun w : U => w.1) ∘ (s ∣_ U) := by
      funext z; exact (morphismRestrict_base_coe s U z).symm
    rw [this]
    exact U.isOpenEmbedding'.isOpenMap.comp (s ∣_ U).homeomorph.isOpenMap
  have h2 : s '' (A ∩ s ⁻¹ᵁ U) = (fun z : (s ⁻¹ᵁ U) => s z.1) '' ((fun z : (s ⁻¹ᵁ U) => z.1) ⁻¹' A) := by
    ext y; constructor
    · rintro ⟨x, ⟨hxA, hxU⟩, rfl⟩; exact ⟨⟨x, hxU⟩, hxA, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.1, ⟨hz, z.2⟩, rfl⟩
  rw [h2]
  exact h1 _ (hA.preimage continuous_subtype_val)

end GlobalTheory.SeqFirst


open GlobalTheory.SeqFirst in
theorem GlobalTheory.isIso_near_or_centre_meets : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  intro S Y f B y Y' s h
  induction h with
  | id => exact Or.inl ⟨⊤, trivial, inferInstance⟩
  | @step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih =>
    rcases ih with ⟨U, hyU, hU⟩ | hr
    · obtain ⟨y', hy'U, hy'⟩ := exists_preimage s hyU
      by_cases hJ : y' ∈ J.support
      · exact Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩
      · left
        have hA : IsOpen ((J.support : Set Y₁)ᶜ) := J.support.isClosed.isOpen_compl
        let V : Y.Opens := ⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩
        have hVU : V ≤ U := by
          rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
        have hyV : y ∈ V := ⟨y', ⟨hJ, hy'U⟩, hy'⟩
        refine ⟨V, hyV, ?_⟩
        have : IsIso (s ∣_ V) := isIso_restrict_of_le s hVU
        have hπ : IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
          refine Principalise.isIso_restrict_of_blowup h₃ _ ?_
          intro x hx hxJ
          have hxU : x ∈ s ⁻¹ᵁ U := hVU hx
          obtain ⟨w, ⟨hwA, hwU⟩, hw⟩ := (hx : s x ∈ V)
          exact hwA (injOn s hwU hxU hw ▸ hxJ)
        rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' hπ this
    · right; exact hr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeetsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  first | exact @GlobalTheory.isIso_near_or_centre_meets | exact GlobalTheory.isIso_near_or_centre_meets | (intros; apply GlobalTheory.isIso_near_or_centre_meets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.WeakRes

theorem isProjOver_comp_closed {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem isProjOver_seq {F : Type} [Field F] {Y Y' : Scheme.{0}} (f : Y ⟶ Sp F) {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) (hf : IsProjOver f) : IsProjOver (s ≫ f) := by
  induction h with
  | id => simpa using hf
  | @step Y₁ Y₂ s J π _ _ _ hb ih =>
    obtain ⟨X', b, hb', hproj, -⟩ := ProjBlowup.exists_blowup (s ≫ f) ih J
    obtain ⟨e, he, heb⟩ := ProjBlowup.exists_iso_of_blowup J π b hb hb'
    rw [← heb, Category.assoc]
    exact isProjOver_comp_closed e hproj


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem weak_resolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  intro hP F _ _ W _ p n hp hdim
  obtain ⟨N, i₀, hi₀, hi₀p⟩ := hp
  obtain ⟨ℓ, hℓ, hℓs, hℓd⟩ := GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo F N
  let i := i₀ ≫ ℓ
  let f := PSpace.str F (N + 2)
  have hif : i ≫ f = p := by simp [i, f, hℓs, hi₀p]
  have hsmf : SmoothOfRelativeDimension (N + 2) f := Adelic.smoothOfRelativeDimension_pspace F _
  have : Smooth f := by haveI := hsmf; exact SmoothOfRelativeDimension.smooth (N + 2) f
  have : IsLocallyNoetherian (PSpace F (N + 2)) := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hne, hnc⟩ := GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim i (hℓd _)
  obtain ⟨Y', s, -, -, -, hseq, -, hE, -⟩ := hP F (N + 2) _ f inferInstance hsmf
    (ProjSpace.isProjOver_pspace_str F _) i.ker hne
  rcases GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over f _ (i (genericPoint W)) s hseq with ⟨U, hU, hiso⟩ |
    ⟨Y₁, s₁, J, U, y₁, hseq₁, hsm, hJB, hU, hiso, hy₁, hs₁⟩
  · exact (hnc U hU (GlobalTheory.T.effCartier_comap_of_isIso_restrict_open s _ U hiso hE)).elim
  · obtain ⟨z, hz⟩ : ∃ z, J.subschemeι z = y₁ := by
      rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]; exact hy₁
    obtain ⟨W', j, hjc, hjo, hW', w', rfl⟩ := GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' F J.subscheme (J.subschemeι ≫ s₁ ≫ f) hsm z
    have hg : ∀ w, (j ≫ J.subschemeι ≫ s₁) w ∈ i.ker.support := fun w =>
      hJB (Scheme.IdealSheafData.range_subschemeι J ▸ Set.mem_range_self _)
    have : IsReduced W' := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support i (j ≫ J.subschemeι ≫ s₁) hg
    have hw' : h w' = genericPoint W := by
      apply i.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hh]
      simp [hz, hs₁]
    obtain ⟨U', hU'ne, hU'iso⟩ := GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem i h (j ≫ J.subschemeι) s₁ U hiso (by rw [hh]; simp)
      hU ⟨w', hw'⟩
    have hq : h ≫ p = j ≫ J.subschemeι ≫ s₁ ≫ f := by rw [← hif, reassoc_of% hh]
    have : Smooth (j ≫ J.subschemeι ≫ s₁ ≫ f) := by
      have := hsm; infer_instance
    have hpft : LocallyOfFiniteType p := by rw [← hif]; infer_instance
    have hd := GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' F W W' p (h ≫ p) h hpft (by rw [hq]; infer_instance) rfl U' hU'ne hU'iso
    refine ⟨W', h, U', hW', ?_, ?_, hU'ne, hU'iso⟩
    · rw [hq]; exact GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F W' _ n inferInstance (hd.trans hdim)
    · rw [hq, ← Category.assoc]
      exact isProjOver_comp_closed _ (isProjOver_seq f hseq₁ (ProjSpace.isProjOver_pspace_str F _))

end GlobalTheory.WeakRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_resolution_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n → ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  first | exact @GlobalTheory.WeakRes.weak_resolution | exact GlobalTheory.WeakRes.weak_resolution | (intros; apply GlobalTheory.WeakRes.weak_resolution <;> assumption)
end
