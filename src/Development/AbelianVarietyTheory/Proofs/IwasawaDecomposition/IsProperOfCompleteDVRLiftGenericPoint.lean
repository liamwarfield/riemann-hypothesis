module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TraitProper


open GlobalTheory.ArcProper in
theorem isProper_of_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro k _ _ Y _ s _ _ _ H
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  have : IsLocallyNoetherian ψ.image := LocallyOfFiniteType.isLocallyNoetherian z
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  let η : U.toScheme := ⟨_, hU⟩
  have hη : ∀ u : U.toScheme, η ⤳ u := fun u ↦
    (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))
  have hs : ∀ x : ψ.image, ψ.toImage η ⤳ x := by
    intro x
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)
    rintro _ ⟨u, rfl⟩
    exact specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)
  have key : ∀ x : ψ.image, ∃ i, x ∈ V i := by
    intro x
    by_cases hne : ψ.toImage η = x
    · refine ⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩
      rw [← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]
    obtain ⟨O, _, _, _, c, hc₀, hcx⟩ :=
      exists_complete_discreteValuationRing_of_specializes (hs x) hne
    have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
    have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c)
        (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η := by
      refine Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀
      change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨l, hl, hlη⟩ := ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage
      (FractionRing O) _ η hpt'
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z := by
      rw [Category.assoc, ← hz, reassoc_of% hl]
    obtain ⟨b, hb⟩ := H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Hom.comp_apply, hlη]
      rfl) hls
    have hbs : b ≫ s = c ≫ z := by
      refine ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_
      rw [← Category.assoc, hb, hls]
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint O))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap O (FractionRing O))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint O), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint O) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 (key x)
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

end GlobalTheory.TraitProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.TraitProper.isProper_of_lift_genericPoint | exact GlobalTheory.TraitProper.isProper_of_lift_genericPoint | (intros; apply GlobalTheory.TraitProper.isProper_of_lift_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleStageOfPackage
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

end Lat

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Pts

section Stages

variable {D : D7} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)


end Stages

section Sign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Sign

section Phi

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end Phi

end GlobalTheory.ShFam.Pad.Test
end
end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)


open MonObj in
theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Ext

end GlobalTheory.HTFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.PartSpan

theorem mem_span_rat {K V E : Type} [Field K] [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    {τ : K →+* ℂ} {n : ℕ} (u : (Fin n → K) →ₛₗ[τ] V) (Φ : V →ₗ[ℂ] E) (P : Submodule ℂ E)
    (hinj : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0)
    (hspan : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ P →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ P ∧ u a = y}))
    (x : V) (hx : x ∈ Submodule.span ℂ (Set.range u)) (hP : Φ x ∈ P) :
    x ∈ Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} := by
  have hexp : ∀ a : Fin n → K, u a = ∑ k, τ (a k) • u (Pi.single k 1) := by
    intro a
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ]
  have hsp : ∀ z ∈ Submodule.span ℂ (Set.range u), ∃ c : Fin n → ℂ, z = ∑ k, c k • u (Pi.single k 1) := by
    intro z hz
    have hle : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range fun k => u (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, hexp]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hz)
    exact ⟨c, hc.symm⟩
  obtain ⟨c, rfl⟩ := hsp x hx
  have h1 := hspan c hP
  rw [← Submodule.map_span] at h1
  obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
  have hsS : Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} ≤ Submodule.span ℂ (Set.range u) :=
    Submodule.span_mono (by rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩)
  obtain ⟨d, rfl⟩ := hsp w (hsS hw)
  have hcd : c - d = 0 := by
    apply hinj
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, map_sub, hwe, sub_self]
  rw [sub_eq_zero.1 hcd]
  exact hw


set_option maxHeartbeats 4000000 in
theorem mem_span_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p x hx hW
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have e1 := GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  have h5 := hR.lifts0.1
  let Φ : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H :=
    (Y.mj.eW i).comp (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1))
  let u := ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap).comp
    (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVecLin
  let m : (R.HW i (sg0 D A3.A)).H →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.toCx3 F).W i := Tw.mkL (twAt D.what₂.embLL A3.A.v0) _
  have hcon : ∀ a, m (Φ (u a)) =
      (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) := by
    intro a
    refine Eq.trans ?_ ((R.toCx3 F).tC_cpt_eq F.cr false i t a).symm
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))))) =
      R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) (F.cr.toL (R.toCx3 F).zs false i t a))
    have h3' : F.cr.toL (R.toCx3 F).zs false i t a =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) :=
      (LiftForms.lvlForm_lE (v0 := A3.A.v0) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ a).symm
    rw [hP.phs i, one_smul, e1, h3']
    rfl

  have hsing : ∀ k : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)),
      cpt A3.fam3.base3.v0.embedding (Pi.single k (1 : D.what₂.LL)) = Pi.single k 1 := by
    intro k
    funext j
    by_cases h : j = k
    · subst h; simp [cpt]
    · simp [cpt, Pi.single_apply, h]
  have hsum : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, m (Φ (∑ k, c k • u (Pi.single k 1))) =
      (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) := by
    intro c
    have hc : (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        ∑ k, cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    refine Eq.trans ?_ (congrArg ((R.toCx3 F).tC F.cr false i t) hc).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Eq.trans ?_ (map_sum ((R.toCx3 F).tC F.cr false i t) (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    refine Eq.trans ?_ (map_smul ((R.toCx3 F).tC F.cr false i t) _ _).symm
    exact congrArg (fun z => cj (twAt D.what₂.embLL A3.A.v0) (c k) • z)
      ((hcon (Pi.single k 1)).trans (congrArg ((R.toCx3 F).tC F.cr false i t) (hsing k)))

  have hinj : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0 := by
    intro c hc
    have h0 : (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        0 := by
      rw [← hsum c]
      show Tw.mk _ (Φ _) = 0
      rw [hc]
      rfl
    have h1 := (h5 i t).1 (h0.trans (map_zero _).symm)
    funext k
    have hk := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrFun h1 k)
    rw [Links.cj_cj] at hk
    exact hk.trans (map_zero (cj (twAt D.what₂.embLL A3.A.v0)))
  have hw0 := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
  have hC : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≤
      Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) := by
    have hSpW : Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) ≤
        (R.toCx3 F).Wp i p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      exact ha
    have hle := finrank_le_cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).w0C false i) hw0
      (Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})))
      ((R.toCx3 F).WpK false i p) (fun y hy => by
        obtain ⟨a, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) h5 hR.ratTh i t).2 y
        have hk := (R.toCx3 F).key_lift F.cr false h5 hR.ratTh i t a
        have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMat F.cr false i t *ᵥ a)) ∈
            (R.toCx3 F).Wp i p := hy
        rw [hk, ← hcon a] at hy'
        rw [hk, ← hcon a]
        exact Submodule.subset_span ⟨Φ (u a), ⟨u a, ⟨a, hy', rfl⟩, rfl⟩, rfl⟩)
    rw [(R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 h5 hR.ratTh hR.liftHyp0.h3W hR.partsW i p] at hle
    have heq := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hSpW) hle
    exact heq.symm.le.trans inf_le_left
  have hspan : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ R.Wp3 i p →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y}) := by
    intro c hc
    have hm : m (Φ (∑ k, c k • u (Pi.single k 1))) ∈
        (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      refine ⟨hc, ?_⟩
      rw [← (h5 i t).2]
      exact ⟨_, (hsum c).symm⟩
    have h1 := hC hm
    rw [← Submodule.map_span] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
    have hwe' : w = Φ (∑ k, c k • u (Pi.single k 1)) := hwe
    rw [← hwe']
    exact hw
  exact mem_span_rat u Φ (R.Wp3 i p) hinj hspan x hx hW

end GlobalTheory.Mem.R3.PartSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpanStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  first | exact @GlobalTheory.Mem.R3.PartSpan.mem_span_part | exact GlobalTheory.Mem.R3.PartSpan.mem_span_part | (intros; apply GlobalTheory.Mem.R3.PartSpan.mem_span_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DivisionRationalLift

section Core

variable {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {M W : Type} [NormedAddCommGroup M]
  [InnerProductSpace ℂ M] [AddCommGroup W] [Module ℂ W]


omit [NumberField K] [StarRing K] in
theorem mulVec_map_injective {a b : ℕ} (Θ : Matrix (Fin a) (Fin b) K) (hΘ : Function.Injective Θ.mulVec) :
    Function.Injective (Θ.map σ).mulVec := by
  obtain ⟨g, hg⟩ := Θ.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΘ)
  have hL : LinearMap.toMatrix' g * Θ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hL' : (LinearMap.toMatrix' g).map σ * Θ.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have := congrArg (fun v => (LinearMap.toMatrix' g).map σ *ᵥ v) hxy
  simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
  exact this

theorem orth_ker_inf_range {n d e : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (hsp : Submodule.span ℂ (Set.range fun k => J (Pi.single k 1)) = ⊤)
    (H : Matrix (Fin n) (Fin n) K) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (Formalism.DivisionValues.hform H x y))
    (eM : M →ₗ[ℂ] M) (E : Matrix (Fin n) (Fin n) K) (hop : ∀ x, eM (J x) = J (E *ᵥ x))
    (Zm : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : Formalism.DivisionValues.IsOrthProj H Zm Pr)
    (hEZ : ∀ z, E *ᵥ (Zm *ᵥ z) = Zm *ᵥ z)
    (jW : (Fin e → K) →ₛₗ[σ] W) (hW : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin e) (Fin d) K) (hΘ : Function.Injective Θ.mulVec)
    (θ' : M →ₗ[ℂ] W) (hθ : ∀ x, θ' (J x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ')ᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (Set.range fun k => J (Zm *ᵥ Pi.single k 1)) := by

  classical
  set S := Submodule.span ℂ (J '' Set.range fun z => Zm *ᵥ z) with hS
  set N := Submodule.span ℂ (J '' {y | Pr *ᵥ y = 0}) with hN
  have hSN : ∀ a ∈ S, ∀ b ∈ N, inner ℂ a b = 0 := by
    have hle : N ≤ Sᗮ := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      have hle2 : S ≤ (Submodule.span ℂ {J y})ᗮ := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
        have h0 := GlobalTheory.Mem.LiftForms.hform_orth hP z y
        rw [show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero] at h0
        rw [← h0, map_zero]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle2 hu)
    intro a ha b hb
    exact (Submodule.mem_orthogonal _ _).1 (hle hb) a ha
  have hker : ∀ x, Pr *ᵥ (x - Zm *ᵥ (Pr *ᵥ x)) = 0 := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec, sub_self]
  have htop : ∀ v : M, ∃ a ∈ S, ∃ b ∈ N, a + b = v := by
    intro v
    have hv : v ∈ S ⊔ N := by
      have : (⊤ : Submodule ℂ M) ≤ S ⊔ N := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have hd : J (Pi.single k 1) = J (Zm *ᵥ (Pr *ᵥ Pi.single k 1)) + J (Pi.single k 1 - Zm *ᵥ (Pr *ᵥ Pi.single k 1)) := by
          rw [← map_add (f := _), add_sub_cancel]
        show J (Pi.single k 1) ∈ S ⊔ N
        rw [hd]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩) (Submodule.subset_span ⟨_, hker _, rfl⟩)
      exact this Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    exact ⟨a, ha, b, hb, hab⟩
  have hNk : N ≤ LinearMap.ker θ' := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hθ, show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]
  have hexp : ∀ y : Fin e → K, jW y = ∑ l, σ (y l) • jW (Pi.single l 1) := by
    intro y
    have hz : y = ∑ l, y l • (Pi.single l 1 : Fin e → K) := by
      ext i; simp [Pi.single_apply]
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ]
  have hSk : ∀ a ∈ S, θ' a = 0 → a = 0 := by
    intro a ha h0
    rw [hS, GlobalTheory.Mem.LiftForms.span_range_mulVec, ← Fintype.range_linearCombination] at ha
    obtain ⟨c, rfl⟩ := ha
    have hcomp : θ' (Fintype.linearCombination ℂ (fun k => J (Zm *ᵥ Pi.single k 1)) c) =
        ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.linearCombination_apply, map_sum, map_smul, hθ, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec]
      simp only [hexp (Θ *ᵥ _), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [hcomp] at h0
    have hc0 : (Θ.map σ) *ᵥ c = 0 := funext fun l => Fintype.linearIndependent_iff.1 hW _ h0 l
    have hc : c = 0 := mulVec_map_injective Θ hΘ (hc0.trans (Matrix.mulVec_zero _).symm)
    rw [hc, map_zero]
  have hSZ : S ≤ LinearMap.range eM := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨J (Zm *ᵥ z), by rw [hop, hEZ]⟩
  have hmain : (LinearMap.ker θ')ᗮ = S := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := htop v
      have h1 : inner ℂ b (a + b) = 0 := (Submodule.mem_orthogonal _ _).1 hv b (hNk hb)
      have h2 : inner ℂ b a = 0 := by rw [← inner_conj_symm, hSN a ha b hb, map_zero]
      rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
      rw [h1, add_zero]
      exact ha
    · intro s hs
      rw [Submodule.mem_orthogonal]
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := htop w
      have hθa : θ' a = 0 := by
        have h3 := LinearMap.mem_ker.1 hw
        rwa [map_add, LinearMap.mem_ker.1 (hNk hb), add_zero] at h3
      rw [hSk a ha hθa, zero_add, ← inner_conj_symm, hSN s hs b hb, map_zero]
  rw [hmain, inf_eq_left.2 hSZ, hS, GlobalTheory.Mem.LiftForms.span_range_mulVec]

end Core

section Main

theorem divisionRows_rationalLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  have he : ∀ z, lE D A3.A F.P0 F.ψ0 i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) =
      lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z := fun z => GlobalTheory.Mem.LiftForms.lvlOp_lE hB z
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hf := Y.formsL i t
  exact orth_ker_inf_range ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap) hf.span
    (lH D A3.A F.P0 F.ψ0 i t) hf.inner (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (lE D A3.A F.P0 F.ψ0 i t) hf.op_eq
    _ _ hp he (Z.jW i) (hTh.li i) _ hb.1 (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (hθ i t)

end Main

end GlobalTheory.Mem.R3.DivisionRationalLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZeroSubspaceSpannedByDataZeroSubspaceLiftsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  first | exact @GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | exact GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | (intros; apply GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedFramesParabolicRelation
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram.Comb

theorem sum_shift {r p m : ℕ} (hm : p + m = r) (f : Fin r → ℂ) (h : ∀ c : Fin r, (c : ℕ) < p → f c = 0) :
    ∑ c, f c = ∑ i : Fin m, f ⟨p + i, by omega⟩ := by
  subst hm
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (fun c _ => h _ (by simp)), zero_add]
  rfl

theorem sum_rev {r p : ℕ} (hp : p ≤ r) (f : Fin r → ℂ) (h : ∀ c : Fin r, p ≤ (c : ℕ) → f c = 0) :
    ∑ c, f c = ∑ i : Fin p, f ⟨p - 1 - i, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := Finset.univ) (f := fun i : Fin m => f (Fin.natAdd p i))
    (fun c _ => h _ (by simp)), add_zero, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply Fin.ext
  simp [Fin.val_rev]
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_comb (X : Data E r) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (ρ : E →+* ℂ) (m : ℕ) (hm : ρ ∈ X.Ψ → m = r - X.p0) (hm' : ρ ∉ X.Ψ → m = X.p0)
    (v : Fin r → E) (b : ℕ) (hb : b < m) :
    Formalism.L2.PjFree.perFr X x' v ρ b = ∑ i : Fin m, coef X x x' ρ b i * Formalism.L2.PjFree.perFr X x v ρ i := by
  have hp := X.p0_le
  by_cases h : ρ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨ρ, h⟩).det := (hx _).1.isUnit
    have hb' : X.p0 + b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) ⟨_, hb'⟩ c *
        ((mat x ⟨ρ, h⟩)⁻¹.mulVec (Data.emb ρ v)) c := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨ρ, h⟩) (mat x' ⟨ρ, h⟩)⁻¹ hd, ← mulVec_mulVec]
      rfl
    rw [e1, sum_shift (p := X.p0) (m := m) (by omega) _
      (fun c hc => by rw [h2 _ _ _ (Nat.le_add_right _ _) hc, zero_mul])]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
    congr 1
    · simp only [coef, dif_pos h, ent]
      rw [dif_pos (And.intro hb' hi)]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hi]
  · obtain rfl := hm' h
    have h' : conjEmb ρ ∈ X.Ψ := by_contra fun h' => h ((X.cmType ρ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hb' : X.p0 - 1 - b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) c ⟨_, hb'⟩ *
        hermC (conjEmb ρ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) c) (Data.emb (conjEmb ρ) v) := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
      generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
      change Matrix (Fin r) (Fin r) ℂ at n
      simp only [hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e1]
    refine Eq.trans (sum_rev hp _ fun c hc => ?_) ?_
    · rw [h1 _ _ _ hc (by simp only; omega), zero_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 - 1 - (i : ℕ) < r := by omega
    have hi2 : (i : ℕ) < X.p0 := by have := i.2; omega
    congr 1
    · simp only [coef, dif_neg h, dif_pos h', ent]
      rw [dif_pos (And.intro hi hb')]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hi]

def hmap {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) :
    (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z := fun j => ∑ i : Fin (μ (e j).1), C (e j).1 (e j).2 i * z (e.symm ⟨(e j).1, i⟩)
  map_add' z w := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem hmap_apply {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (z : Fin g → ℂ)
    (τ : T) (b : Fin (μ τ)) : hmap e C z (e.symm ⟨τ, b⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
  have key : ∀ s : Σ τ : T, Fin (μ τ), s = ⟨τ, b⟩ →
      ∑ i : Fin (μ s.1), C s.1 s.2 i * z (e.symm ⟨s.1, i⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
    rintro _ rfl
    rfl
  exact key _ (e.apply_symm_apply _)

theorem hmap_single {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (τ : T)
    (i : Fin (μ τ)) : hmap e C (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ b : Fin (μ τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) := by
  funext j
  obtain ⟨⟨τ', b'⟩, rfl⟩ := e.symm.surjective j
  rw [hmap_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    have hs : ∀ a b : Fin (μ τ'), (Pi.single (e.symm ⟨τ', a⟩) (1 : ℂ) : Fin g → ℂ) (e.symm ⟨τ', b⟩) =
        if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg hab, Pi.single_eq_of_ne (fun h => hab (by simpa using h.symm))]
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [hd.1, ← he 0, map_zero]
  · rw [hd.2 U hU f]
    let hc : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := h.toContinuousLinearEquiv
    have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ hc := by
      funext z
      simp only [Function.comp, hc, LinearEquiv.coe_toContinuousLinearEquiv', he]
    rw [e1, hc.comp_right_fderiv]
    simp [hc]

end GlobalTheory.FramePairGram.Comb


open GlobalTheory.FramePairGram.Comb in
theorem GlobalTheory.FramePairGram.lie_comb_of_block : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.GoodEmb c σ → ∀ (k : U.Comp) (x x' : (U.X k).dom), (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0) → (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Formalism.L2.Pj.IsCombAt (U.un k x').x ((U.un k x').u τ) (fun b => (coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i : CAt σ)) ((U.un k x).u τ i) := by
  intro E _ _ _ r H Dw l Xo c σ U hU hσ k x x' h1 h2 τ i
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, hu, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', hu', -⟩ := hF k x'
  obtain ⟨hEU, hEL, -, -⟩ := GlobalTheory.exp_four_clauses E H Dw l Xo c σ hσ g e F
  let C : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ b i => coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i
  have hL : ∀ a, P' a = hmap e C (P a) := fun a => funext fun j => by
    rw [hP', perFr_comb (U.X k) x.2 h1 h2 _ (Dw.mult (e j).1)
      (fun h => (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega))
      (fun h => (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm) _ _ (e j).2.2]
    simp only [hmap, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, Equiv.apply_symm_apply]
  have hsurj : Function.Surjective (hmap e C) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (hmap e C)).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  let hE : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (hmap e C) ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have hex : ∀ z, (F.ex (ik k) P' (hE z)).left = (F.ex (ik k) P z).left :=
    hEU (ik k) P P' hper hper' (LinearEquiv.refl _ _) hE (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
      (fun a => ⟨0, by simp⟩) hL
  have hd := isDerivAt0_comp (fun z => (F.ex (ik k) P z).left) (fun z => (F.ex (ik k) P' z).left) hE hex (hu τ i)
  have hs : hE (Pi.single (e.symm ⟨τ, i⟩) 1) = ∑ b : Fin (Dw.mult τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) :=
    hmap_single e C τ i
  rw [hs] at hd
  rw [hx']
  exact hEL (ik k) P' hper' _ (fun b => Pi.single (e.symm ⟨τ, b⟩) 1) ((U.un k x').u τ) _ _ (fun b => hu' τ b) hd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
open NumberField IsDedekindDomain

namespace GlobalTheory.PrimeBelow

theorem exists_prime_below {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] (σ : K →+* ℂ) (τ : L →+* ℂ)
    (h : Set.range σ ⊆ Set.range τ) (P : HeightOneSpectrum (𝓞 L)) :
    ∃ p : HeightOneSpectrum (𝓞 K), ∀ (x : 𝓞 K) (y : 𝓞 L), σ (x : K) = τ (y : L) → (x ∈ p.asIdeal ↔ y ∈ P.asIdeal) := by
  classical

  have hmem : ∀ x : K, σ x ∈ τ.range := fun x => RingHom.mem_range.2 (h ⟨x, rfl⟩)
  obtain ⟨ι, hι⟩ : ∃ ι : K →+* L, ∀ x, τ (ι x) = σ x := by
    let e := RingEquiv.ofBijective τ.rangeRestrict
      ⟨fun a b hab => τ.injective (congrArg Subtype.val hab), τ.rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (σ.codRestrict τ.range hmem), fun x => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨σ x, hmem x⟩)
  let φ : 𝓞 K →+* 𝓞 L := RingOfIntegers.mapRingHom ι

  have hne : P.asIdeal.comap φ ≠ ⊥ := by
    have hZ : P.asIdeal.comap (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
      fun hb => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    intro hbot
    have hmK : ((m : 𝓞 K)) ∈ P.asIdeal.comap φ := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hm
    rw [hbot, Ideal.mem_bot] at hmK
    have : ((m : K)) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hmK
      simpa using this
    exact hm0 (by exact_mod_cast this)
  have := P.isPrime
  refine ⟨⟨P.asIdeal.comap φ, Ideal.comap_isPrime φ P.asIdeal, hne⟩, fun x y hxy => ?_⟩
  have hxy' : φ x = y := by
    apply RingOfIntegers.ext
    apply τ.injective
    rw [RingOfIntegers.mapRingHom_apply, hι, hxy]
  show x ∈ P.asIdeal.comap φ ↔ y ∈ P.asIdeal
  rw [Ideal.mem_comap, hxy']

theorem exists_below : ∀ (D D' : Formalism.BasicNotions.D7), Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D)) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D) → ℂ) ⊆ Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D')) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D') → ℂ) → ∀ (v' : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D'))), ∃ (v : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D))), GlobalTheory.Mem.Top.Bl.Below D D' v v' := by
  intro D D' h v'
  obtain ⟨p, hp⟩ := exists_prime_below _ _ h (D'.plEq v')
  refine ⟨D.plEq.symm p, fun x x' hx => ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hp x x' hx

end GlobalTheory.PrimeBelow
end
