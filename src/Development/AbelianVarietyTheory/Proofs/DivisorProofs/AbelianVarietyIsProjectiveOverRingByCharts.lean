module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField

def NormChart {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (N₀ : LB B.left) : Prop :=
  ∃ (W V : Over (Sp k)) (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (N : LB (V ⊗ B).left) (n : N.Sec),
    IsFinite π.left ∧ IsOpenImmersion a.left ∧ Nonempty W.left ∧ LocallyOfFiniteType W.hom ∧
    IsAffineOpen U ∧ (U : Set B.left).Nonempty ∧ N.IsLB ∧ LBIso N (N₀.pull (snd V B).left) ∧
    ∀ x : (V ⊗ B).left, x ∈ Out.nonzeroLocus n ↔
      ∀ z : (W ⊗ B).left, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U

end GlobalTheory.ProjField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjField

open GlobalTheory.AbelianProjective

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

abbrev bcProj (X : Over S) : ((Over.pullback f).obj X).left ⟶ X.left := pullback.fst X.hom f

theorem map_left_bcProj {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ bcProj f Y = bcProj f X ≫ g.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem isPullback_bcProj {X Y : Over S} (g : X ⟶ Y) :
    IsPullback (bcProj f X) ((Over.pullback f).map g).left g.left (bcProj f Y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f) ?_ (map_left_bcProj f g).symm
    (IsPullback.of_hasPullback Y.hom f)
  have e : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  rw [e, Over.w]
  exact IsPullback.of_hasPullback X.hom f

def bcProd (X Y : Over S) : ((Over.pullback f).obj X ⊗ (Over.pullback f).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) X Y).left ≫ bcProj f (X ⊗ Y)

theorem bcProd_fst (X Y : Over S) :
    bcProd f X Y ≫ (fst X Y).left = (fst ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f X := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

theorem bcProd_snd (X Y : Over S) :
    bcProd f X Y ≫ (snd X Y).left = (snd ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f Y := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

theorem bcProd_whiskerRight {W V : Over S} (π : W ⟶ V) (X : Over S) :
    ((Over.pullback f).map π ▷ (Over.pullback f).obj X).left ≫ bcProd f V X = bcProd f W X ≫ (π ▷ X).left := by
  rw [bcProd, bcProd, ← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural_left, Over.comp_left,
    Category.assoc, map_left_bcProj, Category.assoc]

end BaseChange

section Group

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem bcSum_eq {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    (fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X) =
      Functor.LaxMonoidal.μ (Over.pullback f) W X ≫ (Over.pullback f).map ((fst W X ≫ a) * snd W X) := by
  rw [Hom.mul_def, Hom.mul_def, Functor.map_comp, Functor.obj.μ_def, ← Functor.Monoidal.lift_μ]
  simp only [← Category.assoc]
  congr 2
  rw [comp_lift, Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd]

theorem bcSum_left {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    ((fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X)).left ≫ bcProj f X =
      bcProd f W X ≫ ((fst W X ≫ a) * snd W X).left := by
  rw [bcSum_eq, Over.comp_left, Category.assoc, map_left_bcProj, bcProd, Category.assoc]

end Group

theorem surjective_spMap (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] : Surjective (spMap (algebraMap K Ω)) := by
  refine ⟨fun x => ?_⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Sp Ω) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

theorem normChart_baseChange : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A],
    IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ →
      NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A)
        (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  intro K Ω _ _ _ A _ _ N₀ hN₀ ⟨W, V, π, a, U, N, n, hπ, ha, hW, hWt, hU, hUne, hN, H, hloc⟩
  have hf := surjective_spMap K Ω
  set f := spMap (algebraMap K Ω)
  have hsurj : ∀ X : Over (Sp K), Function.Surjective (bcProj f X) := fun X =>
    (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.hom f).flip hf).surj
  have sq := bcProd_whiskerRight f π A
  have pb : IsPullback (bcProd f W A) ((Over.pullback f).map π ▷ (Over.pullback f).obj A).left (π ▷ A).left
      (bcProd f V A) := by
    refine IsPullback.of_right (h₁₂ := (fst W A).left) (v₁₃ := π.left) (h₂₂ := (fst V A).left) ?_ sq.symm
      (isPullback_whiskerRight π A)
    rw [bcProd_fst, bcProd_fst]
    exact (isPullback_whiskerRight _ _).paste_horiz (isPullback_bcProj f π)
  refine ⟨(Over.pullback f).obj W, (Over.pullback f).obj V, (Over.pullback f).map π, (Over.pullback f).map a,
    bcProj f A ⁻¹ᵁ U, N.pull (bcProd f V A), GlobalTheory.Cartier.secPull n (bcProd f V A),
    MorphismProperty.of_isPullback (isPullback_bcProj f π) hπ,
    MorphismProperty.of_isPullback (isPullback_bcProj f a) ha, ?_, ?_, ?_, ?_, LB.isLB_pull hN _, ?_, ?_⟩
  · obtain ⟨w⟩ := hW
    obtain ⟨w', -⟩ := hsurj W w
    exact ⟨w'⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback W.hom f) hWt
  · have : IsAffineHom (bcProj f A) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback A.hom f).flip inferInstance
    exact hU.preimage _
  · obtain ⟨u, hu⟩ := hUne
    obtain ⟨u', rfl⟩ := hsurj A u
    exact ⟨u', hu⟩
  · let r := bcProd f V A
    let b := (snd V A).left
    let d := bcProj f A
    let c := (snd ((Over.pullback f).obj V) ((Over.pullback f).obj A)).left
    change LBIso (N.pull r) ((N₀.pull d).pull c)
    refine LBIso.trans (LB.isLB_pull hN r) (LB.isLB_pull (LB.isLB_pull hN₀ b) r)
      (LB.isLB_pull (LB.isLB_pull hN₀ d) c) ?_ ?_
    · obtain ⟨w, hw⟩ := H
      exact ⟨GlobalTheory.lbIsoPull w r, ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_isGen w hw _ _⟩
    · exact GlobalTheory.FiniteAmple.lbIso_pull_pull b hN₀ (bcProd_snd f V A)
  · intro x'
    rw [GlobalTheory.Cartier.nonzeroLocus_secPull]
    change bcProd f V A x' ∈ Out.nonzeroLocus n ↔ _
    rw [hloc]
    constructor
    · intro h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]
      refine h _ ?_
      rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hz']
    · intro h z hz
      obtain ⟨z', rfl, hz'⟩ := Scheme.exists_preimage_of_isPullback pb z x' hz
      have h' := h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U at h'
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply] at h'
      exact h'

end GlobalTheory.ProjField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normChartLineBundle_baseChange_field_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ → NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A) (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  first | exact @GlobalTheory.ProjField.normChart_baseChange | exact GlobalTheory.ProjField.normChart_baseChange | (intros; apply GlobalTheory.ProjField.normChart_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField
open GlobalTheory.AbelianProjective

theorem exists_affine_loci_of_normChart : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∀ N₀ : LB B.left, N₀.IsLB → NormChart B N₀ → ∃ (I : Type) (t : I → N₀.Sec), (⨆ i, Out.nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (t i)) := by
  intro Ω _ _ B _ hB N₀ hN₀ ⟨W, V, π, a, U, N, n, hfin, hop, hne, hlft, hU, hUne, hN, H, hn⟩
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨_, t, ?_, fun w => ?_⟩
  · by_contra hne'
    have hc : ((⨆ i, Out.nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne' (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U hUne (Out.nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint Ω) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : Out.nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (Out.nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

theorem exists_normChart : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ N₀ : LB A.left, N₀.IsLB ∧ NormChart A N₀ := by
  intro K _ B _ hB
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (LB.isLB_pull hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (LB.isLB_pull hN' _) (LB.isLB_pull hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  exact ⟨N₀, hN₀, W, V, π, a, U, N, n, hfin, inferInstance, inferInstance, inferInstance, hU, ⟨_, hxU⟩, hN, H, hn⟩

theorem isProjBy_of_cover_baseChange {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (A : Over (Sp K)) [IsProper A.hom]
    {B : Over (Sp Ω)} {φ : B.left ⟶ A.left} (h : IsPullback φ B.hom A.hom (spMap i)) {N₀ : LB A.left} (hN₀ : N₀.IsLB)
    {I : Type} (t : I → (N₀.pull φ).Sec) (hc : ⨆ j, Out.nonzeroLocus (t j) = ⊤)
    (ha : ∀ j, IsAffineOpen (Out.nonzeroLocus (t j))) : GlobalTheory.AbLaw.IsProjBy A.hom := by
  have : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have hN := LB.isLB_pull hN₀ φ
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun j => (Out.nonzeroLocus (t j) : Set B.left))
    (fun j => (Out.nonzeroLocus (t j)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ j, Out.nonzeroLocus (t j) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hamp : GlobalTheory.IsAmpleLB (N₀.pull φ) := GlobalTheory.isAmpleLB_of_cover hN le_rfl
    (fun j : F => GlobalTheory.secToPow (t j.1) 1) (top_unique fun x _ => by
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, hj⟩, ?_⟩
      rw [GlobalTheory.nonzeroLocus_secToPow _ le_rfl]
      exact hx)
    fun j => (GlobalTheory.nonzeroLocus_secToPow (t j.1) le_rfl).symm ▸ ha j.1
  exact GlobalTheory.ProjFinite.isProjBy_of_fieldExtension i h hN₀ hN (GlobalTheory.lbIso_refl hN)
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 hamp)

theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  obtain ⟨N₀, hN₀, hc⟩ := exists_normChart K A hA
  let Ω := AlgebraicClosure K
  let B : Over (Sp Ω) := (Over.pullback (spMap (algebraMap K Ω))).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap (algebraMap K Ω))) B.hom A.hom (spMap (algebraMap K Ω)) :=
    IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨I, t, hcov, ha⟩ := exists_affine_loci_of_normChart Ω B hB _ (LB.isLB_pull hN₀ _) (GlobalTheory.T.normChartLineBundle_baseChange_field_extension K Ω A hA N₀ hN₀ hc)
  exact isProjBy_of_cover_baseChange _ A sqB hN₀ t hcov ha
end GlobalTheory.ProjField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  first | exact @GlobalTheory.ProjField.isProjBy_of_isAbelianScheme | exact GlobalTheory.ProjField.isProjBy_of_isAbelianScheme | (intros; apply GlobalTheory.ProjField.isProjBy_of_isAbelianScheme <;> assumption)
end
