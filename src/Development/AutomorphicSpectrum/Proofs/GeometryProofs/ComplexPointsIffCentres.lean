module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieB
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_mcPts_iff_exists_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  intro X Ω _ ξ K _ J _ y tie w
  have key := GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie ℂ
  have hval : ∀ g : MvPolynomial (Σ k, J k) ℤ,
      MvPolynomial.aeval w g = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) := by
    intro g
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  constructor
  · rintro ⟨hne, hvan⟩
    obtain ⟨z, ⟨hz, hc⟩, -⟩ := key.1 w
      (fun k => (hne k).imp fun _ h => isUnit_iff_ne_zero.mpr h)
      (fun g hg => by rw [hval]; exact hvan g hg)
    exact ⟨z, hz, hc⟩
  · rintro ⟨z, hz, hc⟩
    refine ⟨fun k => (hc.1 k).imp fun _ h => h.ne_zero, fun f hf => ?_⟩
    rw [← hval]
    exact (key.2.2 z w hz hc).1 f hf

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_iff_centres : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt | exact GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt | (intros; apply GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  have hbase : f.base = g.base := by
    ext q
    exact hb q
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun q hq => ?_
  have hqg : g q ∈ U := hq
  have hqf : f q ∈ U := by rw [hb q]; exact hqg
  have hpf : genPt ξ ⤳ f q := RegAtDom.map_genPt hf ▸ (hall q).map f.continuous
  have hpg : genPt ξ ⤳ g q := RegAtDom.map_genPt hg ▸ (hall q).map g.continuous
  have key : ∀ (a b : X) (_ : a = b) (ha : genPt ξ ⤳ a) (hb : genPt ξ ⤳ b) (h1 : a ∈ U) (h2 : b ∈ U),
      genMap ξ ⟨a, ha⟩ ((X.presheaf.germ U a h1).hom s) = genMap ξ ⟨b, hb⟩ ((X.presheaf.germ U b h2).hom s) := by
    rintro a _ rfl ha hb h1 h2
    rfl
  apply hgen.inj ⟨q, hall q⟩
  have e1 := RegAtDom.genMap_stalkMap hf q (hall q) hpf ((X.presheaf.germ U (f q) hqf).hom s)
  have e2 := RegAtDom.genMap_stalkMap hg q (hall q) hpg ((X.presheaf.germ U (g q) hqg).hom s)
  rw [Scheme.Hom.germ_stalkMap_apply] at e1 e2
  have e3 := key _ _ (hb q) hpf hpg hqf hqg
  rw [← e3, ← e1] at e2
  refine (congrArg (genMap ξ' ⟨q, hall q⟩) ?_).trans e2.symm
  exact TopCat.Presheaf.germ_res_apply X'.presheaf _ q hqg _

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := GlobalTheory.T.chart_unit_basic_open o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end GlobalTheory.CompanionTheory.Ar.ChMorph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dominating_map : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | exact GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

theorem mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hv : ∀ p, (v p).1 = κ p.1) (f : MvPolynomial (Σ k, ι k) ℤ) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv]

theorem imageZ_coord {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) {Ω : Type} [Field Ω] (y : (Σ k, ι' k) → Ω)
    (hκ : Function.Injective κ) (hv : ∀ p, (v p).1 = κ p.1) :
    imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  change mConeMap y (rename v f) = 0 ↔ _
  rw [mConeMap_rename κ v y hv f]
  exact map_eq_zero_iff _ (rename_injective κ hκ)

theorem pullDeg_comp {K K' K'' : Type} (κ : K → K') (κ' : K' → K'')
    (hκ : Function.Injective κ) (hκ' : Function.Injective κ') (a : K → ℤ) :
    pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a) := by
  funext k''
  simp only [pullDeg]
  by_cases h' : ∃ k', κ' k' = k''
  · obtain ⟨k', rfl⟩ := h'
    rw [hκ'.extend_apply]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hκ.extend_apply]
      exact (hκ'.comp hκ).extend_apply a 0 k
    · have h2 : ¬∃ k, (κ' ∘ κ) k = κ' k' := fun ⟨k, hk⟩ => h ⟨k, hκ' hk⟩
      rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h2]
      rfl
  · have h2 : ¬∃ k, (κ' ∘ κ) k = k'' := fun ⟨k, hk⟩ => h' ⟨κ k, hk⟩
    rw [Function.extend_apply' _ _ _ h', Function.extend_apply' _ _ _ h2]

end GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock

namespace GlobalTheory.CompanionTheory.Ar.Cmp


open GlobalTheory.CompanionTheory.Ar.Cmp.JoinBlock in
theorem join_block_maps : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K₁ _ ι₁ _ K₂ _ ι₂ _ Ω y₁ y₂
    refine ⟨⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩, ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      cases h
      rfl
    · rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
    · funext ⟨k, i⟩
      rfl
    · funext ⟨k, i⟩
      rfl
  · intro K _ ι _ K' _ ι' _ κ v Ω _ y h
    exact imageZ_coord κ v y h.1 h.2.2.1
  · intro K _ ι _ K' _ ι' _ K'' _ ι'' _ κ v κ' v' h h'
    obtain ⟨hκ, hv, hc, hs⟩ := h
    obtain ⟨hκ', hv', hc', hs'⟩ := h'
    refine ⟨⟨hκ'.comp hκ, hv'.comp hv, fun p => ?_, ?_⟩, pullDeg_comp κ κ' hκ hκ'⟩
    · simp [hc', hc]
    · rintro q ⟨k, hk⟩
      obtain ⟨q', rfl⟩ := hs' q ⟨κ k, hk⟩
      have h1 : q'.1 = κ k := hκ' ((hc' q').symm.trans hk.symm)
      obtain ⟨p, rfl⟩ := hs q' ⟨k, h1.symm⟩
      exact ⟨p, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_join_inclusions_compat : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | exact GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigProjMemOfFree
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.QuotEig

section Free

variable {K : Type} [Field K] {A : Subring K} {W : Type} [AddCommGroup W] [Module K W]
  {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K W} {Y : Submodule A W} {N : ℕ} {t : Fin N → W}

theorem act_mem_of_free (h : HT.IsFreeOn ρ Y t) (a : 𝓞 E) {y : W} (hy : y ∈ Y) : ρ a y ∈ Y := by
  have key : Y ≤ Y.comap ((ρ a).restrictScalars A) := by
    conv_lhs => rw [h.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change ρ a (ρ (RingOfIntegers.basis E q.2) (t q.1)) ∈ Y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Module.End.mul_apply, ← map_mul, h.2.2,
      ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2), map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(q.1, k), rfl⟩)) _
  exact key hy

theorem eigProj_mem_of_free (h : HT.IsFreeOn ρ Y t) (σ : E →+* K) (hσ : ∀ a : E, σ a ∈ A) {y : W} (hy : y ∈ Y) :
    HT.eigProj ρ σ y ∈ Y := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Y.smul_mem (⟨_, hσ (HT.dualInt E k)⟩ : A) (act_mem_of_free h _ hy)

end Free

section Main

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem fst_eigProj (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (y : V × Module.Dual Ω V) :
    (HT.eigProj 𝓗.ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, 𝓗.act_fst]

theorem mem_L_iff (𝓗 : HodgeLat L ρ bar r) (x : Cpt ξ) {z : V} :
    z ∈ L x ↔ ∃ h ∈ 𝓗.HL x, h.1 = z := by
  have e : L x = (𝓗.HL.map (LinearMap.fst Ω V (Module.Dual Ω V))) x := congrFun 𝓗.map_fst.symm x
  rw [e]
  exact Iff.rfl

end Main

theorem quot_eig : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (x : Cpt ξ), (∀ a : E, σ a ∈ regAt ξ x) → (∀ y, y ∈ 𝓗.quot σ x ↔ y ∈ 𝓗.HL x ∧ y ∈ HT.eigSp 𝓗.ρH σ) ∧ (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) ∧ (𝓗.quot σ x).map ((LinearMap.fst Ω V (Module.Dual Ω V)).restrictScalars (regAt ξ x)) = (L.inter (HT.eigSp ρ σ)) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ x hσ
  obtain ⟨U, hU, t, ht⟩ := 𝓗.free x
  have hfree := ht x hU
  have hstab : ∀ {h}, h ∈ 𝓗.HL x → HT.eigProj 𝓗.ρH σ h ∈ 𝓗.HL x := fun hh =>
    eigProj_mem_of_free hfree σ hσ hh
  refine ⟨fun y => ⟨?_, ?_⟩, fun z hz => ?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hstab hh, HT.LatBasic.eigProj_mem _ _ _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, HT.LatBasic.eigProj_of_mem h2⟩
  · obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
    exact (mem_L_iff 𝓗 x).2 ⟨_, hstab hh, fst_eigProj 𝓗 σ h⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      have e : (HT.eigProj 𝓗.ρH σ h).1 = HT.eigProj ρ σ h.1 := fst_eigProj 𝓗 σ h
      refine ⟨(mem_L_iff 𝓗 x).2 ⟨_, hstab hh, rfl⟩, ?_⟩
      change (HT.eigProj 𝓗.ρH σ h).1 ∈ HT.eigSp ρ σ
      rw [e]
      exact HT.LatBasic.eigProj_mem _ _ _
    · rintro ⟨hz, hz'⟩
      obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
      refine ⟨HT.eigProj 𝓗.ρH σ h, ⟨h, hh, rfl⟩, ?_⟩
      exact (fst_eigProj 𝓗 σ h).trans (HT.LatBasic.eigProj_of_mem hz')

end GlobalTheory.CompanionTheory.Ar.Flat.QuotEig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmooth
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.UnitarySelfGeneration

theorem der_coords {B A R : Type} [CommRing B] [CommRing A] [CommRing R] [Nontrivial R] (c : B →+* A) (g : ℕ)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (u : A →+* R) :
    ∃ d : Fin g → A → R, (∀ i a b, d i (a + b) = d i a + d i b) ∧
      (∀ i a b, d i (a * b) = u a * d i b + u b * d i a) ∧ (∀ i b, d i (c b) = 0) ∧
      (∀ e e' : Fin g → R, (∀ a, ∑ i, e i * d i a = ∑ i, e' i * d i a) → e = e') ∧
      ∀ δ : A → R, (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        (∀ b, δ (c b) = 0) → ∃ e : Fin g → R, ∀ a, ∑ i, e i * d i a = δ a := by
  classical
  let _ := c.toAlgebra
  let _ := u.toAlgebra
  let _ := (u.comp c).toAlgebra
  have : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension g B A := hc
  have : Algebra.IsStandardSmooth B A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Nontrivial A := u.domain_nontrivial
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := B) (S := A) g
  have : Module.Finite A (KaehlerDifferential B A) := inferInstance
  let β : Module.Basis (Fin g) A (KaehlerDifferential B A) :=
    Module.finBasisOfFinrankEq A _ (Module.finrank_eq_of_rank_eq hr)
  have hsm : ∀ (a : A) (r : R), a • r = u a * r := fun a r => Algebra.smul_def a r
  have key : ∀ (e : Fin g → R) (w : KaehlerDifferential B A), ∑ i, e i * u (β.repr w i) = β.constr A e w := by
    intro e w
    rw [Module.Basis.constr_apply_fintype]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, mul_comm]; rfl
  refine ⟨fun i a => u (β.repr (KaehlerDifferential.D B A a) i), fun i a b => by simp, fun i a b => by simp,
    fun i b => ?_, fun e e' h => ?_, fun δ h1 h2 h3 => ?_⟩
  · have : KaehlerDifferential.D B A (c b) = 0 := Derivation.map_algebraMap _ b
    simp [this]
  · have h' : β.constr A e = β.constr A e' := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      simpa [key] using h a
    exact (β.constr A).injective h'
  · let D : Derivation B A R := Derivation.mk'
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          rw [Algebra.smul_def, h2, RingHom.id_apply, Algebra.smul_def]
          have : δ (algebraMap B A b) = 0 := h3 b
          rw [this, mul_zero, add_zero]; rfl }
      (fun a b => by simpa [hsm] using h2 a b)
    refine ⟨fun i => D.liftKaehlerDifferential (β i), fun a => ?_⟩
    rw [key]
    have : β.constr A (fun i => D.liftKaehlerDifferential (β i)) = D.liftKaehlerDifferential :=
      β.ext fun i => by simp
    rw [this, Derivation.liftKaehlerDifferential_comp_D]
    rfl

theorem lie_free : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  intro S G _ g hG R _ _ x E _ _ M
  let t : Spec (CommRingCat.of R) ⟶ G.left := (1 : Over.mk x ⟶ G).left
  obtain ⟨V, hV, U, hU, hq, hUV, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (t (IsLocalRing.closedPoint R))
  have hrange : Set.range t ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_open (t ⁻¹ᵁ U).isOpen hq
  let l := IsOpenImmersion.lift hU.fromSpec t hrange
  have hl : spMap (Spec.preimage l).hom = l := by simp [spMap]
  have h1 : (1 : Over.mk x ⟶ G).left = spMap (Spec.preimage l).hom ≫ hU.fromSpec := by
    rw [hl]; exact (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := der_coords (G.hom.appLE V U hUV).hom g hs (Spec.preimage l).hom
  obtain ⟨M', -⟩ := PositivityTheory.HtPt.Htat.Lie.exists_lieModel (E := Fin g → R) G U V hU hV hUV R x _ h1
    (fun e a => ∑ i, e i * d i a)
    (fun e a b => by simp only [d1, mul_add, Finset.sum_add_distrib])
    (fun e a b => by
      simp only [d2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun e b => by simp only [d3, mul_zero, Finset.sum_const_zero])
    (fun e e' a => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c e a => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _) d4 d5
  obtain ⟨f, -, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv S G R x E (Fin g → R) M M'
  exact ⟨Module.Basis.ofEquivFun f⟩

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.lie_free | exact PositivityTheory.UnitarySelfGeneration.lie_free
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | exact GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializes
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_le_regAt_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 :=
  @PositivityTheory.HtPt.Ma.reg_le_spec

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializesStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_le_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | exact GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPoint
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' hp'
  obtain ⟨c, hc, hreg⟩ := hp'
  haveI : IsLocalRing (regAt ξ' p') := (GlobalTheory.T.regAt_local_order_fraction X' Ω' ξ').1 p'
  let φ : chRing o x c →+* regAt ξ' p' :=
    (i.comp (chRing o x c).val.toRingHom).codRestrict (regAt ξ' p') (fun a => hreg a a.2)
  let P : Ideal (chRing o x c) := (IsLocalRing.maximalIdeal (regAt ξ' p')).comap φ
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p₀, ⟨hin, hP⟩, -⟩ := GlobalTheory.T.chart_prime_existsUnique_point o Ω κ x M c hc P hPp
  have key : ∀ u : chRing o x c, unitAt M.ξ p₀ (u : Ω) ↔ unitAt ξ' p' (i u) := by
    intro u
    have h := hP u
    have h2 : u ∈ P ↔ ¬ unitAt ξ' p' (i u) := by
      change φ u ∈ IsLocalRing.maximalIdeal (regAt ξ' p') ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
      rfl
    tauto
  have hloc := fun (c₁ : κ) (p : Cpt M.ξ) (h : InChart M.ξ x c₁ p) =>
    GlobalTheory.T.regAt_chart_localization o Ω κ x M c₁ p h
  have hch : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := (hloc c p₀ hin).1
  have hdom : ∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have h1 := (key ⟨v, hv⟩).1 hvu
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hreg u hu) h1.2.2
  have hlift : ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a := by
    intro a ha hu'
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have hiu : unitAt ξ' p' (i u) := by
      have h1 : i u = i (u / v) * i v := by rw [← map_mul, div_mul_cancel₀ _ hvu.1]
      rw [h1]
      exact Flat.ZUnit.mul hu' ((key ⟨v, hv⟩).1 hvu)
    have hu0 : unitAt M.ξ p₀ u := (key ⟨u, hu⟩).2 hiu
    rw [div_eq_mul_inv]
    exact Flat.ZUnit.mul hu0 (Flat.ZUnit.inv hvu)
  have hchart : ∀ c₁, x c₁ ≠ 0 → (∀ j, i (x j / x c₁) ∈ regAt ξ' p') → InChart M.ξ x c₁ p₀ := by
    intro c₁ h1 hj
    have hmem : x c₁ / x c ∈ regAt M.ξ p₀ := hch _ (Algebra.subset_adjoin ⟨c₁, rfl⟩)
    have hunit : unitAt ξ' p' (i (x c₁ / x c)) := by
      refine ⟨(map_ne_zero i).2 (div_ne_zero h1 hc), hdom _ hmem, ?_⟩
      rw [← map_inv₀, inv_div]
      exact hj c
    have hu := hlift _ hmem hunit
    refine ⟨h1, fun j => ?_⟩
    have h2 : x j / x c₁ = x j / x c * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [h2]
    exact mul_mem (hch _ (Algebra.subset_adjoin ⟨j, rfl⟩)) hu.2.2
  refine ⟨p₀, ⟨hdom, hlift⟩, ?_, hchart⟩
  intro p hp
  rw [← GlobalTheory.T.regAt_le_iff_specializes o Ω κ x M p p₀]
  obtain ⟨c₁, hc₁⟩ := M.tie.cover p
  have hin₁ := hchart c₁ hc₁.1 (fun j => hp _ (hc₁.2 j))
  intro a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c₁ p hc₁).2 a).1 ha
  have hch₁ := (hloc c₁ p₀ hin₁).1
  have hv' : unitAt M.ξ p₀ v := hlift v (hch₁ v hv)
    ⟨(map_ne_zero i).2 hvu.1, hp v hvu.2.1, by rw [← map_inv₀]; exact hp _ hvu.2.2⟩
  rw [div_eq_mul_inv]
  exact mul_mem (hch₁ u hu) hv'.2.2

end GlobalTheory.CompanionTheory.Ar.Centre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CentreSetDominatingPointStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_set_dominating_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Centre.exists_centre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.PushLoc

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξg : Spec (CommRingCat.of Ω) ⟶ Y} {e : Y ⟶ X}

theorem dominates_id (h : ξg ≫ e = ξ) : Dominates ξg ξ e (RingHom.id Ω) := by
  have h0 : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
  unfold Dominates
  rw [h0, Category.id_comp, h]

def emb (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) : Cpt ξ := ⟨e p.1, hD.specializes p⟩

theorem genMap_stalkMap (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) (s : X.presheaf.stalk (e p.1)) :
    genMap ξg p ((e.stalkMap p.1).hom s) = genMap ξ (emb hD p) s :=
  PullReg.stalkMap_comp_genMap hD p (hD.specializes p) s

theorem regAt_emb [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) :
    regAt ξg p = regAt ξ (emb hD p) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 s
    exact ⟨s', (genMap_stalkMap hD p s').symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, genMap_stalkMap hD p s⟩

theorem isCptGen_of [IsPreimmersion e] (h : ξg ≫ e = ξ) (hg : IsCptGen ξ) : IsCptGen ξg := by
  subst h
  have hD : Dominates ξg (ξg ≫ e) e (RingHom.id Ω) := dominates_id rfl
  refine ⟨?_, fun p => ?_⟩
  · have hb := hg.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb
    have hs := Scheme.Hom.stalkMap_surjective e (ξg (IsLocalRing.closedPoint Ω))
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      have : a' = b' := hb.1 hab
      rw [this]
    · intro c
      obtain ⟨a, rfl⟩ := hb.2 c
      exact ⟨_, rfl⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 a
    obtain ⟨b', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 b
    have h1 := genMap_stalkMap hD p a'
    have h2 := genMap_stalkMap hD p b'
    have : a' = b' := hg.inj (emb hD p) (h1.symm.trans (Eq.trans hab h2))
    rw [this]

theorem isIntegral_congr {R S : Subring Ω} (h : R = S) {a : Ω} (ha : IsIntegral R a) : IsIntegral S a := by
  subst h
  exact ha

theorem normalCpt_of [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (hn : NormalCpt ξ) :
    NormalCpt ξg := by
  intro p a ha
  rw [regAt_emb hD p]
  exact hn (emb hD p) a (isIntegral_congr (regAt_emb hD p) ha)

theorem coe_span_eq {R S : Subring Ω} (h : R = S) (M : Submodule S Ω) :
    ((Submodule.span R (M : Set Ω) : Submodule R Ω) : Set Ω) = M := by
  subst h
  rw [Submodule.span_eq]

theorem eq_span_of_coe {R S : Subring Ω} (h : R = S) {N : Submodule R Ω} {M : Submodule S Ω}
    (hNM : (N : Set Ω) = M) {A : Set Ω} (hM : M = Submodule.span S A) : N = Submodule.span R A := by
  subst h
  exact (SetLike.coe_injective hNM).trans hM

theorem coe_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) (p : Cpt ξg) :
    ((L.pull ξg e (AddMonoidHom.id Ω) p : Submodule (regAt ξg p) Ω) : Set Ω) = L (emb hD p) := by
  rw [Lat.pull_apply L hD]
  have h0 : (AddMonoidHom.id Ω) '' (L (emb hD p) : Set Ω) = (L (emb hD p) : Set Ω) := Set.image_id _
  exact (congrArg (fun A : Set Ω => ((Submodule.span (regAt ξg p) A : Submodule _ Ω) : Set Ω)) h0).trans
    (coe_span_eq (regAt_emb hD p) _)

theorem isVBOn_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) {T : Set (Cpt ξ)}
    (hT : ∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) (h : L.IsVBOn T 1 ⊤) :
    (L.pull ξg e (AddMonoidHom.id Ω)).IsVBOn Set.univ 1 ⊤ := by
  have hmem : ∀ p : Cpt ξg, emb hD p ∈ T := fun p => (hT _).2 ⟨p.1, rfl⟩
  intro p _
  obtain ⟨U, hU, b, hb, hq⟩ := h (emb hD p) (hmem p)
  refine ⟨e ⁻¹ᵁ U, hU, b, hb, fun q _ hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hq (emb hD q) (hmem q) hqU
  exact ⟨h1, eq_span_of_coe (regAt_emb hD q) (coe_pull hD L q) h2⟩

theorem pull_pull_eq [IsPreimmersion e] {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ Y}
    (hD : Dominates ξg ξ e (RingHom.id Ω)) (hD' : Dominates ξ' ξg f (RingHom.id Ω))
    (hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω)) (L : Lat ξ Ω) (p' : Cpt ξ') :
    (L.pull ξg e (AddMonoidHom.id Ω)).pull ξ' f (RingHom.id Ω).toAddMonoidHom p' =
      L.pull ξ' (f ≫ e) (AddMonoidHom.id Ω) p' := by
  rw [Lat.pull_apply _ hD', Lat.pull_apply _ hD'']
  congr 1
  have h1 := coe_pull hD L ⟨f p'.1, hD'.specializes p'⟩
  have h2 : emb hD ⟨f p'.1, hD'.specializes p'⟩ = ⟨(f ≫ e) p'.1, hD''.specializes p'⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply f e p'.1).symm
  rw [h1, h2]
  rfl

theorem gen_descends : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  intro X₀ Xg X' Ω _ ξ ξg ξ' e f L T t hpre hprop hloc h1 h2 hgen hnorm hT hVB hG x hx
  haveI := hpre
  haveI := hprop
  haveI := hloc
  have hD : Dominates ξg ξ e (RingHom.id Ω) := dominates_id h1
  have hD' : Dominates ξ' ξg f (RingHom.id Ω) := dominates_id h2
  have hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω) := dominates_id (by rw [← Category.assoc, h2, h1])
  obtain ⟨z, hz⟩ := (hT x).1 hx
  have hs : genPt ξg ⤳ z := by
    have h3 : e (genPt ξg) ⤳ e z := by
      rw [hD.map_genPt, hz]
      exact x.2
    exact (e.isEmbedding.isInducing.specializes_iff).1 h3
  have hp : (L.pull ξg e (AddMonoidHom.id Ω)).IsGenAt ⟨z, hs⟩ t :=
    GlobalTheory.T.line_bundle_normal_proper_pullback Xg Ω ξg X' Ω ξ' f (RingHom.id Ω) hD' Function.bijective_id (isCptGen_of h1 hgen)
      (normalCpt_of hD hnorm) (L.pull ξg e (AddMonoidHom.id Ω)) Set.univ ⟨z, hs⟩ t (isVBOn_pull hD L hT hVB)
      (fun _ _ => trivial) (fun p' _ => by
        have h4 := hG p'
        refine ⟨h4.1, ?_⟩
        rw [pull_pull_eq hD hD' hD'' L p']
        exact h4.2)
  have hx' : x = emb hD ⟨z, hs⟩ := Subtype.ext hz.symm
  rw [hx']
  exact ⟨hp.1, eq_span_of_coe (regAt_emb hD _).symm (coe_pull hD L _).symm hp.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PushLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundleStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pullback_line_bundle : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | exact GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualAction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualAction
namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li))
    (hspan : Submodule.span K (D.om : Set (Module.Dual K Li)) = ⊤)
    {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [hspan] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ HT.eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ HT.eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  let : Module A Li := Module.compHom Li (algebraMap A K)
  have : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  have hvW : ∀ g, vec g ∈ latOn D (HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add (f := _), mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hF0 : ∀ (e : Wsub) (z : D.omHT (σ.comp c.toRingHom)), ∃ a : A,
      algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
    rintro ⟨e, he⟩ z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
    change algebraMap A K d * (z : Module.Dual K Li) e ∈ (algebraMap A K).range
    rw [← hz', hE e he.1 w]
    exact he.2 w hw
  choose F hF using hF0
  let eval : Wsub →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)) :=
    { toFun := fun e =>
        { toFun := F e
          map_add' := fun x y => hinj <| by
            rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
          map_smul' := fun a x => hinj <| by
            rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul,
              LinearMap.smul_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun x y => by
        ext z
        apply hinj
        change algebraMap A K (F (x + y) z) = algebraMap A K (F x z + F y z)
        rw [map_add, hF, hF, hF, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun a x => by
        ext z
        apply hinj
        change algebraMap A K (F (a • x) z) = algebraMap A K (a * F x z)
        rw [map_mul, hF, hF, Submodule.coe_smul, hsmul, map_smul, smul_eq_mul, mul_left_comm] }
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ eval)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRrS (y : Fin N → K) : Rr y ∈ HT.eigSp ρ σ := by
    simp only [Rr, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hvecS _)
  have hRr (y : Fin N → A) (z : D.omHT (σ.comp c.toRingHom)) :
      algebraMap A K d * (z : Module.Dual K Li) (Rr (fun l => algebraMap A K (y l))) =
        algebraMap A K (r y z) := by
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [Rr, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hvec]
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · exact ⟨eval ⟨e, he⟩, hF _, fun l => congrFun (hG ⟨e, he⟩) l⟩
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · let f := eval ⟨e, he⟩
    obtain ⟨w', hw'⟩ := hr f
    have hGe : G e = fun l => algebraMap A K (i f l) := hG ⟨e, he⟩
    let q := (p : K) ^ m
    have hq : q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let e' := q⁻¹ • (Rr (G e) - e)
    have he'S : e' ∈ HT.eigSp ρ σ :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hRrS _) he.1)
    refine ⟨e', ⟨he'S, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨z, hz⟩ := hmem w hw
      have hzEval : algebraMap A K d * (z : Module.Dual K Li) (Rr (G e) - e) =
          q * algebraMap A K (w' z) := by
        have hf : algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := hF _ _
        rw [map_sub, mul_sub, hGe, hRr, hw', LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, map_add, map_mul, map_pow, map_natCast, ← hf, add_sub_cancel_left]
      refine ⟨w' z, ?_⟩
      rw [← hE e' he'S w, ← hz]
      change algebraMap A K (w' z) = algebraMap A K d * (z : Module.Dual K Li) (q⁻¹ • (Rr (G e) - e))
      rw [map_smul, smul_eq_mul, mul_left_comm, hzEval, inv_mul_cancel_left₀ hq]
    · change Rr (G e) = e + q • (q⁻¹ • (Rr (G e) - e))
      rw [smul_inv_smul₀ hq]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualActionStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_dual_action : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract | exact GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract <;> assumption)
end
end
