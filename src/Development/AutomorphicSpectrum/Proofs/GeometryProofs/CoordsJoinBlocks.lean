module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AddBlockMulti

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Reindex

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem inChart_comp_equiv (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ κ' : Type} (e : κ' ≃ κ) (x : κ → Ω) (c : κ')
    (p : Cpt ξ) : InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
  unfold InChart
  refine and_congr Iff.rfl ⟨fun h c' => ?_, fun h c' => h _⟩
  simpa using h (e.symm c')

theorem coordTie_comp_equiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type}
    (e : κ' ≃ κ) {x : κ → Ω} (h : CoordTie o ξ x) : CoordTie o ξ (x ∘ e) := by
  have hr : ∀ c : κ', (Set.range fun j => (x ∘ e) j / (x ∘ e) c) = Set.range fun j => x j / x (e c) := fun c =>
    e.surjective.range_comp (fun j => x j / x (e c))
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (inChart_comp_equiv ξ e x _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    refine ⟨U, hU, fun q => ?_⟩
    rw [hq q]
    exact exists_congr fun hh => (inChart_comp_equiv ξ e x c ⟨q, hh⟩).symm
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (inChart_comp_equiv ξ e x c p).symm Iff.rfl

end Reindex

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
variable (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]

theorem specializes_of_openImm {y : Y} (h : genPt (ζ ≫ f) ⤳ f y) : genPt ζ ⤳ y := by
  have e2 : genPt (ζ ≫ f) = f (genPt ζ) := Scheme.Hom.comp_apply _ _ _
  rw [e2] at h
  exact f.isOpenEmbedding.isInducing.specializes_iff.1 h

theorem inChart_push {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ζ) :
    InChart (ζ ≫ f) x c (push ζ f p) ↔ InChart ζ x c p := by
  unfold InChart
  rw [regAt_push]

variable {ζ f}

theorem exists_push (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (q : Cpt (ζ ≫ f)) :
    ∃ p : Cpt ζ, push ζ f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := hR q hq
  exact ⟨⟨y, specializes_of_openImm ζ f hq⟩, rfl⟩

theorem coordTie_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o ζ x) : CoordTie o (ζ ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp ζ f]
    have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push hR q
    exact genMap_push_injective ζ f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push hR q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push ζ f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f, fun q => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := (hq y).1 hy
      exact ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := hR q h1
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨y, (hq y).2 ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩, rfl⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this

theorem coordTie_of_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o (ζ ≫ f) x) : CoordTie o ζ x := by
  refine ⟨⟨?_, fun p => ?_⟩, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    have h1 := h.gen.bij
    rw [Scheme.stalkClosedPointTo_comp ζ f] at h1
    exact (Function.Bijective.of_comp_iff _ hb).1 h1
  · have h1 := h.gen.inj (push ζ f p)
    rw [genMap_push] at h1
    have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
    exact (Function.Injective.of_comp_iff' _ hb).1 h1
  · obtain ⟨c, hc⟩ := h.cover (push ζ f p)
    exact ⟨c, (inChart_push ζ f x c p).1 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    have hle : U ≤ f.opensRange := fun q hqU => hR q ((hq q).1 hqU).1
    refine ⟨f ⁻¹ᵁ U, ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
    · have e : f ''ᵁ (f ⁻¹ᵁ U) = U := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
        exact inf_eq_right.2 hle
      rw [← f.isAffineOpen_iff_of_isOpenImmersion, e]
      exact hU
    · obtain ⟨h1, h2⟩ := (hq (f y)).1 hy
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact (hq (f y)).2 ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)

end OpenImm

section Model

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem spec_int_hom_ext (g g' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ)) : g = g' := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage g']
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_int _ _)

theorem exists_openModel {κ : Type} {x : κ → Ω} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) :
    ∃ (Y : Scheme.{0}) (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (_ : IsOpenImmersion f), ζ ≫ f = ξ ∧
      (∀ q : X, genPt ξ ⤳ q → q ∈ Set.range f) ∧ ∀ q : Y, genPt ζ ⤳ q := by
  let W : X.Opens := sSup {U : X.Opens | ∀ q ∈ U, genPt ξ ⤳ q}
  have hW : ∀ q ∈ W, genPt ξ ⤳ q := by
    intro q hq
    obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 hq
    exact hU q hqU
  have hC : ∀ q : X, genPt ξ ⤳ q → q ∈ W := by
    intro q hq
    obtain ⟨c, hc⟩ := h.cover ⟨q, hq⟩
    obtain ⟨U, -, hU⟩ := h.affine c hc.1
    refine TopologicalSpace.Opens.mem_sSup.2 ⟨U, fun r hr => ((hU r).1 hr).1, (hU q).2 ⟨hq, hc⟩⟩
  have hr : Set.range ξ ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hz
    rw [Scheme.Opens.range_ι]
    exact hC _ specializes_rfl
  have e : IsOpenImmersion.lift W.ι ξ hr ≫ W.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ q : X, genPt ξ ⤳ q → q ∈ Set.range W.ι := fun q hq => by
    rw [Scheme.Opens.range_ι]
    exact hC q hq
  refine ⟨W, IsOpenImmersion.lift W.ι ξ hr, W.ι, inferInstance, e, hR, fun q => ?_⟩
  refine specializes_of_openImm _ W.ι ?_
  rw [e]
  exact hW _ q.2

theorem coordTie_join {κ κ' : Type} [Finite κ] [Finite κ'] {x : κ → Ω} {w : κ' → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) (hw : ∀ p : Cpt ξ, ∃ l, InChart ξ w l p) :
    CoordTie ℤ ξ (joinCo (RingHom.id Ω) x w) := by
  obtain ⟨Y, ζ, f, _, rfl, hR, hall⟩ := exists_openModel h
  let M : PModel ℤ x :=
    { X := Y
      ξ := ζ
      s := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom _))
      hover := spec_int_hom_ext _ _
      all := hall
      tie := coordTie_of_push hR h }
  refine coordTie_push hR (GlobalTheory.T.join_coords_coordTie ℤ Ω κ x M κ' w fun p => ?_)
  obtain ⟨l, hl⟩ := hw (push ζ f p)
  exact ⟨l, (inChart_push ζ f w l p).1 hl⟩

end Model

theorem add_block_multi : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K']
    (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) →
    CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k =>
      (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  intro X Ω _ ξ K _ J _ y K' _ J' _ s h hs
  have hw : ∀ p : Cpt ξ, ∃ i, InChart ξ (fun c : (k : K') → J' k => ∏ k, s ⟨k, c k⟩) i p := by
    intro p
    choose i hi using fun k => hs k p
    refine ⟨i, Finset.prod_ne_zero_iff.2 fun k _ => (hi k).1, fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => (hi k).2 (c' k)
  have h2 := coordTie_join (κ := (k : K) → J k) (κ' := (k : K') → J' k) h hw
  exact coordTie_comp_equiv (Equiv.sumPiEquivProdPi (Sum.elim J J')) h2

end GlobalTheory.CompanionTheory.Ar.AddBlockMulti
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_join_blocks : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) → CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k => (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | exact GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | (intros; apply GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExt

theorem mem_eigSp_iff' {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (v : E) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_ext :
    ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ hj hspan hcomp
  obtain ⟨n, a, c, hsum, hcas⟩ := GlobalTheory.CompanionTheory.Ar.ScaledCasimir.exists_scaledCasimir F

  let P' : V' →ₗ[Ω'] V' := ∑ m, i (σ (c m)) • ρ' (a m)
  have hP'apply : ∀ w, P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := fun w => by
    simp [P', LinearMap.sum_apply]
  have hscal : ∑ m, i (σ (c m)) * i (σ (a m)) = ((NumberField.discr F : ℤ) : Ω') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_intCast (i.comp σ), ← hsum, map_sum]
    simp [map_mul]
  have hP'eig : ∀ w ∈ eigSp ρ' (i.comp σ), P' w = ((NumberField.discr F : ℤ) : Ω') • w := by
    intro w hw
    have hw' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) w).mp hw
    calc P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := hP'apply w
      _ = ∑ m, (i (σ (c m)) * i (σ (a m))) • w :=
          Finset.sum_congr rfl fun m _ => by rw [hw', RingHom.comp_apply, smul_smul]
      _ = _ := by rw [← Finset.sum_smul, hscal]
  have hP'j : ∀ e, P' (j e) = j (∑ m, σ (c m) • ρ (a m) e) := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP'apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcomp, hj.1]
  have hPe : ∀ e, ∑ m, σ (c m) • ρ (a m) e ∈ eigSp ρ σ := fun e =>
    (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ _).mpr fun b => hcas Ω V ρ σ b e
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span Ω' (Set.range j) ≤
        (Submodule.span Ω' (j '' (eigSp ρ σ : Set V))).comap P' := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hP'j]
      exact Submodule.subset_span ⟨_, hPe e, rfl⟩
    have hmem : P' w ∈ Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) :=
      hle (by rw [hspan]; exact Submodule.mem_top)
    rw [hP'eig w hw] at hmem
    have hd : ((NumberField.discr F : ℤ) : Ω') ≠ 0 := by
      rw [← map_intCast i]
      exact (map_ne_zero i).mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
    have h2 := Submodule.smul_mem _ ((NumberField.discr F : ℤ) : Ω')⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ v).mp hv
    refine (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) (j v)).mpr fun b => ?_
    rw [hcomp, hv' b, hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigExt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | exact GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigLat

theorem mem_eigSp_iff' {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {x : W} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem sum_smul_of_eig {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {n : ℕ} (a c : Fin n → O) {x : W}
    (hx : ∀ b, ρ b x = τ b • x) :
    ∑ m, τ (c m) • ρ (a m) x = τ (∑ m, c m * a m) • x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]

theorem span_inf_eigSp : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd
  obtain ⟨n, a, c, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir F
  have hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)
  have hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω) := by rw [hsum, map_intCast]
  have hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω) := by
    rw [RingHom.comp_apply, hσd]
  have hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0 := (map_ne_zero i).2 hd0

  let P : V → V := fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v

  let P' : Module.End Ω' V' := (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)
  have hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x := by
    intro x
    simp [P', LinearMap.sum_apply]
  have hPeig : ∀ v, P v ∈ eigSp ρ σ := by
    intro v
    refine mem_eigSp_iff'.2 fun b => ?_
    simp only [P]
    rw [map_smul, heq Ω V ρ σ b v, smul_comm]
  have hPL : ∀ v ∈ L, P v ∈ L := by
    intro v hv
    have h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L := by
      refine Submodule.sum_mem _ fun m _ => ?_
      exact L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)
    exact L.smul_mem ⟨_, hd⟩ h1
  have hjP : ∀ v, P' (j v) = j (P v) := by
    intro v
    rw [hP'apply]
    simp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj.1, map_inv₀, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hj.1, hρ, RingHom.comp_apply]
  have hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x := by
    intro x hx
    rw [hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul,
      inv_mul_cancel₀ hid0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx2' : x ∈ eigSp ρ' (i.comp σ) := hx2
    have key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R'
        (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        rw [hjP]
        exact Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        have h1 : P' (r • y) = r • P' y := by
          rw [Subring.smul_def, Subring.smul_def, map_smul]
        rw [h1]
        exact Submodule.smul_mem _ r hy
    have h2 := key x hx1
    rwa [hP'id x hx2'] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := Submodule.mem_inf.1 he
    have he2' : e ∈ eigSp ρ σ := he2
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ eigSp ρ' (i.comp σ)
    refine mem_eigSp_iff'.2 fun b => ?_
    rw [hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_eigen_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagModOfDvd
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GfMono
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_mono : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  intro o _ Ω _ _ K _ J _ y ϖ ϖ' N b ⟨c, hc⟩ ⟨g, h1, h2⟩
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, h, hh, r, hr, e⟩ := h1 s hs
    refine ⟨hg, h, hh, algebraMap o Ω c * r, mul_mem (Subalgebra.algebraMap_mem _ c) hr, ?_⟩
    rw [e, hc, map_mul, mul_assoc]
  · obtain ⟨m, U, Z, hU, hZ, hU0, hUd, hm, e⟩ := h2 s t hs ht
    refine ⟨m, U, algebraMap o Ω c • Z, hU, fun i j => ?_, hU0, hUd, hm, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (hZ i j)
    · rw [e, hc, map_mul, mul_smul]

end PositivityTheory.HtPt.Gf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagModOfDvd
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivFlagMod_of_dvd : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b :=
  @PositivityTheory.HtPt.Gf.trivflag_mono

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagModOfDvdStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triv_flag_mod_of_dvd : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd | exact GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_of_dvd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEq
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li]
      [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O]
      (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q →
      M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) →
        (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ Li _ _ M L n g O _ ρ σ q hVB hOm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat {q} g hVB).2 q rfl
  have hD : M.htDual L n ρ σ q = M.eigLat ρ σ q := by
    refine le_antisymm (fun e he => ?_) (M.eigLat_le_htDual L n ρ σ q)
    obtain ⟨he1, he2⟩ := (M.mem_htDual_iff L n ρ σ q e).1 he
    refine ⟨(hbi e).2 fun w hw => he2 w ?_, he1⟩
    rw [hOm]
    exact hw
  refine ⟨hD, fun 𝔡 hσ ⟨d, hd, hu, _, hinv⟩ => le_antisymm ?_ fun e he => ?_⟩
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 : σ d • e ∈ M.eigLat ρ σ q := hD ▸ he.2 d hd
    have h2 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) ∈ M.eigLat ρ σ q := Submodule.smul_mem _ _ h1
    have h3 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) = e := by
      change (σ d)⁻¹ • (σ d • e) = e
      rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    rwa [h3] at h2
  · refine Submodule.subset_span ⟨he.2, fun a ha => ?_⟩
    rw [hD]
    exact Submodule.smul_mem (M.eigLat ρ σ q) (⟨σ a, hσ a⟩ : regAt ξ q) he

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_eigen_lattice_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O] (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q → M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) → (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat | exact GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat | (intros; apply GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparison
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieIntertwining

theorem act_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  intro E _ _ _ H g Ω _ X X' ξ ξ' t t' tΩ m m' V V' _ _ _ _ M M' ρ ρ' φ hM hM' tie a v
  obtain ⟨w, hw, hw'⟩ := tie v
  obtain ⟨w₃, hw₃, hw₃'⟩ := tie (ρ (g.s a) v)

  have h1 : (M.pt (ρ (g.s a) v)).left = (M.pt v).left ≫ (t.act.act (g.s a)).left := by
    rw [hM (g.s a) v]; rfl
  have h2 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ m.φ = w₃.left ≫ m.φ := by
    rw [hw₃, h1, ← hw, Category.assoc, Category.assoc, m.act]
  have h3 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ tΩ.G.hom = w₃.left ≫ tΩ.G.hom := by
    rw [Category.assoc, Over.w, Over.w, Over.w]
  have h4 : w.left ≫ (tΩ.act.act (g.s a)).left = w₃.left := m.cart.1.hom_ext h2 h3
  have h5 : (M'.pt (φ (ρ (g.s a) v))).left = (M'.pt (ρ' a (φ v))).left := by
    have h6 : (tΩ.act.act (g.s a)).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
    rw [← hw₃', ← h4, hM' a (φ v), Over.comp_left, ← hw']
    exact (Category.assoc _ _ _).trans ((congrArg (w.left ≫ ·) h6).trans (Category.assoc _ _ _).symm)
  exact M'.inj (Over.OverMorphism.ext h5)

end GlobalTheory.CompanionTheory.Ar.LieIntertwining
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparisonStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_twisted_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | exact GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | (intros; apply GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPoint
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_open_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over

  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  have hfn : 𝔐.fn.comp cst₀ = 𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [RingHom.comp_assoc, hl, hc]
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by rw [hl, hb]
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    rw [← Spec.map_comp]; rfl

  let w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])

  let u : c.F →+* Ω := (Spec.preimage (y₀ ≫ pullback.snd _ _)).hom
  have hu : y₀ ≫ pullback.snd _ _ = spMap u := (Spec.map_preimage _).symm
  have huc : u = 𝔐.cst := by
    have hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    have h1 := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    have h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by simpa using h1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  have hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a :=
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y₀ a', ?_⟩
    have := congrArg (fun φ => φ a') hw
    simpa using this.symm
  refine ⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | exact GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentiableOnStarStar
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.Regular

section Polydisc

variable {n a : ℕ}

theorem norm_star_vec (z : Fin n → ℂ) : ‖star z‖ = ‖z‖ := by
  simp only [Pi.norm_def, Pi.star_apply]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  simp [nnnorm_star]

theorem star_mem_ball {ρ : ℝ} {z : Fin n → ℂ} :
    star z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  simp only [mem_ball_zero_iff, norm_star_vec]

theorem star_mem_punct {ρ : ℝ} {z : Fin n → ℂ} : star z ∈ punct n a ρ ↔ z ∈ punct n a ρ := by
  simp only [punct, Set.mem_setOf_eq, star_mem_ball, Pi.star_apply, ne_eq, star_eq_zero]

theorem star_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} : star w ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_setOf_eq, Pi.star_apply, Complex.star_def, Complex.conj_re,
    RCLike.norm_conj, Complex.norm_conj]

theorem star_expCover (w : Fin n → ℂ) : star (expCover a w) = expCover a (star w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · simp [Complex.exp_conj]
  · rfl

theorem star_real_smul (ρ : ℝ) (z : Fin n → ℂ) : star ((ρ : ℂ) • z) = (ρ : ℂ) • star z := by
  funext k
  simp

theorem differentiableOn_star_star {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [ContinuousStar V] {f : V → F} {B : Set V} (hB : IsOpen B) (hs : ∀ z, star z ∈ B ↔ z ∈ B)
    (hf : DifferentiableOn ℂ f B) : DifferentiableOn ℂ (fun z => star (f (star z))) B := by
  intro z hz
  have h1 : DifferentiableAt ℂ f (star z) := hf.differentiableAt (hB.mem_nhds ((hs z).2 hz))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

end Polydisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def conjPts {R : Type} [CommRing R] {n : ℕ} (ψ : (Fin n → ℂ) → (R →+* ℂ)) (z : Fin n → ℂ) : R →+* ℂ :=
  (starRingEnd ℂ).comp (ψ (star z))

theorem isHolPts_conjPts {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {ρ : ℝ}
    (h : IsHolPts (Metric.ball 0 ρ) ψ) : IsHolPts (Metric.ball 0 ρ) (conjPts ψ) :=
  ⟨Metric.isOpen_ball, fun r => differentiableOn_star_star (f := fun b => ψ b r) Metric.isOpen_ball
    (fun _ => star_mem_ball) (h.2 r)⟩

def chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) :
    BdryChart Xo ((starRingEnd ℂ).comp σ) n a where
  a_le := C.a_le
  R := C.R
  t := C.t
  g := C.g
  dim := C.dim
  M := C.M
  ψ := conjPts C.ψ
  hol := isHolPts_conjPts C.hol
  V := C.V
  j := C.j
  j_open := C.j_open
  k := C.k
  tV := C.tV
  m₁ := C.m₁
  m₂ := C.m₂
  pt z := spMap (starRingEnd ℂ) ≫ C.pt (star z)
  pt_eq z hz := by
    obtain ⟨h1, h2⟩ := C.pt_eq (star z) (star_mem_punct.2 hz)
    constructor
    · rw [Category.assoc, h1]
      exact (Spec.map_comp _ _).symm
    · rw [Category.assoc, h2]
      exact (Spec.map_comp _ _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.Conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSq
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSq
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.KappaDvd

theorem kappa_dvd_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A),
    IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  intro A Ω _ _ _ _ _ _ _ p hp κ h
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  unfold IsCp at h
  split_ifs at h with h2
  · subst h2
    have : κ = 4 := hinj (by rw [h]; exact (map_ofNat _ 4).symm)
    subst this
    exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, hκ⟩ := h
    have hp1 : 1 < p := hp.out.one_lt
    have hint : IsIntegral A ζ := by
      refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
      simp [hζ.pow_eq_one]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hz' : IsPrimitiveRoot z p := by
      rw [← hz] at hζ
      exact hζ.of_map_of_injective hinj
    have hκz : κ = z - 1 := hinj (by rw [hκ, map_sub, map_one, hz])
    have hsum : ∑ i ∈ Finset.range p, z ^ i = 0 := hz'.geom_sum_eq_zero hp1
    have hp_eq : (p : A) = ∑ i ∈ Finset.range p, (1 - z ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    have hdvd : κ ∣ (p : A) := by
      rw [hp_eq, hκz]
      refine Finset.dvd_sum fun i _ => ?_
      have := sub_dvd_pow_sub_pow z 1 i
      rw [one_pow] at this
      rw [show (1 : A) - z ^ i = -(z ^ i - 1) by ring]
      exact dvd_neg.mpr this
    exact hdvd.trans (dvd_pow_self _ two_ne_zero)

end GlobalTheory.CompanionTheory.Ar.HT.KappaDvd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSqStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_element_divides_prime_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A), IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | exact GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartTransitionIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartTransitionIntegral
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.Overlap

theorem omHT_pow_smul_mem : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R N V), (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin N → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ R) • w) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ a ∈ chartRing o (mseg y) s.1, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n * a ∈ chartRing o (mseg y) t.1) → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ' := by
  intro o _ Ω _ _ K _ J _ y E _ _ c p R N V _ _ Dc hom hh hρ hring s t σ'
  set f : Ω := mseg y s.1 / mseg y t.1 with hf
  have hfA : f ∈ chartRing o (mseg y) t.1 := Algebra.subset_adjoin ⟨s.1, rfl⟩
  have hfMn : ∀ n : ℕ, ∀ z ∈ (Dc t).om', f ^ n • z ∈ (Dc t).om' := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact (Dc t).om'.smul_mem (⟨f, hfA⟩ : chartRing o (mseg y) t.1) (ih z hz)
  let P : Submodule (chartRing o (mseg y) s.1) V :=
    { carrier := {z | ∃ n : ℕ, f ^ n • z ∈ (Dc t).om'}
      add_mem' := by
        rintro a b ⟨n, hn⟩ ⟨m, hm⟩
        refine ⟨n + m, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [add_comm, pow_add, mul_smul]; exact hfMn m _ hn
        · rw [pow_add, mul_smul]; exact hfMn n _ hm
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro a z ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hring s t (a : Ω) a.2
        refine ⟨n + m, ?_⟩
        have e1 : f ^ (n + m) • (a • z) = (⟨f ^ m * a, hm⟩ : chartRing o (mseg y) t.1) • (f ^ n • z) := by
          show f ^ (n + m) • ((a : Ω) • z) = (f ^ m * a) • (f ^ n • z)
          rw [smul_smul, smul_smul]; congr 1; ring
        rw [e1]; exact (Dc t).om'.smul_mem _ hn }
  have hle : (Dc s).om' ≤ P := by
    unfold HTChart.om'
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨δ, rfl⟩
      obtain ⟨n, w, hw, he⟩ := hh s t δ
      refine ⟨n, ?_⟩
      have e2 : f ^ n • (Dc s).h δ = f ^ n • (Dc t).h δ + ((p : Ω) ^ R) • w := by
        rw [← he, smul_sub]; abel
      rw [e2]
      refine add_mem (hfMn n _ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨δ, rfl⟩)
      · refine Submodule.mem_sup_right ⟨w, hw, ?_⟩
        simp [Subalgebra.smul_def]
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := hom s t u hu
      refine ⟨n, ?_⟩
      refine Submodule.mem_sup_right ⟨f ^ n • u, hn, ?_⟩
      simp [Subalgebra.smul_def, smul_comm ((p : Ω) ^ R) (f ^ n) u]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hle hz
  refine ⟨n, ⟨f ^ n • z, hn, ?_⟩⟩
  show eigProj (Dc t).ρΩ σ' (f ^ n • z) = f ^ n • eigProj (Dc s).ρΩ σ' z
  rw [hρ s t, map_smul]

end GlobalTheory.CompanionTheory.Ar.HT.Overlap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartTransitionIntegralStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_chart_transition_integral : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R N V), (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin N → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ R) • w) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ a ∈ chartRing o (mseg y) s.1, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n * a ∈ chartRing o (mseg y) t.1) → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.Overlap.omHT_pow_smul_mem | exact GlobalTheory.CompanionTheory.Ar.HT.Overlap.omHT_pow_smul_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.Overlap.omHT_pow_smul_mem <;> assumption)
end
end
