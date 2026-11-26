module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfGalAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFinsetClosedFibreSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNearGaloisQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_closedFibre_subset_isAffineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) →
    ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR _ _ G _ _ hG _ s hs
  exact GlobalTheory.T.exists_affineOpen_finset_closedFibre_semiAbelian R hR.1 G hG s hs

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | exact GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | (intros; apply GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_invariant_nbhd_of_orbits {X : Scheme.{0}} [X.IsSeparated] {Γ : Type} [Group Γ] [Finite Γ]
    (act : Γ → (X ⟶ X)) (act_one : act 1 = 𝟙 X) (act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ)
    (Z : Set X) (hZ : IsCompact Z)
    (horb : ∀ z ∈ Z, ∃ O : X.Opens, IsAffineOpen O ∧ ∀ σ, act σ z ∈ O) :
    ∃ H : X.Opens, (∀ σ, act σ ⁻¹ᵁ H = H) ∧ (∀ z ∈ Z, z ∈ H) ∧ IsCompact (H : Set X) ∧
      (∀ x ∈ H, ∃ O : X.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) := by
  classical
  have hiso : ∀ σ, IsIso (act σ) := fun σ =>
    ⟨act σ⁻¹, by rw [← act_mul, mul_inv_cancel, act_one], by rw [← act_mul, inv_mul_cancel, act_one]⟩
  have hmul : ∀ σ τ (x : X), act (σ * τ) x = act τ (act σ x) := fun σ τ x => by
    rw [act_mul, Scheme.Hom.comp_apply]
  have hone : ∀ x : X, act 1 x = x := fun x => by rw [act_one]; rfl
  have hW : ∀ z : Z, ∃ V : X.Opens, IsAffineOpen V ∧ z.1 ∈ V ∧ ∀ σ, ∀ x ∈ V, act σ x ∈ V := by
    intro z
    obtain ⟨O, hO, hz⟩ := horb z.1 z.2
    have hmem : ∀ x : X, x ∈ (⨅ σ, act σ ⁻¹ᵁ O) ↔ ∀ σ, act σ x ∈ O := fun x => by
      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      rfl
    refine ⟨⨅ σ, act σ ⁻¹ᵁ O, IsAffineOpen.iInf fun σ => ?_, (hmem _).2 hz, fun σ x hx => (hmem _).2 fun τ => ?_⟩
    · have := hiso σ
      exact hO.preimage (act σ)
    · rw [← hmul]
      exact (hmem _).1 hx _
  choose V hV hzV hVa using hW
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun z : Z => (V z : Set X)) (fun z => (V z).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
  have hH : ∀ x : X, x ∈ (⨆ z ∈ t, V z) ↔ ∃ z ∈ t, x ∈ V z := fun x => by
    simp [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⨆ z ∈ t, V z, fun σ => ?_, fun z hz => ?_, ?_, fun x hx => ?_⟩
  · ext x
    change act σ x ∈ (⨆ z ∈ t, V z) ↔ x ∈ (⨆ z ∈ t, V z)
    rw [hH, hH]
    refine ⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, ?_⟩, fun ⟨z, hz, hx⟩ => ⟨z, hz, hVa z σ x hx⟩⟩
    have := hVa z σ⁻¹ _ hx
    rwa [← hmul, mul_inv_cancel, hone] at this
  · rw [hH]
    simpa using ht hz
  · have : ((⨆ z ∈ t, V z : X.Opens) : Set X) = ⋃ z ∈ t, (V z : Set X) := by
      ext x
      rw [SetLike.mem_coe, hH]
      simp
    rw [this]
    exact t.isCompact_biUnion fun z _ => (hV z).isCompact
  · obtain ⟨z, hz, hx⟩ := (hH x).1 hx
    exact ⟨V z, hV z, fun y hy => (hH y).2 ⟨z, hz, hy⟩, fun σ => hVa z σ x hx⟩

theorem eq_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {ρ : R →+* R'} (hρ : ρ.Finite) (p : Sp R') (hp : spMap ρ p = closedPoint R) : p = closedPoint R' := by
  have h₁ : Ideal.comap ρ (PrimeSpectrum.asIdeal p) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
  have h₂ : (PrimeSpectrum.asIdeal p).IsMaximal := by
    have := PrimeSpectrum.isPrime p
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ ?_
    rw [h₁]
    infer_instance
  exact PrimeSpectrum.ext (eq_maximalIdeal h₂)

theorem exists_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hS U' a
  classical
  have := hR.2
  have hR' : Base R' := ⟨hρ.1, charZero_of_injective_ringHom hρ.2.1⟩
  have := hG.1
  have := Fintype.ofFinite (Gal ρ)
  have := hS.separated
  have := hS.quasiCompact
  have : G'.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G'.hom]
    infer_instance⟩
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  have hover : ∀ (σ : Gal ρ) (g : G'.left), spMap ρ (G'.hom (a.act σ g)) = spMap ρ (G'.hom g) := fun σ g => by
    have h₁ : a.act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ) := (a.cart σ).1.w
    have h₂ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact σ.2 r
    rw [← Scheme.Hom.comp_apply (a.act σ), h₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (spMap (Gal.hom σ)), h₂]
  have hZ : IsClosed {g : G'.left | spMap ρ (G'.hom g) = closedPoint R} :=
    (isClosed_singleton_closedPoint R).preimage ((spMap ρ).continuous.comp G'.hom.continuous)
  refine exists_invariant_nbhd_of_orbits a.act a.act_one a.act_mul _ hZ.isCompact fun z hz => ?_
  obtain ⟨O, hO, h⟩ := GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen R' hR' D' A' G' hS U' (Finset.univ.image fun σ => a.act σ z) (fun x hx => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
    exact eq_closedPoint_of_finite hρ.2.2 _ ((hover σ z).trans hz))
  exact ⟨O, hO, fun σ => h _ (Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩)⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  first | exact @GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | exact GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | (intros; apply GlobalTheory.Mum.exists_invariant_nbhd_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LawDesc

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G)

theorem pt_unique {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x x' : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s a x') : x = x' := by
  obtain ⟨x₀, h₁, h₂, rfl⟩ := h
  obtain ⟨x₁, h₃, h₄, rfl⟩ := h'
  rw [pullback.hom_ext (h₁.trans h₃.symm) (h₂.trans h₄.symm)]

theorem pt_unique_left {T : Scheme.{0}} {s s' : T ⟶ S} {a a' : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s' a' x) : a = a' := by
  obtain ⟨x₀, rfl, -, h₂⟩ := h
  obtain ⟨x₁, rfl, -, h₄⟩ := h'
  have := N.isOpen
  rw [(cancel_mono N.u).1 (h₂.trans h₄.symm)]

theorem pt_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : N.Pt (k ≫ s) (k ≫ a) (k ≫ x) := by
  obtain ⟨x₀, rfl, rfl, rfl⟩ := h
  exact ⟨k ≫ x₀, Category.assoc _ _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem pt_over {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : s ≫ π = a ≫ N.U.hom := by
  obtain ⟨x₀, rfl, rfl, -⟩ := h
  rw [Category.assoc, Category.assoc, pullback.condition]

theorem pt_exists {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} (h : s ≫ π = a ≫ N.U.hom) :
    ∃ x : Over.mk s ⟶ G, N.Pt s a x.left :=
  ⟨Over.homMk (pullback.lift a s h.symm ≫ N.u) (by
      change (pullback.lift a s h.symm ≫ N.u) ≫ G.hom = s
      rw [Category.assoc, N.u_over, pullback.lift_snd]),
    pullback.lift a s h.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩

variable [GrpObj G]

def Prod {T : Scheme.{0}} (s : T ⟶ S) (v : T ⟶ (N.U ⊗ N.U).left) (z : T ⟶ G.left) : Prop :=
  ∃ x y : Over.mk s ⟶ G, N.Pt s (v ≫ (fst N.U N.U).left) x.left ∧ N.Pt s (v ≫ (snd N.U N.U).left) y.left ∧
    (x * y).left = z

theorem prod_exists {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} (h : s ≫ π = v ≫ (N.U ⊗ N.U).hom) :
    ∃ z, Prod N s v z := by
  obtain ⟨x, hx⟩ := pt_exists N (s := s) (a := v ≫ (fst N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (fst N.U N.U)).symm)
  obtain ⟨y, hy⟩ := pt_exists N (s := s) (a := v ≫ (snd N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (snd N.U N.U)).symm)
  exact ⟨_, x, y, hx, hy, rfl⟩

theorem prod_unique {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z z' : T ⟶ G.left}
    (h : Prod N s v z) (h' : Prod N s v z') : z = z' := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  obtain ⟨x', y', hx', hy', rfl⟩ := h'
  obtain rfl : x = x' := Over.OverMorphism.ext (pt_unique N hx hx')
  obtain rfl : y = y' := Over.OverMorphism.ext (pt_unique N hy hy')
  rfl

theorem prod_over {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : z ≫ G.hom = s := by
  obtain ⟨x, y, -, -, rfl⟩ := h
  exact Over.w (x * y)

theorem prod_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (k ≫ s) (k ≫ v) (k ≫ z) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  let k' : Over.mk (k ≫ s) ⟶ Over.mk s := Over.homMk k rfl
  refine ⟨k' ≫ x, k' ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact pt_comp N k hx
  · rw [Category.assoc]; exact pt_comp N k hy
  · rw [← comp_mul]; rfl

theorem prod_act {c : S ⟶ S} {φ : G.left ⟶ G.left} (hφ : IsGrpPullback G G c φ)
    (hN : ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ c) u (x ≫ φ))
    {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (s ≫ c) v (z ≫ φ) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  have hx' := hN _ _ _ _ hx
  have hy' := hN _ _ _ _ hy
  obtain ⟨x₀, hx₀⟩ := pt_exists N (pt_over N hx')
  obtain ⟨y₀, hy₀⟩ := pt_exists N (pt_over N hy')
  exact ⟨x₀, y₀, hx₀, hy₀, hφ.2 (Over.mk s) x y x₀ y₀ (pt_unique N hx₀ hx') (pt_unique N hy₀ hy')⟩

theorem law_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {α : Γ →* Aut S} (hq : IsAffineQuotient α π)
    (φ : Γ → (G.left ⟶ G.left)) (hφ : ∀ g, IsGrpPullback G G (α g).asIso.hom (φ g))
    (hN : ∀ g (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ (α g).asIso.hom) u (x ≫ φ g)) : N.Law := by
  have := N.smooth
  have := N.isOpen
  have hy : Flat (N.U ⊗ N.U).hom := by
    change Flat (pullback.fst N.U.hom N.U.hom ≫ N.U.hom)
    infer_instance
  have quot : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) [Flat y],
      IsAffineQuotient (pullbackAction α π hq.comp_eq y) (pullback.snd π y) := fun y _ =>
    hq.of_isPullback (IsPullback.of_hasPullback π y) (pullbackAction_fst α π hq.comp_eq y)
      (pullbackAction_snd α π hq.comp_eq y)
  have equiv : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) (j : Y ⟶ (N.U ⊗ N.U).left) (z : pullback π y ⟶ G.left),
      Prod N (pullback.fst π y) (pullback.snd π y ≫ j) z →
      ∀ g, (pullbackAction α π hq.comp_eq y g).asIso.hom ≫ z = z ≫ φ g := fun y j z hz g => by
    have h₁ := prod_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hz
    rw [pullbackAction_fst, pullbackAction_snd_assoc] at h₁
    exact prod_unique N h₁ (prod_act N (hφ g) (hN g) hz)
  obtain ⟨z₀, hz₁⟩ := prod_exists N (pullback.condition (f := π) (g := (N.U ⊗ N.U).hom))
  have hrange : ∀ g, pullback.map N.U.hom π N.U.hom π (𝟙 _) (α g).asIso.hom (𝟙 _) (by simp) (by simp [hq.comp_eq]) ≫ N.u
      = N.u ≫ φ g := fun g => by
    refine pt_unique N (s := pullback.snd N.U.hom π ≫ (α g).asIso.hom) (a := pullback.fst N.U.hom π)
      ⟨_, ?_, pullback.lift_snd _ _ _, rfl⟩
      (hN g _ _ _ _ ⟨𝟙 _, Category.id_comp _, Category.id_comp _, Category.id_comp _⟩)
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  obtain ⟨V, hV⟩ := (quot (N.U ⊗ N.U).hom).exists_preimage_eq (U := z₀ ⁻¹ᵁ N.u.opensRange) fun g w hw => by
    obtain ⟨w', hw'⟩ := hw
    change ((pullbackAction α π hq.comp_eq (N.U ⊗ N.U).hom g).asIso.hom ≫ z₀) w ∈ Set.range N.u
    rw [equiv _ (𝟙 _) z₀ (by rw [Category.comp_id]; exact hz₁) g, Scheme.Hom.comp_apply, ← hw',
      ← Scheme.Hom.comp_apply, ← hrange g, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let y : V.toScheme ⟶ Sp R := V.ι ≫ (N.U ⊗ N.U).hom
  let k : pullback π y ⟶ pullback π (N.U ⊗ N.U).hom :=
    pullback.lift (pullback.fst π y) (pullback.snd π y ≫ V.ι) (by rw [pullback.condition, Category.assoc])
  have hk : k ≫ pullback.snd _ _ = pullback.snd π y ≫ V.ι := pullback.lift_snd _ _ _
  have hz : Prod N (pullback.fst π y) (pullback.snd π y ≫ V.ι) (k ≫ z₀) := by
    have := prod_comp N k hz₁
    rwa [hk, pullback.lift_fst] at this
  have hsub : Set.range (k ≫ z₀) ⊆ Set.range N.u := by
    rintro _ ⟨w, rfl⟩
    have : k w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V := by
      change (k ≫ pullback.snd π (N.U ⊗ N.U).hom) w ∈ V
      rw [hk, Scheme.Hom.comp_apply]
      exact (pullback.snd π y w).2
    rw [hV] at this
    exact this
  let l := IsOpenImmersion.lift N.u (k ≫ z₀) hsub
  have hl : l ≫ N.u = k ≫ z₀ := IsOpenImmersion.lift_fac _ _ _
  have hf : N.Pt (pullback.fst π y) (l ≫ pullback.fst _ _) (k ≫ z₀) :=
    ⟨l, rfl, by rw [← N.u_over, ← Category.assoc, hl, prod_over N hz], hl⟩
  obtain ⟨m, hm⟩ := (quot y).exists_comp_eq (l ≫ pullback.fst _ _) fun g => by
    have h₁ := pt_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hf
    rw [equiv y V.ι _ hz g] at h₁
    exact pt_unique_left N h₁ (hN g _ _ _ _ hf)
  refine ⟨V, m, fun z hz₀ => ?_, (quot y).hom_ext ?_, fun T v s a b ha hb => ?_⟩
  · obtain ⟨w, rfl⟩ := (quot (N.U ⊗ N.U).hom).surjective.surj z
    change w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V
    rw [hV]
    refine N.all (z₀ w) ?_
    rw [← hz₀, ← Scheme.Hom.comp_apply z₀, prod_over N hz₁, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  · rw [← Category.assoc, hm, ← pt_over N hf, pullback.condition]
  · have hs : s ≫ π = v ≫ y := by
      rw [pt_over N ha, Category.assoc, Category.assoc]
      exact congrArg (fun t => v ≫ V.ι ≫ t) (Over.w (fst N.U N.U))
    have h₁ := pt_comp N (pullback.lift s v hs) hf
    have h₂ := prod_comp N (pullback.lift s v hs) hz
    rw [pullback.lift_fst, pullback.lift_snd_assoc] at h₂
    have h₃ : Prod N s (v ≫ V.ι) (a * b).left :=
      ⟨a, b, by rw [Category.assoc]; exact ha, by rw [Category.assoc]; exact hb, rfl⟩
    rw [← hm, pullback.lift_fst, pullback.lift_snd_assoc, prod_unique N h₂ h₃] at h₁
    exact h₁

end

end GlobalTheory.Mum.LawDesc

namespace GlobalTheory.Mum

theorem law_of_galAct_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hG D D' hD A' G' _ _ _ U' a N hN
  have := hG.1
  let _ : Algebra R R' := ρ.toAlgebra
  let _ : MulSemiringAction (R' ≃+* R') R' := RingAut.applyMulSemiringAction
  let _ : MulSemiringAction (Gal ρ) R' := Subgroup.mulSemiringAction _
  have : SMulCommClass (Gal ρ) R R' := ⟨fun σ r x => by
    change σ.1 (ρ r * x) = ρ r * σ.1 x
    rw [map_mul, σ.2 r]⟩
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ.2.1
  have : Algebra.IsInvariant R R' (Gal ρ) := ⟨fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩
  have hq : IsAffineQuotient (specAction (Gal ρ) R') (spMap ρ) := isAffineQuotient_spec R R'
  have e : ∀ σ : Gal ρ, (specAction (Gal ρ) R' σ).asIso.hom = spMap (Gal.hom σ⁻¹) := fun σ => by
    rw [specAction_hom]; rfl
  refine LawDesc.law_of_isAffineQuotient N hq (fun σ => a.act σ⁻¹) (fun σ => ?_) fun σ => ?_
  · rw [e]; exact a.cart σ⁻¹
  · rw [e]; exact hN σ⁻¹

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupLaw_descends_galois_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  first | exact @GlobalTheory.Mum.law_of_galAct_invariant | exact GlobalTheory.Mum.law_of_galAct_invariant | (intros; apply GlobalTheory.Mum.law_of_galAct_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GlueNear

theorem isSeparated_of_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
    pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have e : j ≫ pullback.diagonal f = pullback.diagonal (j ≫ f) ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  have : UniversallyClosed (j ≫ pullback.diagonal f) := by rw [e]; infer_instance
  have : UniversallyClosed (pullback.diagonal f) := UniversallyClosed.of_comp_surjective j _
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩

theorem isPullback_iSup {Y X S S' : Scheme.{0}} (π : Y ⟶ X) (q : X ⟶ S) (t : Y ⟶ S') (f : S' ⟶ S)
    {I : Type} (V : I → X.Opens)
    (h : ∀ i, IsPullback (π ∣_ V i) ((π ⁻¹ᵁ V i).ι ≫ t) ((V i).ι ≫ q) f) :
    IsPullback (π ∣_ (⨆ i, V i)) ((π ⁻¹ᵁ (⨆ i, V i)).ι ≫ t) ((⨆ i, V i).ι ≫ q) f := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  have e : V i ≤ ⨆ i, V i := le_iSup V i
  have sq : IsPullback (Y.homOfLE (π.preimage_mono e)) (π ∣_ V i) (π ∣_ (⨆ i, V i)) (X.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ (⨆ i, V i)).ι) (h₂₂ := (⨆ i, V i).ι) (v₁₃ := π) ?_ ?_
      (isPullback_morphismRestrict π _).flip
    · simpa using (isPullback_morphismRestrict π (V i)).flip
    · rw [← cancel_mono (⨆ i, V i).ι]; simp
  refine (h i).of_iso sq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans sq.isoPullback_hom_snd.symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    erw [sq.isoPullback_hom_fst]
    simp
  · change _ = 𝟙 _ ≫ X.homOfLE e ≫ _
    simp
  · simp

theorem smooth_iSup {X S : Scheme.{0}} (q : X ⟶ S) {I : Type} (V : I → X.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  change Smooth (X.homOfLE (le_iSup V i) ≫ _)
  simpa using h i

theorem exists_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (f : S ⟶ Sp R) [IsFinite f] [Surjective f]
    (G : Over S) [IsSeparated G.hom] (H : G.left.Opens)
    (hcl : ∀ g : G.left, f (G.hom g) = closedPoint R → g ∈ H) (hc : IsCompact (H : Set G.left))
    (X : Over (Sp R)) (π : H.toScheme ⟶ X.left)
    (hloc : ∀ x : H.toScheme, f (G.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧
      Smooth (V.ι ≫ X.hom) ∧ IsPullback (π ∣_ V) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G.hom) (V.ι ≫ X.hom) f) :
    ∃ N : Near f G, ∀ (α : G.left ⟶ G.left) (β : S ⟶ S) (hα : H ≤ α ⁻¹ᵁ H), α ≫ G.hom = G.hom ≫ β →
      α.resLE H H hα ≫ π = π →
      ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left), N.Pt s u x → N.Pt (s ≫ β) u (x ≫ α) := by
  classical
  have : CompactSpace H.toScheme := isCompact_iff_compactSpace.mp hc
  let Z : Set H.toScheme := {x | f (G.hom (H.ι x)) = closedPoint R}
  have hZ : IsCompact Z := by
    refine IsClosed.isCompact ?_
    exact (isClosed_singleton_closedPoint R).preimage
      (f.continuous.comp (G.hom.continuous.comp H.ι.continuous))
  choose V hV hVa hVs hVp using fun x : Z => hloc x.1 x.2
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun x : Z => ((π ⁻¹ᵁ V x : H.toScheme.Opens) : Set H.toScheme))
    (fun x => (π ⁻¹ᵁ V x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hV ⟨x, hx⟩⟩)
  let W : t → X.left.Opens := fun i => V i.1
  have P := isPullback_iSup π X.hom (H.ι ≫ G.hom) f W fun i => hVp i.1
  have hS := smooth_iSup X.hom W fun i => hVs i.1
  have hC : IsCompact ((⨆ i, W i : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => (hVa i.1).isCompact
  have hA : ∀ x ∈ Z, π x ∈ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hx⟩
  generalize (⨆ i, W i) = U at P hS hC hA
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hC
  have hq : QuasiCompact (U.ι ≫ X.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hsep : IsSeparated (U.ι ≫ X.hom) := by
    have h₁ : IsFinite (π ∣_ U) := MorphismProperty.of_isPullback (P := @IsFinite) P.flip inferInstance
    have h₂ : Surjective (π ∣_ U) := MorphismProperty.of_isPullback (P := @Surjective) P.flip inferInstance
    have h₃ : IsSeparated (π ∣_ U ≫ U.ι ≫ X.hom) := by rw [P.w]; infer_instance
    exact isSeparated_of_surjective (π ∣_ U) _
  let N : Near f G :=
    { U := Over.mk (U.ι ≫ X.hom)
      smooth := hS
      separated := hsep
      quasiCompact := hq
      u := P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι
      isOpen := inferInstanceAs (IsOpenImmersion (P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι))
      u_over := (Category.assoc _ _ _).trans
        ((congrArg (P.isoPullback.inv ≫ ·) (Category.assoc _ _ _)).trans P.isoPullback_inv_snd)
      all := by
        intro g hg
        refine ⟨P.isoPullback.hom ⟨⟨g, hcl g hg⟩, hA ⟨g, hcl g hg⟩ hg⟩, ?_⟩
        change (P.isoPullback.hom ≫ P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι) _ = g
        rw [Iso.hom_inv_id_assoc]
        rfl }
  have pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (u : T ⟶ U.toScheme) (x : T ⟶ G.left), N.Pt s u x ↔
      ∃ y : T ⟶ (π ⁻¹ᵁ U).toScheme, y ≫ π ∣_ U = u ∧ y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι ≫ G.hom = s ∧
        y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = x := by
    intro T s u x
    constructor
    · rintro ⟨x₀, h₁, h₂, h₃⟩
      refine ⟨x₀ ≫ P.isoPullback.inv, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans h₃
    · rintro ⟨y, h₁, h₂, h₃⟩
      refine ⟨y ≫ P.isoPullback.hom, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (P.isoPullback.hom_inv_id_assoc _)).trans h₃)
  refine ⟨N, fun α β hα hαβ hπ T s u x hx => ?_⟩
  obtain ⟨y, rfl, rfl, rfl⟩ := (pt s u x).1 hx
  have Q := isPullback_morphismRestrict π U
  let δ : (π ⁻¹ᵁ U).toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
    Q.lift (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ α.resLE H H hα) (by rw [Category.assoc, hπ, Q.w])
  have hδ : δ ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = (π ⁻¹ᵁ U).ι ≫ H.ι ≫ α := by
    rw [Q.lift_snd_assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
  refine (pt _ _ _).2 ⟨y ≫ δ, ?_, ?_, ?_⟩
  · rw [Category.assoc, Q.lift_fst]
  · simp only [Category.assoc]
    rw [reassoc_of% hδ, hαβ]
  · simp only [Category.assoc]
    rw [hδ]

theorem glue_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ _ D D' hD A' G' _ _ hG U' a H hH hcl hc X π hX _ _ hπ _ _ hloc
  have := hG.separated
  have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hρ.2.2
  have : Surjective (spMap ρ) := ⟨RingHom.IsIntegral.comap_surjective hρ.2.2.to_isIntegral hρ.2.1⟩
  obtain ⟨N, hN⟩ := exists_near (spMap ρ) G' H hcl hc X π fun x hx => by
    obtain ⟨V, h₁, h₂, h₃, h₄⟩ := hloc x hx
    refine ⟨V, h₁, h₂, h₃, ?_⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (@asIso _ _ _ _ _ h₄) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [Scheme.Hom.resLE_comp_ι_assoc, hX]
    simp only [Category.assoc]
  exact ⟨N, fun σ => hN (a.act σ) _ (hH σ).ge (a.cart σ).1.w (hπ σ)⟩

end GlobalTheory.Mum.GlueNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_local_descents_near_closedFibre_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  first | exact @GlobalTheory.Mum.GlueNear.glue_near | exact GlobalTheory.Mum.GlueNear.glue_near | (intros; apply GlobalTheory.Mum.GlueNear.glue_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_quotient_of_invariant_open {Γ : Type} [Group Γ] [Finite Γ] {Y S : Scheme.{0}} (act : Γ → (Y ⟶ Y))
    (h1 : act 1 = 𝟙 _) (hm : ∀ σ τ, act (σ * τ) = act σ ≫ act τ) (s : Y ⟶ S) (hs : ∀ σ, act σ ≫ s = s)
    (H : Y.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H)
    (hO : ∀ x ∈ H, ∃ O : Y.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) :
    ∃ (X : Over S) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ s ∧ IsAffineHom π ∧ Surjective π ∧
      (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) ∧
      (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) ∧
      ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V),
        (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  let r : Γ → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hr : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  have r1 : r 1 = 𝟙 _ := by
    rw [← cancel_mono H.ι, hr, h1, Category.id_comp, Category.comp_id]
  have rm : ∀ σ τ, r (σ * τ) = r σ ≫ r τ := fun σ τ => by
    rw [← cancel_mono H.ι, hr, hm, Category.assoc, hr, reassoc_of% hr]
  let ρ : Γ →* Aut H.toScheme := MonoidHom.mk'
    (fun σ => ⟨r σ⁻¹, r σ, by rw [← rm, inv_mul_cancel, r1], by rw [← rm, mul_inv_cancel, r1]⟩)
    (fun σ τ => Aut.ext (Iso.ext (show r (σ * τ)⁻¹ = r τ⁻¹ ≫ r σ⁻¹ by rw [mul_inv_rev, rm])))
  have hρ : ∀ σ, (ρ σ).asIso.hom = r σ⁻¹ := fun _ => rfl
  have hρ' : ∀ σ, r σ = (ρ σ⁻¹).asIso.hom := fun σ => by rw [hρ, inv_inv]
  have hpt : ∀ σ (x : H.toScheme), H.ι (r σ x) = act σ (H.ι x) := fun σ x => congr($(hr σ) x)
  have : OrbitsInAffineOpens ρ := ⟨fun x => by
    obtain ⟨O, hO₁, hO₂, hO₃⟩ := hO (H.ι x) x.2
    refine ⟨H.ι ⁻¹ᵁ O, hO₁.preimage_of_isOpenImmersion H.ι (by rwa [Scheme.Opens.opensRange_ι]), fun g => ?_⟩
    change H.ι (r g⁻¹ x) ∈ O
    rw [hpt]
    exact hO₃ _⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hinv : ∀ g, (ρ g).asIso.hom ≫ H.ι ≫ s = H.ι ≫ s := fun g => by
    rw [hρ, reassoc_of% hr, hs]
  refine ⟨Over.mk (hπ.desc (H.ι ≫ s) hinv), π, hπ.comp_desc _ hinv, hπ.isAffineHom, hπ.surjective, fun σ => ?_,
    fun x y hxy => ?_, fun V => ⟨hπ.app_injective V, fun f hf => ?_⟩⟩
  · exact (congrArg (· ≫ π) (hρ' σ)).trans (hπ.comp_eq _)
  · obtain ⟨g, rfl⟩ := (hπ.apply_eq_iff x y).mp hxy
    exact ⟨g⁻¹, (hpt _ _).symm⟩
  · exact hπ.mem_range_app V f fun g => ⟨hπ.preimage_le V g, hf g⁻¹ _⟩

theorem exists_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  intro R _ _ _ _ R' _ _ _ ρ _ hG D D' hD A' G' _ _ _ U' a H hH hO
  have := hG.1
  refine exists_quotient_of_invariant_open a.act a.act_one a.act_mul (G'.hom ≫ spMap ρ) (fun σ => ?_) H hH hO
  have e : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.2 x
  rw [← Category.assoc, (a.cart σ).1.w, Category.assoc, e]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_quotient_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  first | exact @GlobalTheory.Mum.exists_galois_quotient | exact GlobalTheory.Mum.exists_galois_quotient | (intros; apply GlobalTheory.Mum.exists_galois_quotient <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ N : Near (spMap ρ) G', N.Law ∧ ∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS U' a
  obtain ⟨H, hH, hall, hc, horb⟩ := GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a
  obtain ⟨X, π, hX, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_galois_quotient_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb
  obtain ⟨N, hN⟩ := GlobalTheory.T.glue_local_descents_near_closedFibre_galois R hR R' ρ hF hG D D' hD A' G' hS U' a H hH hall hc X π hX h1 h2 h3 h4 h5
    (GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb X π hX h1 h2 h3 h4 h5)
  exact ⟨N, GlobalTheory.T.groupLaw_descends_galois_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a N hN, hN⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapClosedPointOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dense_of_closedFibre_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G],
    IsSemiAbelian G → ∀ O : G.left.Opens, (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → Dense (O : Set G.left) := by
  intro R _ _ _ G _ hG O hO
  haveI := hG.smooth
  haveI := hG.geomConnected
  let g₀ : G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)
  have hg₀ : G.hom g₀ = closedPoint R := by
    have := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
    change ((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
    rw [this]; rfl
  have : IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩
  exact O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩

theorem spMap_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) : spMap ρ (closedPoint R') = closedPoint R := by
  algebraize [ρ]
  have : Algebra.IsIntegral R R' := ⟨fun x => hf.to_isIntegral x⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R
  have : (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R')
  exact IsLocalRing.eq_maximalIdeal this

theorem comp_eq_of_near {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) (G' : Over (Sp R')) [GrpObj G'] (hG' : IsSemiAbelian G') (N : Near (spMap ρ) G')
    (G : Over (Sp R)) [GrpObj G] (hG : IsSeparated G.hom) (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ)
    (i : N.U ⟶ G) (hu : N.u ≫ β = pullback.fst _ _ ≫ i.left) (σ : Gal ρ) (g : G'.left ⟶ G'.left)
    (hg : g ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ))
    (hinv : ∀ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x →
      N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ g)) : g ≫ β = β := by
  haveI := hG'.smooth
  haveI := N.isOpen
  have hred : IsReduced G'.left := GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom
  have hd := dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by
    obtain ⟨y, hy⟩ := N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)
    exact ⟨y, hy⟩)
  haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩
  have hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  refine ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_
  · rw [Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]
  · obtain ⟨x₁, h1, -, h3⟩ := hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩
    rw [← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galois_action : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hG' U' a
  obtain ⟨N, hL, hinv⟩ := exists_near_galois_quotient R hB R' ρ hF hG D D' hD A' G' hG' U' a
  have hP : IsProper (spMap ρ) := by
    have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    infer_instance
  have hS : Surjective (spMap ρ) := ⟨hF.2.2.to_isIntegral.comap_surjective hF.2.1⟩
  obtain ⟨G, _, _, β, i, hGs, hpb, -, hu⟩ :=
    descend_of_near R hB.1 (Sp R') (spMap ρ) hP hS inferInstance G' hG' N hL
  exact has_of_galAct R hB R' ρ hF hG D D' hD A' G' hG' U' a G β hGs hpb fun σ =>
    comp_eq_of_near ρ hF.2.2 G' hG' N G hGs.separated β hpb.1.w i hu σ (a.act σ) (a.cart σ).1.w (hinv σ)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_semiAbelian_galois_descent : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  first | exact @GlobalTheory.Mum.has_of_galois_action | exact GlobalTheory.Mum.has_of_galois_action | (intros; apply GlobalTheory.Mum.has_of_galois_action <;> assumption)
end
