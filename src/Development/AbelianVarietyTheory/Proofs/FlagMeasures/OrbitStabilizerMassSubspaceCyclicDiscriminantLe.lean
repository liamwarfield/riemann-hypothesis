module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGenerato
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGenerato
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimDisc

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [dual, Formalism.E.hdual, Submodule.mem_iInf]

omit [NumberField K] in
theorem star_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  constructor
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this

omit [StarRing K] [FiniteDimensional K V] in
theorem lat_map (A : Submodule K V) (p : V →ₗ[K] A) (hp : Function.Surjective p)
    (N : Submodule (𝓞 K) V) (hN : Submodule.IsFullLattice K N) :
    Submodule.IsFullLattice K (N.map (p.restrictScalars (𝓞 K))) := by
  haveI : Submodule.IsLattice K (N.map (p.restrictScalars (𝓞 K))) :=
    Submodule.IsLattice.of_fg K (hN.fg.map _)
  refine ⟨?_⟩
  change Submodule.span K (p '' (N : Set V)) = ⊤
  rw [← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hp]

theorem dual_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hp : PD h) (A : Submodule K V)
    (hsA : (hRes h A).IsSymm) (hpA : PD (hRes h A)) (p : V →ₗ[K] A) (hsur : Function.Surjective p)
    (hh : ∀ (x : V) (a : A), h (p x : V) (a : V) = h x a)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    IsIntLat (hRes h A) (latIn A L) ∧
      dual (hRes h A) (latIn A L) = (dual h L).map (p.restrictScalars (𝓞 K)) := by
  obtain ⟨h1, h2, -⟩ := dualLattice (𝓞 K) K V h hs (nondeg h hp) star_range L hL.1
  obtain ⟨k1, k2, -⟩ := dualLattice (𝓞 K) K A (hRes h A) hsA (nondeg _ hpA) star_range _
    (lat_map A p hsur _ h1)
  have e : dual (hRes h A) ((dual h L).map (p.restrictScalars (𝓞 K))) = latIn A L := by
    ext a
    have : a ∈ latIn A L ↔ (a : V) ∈ dual h (dual h L) := by rw [h2]; rfl
    rw [this, mem_dual, mem_dual]
    constructor
    · intro H y hy
      rw [← hh]
      exact H (p y) ⟨y, hy, rfl⟩
    · rintro H _ ⟨y, hy, rfl⟩
      have := H y hy
      rw [← hh] at this
      exact this
  rw [e] at k1 k2
  exact ⟨⟨k1, fun x hx y hy => hL.2 x hx y hy⟩, k2⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) :
    idxN (L.map (p.restrictScalars (𝓞 K))) (latIn A L) =
      idxN (L.map (q.restrictScalars (𝓞 K))) (latIn B L) := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right]
  conv_rhs => rw [← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  change ((p x : V) ∈ L ∧ x ∈ L) ↔ ((q x : V) ∈ L ∧ x ∈ L)
  refine and_congr_left fun hx => ?_
  rw [← hpq x] at hx
  exact ⟨fun H => (L.add_mem_iff_right H).1 hx, fun H => (L.add_mem_iff_left H).1 hx⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_map_dvd (A : Submodule K V) (p : V →ₗ[K] A) (L N : Submodule (𝓞 K) V) :
    idxN (N.map (p.restrictScalars (𝓞 K))) (L.map (p.restrictScalars (𝓞 K))) ∣ idxN N L := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup _ N, ← AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_dvd_of_le_left _ fun x hx => ⟨x, hx, rfl⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem idx_mul (A B C : Submodule (𝓞 K) V) (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem latIn_le (A : Submodule K V) (p : V →ₗ[K] A) (hp : ∀ a : A, p a = a)
    (L : Submodule (𝓞 K) V) : latIn A L ≤ L.map (p.restrictScalars (𝓞 K)) :=
  fun a ha => ⟨a, ha, hp a⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem gens_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hp : ∀ a : A, p a = a) (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) (t : Finset B)
    (ht : L.map (q.restrictScalars (𝓞 K)) = latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B)) :
    ∃ t' : Finset A, t'.card ≤ t.card ∧
      L.map (p.restrictScalars (𝓞 K)) = latIn A L ⊔ Submodule.span (𝓞 K) (t' : Set A) := by
  have hl : ∀ b : t, ∃ l ∈ L, q l = b := fun b => by
    have : (b : B) ∈ L.map (q.restrictScalars (𝓞 K)) := by
      rw [ht]
      exact Submodule.mem_sup_right (Submodule.subset_span b.2)
    exact this
  choose f hf1 hf2 using hl
  refine ⟨Finset.univ.image fun b => p (f b), Finset.card_image_le.trans (by simp), ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hq : q x ∈ latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B) := ht ▸ ⟨x, hx, rfl⟩
    have e : (t : Set B) = (q.restrictScalars (𝓞 K)) '' Set.range f := by
      ext b
      constructor
      · intro hb
        exact ⟨f ⟨b, hb⟩, ⟨_, rfl⟩, hf2 _⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        have : q (f c) ∈ t := by rw [hf2]; exact c.2
        exact this
    rw [e, ← Submodule.map_span] at hq
    obtain ⟨s, hs, _, ⟨y, hy, rfl⟩, hsy⟩ := Submodule.mem_sup.1 hq
    have hyL : y ∈ L := (Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hf1 c)) hy
    refine Submodule.mem_sup.2 ⟨p (x - y), ?_, p y, ?_, by simp⟩
    · have e1 : q (x - y) = s := by
        rw [map_sub, ← hsy]; simp
      have e2 := hpq (x - y)
      rw [e1] at e2
      change (p (x - y) : V) ∈ L
      rw [eq_sub_of_add_eq e2]
      exact L.sub_mem (L.sub_mem hx hyL) hs
    · have : p y ∈ (Submodule.span (𝓞 K) (Set.range f)).map (p.restrictScalars (𝓞 K)) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
  · refine sup_le (latIn_le A p hp L) (Submodule.span_le.2 ?_)
    intro a ha
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨f b, hf1 b, rfl⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L U e hL ⟨t, hte, ht⟩
  obtain ⟨hc, hsU, hpU, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 (perp h U)
  set W := perp h U with hW
  have horth : ∀ (u : U) (w : W), h (u : V) (w : V) = 0 := fun u w => by
    have := w.2
    simp only [hW, perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this u u.2
  have horth' : ∀ (u : U) (w : W), h (w : V) (u : V) = 0 := fun u w => by
    rw [← hs.eq, horth, map_zero]
  let p : V →ₗ[K] U := U.projectionOnto W hc
  let q : V →ₗ[K] W := W.projectionOnto U hc.symm
  have hpq : ∀ x, (p x : V) + q x = x := Submodule.projection_add_projection_eq_self hc
  have hp1 : ∀ a : U, p a = a := Submodule.projectionOnto_apply_left hc
  have hq1 : ∀ a : W, q a = a := Submodule.projectionOnto_apply_left hc.symm
  obtain ⟨iU, dU⟩ := dual_latIn h hs hp U hsU hpU p (Submodule.projectionOnto_surjective hc)
    (fun x a => by conv_rhs => rw [← hpq x, map_add (f := _), LinearMap.add_apply, horth', add_zero]) L hL
  obtain ⟨iW, dW⟩ := dual_latIn h hs hp W hsW hpW q (Submodule.projectionOnto_surjective hc.symm)
    (fun x a => by conv_rhs => rw [← hpq x, map_add (f := _), LinearMap.add_apply, horth, zero_add]) L hL
  have hLd : L ≤ dual h L := by rw [ht]; exact le_sup_left
  have nL := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs (nondeg h hp) L hL).1
  have nU := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K U _ hK hsU (nondeg _ hpU) _ iU).1
  have mU := idx_mul _ _ _ (latIn_le U p hp1 L) (Submodule.map_mono hLd)
  have mW := idx_mul _ _ _ (latIn_le W q hq1 L) (Submodule.map_mono hLd)
  have sw := idx_swap U W p q hpq L
  have dvU : idxN (L.map (q.restrictScalars (𝓞 K))) (latIn W L) ∣ discN (hRes h U) (latIn U L) := by
    rw [discN, dU, ← mU, sw]
    exact dvd_mul_right _ _
  refine ⟨iU, iW, ?_, ?_⟩
  · rw [discN, dW, ← mW]
    exact Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero nU) dvU)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero nL) (idx_map_dvd W q L _))
  · obtain ⟨s, hs1, hs2⟩ := (GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K W _ _ (latIn_le W q hq1 L)
      (ne_zero_of_dvd_ne_zero nU dvU)).1 (hL.1.fg.map _)
    obtain ⟨s', h1, h2⟩ := gens_swap U W p q hp1 hpq L s hs2
    refine ⟨s' ∪ t.image p, (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h1.trans hs1) (Finset.card_image_le.trans hte)), ?_⟩
    rw [dU, ht, Submodule.map_sup, h2, Submodule.map_span, Finset.coe_union, Submodule.span_union,
      sup_assoc, Finset.coe_image]
    rfl

end GlobalTheory.Mass.PrimDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGeneratoStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  first | exact @GlobalTheory.Mass.PrimDisc.main | exact GlobalTheory.Mass.PrimDisc.main | (intros; apply GlobalTheory.Mass.PrimDisc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplement
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Glue

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

private lemma apply_self_ne_zero_of_PD {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hpd : _root_.GlobalTheory.Mass.PD h) {x : V} (hx : x ≠ 0) : h x x ≠ 0 := by
  unfold _root_.GlobalTheory.Mass.PD at hpd
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  intro h0
  have := hpd τ x hx
  simp [h0] at this

private lemma nondegenerate_of_PD {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hpd : _root_.GlobalTheory.Mass.PD h) : h.Nondegenerate :=
  ⟨fun x hx => by_contra fun h0 => apply_self_ne_zero_of_PD hpd h0 (hx x),
    fun y hy => by_contra fun h0 => apply_self_ne_zero_of_PD hpd h0 (hy y)⟩

private lemma idxN_dual_hRes_ne_zero_of_isIntLat [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hK : _root_.Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hpd : _root_.GlobalTheory.Mass.PD h)
    (W : Submodule K V) {A : Submodule (𝓞 K) W}
    (hA : _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h W) A) :
    _root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h W) A) A ≠ 0 := by
  have hw := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hpd).2 W
  have := (_root_.GlobalTheory.Mass.DiscOrder.main K W _ hK hw.2.1
    (nondegenerate_of_PD hw.2.2.1) A hA).1
  unfold _root_.GlobalTheory.Mass.discN at this
  exact this

private lemma index_sup_map_le_lemma_2 {W₁ W₂ : Submodule K V} {A₁ A₁' : Submodule (𝓞 K) W₁}
    {A₂ A₂' : Submodule (𝓞 K) W₂}
    (hn : _root_.GlobalTheory.Mass.idxN A₁' A₁ * _root_.GlobalTheory.Mass.idxN A₂' A₂ ≠ 0) :
    _root_.GlobalTheory.Mass.idxN
        (A₁'.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂'.map (W₂.subtype.restrictScalars (𝓞 K)))
        (A₁.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂.map (W₂.subtype.restrictScalars (𝓞 K))) ≤
      _root_.GlobalTheory.Mass.idxN A₁' A₁ * _root_.GlobalTheory.Mass.idxN A₂' A₂ ∧
    _root_.GlobalTheory.Mass.idxN
        (A₁'.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂'.map (W₂.subtype.restrictScalars (𝓞 K)))
        (A₁.map (W₁.subtype.restrictScalars (𝓞 K)) ⊔ A₂.map (W₂.subtype.restrictScalars (𝓞 K))) ≠ 0 := by
  simp only [_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_card] at hn ⊢
  rw [← Nat.card_prod] at hn ⊢
  let ι₁ := W₁.subtype.restrictScalars (𝓞 K)
  let ι₂ := W₂.subtype.restrictScalars (𝓞 K)
  let Y := A₁'.map ι₁ ⊔ A₂'.map ι₂
  let X := A₁.map ι₁ ⊔ A₂.map ι₂
  let Z := Submodule.comap Y.subtype X
  let φ₁ : A₁' →ₗ[𝓞 K] Y ⧸ Z := Z.mkQ ∘ₗ LinearMap.codRestrict Y (ι₁ ∘ₗ A₁'.subtype)
    (fun x => Submodule.mem_sup_left (Submodule.mem_map_of_mem x.2))
  let φ₂ : A₂' →ₗ[𝓞 K] Y ⧸ Z := Z.mkQ ∘ₗ LinearMap.codRestrict Y (ι₂ ∘ₗ A₂'.subtype)
    (fun x => Submodule.mem_sup_right (Submodule.mem_map_of_mem x.2))
  let g₁ := (Submodule.comap A₁'.subtype A₁).liftQ φ₁ (fun x hx => by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)))
  let g₂ := (Submodule.comap A₂'.subtype A₂).liftQ φ₂ (fun x hx => by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem hx)))
  let G : (A₁' ⧸ Submodule.comap A₁'.subtype A₁) × (A₂' ⧸ Submodule.comap A₂'.subtype A₂) →
      Y ⧸ Z := fun p => g₁ p.1 + g₂ p.2
  have hG : Function.Surjective G := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Z z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 y.2
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Submodule.mem_map.1 hb
    refine ⟨(Submodule.Quotient.mk ⟨a₀, ha₀⟩, Submodule.Quotient.mk ⟨b₀, hb₀⟩), ?_⟩
    simp only [G, g₁, g₂, Submodule.liftQ_apply, φ₁, φ₂, LinearMap.comp_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext hab
  haveI : Finite ((A₁' ⧸ Submodule.comap A₁'.subtype A₁) ×
      (A₂' ⧸ Submodule.comap A₂'.subtype A₂)) := Nat.finite_of_card_ne_zero hn
  haveI : Finite (Y ⧸ Z) := Finite.of_surjective G hG
  haveI : Nonempty (Y ⧸ Z) := ⟨0⟩
  exact ⟨Nat.card_le_card_of_surjective G hG, Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩⟩

private lemma le_dual_of_apply_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    (hL : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ _root_.Formalism.HermitianLatticesTheory.dual h L := by
  intro y hy
  rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro x hx
  exact hL x hx y hy

private lemma apply_mem_one_of_isIntLat {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : _root_.GlobalTheory.Mass.IsIntLat h L) :
    ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K) := by
  unfold _root_.GlobalTheory.Mass.IsIntLat at hL
  have := hL.2
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat at this
  exact this

private lemma mem_latIn_iff {W : Submodule K V} {L : Submodule (𝓞 K) V}
    {x : W} : x ∈ _root_.GlobalTheory.Mass.latIn W L ↔ (x : V) ∈ L := by
  unfold _root_.GlobalTheory.Mass.latIn; exact Iff.rfl

private lemma hRes_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V)
    (x y : W) : _root_.GlobalTheory.Mass.hRes h W x y = h x y := by
  unfold _root_.GlobalTheory.Mass.hRes; rfl

private lemma apply_eq_zero_of_mem_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {W : Submodule K V} {x w : V} (hx : x ∈ W) (hw : w ∈ _root_.GlobalTheory.Mass.perp h W) :
    h w x = 0 := by
  rw [← hs.eq x w, (_root_.GlobalTheory.Mass.Witt.mem_perp h W w).1 hw x hx, map_zero]

private lemma le_sup_map_dual_latIn_perp {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {W : Submodule K V}
    (hc : IsCompl W (_root_.GlobalTheory.Mass.perp h W)) {L : Submodule (𝓞 K) V}
    (hL : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) :
    L ≤ (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h W) (_root_.GlobalTheory.Mass.latIn W L)).map
        (W.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h W))
        (_root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h W) L)).map
        ((_root_.GlobalTheory.Mass.perp h W).subtype.restrictScalars (𝓞 K)) := by
  intro x hx
  have hxs : x ∈ W ⊔ _root_.GlobalTheory.Mass.perp h W := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hxs
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨⟨u, hu⟩, ?_, rfl⟩)
    (Submodule.mem_map.2 ⟨⟨w, hw⟩, ?_, rfl⟩)
  · rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hyL := hL _ (mem_latIn_iff.1 hy) _ hx
    rw [map_add (f := _), (_root_.GlobalTheory.Mass.Witt.mem_perp h W w).1 hw _ y.2, add_zero] at hyL
    rw [hRes_apply]
    exact hyL
  · rw [_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hyL := hL _ (mem_latIn_iff.1 hy) _ hx
    rw [map_add (f := _), apply_eq_zero_of_mem_perp hs hu y.2, zero_add] at hyL
    rw [hRes_apply]
    exact hyL

theorem _root_.GlobalTheory.Mass.Glue.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U)
    (B : Submodule (𝓞 K) (_root_.GlobalTheory.Mass.perp h U)) (e e' : ℕ),
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h U) A →
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B →
    (∃ t : Finset ↥U, t.card ≤ e ∧ _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A =
      A ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    (∃ t : Finset ↥(_root_.GlobalTheory.Mass.perp h U), t.card ≤ e' ∧
      _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B =
        B ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    {L : Submodule (𝓞 K) V | _root_.GlobalTheory.Mass.IsIntLat h L ∧ _root_.GlobalTheory.Mass.latIn U L = A ∧
      _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) L = B}.encard ≤
      (((_root_.GlobalTheory.Mass.discN (_root_.GlobalTheory.Mass.hRes h U) A *
        _root_.GlobalTheory.Mass.discN
          (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B e e' hA hB ⟨t, ht, htA⟩ ⟨t', ht', htB⟩
  have hc := ((_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hpd).2 U).1
  have hdA := idxN_dual_hRes_ne_zero_of_isIntLat hK hs hpd U hA
  have hdB := idxN_dual_hRes_ne_zero_of_isIntLat hK hs hpd _ hB
  unfold _root_.GlobalTheory.Mass.discN
  obtain ⟨hle, hne⟩ := index_sup_map_le_lemma_2 (A₁ := A) (A₁' := _root_.Formalism.HermitianLatticesTheory.dual _ A) (A₂ := B)
    (A₂' := _root_.Formalism.HermitianLatticesTheory.dual _ B) (mul_ne_zero hdA hdB)
  have hXY : A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
      B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) ≤
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map (U.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map
        ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) :=
    sup_le_sup (Submodule.map_mono (le_dual_of_apply_mem_one _ (apply_mem_one_of_isIntLat hA)))
      (Submodule.map_mono (le_dual_of_apply_mem_one _ (apply_mem_one_of_isIntLat hB)))
  have hT : (t.image Subtype.val ∪ t'.image Subtype.val).card ≤ e + e' :=
    (Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_image_le.trans ht) (Finset.card_image_le.trans ht'))
  have hY : (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map
      (U.subtype.restrictScalars (𝓞 K)) ⊔
      (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)) =
      (A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
        B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K))) ⊔
      Submodule.span (𝓞 K) ((t.image Subtype.val ∪ t'.image Subtype.val : Finset V) : Set V) := by
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Submodule.span_union, htA, htB,
      Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Submodule.map_span]
    exact sup_sup_sup_comm _ _ _ _
  have hcount := ((_root_.GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ hXY hne).2 (e + e') _
    hT hY).1
  have hpow : ((_root_.GlobalTheory.Mass.idxN
      ((_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A).map (U.subtype.restrictScalars (𝓞 K)) ⊔
        (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B).map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K)))
      (A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
        B.map ((_root_.GlobalTheory.Mass.perp h U).subtype.restrictScalars (𝓞 K))) ^ (e + e')
        : ℕ) : ℕ∞) ≤
      (((_root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A) A *
        _root_.GlobalTheory.Mass.idxN (_root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h
          (_root_.GlobalTheory.Mass.perp h U)) B) B) ^ (e + e') : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.pow_le_pow_left hle (e + e')
  refine le_trans (Set.encard_le_encard ?_) (hcount.trans hpow)
  rintro L ⟨hL, hLU, hLP⟩
  refine ⟨sup_le ?_ ?_, ?_⟩
  · rw [Submodule.map_le_iff_le_comap, ← hLU]
    unfold _root_.GlobalTheory.Mass.latIn
    exact le_rfl
  · rw [Submodule.map_le_iff_le_comap, ← hLP]
    unfold _root_.GlobalTheory.Mass.latIn
    exact le_rfl
  · have := le_sup_map_dual_latIn_perp hs hc (apply_mem_one_of_isIntLat hL)
    rw [hLU, hLP] at this
    exact this
end

end GlobalTheory.Mass.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplementStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitianLattices_glued_subspace_complement : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (e e' : ℕ), IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → (∃ t : Finset ↥U, t.card ≤ e ∧ dual (hRes h U) A = A ⊔ Submodule.span (𝓞 K) (t : Set _)) → (∃ t : Finset ↥(perp h U), t.card ≤ e' ∧ dual (hRes h (perp h U)) B = B ⊔ Submodule.span (𝓞 K) (t : Set _)) → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ (((discN (hRes h U) A * discN (hRes h (perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.Glue.main | exact GlobalTheory.Mass.Glue.main | (intros; apply GlobalTheory.Mass.Glue.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMul
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.ProdMass

noncomputable def wt (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (x : α) : ℝ≥0∞ :=
  if x ∈ X then ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ else 0

theorem orbMass_eq (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) :
    orbMass G X = ∑' q : MulAction.orbitRel.Quotient G α, wt G X (Quotient.out q) := by
  unfold orbMass orbSum
  have := tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
  refine this.trans (tsum_congr fun q => ?_)
  simp [Set.indicator, wt]

theorem wt_rel (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (hX : Stable G X)
    {x y : α} (h : MulAction.orbitRel G α x y) : wt G X x = wt G X y := by
  have hc : ENat.card (MulAction.stabilizer G x) = ENat.card (MulAction.stabilizer G y) :=
    ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv
  obtain ⟨g, hg⟩ := h
  simp only at hg
  have hm : x ∈ X ↔ y ∈ X := by
    constructor
    · intro hx
      have := hX g⁻¹ x hx
      rwa [← hg, inv_smul_smul] at this
    · intro hy
      rw [← hg]; exact hX g y hy
  unfold wt
  rw [hc]
  simp only [hm]

variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))

include hφ in
theorem rel_iff (p q : α × β) : MulAction.orbitRel Γ (α × β) p q ↔
    MulAction.orbitRel G α p.1 q.1 ∧ MulAction.orbitRel G' β p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [hφ]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
    refine ⟨φ.symm (g, g'), ?_⟩
    rw [hφ]
    simp [hg, hg']

def stabEquiv (p : α × β) : MulAction.stabilizer Γ p ≃
    MulAction.stabilizer G p.1 × MulAction.stabilizer G' p.2 where
  toFun γ := (⟨(φ γ).1, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.fst this).symm⟩, ⟨(φ γ).2, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.snd this).symm⟩)
  invFun g := ⟨φ.symm (g.1, g.2), by
    rw [MulAction.mem_stabilizer_iff, hφ]
    have h1 : (g.1 : G) • p.1 = p.1 := g.1.2
    have h2 : (g.2 : G') • p.2 = p.2 := g.2.2
    simp [h1, h2]⟩
  left_inv γ := by simp
  right_inv g := by simp

include hφ in
theorem wt_prod (X : Set α) (Y : Set β) (p : α × β) :
    wt Γ (X ×ˢ Y) p = wt G X p.1 * wt G' Y p.2 := by
  unfold wt
  by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ Y <;> simp only [Set.mem_prod, h1, h2, and_self,
    and_true, and_false, if_true, if_false, mul_zero, zero_mul]
  rw [ENat.card_congr (stabEquiv φ hφ p), ENat.card_prod, ENat.toENNReal_mul, ENNReal.mul_inv]
  · left
    exact_mod_cast (ENat.card_pos (α := MulAction.stabilizer G p.1)).ne'
  · right
    exact_mod_cast (ENat.card_pos (α := MulAction.stabilizer G' p.2)).ne'

noncomputable def orbEquiv : MulAction.orbitRel.Quotient Γ (α × β) ≃
    MulAction.orbitRel.Quotient G α × MulAction.orbitRel.Quotient G' β where
  toFun := Quotient.lift (fun p => (Quotient.mk _ p.1, Quotient.mk _ p.2)) fun p q h => by
    obtain ⟨h1, h2⟩ := (rel_iff φ hφ p q).1 h
    exact Prod.ext (Quotient.sound h1) (Quotient.sound h2)
  invFun q := Quotient.mk _ (Quotient.out q.1, Quotient.out q.2)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h p =>
      refine Quotient.sound ((rel_iff φ hφ _ _).2 ⟨?_, ?_⟩)
      · exact Quotient.mk_out (s := MulAction.orbitRel G α) p.1
      · exact Quotient.mk_out (s := MulAction.orbitRel G' β) p.2
  right_inv q := by
    simp

theorem orbMass_prod : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β),
    (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y →
    (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) →
    orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  intro Γ G G' α β _ _ _ _ _ _ φ X Y hφ hX hY _ _
  have hXY : Stable Γ (X ×ˢ Y) := by
    intro γ p hp
    rw [hφ]
    exact ⟨hX _ _ hp.1, hY _ _ hp.2⟩
  rw [orbMass_eq, orbMass_eq, orbMass_eq, ← (orbEquiv φ hφ).symm.tsum_eq, ENNReal.tsum_prod',
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [← wt_prod φ hφ X Y (Quotient.out a, Quotient.out b)]
  exact wt_rel Γ _ hXY (Quotient.mk_out (s := MulAction.orbitRel Γ (α × β)) _)

end GlobalTheory.Mass.ProdMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMulStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_prod_eq_mul : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β), (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y → (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) → orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  first | exact @GlobalTheory.Mass.ProdMass.orbMass_prod | exact GlobalTheory.Mass.ProdMass.orbMass_prod | (intros; apply GlobalTheory.Mass.ProdMass.orbMass_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLe
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.FixedSub

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_def' (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    g • L = gmap (g : V ≃ₗ[K] V) L := rfl

theorem isIntLat_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V)
    (hL : IsIntLat h L) : IsIntLat h (g • L) := by
  have H := isomAct (𝓞 K) K V h g g.2 L
  refine ⟨{ toIsLattice := H.2.2.2.2.2 hL.1.toIsLattice, span_eq_top := ?_ },
    H.2.2.1.2 hL.2⟩
  change Submodule.span K ((g : V ≃ₗ[K] V).toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span, hL.1.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem dual_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    dual h (g • L) = g • dual h L := (isomAct (𝓞 K) K V h g g.2 L).1

theorem discN_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    discN h (g • L) = discN h L := by
  unfold discN
  rw [dual_smul]
  unfold idxN
  exact AddSubgroup.relIndex_map_map_of_injective (f := ((g : V ≃ₗ[K] V) : V →+ V))
    L.toAddSubgroup (dual h L).toAddSubgroup (g : V ≃ₗ[K] V).injective

theorem stable_latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) :
    Stable (isom h) (latsDisc (R := 𝓞 K) h n) := fun g L hL =>
  ⟨isIntLat_smul h g L hL.1, (discN_smul h g L).trans hL.2⟩

theorem gens_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) (e : ℕ)
    (H : ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) :
    ∃ t : Finset V, t.card ≤ e ∧ dual h (g • L) = g • L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨t, ht, H⟩ := H
  refine ⟨t.image (g : V ≃ₗ[K] V), Finset.card_image_le.trans ht, ?_⟩
  rw [dual_smul, H, smul_def', smul_def']
  unfold gmap
  rw [Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem hRes_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (U : Submodule K V) :
    (hRes h U).IsSymm := ⟨fun x y => hs.eq (x : V) (y : V)⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem hRes_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) (U : Submodule K V) :
    PD (hRes h U) := fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

omit [NumberField K] in
theorem star_int (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

theorem gens_rank [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    ∃ t : Finset V, t.card ≤ Module.finrank K V ∧
      dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  have hnd := pd_nondeg h hp
  have h0 := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd L hL).1
  have hle : L ≤ dual h L := fun x hx => (isomAct_mem_dual h L x).2 fun y hy => hL.2 y hy x hx
  exact (GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K V L (dual h L) hle h0).1
    (dualLattice (𝓞 K) K V h hs hnd star_int L hL.1).1.fg

end

theorem orbMass_stabilizer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp U n N₀
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_⟩
    rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    rcases (X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹'
      {(M, M')}).eq_empty_or_nonempty with h0 | ⟨L, ⟨l1, l2, l3, l4⟩, hL⟩
    · simp [h0]
    · have eM : latIn U L = M := congrArg Prod.fst hL
      obtain ⟨b1, b2, b3⟩ := (memB M').1 h2
      have g1 := (GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 l1 l3).2.2.2
      rw [eM] at g1
      have g2 := gens_rank hK _ hs2 hp2 M' b1
      have cnt := GlobalTheory.T.card_hermitianLattices_glued_subspace_complement K V h hK hs hp U M M' _ _ h1.1 b1 g1 g2
      have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
          {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = M ∧ latIn (perp h U) L = M'} :=
        fun N hN => ⟨hN.1.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
      have le : (discN (hRes h U) M * discN (hRes h (perp h U)) M') ^
          (Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U)) ≤
          (n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) := by
        have e : discN (hRes h U) M = n := h1.2
        rw [e, show Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U) =
          2 * Module.finrank K (perp h U) + 1 by ring]
        exact Nat.pow_le_pow_left (Nat.mul_le_mul_left n b3) _
      have fin := ((Set.encard_le_encard sub).trans cnt).trans (Nat.cast_le.2 le)
      have := ENat.toENNReal_le.2 fin
      rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

end GlobalTheory.Mass.FixedSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLeStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_subspace_cyclicDiscriminant_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  first | exact @GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | exact GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le | (intros; apply GlobalTheory.Mass.FixedSub.orbMass_stabilizer_le <;> assumption)
end
