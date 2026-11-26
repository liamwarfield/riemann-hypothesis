module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  let u : ∀ j, Γ(Y, L.U j)ˣ := fun j => t.s j * (t'.s j)⁻¹
  have compat : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (u i) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (u j) := by
    intro i j
    simp only [u, map_mul, map_inv, ht i j, ht' i j, mul_inv]
    simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (v : ∀ j, Γ(Y, L.U j)ˣ),
      (∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (v i) =
        res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (v j)) →
      ∃ s : Γ(Y, ⊤), ∀ j, resG Y (le_top : L.U j ≤ ⊤) s = (v j).val := by
    intro v hv
    exact (TopCat.Sheaf.existsUnique_gluing' Y.sheaf L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL) _ (by
        intro i j
        exact congrArg Units.val (hv i j))).exists
  obtain ⟨s, hs⟩ := glue u compat
  have compat' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) ((u i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) ((u j)⁻¹) := by
    intro i j
    rw [map_inv, map_inv, compat]
  obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compat'
  have hss : s * s' = 1 := by
    apply Y.sheaf.eq_of_locally_eq' L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    change resG Y (le_top : L.U j ≤ ⊤) (s * s') = resG Y (le_top : L.U j ≤ ⊤) 1
    rw [map_mul, map_one, hs, hs']
    exact Units.mul_inv (u j)
  let w : Γ(Y, ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
  refine ⟨w, fun j => ?_⟩
  have hw : res (le_top : L.U j ≤ ⊤) w = u j := Units.ext (hs j)
  rw [hw]
  change t.s j = (t.s j * (t'.s j)⁻¹) * t'.s j
  simp

theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup (M.pull x).U := by
    intro y _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (show x y ∈ (⊤ : X.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  have global : ∃ w : Γ(Sp R, ⊤)ˣ, ∀ j, τ.s j = res (le_top : (M.pull x).U j ≤ ⊤) w * τ'.s j := by
    let u : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ := fun j => τ.s j * (τ'.s j)⁻¹
    have compat : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (u i) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (u j) := by
      intro i j
      simp only [u, map_mul, map_inv, hτ i j, hτ' i j, mul_inv]
      simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
    have glue : ∀ (v : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ),
        (∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (v i) =
          res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (v j)) →
        ∃ s : Γ((Sp R), ⊤), ∀ j, resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) s = (v j).val := by
      intro v hv
      exact (TopCat.Sheaf.existsUnique_gluing' (Sp R).sheaf (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov _ (by
          intro i j
          exact congrArg Units.val (hv i j))).exists
    obtain ⟨s, hs⟩ := glue u compat
    have compaτ' : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) ((u i)⁻¹) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) ((u j)⁻¹) := by
      intro i j
      rw [map_inv, map_inv, compat]
    obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compaτ'
    have hss : s * s' = 1 := by
      apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
      intro j
      change resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) (s * s') = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) 1
      rw [map_mul, map_one, hs, hs']
      exact Units.mul_inv (u j)
    let w : Γ((Sp R), ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
    refine ⟨w, fun j => ?_⟩
    have hw : res (le_top : (M.pull x).U j ≤ ⊤) w = u j := Units.ext (hs j)
    rw [hw]
    change τ.s j = (τ.s j * (τ'.s j)⁻¹) * τ'.s j
    simp
  obtain ⟨w, hw⟩ := global
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IsGaloisCover

theorem exists_algClosed_point (T : Scheme.{0}) (p : T) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : Sp K ⟶ T), p ∈ Set.range j := by
  let k := T.residueField p
  let K := AlgebraicClosure k
  let i : Spec (CommRingCat.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨z, ?_⟩
  have hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hz
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp hz

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}

theorem exists_local_geom (h : IsGaloisCover Ga ρ π) {T : Scheme.{0}} (x x' : T ⟶ X) (hx : x ≫ π = x' ≫ π) (p : T) :
    ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  have := h.etale
  let D := pullback.diagonal π
  let m : Ga → (T ⟶ pullback π π) := fun a =>
    pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])
  obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point T p
  obtain ⟨a, ha, -⟩ := h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])
  have hm1 : m a ≫ pullback.fst π π = x ≫ ρ a := pullback.lift_fst _ _ _
  have hm2 : m a ≫ pullback.snd π π = x' := pullback.lift_snd _ _ _
  have hjm : j ≫ m a = j ≫ x' ≫ D := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      simpa only [Category.assoc] using ha
    · rw [Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  let V : T.Opens := (m a) ⁻¹ᵁ D.opensRange
  have hpV : p ∈ V := by
    show (m a) p ∈ Set.range D
    rw [← hz]
    refine ⟨x' (j z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]
  have hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  let l := IsOpenImmersion.lift D (V.ι ≫ m a) hsub
  have hl : l ≫ D = V.ι ≫ m a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, a, hpV, ?_⟩
  have e1 : V.ι ≫ x ≫ ρ a = l := by
    have h1 : l ≫ D ≫ pullback.fst π π = l := by rw [pullback.diagonal_fst, Category.comp_id]
    rw [← h1, ← Category.assoc l, hl, Category.assoc, hm1]
  have e2 : V.ι ≫ x' = l := by
    have h2 : l ≫ D ≫ pullback.snd π π = l := by rw [pullback.diagonal_snd, Category.comp_id]
    rw [← h2, ← Category.assoc l, hl, Category.assoc, hm2]
  rw [e1, e2]

theorem existsUnique_desc (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]

variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

private theorem existsUnique_act_of_isPullback_isGaloisCover (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a) (hπ : ∀ a, ρ' a ≫ π' = π') (K : Type) [Field K] [IsAlgClosed K]
    (y y' : Sp K ⟶ X') (hy : y ≫ π' = y' ≫ π') : ∃! a, y ≫ ρ' a = y' := by
  have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
    simp only [Category.assoc, hp.w, reassoc_of% hy]
  obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
  refine ⟨a, ?_, ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hu, ← Category.assoc, ha]
    · rw [Category.assoc, hπ, hy]
  · intro b hb
    apply hauniq
    rw [Category.assoc, ← hu, ← Category.assoc, hb]

theorem isPullback (h : IsGaloisCover Ga ρ π) (h' : IsGaloisCover Ga ρ' π') (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (w : u ≫ π = π' ≫ v) : IsPullback u π' π v := by
  have := h.fin
  have := h.etale
  have := h.onto
  have := h'.fin
  have := h'.etale
  let ρP : Ga → (pullback π v ⟶ pullback π v) := fun a =>
    pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])
  have huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a := fun a => pullback.lift_fst _ _ _
  have hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v := fun a => by
    rw [← Category.comp_id (pullback.snd π v)]
    exact pullback.lift_snd _ _ _
  let φ : X' ⟶ pullback π v := pullback.lift u π' w
  have hφ1 : φ ≫ pullback.fst π v = u := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π v = π' := pullback.lift_snd _ _ _
  have hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ := fun a => by
    apply pullback.hom_ext
    · simp only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]
    · simp only [Category.assoc, hπP, hφ2, h'.inv]
  have hmono : Mono φ := by
    constructor
    intro T g₁ g₂ hg
    have hg1 : g₁ ≫ u = g₂ ≫ u := by rw [← hφ1, reassoc_of% hg]
    have hg2 : g₁ ≫ π' = g₂ ≫ π' := by rw [← hφ2, reassoc_of% hg]
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h'.exists_local_geom g₁ g₂ hg2 p
    refine ⟨V, hp, ?_⟩
    have e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u := by
      rw [← hu, hg1]
      simpa only [Category.assoc] using congrArg (· ≫ u) hV
    obtain ⟨K, _, _, j, -⟩ := exists_algClosed_point V.toScheme ⟨p, hp⟩
    have ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u := by
      simp only [Category.assoc] at e ⊢
      rw [e]
    have h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u := by
      rw [h.one, Category.comp_id]
    have ha1 : a = 1 := (h.fibre K _ _ rfl).unique ha h1
    rw [← hV, ha1, h'.one, Category.comp_id]
  have hsurj : Surjective φ := by
    constructor
    intro q
    obtain ⟨y, hy⟩ := h'.onto.surj (pullback.snd π v q)
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v)
      (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])
    obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point _ r
    obtain ⟨a, ha, -⟩ := existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K
      (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
    refine ⟨ρ' a y, ?_⟩
    have hz' := congrArg (fun m : Sp K ⟶ _ => m z) ha
    simp only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'
    rw [← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]
    exact hz'
  have : Etale φ := by
    have : Etale (φ ≫ pullback.snd π v) := by rw [hφ2]; exact h'.etale
    exact Etale.of_comp (f := φ) (pullback.snd π v)
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ pullback.snd π v) := by rw [hφ2]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ
      (pullback.snd π v) inferInstance this
  have : IsIso φ := Flat.isIso_of_surjective_of_mono φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2

theorem of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' := by
  refine ⟨h.finite, ?_, ?_, hπ, ?_, ?_, ?_, existsUnique_act_of_isPullback_isGaloisCover h hp hu hπ⟩
  · apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  · intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  · exact MorphismProperty.of_isPullback hp h.fin
  · exact MorphismProperty.of_isPullback hp h.etale
  · exact MorphismProperty.of_isPullback hp h.onto

end GlobalTheory.ZM.IsGaloisCover

namespace GlobalTheory.ZM

theorem galoisCover_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquaresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.galoisCover_descent_and_cartesian_squares : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  first | exact @GlobalTheory.ZM.galoisCover_descent | exact GlobalTheory.ZM.galoisCover_descent | (intros; apply GlobalTheory.ZM.galoisCover_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HolTorsion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}

theorem isHolTo_comp {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo B c) (φ : X ⟶ Y) :
    IsHolTo B fun b => c b ≫ φ := by
  intro U f
  have := hc (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_congr {X : Scheme.{0}} {c c' : E → (Sp ℂ ⟶ X)} (hc : IsHolTo B c) (h : ∀ b ∈ B, c' b = c b) :
    IsHolTo B c' := by
  intro U f
  have e : {b ∈ B | ⊤ ≤ c' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ c b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [h b hb]
  rw [e]
  exact ⟨(hc U f).1, (hc U f).2.congr fun b hb => by rw [h b hb.1]⟩

theorem isHolTo_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} (ha : IsHolTo B fun w => c w ≫ p)
    (hb : IsHolTo B fun w => c w ≫ q) : IsHolTo B c := by
  intro U f
  refine holFamily_of_affine valAt'_rules B Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ))) isOpen_univ
  have m₁ : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ U₀ := by
    rw [← Category.assoc] at hx₀
    exact hx₀
  have m₂ : (c w₀ ≫ q) (default : PrimeSpectrum ℂ) ∈ t ⁻¹ᵁ U₀ := by
    rw [H.w, ← Category.assoc] at hx₀
    exact hx₀
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, l₁⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open m₁ (s ⁻¹ᵁ U₀).isOpen
  obtain ⟨_, ⟨U₂, hU₂, rfl⟩, hx₂, l₂⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open m₂ (t ⁻¹ᵁ U₀).isOpen
  have hU₀ : IsAffineOpen U₀ := hU₀
  have hU₁ : IsAffineOpen U₁ := hU₁
  have hU₂ : IsAffineOpen U₂ := hU₂
  have l₁ : U₁ ≤ s ⁻¹ᵁ U₀ := l₁
  have l₂ : U₂ ≤ t ⁻¹ᵁ U₀ := l₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hU₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := U₀) (UT := U₂) (UX := U₁) l₂ l₁
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := U₀) (UT := U₂) (UX := U₁) l₂ l₁ hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hU₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w (hw : w ∈ {w ∈ B | ⊤ ≤ c w ⁻¹ᵁ V}) => ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE (c w) p U₁ V _ y hw.2
      · exact ((hb U₂ y).2.mono fun w (hw : w ∈ {w ∈ B | ⊤ ≤ c w ⁻¹ᵁ V}) => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE (c w) q U₂ V _ y hw.2
    | zero => exact (differentiableOn_const (0 : ℂ)).congr fun w _ => valAt'_zero _ _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => exact (hx.add hy).congr fun w _ => valAt'_add _ _ _ _
    | neg x _ hx => exact hx.neg.congr fun w _ => valAt'_neg _ _ _
    | mul x y _ _ hx hy => exact (hx.mul hy).congr fun w _ => valAt'_mul _ _ _ _

theorem exists_isHolTo_lift {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {a : E → (Sp ℂ ⟶ X)} {a' : E → (Sp ℂ ⟶ Y)} (ha : IsHolTo B a) (ha' : IsHolTo B a')
    (h : ∀ w ∈ B, a w ≫ s = a' w ≫ t) {b₀ : E} (hb₀ : b₀ ∈ B) :
    ∃ c : E → (Sp ℂ ⟶ Z), IsHolTo B c ∧ ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := by
  classical
  let c : E → (Sp ℂ ⟶ Z) := fun w =>
    if hw : w ∈ B then H.lift (a w) (a' w) (h w hw) else H.lift (a b₀) (a' b₀) (h b₀ hb₀)
  have hc : ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := fun w hw => by
    simp only [c, dif_pos hw, IsPullback.lift_fst, IsPullback.lift_snd, and_self]
  exact ⟨c, isHolTo_of_isPullback H (isHolTo_congr ha fun w hw => (hc w hw).1)
    (isHolTo_congr ha' fun w hw => (hc w hw).2), hc⟩

theorem mem_of_isClosed {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    (U : Z.Opens) (hU : IsClosed (U : Set Z)) {b₀ : E} (hb₀ : b₀ ∈ B) (h₀ : c b₀ (default : PrimeSpectrum ℂ) ∈ U)
    {b : E} (hb : b ∈ B) : c b (default : PrimeSpectrum ℂ) ∈ U := by
  let U' : Z.Opens := ⟨(U : Set Z)ᶜ, hU.isOpen_compl⟩
  have h := hB.subset_left_of_subset_union (hc U 0).1 (hc U' 0).1
    (Set.disjoint_left.2 fun w h₁ h₂ =>
      (top_le_preimage_iff_mem _ _).1 h₂.2 ((top_le_preimage_iff_mem _ _).1 h₁.2))
    (fun w hw => by
      by_cases hm : c w (default : PrimeSpectrum ℂ) ∈ U
      · exact Or.inl ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩
      · exact Or.inr ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩)
    ⟨b₀, hb₀, hb₀, (top_le_preimage_iff_mem _ _).2 h₀⟩
  exact (top_le_preimage_iff_mem _ _).1 (h hb).2

theorem valAt'_eq_of_pow_eq_one {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    {e : Γ(Z, ⊤)} {k : ℕ} (hk : 0 < k) (he : e ^ k = 1) {b₀ b : E} (hb₀ : b₀ ∈ B) (hb : b ∈ B) :
    valAt' (c b) ⊤ e = valAt' (c b₀) ⊤ e := by
  have hcont : ContinuousOn (fun w => valAt' (c w) ⊤ e) B :=
    (hc ⊤ e).2.continuousOn.mono fun w hw => ⟨hw, le_top⟩
  have hfin : (Polynomial.nthRootsFinset k (1 : ℂ) : Set ℂ).Finite := Finset.finite_toSet _
  refine hB.constant_of_mapsTo hfin.isDiscrete hcont (fun w _ => ?_) hb hb₀
  rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hk, ← valAt'_pow _ le_top, he, valAt'_one _ le_top]

theorem comp_eq_of_unramified {N X : Scheme.{0}} (q : N ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
    [IsSeparated q] {c : E → (Sp ℂ ⟶ pullback q q)} (hc : IsHolTo B c) (hB : IsPreconnected B) {b₀ b : E}
    (hb₀ : b₀ ∈ B) (hb : b ∈ B) (h₀ : c b₀ ≫ pullback.fst q q = c b₀ ≫ pullback.snd q q) :
    c b ≫ pullback.fst q q = c b ≫ pullback.snd q q := by
  have e₀ : c b₀ = (c b₀ ≫ pullback.fst q q) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp
    · simp [h₀]
  have hm : c b (default : PrimeSpectrum ℂ) ∈ (pullback.diagonal q).opensRange := by
    refine mem_of_isClosed hc hB _ (pullback.diagonal q).isClosedEmbedding.isClosed_range hb₀ ?_ hb
    rw [e₀]
    exact ⟨_, rfl⟩
  have hr : Set.range (c b) ⊆ Set.range (pullback.diagonal q) := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hm
  rw [← IsOpenImmersion.lift_fac (pullback.diagonal q) (c b) hr, Category.assoc, Category.assoc,
    pullback.diagonal_fst, pullback.diagonal_snd]

theorem pow_eq_one_of_weilIs (hW : Out.WeilSt) {X : Scheme.{0}} [IsLocallyNoetherian X] (P : Out.PolAV X) (k : ℕ)
    {T : Over X} {u v : T ⟶ P.A} (hu : u ^ k = 1) (hv : v ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : Out.WeilIs P.A P.L k u v e) : e ^ k = 1 := by
  obtain ⟨h₁, h₂, -⟩ := hW X P k T
  obtain ⟨d, hd, hd'⟩ := h₁ 1 v (one_pow k) hv
  have hdd := h₂ 1 1 v d d hd hd
  rw [_root_.mul_one] at hdd
  obtain rfl : d = 1 := mul_eq_left.1 (hd' _ hdd)
  have key : ∀ n : ℕ, Out.WeilIs P.A P.L k (u ^ n) v (e ^ n) := fun n => by
    induction n with
    | zero => simpa only [pow_zero] using hd
    | succ n ih => simpa only [pow_succ] using h₂ _ _ _ _ _ ih he
  have hk := key k
  rw [hu] at hk
  exact hd' _ hk

theorem val_map_appTop {Z : Scheme.{0}} (z : Sp ℂ ⟶ Z) (e : Γ(Z, ⊤)) :
    z.appTop.hom e = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (valAt' z ⊤ e) := by
  rw [valAt'_eq_valAt z (U := ⊤) le_top]
  unfold valAt
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.HolTorsion

namespace GlobalTheory

open HolTorsion in
theorem torsion_eq_and_weilIs_of_isHolTo : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X, ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c))) := by
  intro hL X _ P m k B y x x' c b₀ hk hku _ hB hb₀ hx hx' htor
  obtain ⟨hfin, -, -, het, -⟩ := hL.mulN X P k hk
  have het := het hku
  let o : X ⟶ P.A.left := (η[P.A] : 𝟙_ (Over X) ⟶ P.A).left
  have ho : o ≫ P.A.hom = 𝟙 X := Over.w (η[P.A] : 𝟙_ (Over X) ⟶ P.A)

  have hkill : ∀ (T : Over X) (u : T ⟶ P.A), u ^ k = 1 ↔ u.left ≫ (Out.mulA P.A k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA P.A k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ P.A).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA P.A k).left o
  let q := pullback.snd (Out.mulA P.A k).left o
  have H : IsPullback p q (Out.mulA P.A k).left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ P.A.hom = q := by
    rw [← Over.w (Out.mulA P.A k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx P.A.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ P.A := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ P.A := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, he, -⟩ := (hL.weil X P k T).1 u v hu hv
    have hek : e.val ^ k = 1 :=
      congrArg Units.val (pow_eq_one_of_weilIs hL.weil P k hu hv he)
    have hpull : ∀ w ∈ B, Out.WeilIs P.A P.L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      ((hL.weil X P k _).1 _ _ (htor b₀ hb₀).1 (htor b₀ hb₀).2).unique (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

def autOfRightAction {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X)) (h1 : ρ 1 = 𝟙 X)
    (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) : Ga →* Aut X :=
  MonoidHom.mk' (fun a ↦
    Aut.of
      { hom := ρ a⁻¹
        inv := ρ a
        hom_inv_id := by rw [← hm, inv_mul_cancel, h1]
        inv_hom_id := by rw [← hm, mul_inv_cancel, h1] }) fun a c ↦
    Aut.ext (Iso.ext (show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹ by rw [mul_inv_rev, hm]))

theorem autOfRightAction_hom {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X))
    (h1 : ρ 1 = 𝟙 X) (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) (a : Ga) :
    (autOfRightAction ρ h1 hm a).asIso.hom = ρ a⁻¹ := rfl

theorem _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f := by
  obtain ⟨N, i, hi, hqc, rfl⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K), π ≫ sY = s ∧ _root_.GlobalTheory.ZM.IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ X s Ga _ _ ρ hq h1 hm hs hfree
  set τ := _root_.GlobalTheory.ZM.autOfRightAction ρ h1 hm with hτ
  have horbits : _root_.GlobalTheory.OrbitsInAffineOpens τ :=
    _root_.GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hq τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hs g⁻¹
  have hfreeτ : _root_.GlobalTheory.IsFreeAction τ := by
    refine _root_.GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (_root_.GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_separated_galoisCover_of_free_action : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  first | exact @GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | exact GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | (intros; apply GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp A ⟶ Sp B) : ∃ β : B →+* A, g = spMap β :=
  ⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

def fnOn {L : Type} [CommRing L] {T : Scheme.{0}} (g : T ⟶ Sp L) : L →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom

theorem map_fnOn {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) = unitOn (Units.map β.toMonoidHom c) := by
  apply Units.ext
  show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom (c : L)) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

abbrev TateAt (D : Datum H) (t : SAB H S) {k : Type} [Field k] (x : Sp k ⟶ S) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

theorem datum_free (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La := by
  have := D.fin
  have := D.proj
  have h : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, h⟩

theorem act_nsmul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) (c : 𝓞 E) :
    x ≫ t.act.act (n • c) = (x ^ n) ≫ t.act.act c := by
  have := t.act.hom c
  rw [add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_full (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    obtain ⟨β', hβ'⟩ := exists_spMap (A := k) ((w ≫ i).left ≫ g)
    refine ⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩
    · rw [← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]
      exact congrArg (· ≫ s) (Over.w (w ≫ i))
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨β', hβ', h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩

end GlobalTheory.LevCover
end
end
