module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) (f : Γ(X, U)) :
    gs (𝟙 X) x U f = (X.presheaf.germ U x h).hom f := by
  rw [gs_eq (𝟙 X) x U h]; rfl

theorem lbIso_of_germs (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → (∃ i, IsUnit (gs (𝟙 X) y (A.U k) ((a i).f k))) ∧
      ∃ u : (X.presheaf.stalk y)ˣ, ∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) :
    LBIso A B := by
  have uniq : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → ∀ u u' : (X.presheaf.stalk y)ˣ,
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) →
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u' * gs (𝟙 X) y (A.U k) ((a i).f k)) → u = u' := by
    intro y j k hj hk u u' h h'
    obtain ⟨i, hi⟩ := (H y j k hj hk).1
    exact Units.ext (hi.mul_right_cancel ((h i).symm.trans (h' i)))
  have loc : ∀ (j : B.ι) (k : A.ι) (y : ↥(B.U j ⊓ A.U k : X.Opens)), ∃ (W : X.Opens) (_ : W ≤ B.U j ⊓ A.U k) (c : Γ(X, W)ˣ),
      y.1 ∈ W ∧ ∀ z ∈ W, ∀ i, gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z W c * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    rintro j k ⟨y, hy⟩
    obtain ⟨⟨i₀, hi₀⟩, u, hu⟩ := H y j k hy.1 hy.2
    let t : Γ(X, B.U j ⊓ A.U k) := resG X inf_le_left ((b i₀).f j) * resG X inf_le_right ((a i₀).f k)
    have hle := X.basicOpen_le t
    have ht : IsUnit (resG X hle t) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace t
    rw [map_mul] at ht
    obtain ⟨c₁, h₁⟩ := isUnit_of_mul_isUnit_left ht
    obtain ⟨c₂, h₂⟩ := isUnit_of_mul_isUnit_right ht
    refine ⟨X.basicOpen t, hle, c₁ * c₂⁻¹, ?_, fun z hz i => ?_⟩
    · rw [X.mem_basicOpen t y hy, ← gs_one y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hu]
      exact (u.isUnit.mul hi₀).mul hi₀
    · obtain ⟨-, u', hu'⟩ := H z j k (hle hz).1 (hle hz).2
      have e₁ : (gm (𝟙 X) z _ c₁).val = gs (𝟙 X) z (B.U j) ((b i₀).f j) := by
        rw [← gs_unit _ z _ hz, h₁, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e₂ : (gm (𝟙 X) z _ c₂).val = gs (𝟙 X) z (A.U k) ((a i₀).f k) := by
        rw [← gs_unit _ z _ hz, h₂, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e : gm (𝟙 X) z _ c₁ = u' * gm (𝟙 X) z _ c₂ := Units.ext (by rw [Units.val_mul, e₁, e₂, hu'])
      rw [map_mul, map_inv, e, mul_inv_cancel_right, hu']
  choose W hW c hy hc using loc
  have glue : ∀ (j : B.ι) (k : A.ι), ∃ w : Γ(X, B.U j ⊓ A.U k)ˣ, ∀ z ∈ B.U j ⊓ A.U k, ∀ i,
      gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z _ w * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    intro j k
    obtain ⟨w, hw⟩ := glue_unit (B.U j ⊓ A.U k) (W j k) (hW j k)
      (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hy j k ⟨z, hz⟩⟩) (c j k)
      (fun p q z hz => uniq z j k (hW j k p hz.1).1 (hW j k p hz.1).2 _ _ (hc j k p z hz.1) (hc j k q z hz.2))
    refine ⟨w, fun z hz i => ?_⟩
    rw [← gm_res (𝟙 X) z (hW j k ⟨z, hz⟩) (hy j k ⟨z, hz⟩), hw]
    exact hc j k ⟨z, hz⟩ z (hy j k ⟨z, hz⟩) i
  choose w hw using glue
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    (gm_res _ y _ hy _))).symm)
  refine uniq y p.1 p.2 hy.1.1 hy.1.2 _ _ (hw p.1 p.2 y hy.1) fun i => ?_
  have hB : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  have hA : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have eB := congrArg (gs (𝟙 X) y _) ((b i).compat p.1 q.1)
  have eA := congrArg (gs (𝟙 X) y _) ((a i).compat p.2 q.2)
  rw [gs_mul _ y _ hB, gs_res _ y _ hB, gs_res _ y _ hB, gs_unit _ y _ hB] at eB
  rw [gs_mul _ y _ hA, gs_res _ y _ hA, gs_res _ y _ hA, gs_unit _ y _ hA] at eA
  rw [eB, eA, hw q.1 q.2 y hy.2 i]
  change _ = ((_ * _ * gm (𝟙 X) y _ (w q.1 q.2) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) * _
  rw [Units.val_mul, Units.val_mul]
  have := (gm (𝟙 X) y _ (A.g p.2 q.2)).inv_mul
  linear_combination (-(gm (𝟙 X) y _ (B.g p.1 q.1)).val * (gm (𝟙 X) y _ (w q.1 q.2)).val *
    gs (𝟙 X) y (A.U q.2) ((a i).f q.2)) * this

theorem coord_germ {M : LB X} {th : σ → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : σ → R}
    (h : SecCoord M th x v) (p : Sp R) (k : M.ι) (hk : x p ∈ M.U k) :
    ∃ t : ((Sp R).presheaf.stalk p)ˣ, ∀ i, gs x p (M.U k) ((th i).f k) =
      ((Sp R).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * t := by
  obtain ⟨τ, -, h⟩ := h
  have hp : p ∈ (M.pull x).U (fun _ => k) := mem_pull.2 hk
  refine ⟨gm (𝟙 _) p _ (τ.s fun _ => k), fun i => ?_⟩
  have e := congrArg (gs (𝟙 _) p _) (h i (fun _ => k) (RepBC.pull_le M x _))
  rw [gs_appLE x _ _ _ (𝟙 _) p hp, gs_mul _ p _ hp, gs_res _ p _ hp, gs_one p ⊤ trivial, Category.id_comp] at e
  rw [← gs_unit _ p _ hp]
  exact e

theorem lbIso_of_coord (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ y : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : σ → R), IsOpenImmersion x ∧ y ∈ Set.range x ∧
      Ideal.span (Set.range v) = ⊤ ∧ SecCoord A a x v ∧ SecCoord B b x v) : LBIso A B := by
  refine lbIso_of_germs A B a b fun y j k hj hk => ?_
  obtain ⟨R, _, x, v, _, ⟨p, rfl⟩, hv, hA, hB⟩ := H y
  obtain ⟨t, ht⟩ := coord_germ hA p k hk
  obtain ⟨t', ht'⟩ := coord_germ hB p j hj
  let e := (asIso (x.stalkMap p)).commRingCatIsoToRingEquiv
  have he : ∀ (U : X.Opens) (_ : x p ∈ U) f, gs x p U f = e (gs (𝟙 X) (x p) U f) := fun U h f => gs_stalkMap x p U h f
  let ψ : R →+* (Sp R).presheaf.stalk p :=
    ((Sp R).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  constructor
  · have : ∃ i, IsUnit (ψ (v i)) := by
      by_contra hn
      push_neg at hn
      have : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal _).comap ψ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rw [hv, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [← MulEquiv.isUnit_map e, ← he _ hk, ht]
    exact hi.mul t.isUnit
  · refine ⟨Units.map e.symm.toMonoidHom (t' * t⁻¹), fun i => e.injective ?_⟩
    rw [map_mul, ← he _ hk, ← he _ hj, ht, ht']
    have : e (Units.map e.symm.toMonoidHom (t' * t⁻¹)).val = (t' * t⁻¹).val := e.apply_symm_apply _
    rw [this, Units.val_mul]
    linear_combination (-(ψ (v i)) * t'.val) * t.inv_mul

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (a : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', a = spMap φ :=
  ⟨(Spec.preimage a).hom, (Spec.map_preimage a).symm⟩

theorem exists_factor {U : Scheme.{0}} {R : Type} [CommRing R] (y : Sp R ⟶ X) (u : U ⟶ X) [IsOpenImmersion u]
    (p : Sp R) (h : y p ∈ Set.range u) : ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (a : Sp R' ⟶ U),
      IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ spMap φ ≫ y = a ≫ u := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := u) p q hq.symm
  obtain ⟨i, r, hr⟩ := (pullback y u).affineOpenCover.openCover.exists_eq z
  let C := (pullback y u).affineOpenCover.X i
  let w : Sp C ⟶ pullback y u := (pullback y u).affineOpenCover.f i
  have : IsOpenImmersion w := (pullback y u).affineOpenCover.map_prop i
  obtain ⟨φ, hφ⟩ := exists_spMap (w ≫ pullback.fst y u)
  refine ⟨C, inferInstance, φ, w ≫ pullback.snd y u, ?_, ?_, ?_⟩
  · rw [← hφ]; infer_instance
  · rw [← hφ]; refine ⟨r, ?_⟩
    rw [← hz, ← hr]; rfl
  · rw [← hφ, Category.assoc, Category.assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
theorem exists_map_of_coord : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  intro R σ _ I Z Y s sY M N th ty ⟨hM, hloc, hpts⟩ hN hY
  have uniq : ∀ (T : Type) [CommRing T] (x x' : Sp T ⟶ Z) (v : σ → T), x ≫ s = x' ≫ s → SecCoord M th x v →
      SecCoord M th x' v → x = x' := by
    intro T _ x x' v e h h'
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨h₁, h₂⟩ := hloc T β x v hβ h
    exact (hpts T β v h₁ h₂).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩
  have uni : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ → T), SecCoord N ty y v →
      Ideal.span (Set.range v) = ⊤ ∧ ∃ x : Sp T ⟶ Z, x ≫ s = y ≫ sY ∧ SecCoord M th x v := by
    intro T _ y v h
    obtain ⟨β, hβ⟩ := exists_spMap (y ≫ sY)
    obtain ⟨h₁, h₂⟩ := hY T β y v hβ h
    obtain ⟨x, hx, hx'⟩ := (hpts T β v h₁ h₂).exists
    exact ⟨h₁, x, hx.trans hβ.symm, hx'⟩
  choose A iA u v hu hp hv using (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2
  choose g hg hgv using fun p => (uni (A p) (u p) (v p) (hv p)).2
  have key : ∀ (p : Y) (T : Type) [CommRing T] (a : Sp T ⟶ Sp (A p)), (∃ w, SecCoord N ty (a ≫ u p) w) ∧
      ∀ w, SecCoord N ty (a ≫ u p) w ↔ SecCoord M th (a ≫ g p) w := by
    intro p T _ a
    obtain ⟨φ, rfl⟩ := exists_spMap a
    have h₁ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN (hv p)).1 T φ
    have h₂ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM (hgv p)).1 T φ
    refine ⟨⟨_, h₁⟩, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.1 c
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.1 c
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun p => Sp (A p)) u (fun p => ⟨p, hp p⟩) hu
  have hglue : ∀ p q : Y, pullback.fst (u p) (u q) ≫ g p = pullback.snd (u p) (u q) ≫ g q := by
    intro p q
    refine Scheme.Cover.hom_ext (pullback (u p) (u q)).affineOpenCover.openCover _ _ fun i => ?_
    let C := (pullback (u p) (u q)).affineOpenCover.X i
    let r : Sp C ⟶ pullback (u p) (u q) := (pullback (u p) (u q)).affineOpenCover.f i
    have e : (r ≫ pullback.fst _ _) ≫ u p = (r ≫ pullback.snd _ _) ≫ u q := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨⟨w, hw⟩, h⟩ := key p C (r ≫ pullback.fst _ _)
    have := uniq C _ _ w (by rw [Category.assoc, hg, ← Category.assoc, e, Category.assoc _ (g q), hg, Category.assoc _ (u q)])
      ((h w).1 hw) (((key q C (r ≫ pullback.snd _ _)).2 w).1 (e ▸ hw))
    rw [Category.assoc, Category.assoc] at this
    exact this
  let f : Y ⟶ Z := 𝒰.glueMorphisms g hglue
  have hf : ∀ p, u p ≫ f = g p := fun p => Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue p
  have hfs : f ≫ s = sY := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [← Category.assoc, hf, hg]
  refine ⟨f, hfs, ?_, fun T _ y w => ⟨fun h => ?_, fun h => ?_⟩, fun f' hf' h => ?_⟩
  · refine lbIso_of_coord N (M.pull f) ty (fun i => RepBC.secPull M f (th i)) fun p =>
      ⟨A p, iA p, u p, v p, hu p, hp p, (uni _ _ _ (hv p)).1, hv p, (RepBC.secCoord_pull M th f _ _).2 ?_⟩
    rw [hf]; exact hgv p
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Z M σ th T _ w hM (uni T y w h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [← Category.assoc, e, Category.assoc, hf, ← (key _ T' a).2, ← e]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h).1 T' φ
  · obtain ⟨β, hβ⟩ := exists_spMap ((y ≫ f) ≫ s)
    refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Y N σ ty T _ w hN (hloc T β _ w hβ h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [e, (key _ T' a).2, ← hf, ← Category.assoc, ← e, Category.assoc]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h).1 T' φ
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf', hg]) (h _ _ _ (hv p)) (hgv p)

end GlobalTheory.ZM.RepMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_map_of_projective_coordinates : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  first | exact @GlobalTheory.ZM.RepMap.exists_map_of_coord | exact GlobalTheory.ZM.RepMap.exists_map_of_coord | (intros; apply GlobalTheory.ZM.RepMap.exists_map_of_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertField

theorem differentiableAt_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) :
    DifferentiableAt ℂ (fun z => (M z).det) z₀ := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_adjugate_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (z₀ : E) (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (i j : Fin g) : DifferentiableAt ℂ (fun z => (M z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det (fun z => (M z).updateRow j (Pi.single i 1)) z₀ fun k l => ?_
  by_cases hk : k = j <;> simp [Matrix.updateRow_apply, hk, h k l]

theorem differentiableAt_of_mulVec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (M : E → Matrix (Fin g) (Fin g) ℂ) (b w : E → Fin g → ℂ) (z₀ : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀) (hb : ∀ i, DifferentiableAt ℂ (fun z => b z i) z₀)
    (hdet : (M z₀).det ≠ 0) (hw : ∀ᶠ z in nhds z₀, (M z).mulVec (w z) = b z) :
    DifferentiableAt ℂ w z₀ := by
  have hd : DifferentiableAt ℂ (fun z => (M z).det) z₀ := differentiableAt_det M z₀ h
  have hne : ∀ᶠ z in nhds z₀, (M z).det ≠ 0 := hd.continuousAt.eventually_ne hdet
  have heq : w =ᶠ[nhds z₀] fun z => ((M z).det)⁻¹ • ((M z).adjugate.mulVec (b z)) := by
    filter_upwards [hne, hw] with z hz hzw
    rw [← hzw, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hz, one_smul]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [differentiableAt_pi]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hadj := differentiableAt_adjugate_apply M z₀ h i
  have hi := hd.inv hdet
  fun_prop

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dite_eq_left (by rwa [hpre]), dite_eq_left h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dite_eq_right (by rwa [hpre]), dite_eq_right h]

theorem isOpen_dom_and_differentiableOn_fn {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left}
    (u : HolUnif A₀ L₀ g) {X : Scheme.{0}} (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    IsOpen (dom u m W) ∧ DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have hcomp : ∀ z, ((u.ex z).left ≫ m) ⁻¹ᵁ W = (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W := fun z => by simp
  have hdom : dom u m W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ m ⁻¹ᵁ W} := by
    ext z
    simp only [dom, Set.mem_ofPred_eq, hcomp]
  have hfn : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
    funext z
    exact valAt'_comp _ _ _ _
  rw [hdom, hfn]
  exact u.8 (m ⁻¹ᵁ W) ((m.app W).hom f)

private theorem clm_apply_eq_sum_single_mul {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ a, L (Pi.single a 1) * v a := by
  have hv : v = ∑ a, v a • (Pi.single a 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_differentiableOn_vertical : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  intro P₀ u Hm χ hU R _ x₀ X p m hsm hpb n B G s hB hGd hs hhol
  have key : ∀ z ∈ B, ∃ v : Fin P₀.g → ℂ, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) v :=
    fun z hz => (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hsm hpb (G z) (s z) (hs z hz).1 (hs z hz).2).exists
  choose! w hw using key
  refine ⟨w, fun z₁ hz₁ => ?_, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨W, t, hW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hU R x₀ X p m hsm hpb (G z₁)
  have hD : IsOpen (dom u m W) := (isOpen_dom_and_differentiableOn_fn u m W 0).1
  have hV : IsOpen {z ∈ B | G z ∈ dom u m W} := hB.inter (hD.preimage hGd.continuous)
  have hz₁V : z₁ ∈ {z ∈ B | G z ∈ dom u m W} := ⟨hz₁, hW⟩
  have hT : Matrix.transpose (Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1)) =
      Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) (G z₁) (Pi.single a 1) := by
    ext a b
    rfl
  refine differentiableAt_of_mulVec (fun z => Matrix.of fun b a => fderiv ℂ (fn u m W (t b)) (G z) (Pi.single a 1))
    (fun z b => s z W (t b)) w z₁ (fun b a => ?_) (fun b => ?_) ?_ ?_
  · have h1 := ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex P₀.g (dom u m W) (fn u m W (t b)) hD).2
      (isOpen_dom_and_differentiableOn_fn u m W (t b)).2).2 (Pi.single a 1)
    exact (h1.differentiableAt (hD.mem_nhds hW)).comp z₁ (hGd z₁)
  · exact (hhol W (t b)).differentiableAt (hV.mem_nhds hz₁V)
  · rw [← Matrix.det_transpose, hT]
    exact hdet
  · filter_upwards [hV.mem_nhds hz₁V] with z hz
    ext b
    exact ((hw z hz.1 W (t b) hz.2).trans (clm_apply_eq_sum_single_mul _ _)).symm

end GlobalTheory.KS.VertField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_verticalVectorField : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by
  first | exact @GlobalTheory.KS.VertField.exists_differentiableOn_vertical | exact GlobalTheory.KS.VertField.exists_differentiableOn_vertical | (intros; apply GlobalTheory.KS.VertField.exists_differentiableOn_vertical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

open Topology Filter

theorem t2Space_ptsOver_of_isSeparated {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (s : Sp ℂ ⟶ S) :
    T2Space (Points.PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := Points.PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have hc := (h.isClosedEmbedding.comp
    (Points.PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  convert hc using 1
  have key : ∀ x, h (Points.PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
      (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain rfl : a = b := hab
    exact ⟨a, key a⟩
  · rintro ⟨x, hx⟩
    rw [Function.comp_apply, key] at hx
    rw [← hx]
    rfl

theorem exists_realLinear_lift {V W Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Group Q] [TopologicalSpace T] [T2Space T] (j : Q → T)
    (hj : Function.Injective j) (e : W → Q) (e₀ : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (he₀ : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e) (Λ : Submodule ℤ W) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hc : Continuous (j ∘ e)) (hc₀ : Continuous (j ∘ e₀)) :
    ∃ L : V →L[ℝ] W, ∀ z, e (L z) = e₀ z := by
  have heq : ∀ z w, e z = e w ↔ z - w ∈ Λ := fun z w => by
    rw [← hk, ← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]
  have : CompactSpace (W ⧸ Λ) := by
    refine ⟨?_⟩
    rw [← (Submodule.mkQ_surjective Λ).range_eq]
    refine IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => ?_
    rw [map_add (f := _), Submodule.mkQ_apply _ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]
  let ē : W ⧸ Λ → T := Quotient.lift (j ∘ e) fun a b hab =>
    congrArg j ((heq a b).2 ((Submodule.quotientRel_def Λ).1 hab))
  have hē : ∀ w, ē (Λ.mkQ w) = j (e w) := fun _ => rfl
  have hemb : IsClosedEmbedding ē := by
    refine (hc.quotient_lift _).isClosedEmbedding fun a b hab => ?_
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Λ.mkQ_surjective b
    exact (Submodule.Quotient.eq Λ).2 ((heq a b).1 (hj hab))
  choose σ hσ using hs
  let φ : V →+ W ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (σ (e₀ z))) fun a b => by
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq Λ).2 ((heq _ _).1 (by rw [he, hσ, hσ, hσ, he₀]))
  have hφ : Continuous φ := hemb.isEmbedding.continuous_iff.2 (hc₀.congr fun z => by
    show j (e₀ z) = j (e (σ (e₀ z)))
    rw [hσ])
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift (ex := φ) (isDiscrete_ker_mkQ Λ)
    (Λ.isOpenMap_mkQ.nhds_le 0) hφ.continuousAt
  exact ⟨L, fun z => ((heq _ _).2 ((Submodule.Quotient.eq Λ).1 (hL z))).trans (hσ _)⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

def IsExp {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

theorem continuous_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) : Continuous a :=
  Points.continuous_of_differentiableOn fun U f => by simpa using h U f

theorem differentiableAt_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) (U : X.Opens) (f : Γ(X, U)) {z : V} (hz : ⊤ ≤ a z ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (a b) U f) z :=
  (h U f).2.differentiableAt ((h U f).1.mem_nhds ⟨trivial, hz⟩)

theorem IsExp.eq_of_fderiv {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e) {w w' : Fin g → ℂ}
    (h : ∀ (U : G.left.Opens) (f : Γ(G.left, U)), ⊤ ≤ (e 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e z).left U f) 0 w') : w = w' := by
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  refine (he.2.2.2.2 v hv.1).unique hv ⟨hv.1, fun U hU f => (hv.2 U hU f).trans (h U f ?_)⟩
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := hv.1
  rw [← h1]
  exact Points.le_preimage_comp _ _ hU (Points.le_preimage_top _)

theorem map_zero_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem eq_iff_sub_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  rw [← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]

theorem IsExp.exists_linearEquiv [IsSeparated G.hom] {g g₀ : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ G)} (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t2Space_ptsOver_of_isSeparated G.hom y
  obtain ⟨L, hL⟩ := exists_realLinear_lift (T := Points.PtsOver G.hom y) (fun x : Over.mk y ⟶ G => ⟨x.left, Over.w x⟩)
    (fun a b hab => Over.OverMorphism.ext (congrArg Subtype.val hab)) e e₀ he.1 ha he.2.1 Λ hk
    ((continuous_of_isHolTo he.2.2.1).subtype_mk _) ((continuous_of_isHolTo hh).subtype_mk _)
  have hsm : ∀ (c : ℂ) z, L (c • z) = c • L z := fun c z => he.eq_of_fderiv fun U f hU => by
    have h0 : (e₀ 0).left = (e 0).left := by rw [map_zero_of_add ha, map_zero_of_add he.1]
    have d := (differentiableAt_of_isHolTo he.2.2.1 U f hU).hasFDerivAt.restrictScalars ℝ
    have d₀ := (differentiableAt_of_isHolTo hh U f (z := 0) (by simpa only [h0] using hU)).hasFDerivAt.restrictScalars ℝ
    rw [← L.map_zero] at d
    have d₁ := d.comp 0 L.hasFDerivAt
    rw [L.map_zero] at d₁
    have e₁ : (fun b => valAt' (e b).left U f) ∘ L = fun b => valAt' (e₀ b).left U f := by
      funext b
      simp only [Function.comp_apply, hL]
    rw [e₁] at d₁
    have k := fun x => DFunLike.congr_fun (d₁.unique d₀) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at k
    rw [k, map_smul, map_smul, k]
  have hi : Function.Injective L := realLinear_injective_of_countable_ker L.toLinearMap
    (hc.mono fun x (hx : L x = 0) => by
      show e₀ x = 1
      rw [← hL, hx, map_zero_of_add he.1])
  have hsu : Function.Surjective L := realLinear_surjective_of_mod_countable L.toLinearMap (Γ := Λ)
    (Set.countable_coe_iff.1 (inferInstanceAs (Countable Λ))) fun w => by
      obtain ⟨x, hx⟩ := hs (e w)
      exact ⟨x, (hk _).1 ((eq_iff_sub_of_add he.1 _ _).1 (hx.symm.trans (hL x).symm))⟩
  exact ⟨LinearEquiv.ofBijective ⟨⟨L, L.map_add⟩, hsm⟩ ⟨hi, hsu⟩, hL⟩

end GlobalTheory.UnifPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToLargeSubfield
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GrpDescent

open GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

def sq (w : φ ≫ G.hom = A.hom ≫ j) : (A ⊗ A).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left

theorem isSquare_sq (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · rw [sq, ← Over.comp_left, lift_fst]; rfl
  · rw [sq, ← Over.comp_left, lift_snd]; rfl

theorem sq_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem eq_sq (w : φ ≫ G.hom = A.hom ≫ j) {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq w :=
  sq_ext (h.1.trans (isSquare_sq w).1.symm) (h.2.trans (isSquare_sq w).2.symm)

theorem isPullback_sq (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := (isSquare_sq hA.w).1
  have h₂ := (isSquare_sq hA.w).2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply sq_ext
    · rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem exists_grpObj (j : U ⟶ Z) [Flat j] [Surjective j] [GrpObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w (fun φ₂ h₂ => by rw [eq_sq h.w h₂, hm]) (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, h, fun T x y x₀ y₀ hx hy => ?_⟩
  obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
  obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
  exact congrArg (fun z => z.left) (hM x y)

theorem flat_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Flat (spMap β) := by
  rw [Flat.SpecMap_iff]
  letI := β.toAlgebra
  exact (inferInstance : Module.Flat k K)

theorem surjective_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GrpDescent

namespace GlobalTheory

open GrpDescent

theorem grpObj_descends_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by
  intro K _ K₀ A₀ A _ φ _ _ _ hφ
  have hw := hφ.w
  have hq : QuasiCompact (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiCompact (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  have hs : QuasiSeparated (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiSeparated (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨s₁, H₁⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom (sq hw) _ A₀.hom Unit
    (fun _ => (μ[A]).left ≫ φ) (isPullback_sq hφ) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w, (isPullback_sq hφ).w])
  obtain ⟨s₂, H₂⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ A₀.hom A.hom φ _ A₀.hom Unit
    (fun _ => (ι[A]).left ≫ φ) hφ (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨s₃, H₃⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (𝟙 _) (𝟙 _) (spMap K₀.subtype) _ A₀.hom Unit
    (fun _ => (η[A]).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  classical
  refine ⟨s₁ ∪ s₂ ∪ s₃, fun K₁ h hs A₁ φ₁ ψ hφ₁ hψ hψw => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  have hψp : IsPullback ψ A.hom A₁.hom (spMap K₁.subtype) :=
    IsPullback.of_right (by rwa [hψ, spMap_subtype]) hψw hφ₁
  obtain ⟨m, hm⟩ := H₁ K₁ h hs.1.1 _ (A₁ ⊗ A₁).hom (sq hφ₁.w) (sq hψw) (isPullback_sq hφ₁)
    (eq_sq hw ⟨by rw [Category.assoc, (isSquare_sq _).1, reassoc_of% (isSquare_sq hψw).1, hψ],
      by rw [Category.assoc, (isSquare_sq _).2, reassoc_of% (isSquare_sq hψw).2, hψ]⟩) (isPullback_sq hψp).w
  obtain ⟨i, hi⟩ := H₂ K₁ h hs.1.2 _ A₁.hom φ₁ ψ hφ₁ hψ hψw
  obtain ⟨e, he⟩ := H₃ K₁ h hs.2 _ (𝟙 _) (spMap (Subfield.inclusion h)) (spMap K₁.subtype)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (spMap_subtype h) (by simp)
  have := flat_spMap K₁.subtype
  have := surjective_spMap K₁.subtype
  refine exists_grpObj _ hψp
    (Over.homMk (hφ₁.lift (m ()) (A₁ ⊗ A₁).hom ((hm ()).2.trans (isPullback_sq hφ₁).w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (i ()) A₁.hom ((hi ()).2.trans hφ₁.w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (e ()) (𝟙 _) ((he ()).2.trans (by simp))) (hφ₁.lift_snd _ _ _)) ?_ ?_ ?_
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hm ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [(isPullback_sq hψp).w, ← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hi ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (he ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]; simp

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivOmegaStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem omegaStd_single_single_eq_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      Out.stdSymp g (finCongr (two_mul g).symm (finSumFinEquiv a))
        (finCongr (two_mul g).symm (finSumFinEquiv b)) := by
  unfold Out.stdSymp omegaStd
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_neg_distrib] <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff] <;>
    split_ifs <;> omega

theorem exists_equiv_omegaStd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M)
    (h : ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) :
    ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] M, ∀ x y, B (bas' x) (bas' y) = omegaStd x y := by
  set e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm) with he
  refine ⟨(LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas, ?_⟩
  have hs : ∀ a, (LinearEquiv.funCongrLeft ℤ ℤ e.symm) (Pi.single a (1 : ℤ)) = Pi.single (e a) 1 := by
    intro a
    funext k
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  let Ω : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ) :=
    LinearMap.mk₂ ℤ omegaStd
      (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
      (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
  have hB : B.compl₁₂ ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap
      ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap = Ω := by
    refine LinearMap.ext_basis (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) fun a b => ?_
    simp only [Pi.basisFun_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hs, h,
      Ω, LinearMap.mk₂_apply]
    exact (omegaStd_single_single_eq_stdSymp a b).symm
  intro x y
  exact LinearMap.congr_fun₂ hB x y

theorem sympBasis_std : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), IsSympBasis D bas → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La, ∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y := by
  intro E _ _ _ H D g bas hb
  refine ⟨?_, exists_equiv_omegaStd D.EF bas hb⟩
  have h1 := (LinearEquiv.finrank_eq bas).symm
  rw [finrank_int_lattice D, Module.finrank_fin_fun] at h1
  omega

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemIdealOfOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.DenseFib

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) :
    ∃ φ : A →+* B, spMap φ = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eval₂_scale {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eq_zero_of_dense {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by
  by_contra ha
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)).Nonempty := by
    by_contra hn
    refine ha (IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff a).1 ?_))
    exact eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim
  obtain ⟨q, hqa, hqD⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hne
  let q' : PrimeSpectrum A := q
  let K := AlgebraicClosure q'.asIdeal.ResidueField
  let κ : A →+* K := (algebraMap q'.asIdeal.ResidueField K).comp (algebraMap A _)
  have hker : ∀ z, κ z = 0 ↔ z ∈ q'.asIdeal := fun z => by
    simp only [κ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap q'.asIdeal.ResidueField K).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  have h0 := h K κ (by
    rintro _ ⟨p, rfl⟩
    have : spMap κ p = q := by
      apply PrimeSpectrum.ext
      ext z
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := p.isPrime)
      change κ z ∈ p.asIdeal ↔ z ∈ q'.asIdeal
      rw [hp, ← hker]; rfl
    rwa [this])
  exact hqa ((hker a).1 h0)

theorem mem_idealOf_of_dense : ∀ (R σ : Type) [CommRing R] (Y : Scheme.{0}) (s : Y ⟶ Sp R) (N : LB Y) (ty : σ → N.Sec) (Sg : Set (Sp R)) (F : MvPolynomial σ R) (e : ℕ), IsReduced Y → Flat s → LocallyOfFinitePresentation s → N.IsLB → Dense Sg → F.IsHomogeneous e → (∀ (K : Type) [Field K] [IsAlgClosed K] (β : R →+* K) (y : Sp K ⟶ Y) (v : σ → K), y ≫ s = spMap β → Set.range (spMap β) ⊆ Sg → SecCoord N ty y v → MvPolynomial.eval₂ β v F = 0) → F ∈ idealOf s N ty (𝟙 Y) := by
  intro R σ _ Y s N ty Sg F e hred hflat hlfp hN hSg hF H
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id]
  rintro R' _ β y v ⟨hy, hv⟩
  refine eq_zero_of_localization _ fun J hJ => ?_
  let L := Localization.AtPrime J
  let φ : R' →+* L := algebraMap R' L
  let yL : Sp L ⟶ Y := spMap φ ≫ y
  obtain ⟨A, _, x, w, hx, hp, hw⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2 (yL (IsLocalRing.closedPoint L))
  have hrange : Set.range yL ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := L) p).map yL.continuous).mem_open
      x.isOpenEmbedding.isOpen_range hp
  obtain ⟨ψ, hψ⟩ := exists_spMap (IsOpenImmersion.lift x yL hrange)
  have hψx : spMap ψ ≫ x = yL := by rw [hψ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := exists_spMap (x ≫ s)
  have hcomp : ψ.comp α = φ.comp β := by
    apply spMap_inj
    rw [← sp_comp, ← sp_comp, hα, ← Category.assoc, hψx, ← hy, Category.assoc]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 L ψ
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty R' y v hN hv).1 L φ
  rw [hψx] at h1
  obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty L yL _ hN h1).2.2 _ h2
  have hredA : IsReduced (Sp A) := isReduced_of_isOpenImmersion x
  have hredA' : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 hredA
  have hD : Dense ((x ≫ s) ⁻¹' Sg) := hSg.preimage (x ≫ s).isOpenMap
  have hA : MvPolynomial.eval₂ α w F = 0 := by
    refine eq_zero_of_dense _ hD _ fun K _ _ κ hκ => ?_
    rw [MvPolynomial.eval₂_comp_left]
    refine H K (κ.comp α) (spMap κ ≫ x) _ ?_ ?_
      ((GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 K κ)
    · rw [Category.assoc, ← hα, sp_comp]
    · rintro _ ⟨p, rfl⟩
      rw [← sp_comp, hα, Scheme.Hom.comp_apply]
      exact hκ ⟨p, rfl⟩
  change φ (MvPolynomial.eval₂ β v F) = 0
  rw [MvPolynomial.eval₂_comp_left, ← hcomp]
  have : (φ ∘ v) = fun i => (u : L) * (ψ ∘ w) i := funext hu
  rw [this, eval₂_scale _ _ _ hF, ← MvPolynomial.eval₂_comp_left, hA, map_zero, mul_zero]

end GlobalTheory.ZM.DenseFib
end
