module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalChartResidueFieldDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.SepBModel

theorem gm_field {W : Type} [Field W] {Z : Scheme.{0}} (r : Z ⟶ Sp W) (z : Z) (U : (Sp W).Opens) (h : r z ∈ U)
    (a : Γ(Sp W, U)ˣ) : ∃ x : Wˣ, gm r z U a = gm r z ⊤ (unitOn x) := by
  obtain rfl : U = ⊤ := top_unique fun y _ => by rwa [Subsingleton.elim y (r z)]
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of W)).hom_inv_id_apply a.val).symm

theorem gm_spMap {W V : Type} [CommRing W] [CommRing V] (f : W →+* V) (z : Sp V) (x : Wˣ) :
    gm (spMap f) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn (Units.map f.toMonoidHom x)) := by
  have e : unitOn (Units.map f.toMonoidHom x) = pullU (spMap f) ⊤ (unitOn x) := by
    apply Units.ext
    exact congrArg (fun q => q.hom (x : W)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  rw [e]
  exact (gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn x)).symm

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] (z : Sp V) {x y : Vˣ}
    (h : gm (𝟙 (Sp V)) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn y)) : x = y := by
  have h1 := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at h1
  have h2 := germ_injective_of_isIntegral (Sp V) (U := ⊤) z trivial h1
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1 h2)





theorem lbIso_two {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X) (r : Z ⟶ Y) :
    LBIso (L.pull (r ≫ φ)) ((L.pull φ).pull r) := by
  have h : LBIso L L := by
    refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
    refine (gm_res (𝟙 X) y _ hy _).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res (𝟙 X) y _ hy _))).trans ?_
    have e := (gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2).symm
    exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)
  exact (LBIso.chartPull (Geo.Tor.chartPullPull L φ φ rfl) (Geo.Tor.chartPullPull L φ φ rfl) h).chartPull
    (chartPullSame L (fun _ => r ≫ φ) (fun _ => φ) _ r fun _ => rfl) (Geo.Tor.chartPullPull (L.pull φ) r r rfl)



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem stalkMap_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  apply Units.ext
  rw [gm_val (r ≫ f) z U h]
  show (r.stalkMap z).hom (gm f (r z) U a).val = _
  rw [gm_val f (r z) U h]
  exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _


end GlobalTheory.UChart.SepBModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfLbIsoFieldExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.lbIso_of_lbIso_fieldExt : ∀ (k₀ K : Type) [Field k₀] [Field K] (i₀ : k₀ →+* K) (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ L L' : LB B.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst B.hom (spMap i₀))) (L'.pull (pullback.fst B.hom (spMap i₀))) → LBIso L L' := by
  intro k₀ K _ _ i₀ B _ hB L L' hL hL' h
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap i₀) B hB hL hL' h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

theorem hom_descent : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B B' : Over (Sp k₀)) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B', IsMonHom f → ∃! f₀ : B ⟶ B', IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  intro k₀ K _ _ _ _ B B' _ _ hB hB' f hf
  have hP : IsAbelianScheme (B ⊗ B') := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB'
  let i : B ⟶ B ⊗ B' := lift (𝟙 B) 1
  let j : B' ⟶ B ⊗ B' := lift 1 (𝟙 B')
  have hi : IsMonHom i := by
    have : IsMonHom (1 : B ⟶ B') := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  have hj : IsMonHom j := by
    have : IsMonHom (1 : B' ⟶ B) := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  obtain ⟨F₀, ⟨hF₀, hF⟩, -⟩ := endo_descent (K := K) (B ⊗ B') hP
    ((Over.pullback (spMap (algebraMap k₀ K))).map (fst B B') ≫ f ≫
      (Over.pullback (spMap (algebraMap k₀ K))).map j) inferInstance
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map (i ≫ F₀ ≫ snd B B') = f := by
    rw [Functor.map_comp, Functor.map_comp, hF]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp_assoc, lift_fst, lift_snd,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  exact ⟨i ≫ F₀ ≫ snd B B', ⟨inferInstance, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B' (hf₁.2.trans key.symm)⟩

end GlobalTheory.AlgClosedDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.BaseDescent

theorem exists_descent {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀] {S : Scheme.{0}} (g : Sp k₀ ⟶ S)
    (B₀ : Over (Sp k₀)) [GrpObj B₀] (B₁ : Over S) [GrpObj B₁] (B' : Over (Sp K)) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) (h₁ : IsAbelianScheme B₁) {π₀ : B'.left ⟶ B₀.left} {δ : B'.left ⟶ B₁.left}
    (p₀ : IsGrpPullback B' B₀ (spMap k₀.subtype) π₀) (p₁ : IsGrpPullback B' B₁ (spMap k₀.subtype ≫ g) δ) :
    ∃ κ₀ : B₀.left ⟶ B₁.left, π₀ ≫ κ₀ = δ := by
  let i : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let B₂ := (Over.pullback g).obj B₁
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso (isGrpPullback_pullback B₀ i) p₀
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso p₁ ((isGrpPullback_pullback B₂ i).comp (isGrpPullback_pullback B₁ g))
  obtain ⟨f₀, ⟨-, hf⟩, -⟩ := GlobalTheory.AlgClosedDescent.hom_descent k₀ K B₀ B₂ h₀ (TLinPf.isAb_pullback g B₁ h₁)
    (e₁.hom ≫ e₂.hom) (by exact inferInstanceAs (IsMonHom (e₁.hom ≫ e₂.hom)))
  refine ⟨f₀.left ≫ pullback.fst B₁.hom g, ?_⟩
  have hi : IsIso e₁.hom.left := ⟨⟨e₁.inv.left, by rw [← Over.comp_left, e₁.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e₁.inv_hom_id, Over.id_left]⟩⟩
  have h2 : (e₁.hom ≫ e₂.hom).left ≫ pullback.fst B₂.hom i = pullback.fst B₀.hom i ≫ f₀.left := by
    exact (congrArg (fun q => q.left ≫ pullback.fst B₂.hom i) hf).symm.trans (pullback.lift_fst _ _ _)
  rw [← cancel_epi e₁.hom.left, ← he₂, ← Category.assoc, he₁, ← Category.assoc, ← h2]
  simp only [Over.comp_left, Category.assoc]

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (Geo.Tor.chartPullPull P f f rfl) (Geo.Tor.chartPullPull Q f f rfl)

theorem exists_lbIso {K : Type} [Field K] (k₀ : Subfield K) (B₀ : Over (Sp k₀)) [GrpObj B₀] (B' : Over (Sp K)) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) {A B₁ : Scheme.{0}} {π₀ : B'.left ⟶ B₀.left} {π₁ : B'.left ⟶ A} {β : A ⟶ B₁}
    {κ₀ : B₀.left ⟶ B₁} (p₀ : IsGrpPullback B' B₀ (spMap k₀.subtype) π₀) (hκ₀ : π₀ ≫ κ₀ = π₁ ≫ β)
    {L : LB A} {M₀ : LB B₀.left} {M₁ : LB B₁} (hL : L.IsLB) (hM₀ : M₀.IsLB) (hM₁ : M₁.IsLB)
    (w : LBIso (L.pull π₁) (M₀.pull π₀)) (w' : LBIso L (M₁.pull β)) : LBIso M₀ (M₁.pull κ₀) := by
  obtain ⟨e, -, he⟩ := grpPullback_iso (isGrpPullback_pullback B₀ (spMap k₀.subtype)) p₀
  have P : ∀ {X Y : Scheme.{0}} {N : LB X}, N.IsLB → ∀ f : Y ⟶ X, (N.pull f).IsLB := fun h f => pull_isLB h f
  have a₁ : LBIso (M₀.pull π₀) ((M₁.pull β).pull π₁) :=
    LBIso.trans (P hM₀ _) (P hL _) (P (P hM₁ _) _) w.symm (lbIso_pull w' π₁)
  have a₂ : LBIso ((M₁.pull β).pull π₁) ((M₁.pull κ₀).pull π₀) :=
    LBIso.trans (P (P hM₁ _) _) (P hM₁ (π₁ ≫ β)) (P (P hM₁ _) _) (SepBModel.lbIso_two hM₁ β π₁).symm
      (hκ₀ ▸ SepBModel.lbIso_two hM₁ κ₀ π₀)
  have a₃ := lbIso_pull (LBIso.trans (P hM₀ _) (P (P hM₁ _) _) (P (P hM₁ _) _) a₁ a₂) e.hom.left
  refine lbIso_of_lbIso_fieldExt k₀ K k₀.subtype B₀ h₀ _ _ hM₀ (P hM₁ _) ?_
  have a₄ := LBIso.trans (P hM₀ _) (P (P hM₀ _) _) (P (P (P hM₁ _) _) _) (SepBModel.lbIso_two hM₀ π₀ e.hom.left) a₃
  have a₅ := LBIso.trans (P hM₀ _) (P (P (P hM₁ _) _) _) (P (P hM₁ _) _) a₄
    (SepBModel.lbIso_two (P hM₁ κ₀) π₀ e.hom.left).symm
  rw [he] at a₅
  exact a₅

theorem exists_unit {B' B₀ A B₁ : Scheme.{0}} {π₀ : B' ⟶ B₀} {π₁ : B' ⟶ A} {β : A ⟶ B₁} {κ₀ : B₀ ⟶ B₁}
    (hκ₀ : π₀ ≫ κ₀ = π₁ ≫ β) {L : LB A} {M₀ : LB B₀} {M₁ : LB B₁} (hL : L.IsLB) (hM₀ : M₀.IsLB) (hM₁ : M₁.IsLB)
    {w : LB.Iso (L.pull π₁) (M₀.pull π₀)} {w' : LB.Iso L (M₁.pull β)} {v : LB.Iso M₀ (M₁.pull κ₀)}
    (hw : w.IsGen) (hw' : w'.IsGen) (hv : v.IsGen) :
    ∃ ρ : Γ(B', ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j : L.ι) (m₀ : M₀.ι) (m₁ : M₁.ι),
      π₁ (f z) ∈ L.U j → π₀ (f z) ∈ M₀.U m₀ → β (π₁ (f z)) ∈ M₁.U m₁ →
      gw w' (f ≫ π₁) z m₁ j = gm f z ⊤ ρ * gw v (f ≫ π₀) z m₁ m₀ * gw w f z m₀ (fun _ => j) := by
  have hp : ∀ x : B', κ₀ (π₀ x) = β (π₁ x) := fun x => congrArg (fun q : B' ⟶ B₁ => q x) hκ₀
  let W : L.ι × M₀.ι × M₁.ι → B'.Opens := fun p =>
    π₁ ⁻¹ᵁ ((M₁.pull β).U (fun _ => p.2.2) ⊓ L.U p.1) ⊓ π₀ ⁻¹ᵁ ((M₁.pull κ₀).U (fun _ => p.2.2) ⊓ M₀.U p.2.1) ⊓
      ((M₀.pull π₀).U (fun _ => p.2.1) ⊓ (L.pull π₁).U (fun _ => p.1))
  let u : ∀ p, Γ(B', W p)ˣ := fun p =>
    res (inf_le_left.trans inf_le_left) (pullU π₁ _ (w'.s (fun _ => p.2.2, p.1))) *
      (res (inf_le_left.trans inf_le_right) (pullU π₀ _ (v.s (fun _ => p.2.2, p.2.1))))⁻¹ *
      (res inf_le_right (w.s (fun _ => p.2.1, fun _ => p.1)))⁻¹
  have hW : ∀ (x : B') p, x ∈ W p ↔ π₁ x ∈ L.U p.1 ∧ π₀ x ∈ M₀.U p.2.1 ∧ β (π₁ x) ∈ M₁.U p.2.2 := fun x p =>
    ⟨fun h => ⟨h.1.1.2, h.1.2.2, mem_pull.1 h.1.1.1⟩, fun h => ⟨⟨⟨mem_pull.2 h.2.2, h.1⟩,
      ⟨mem_pull.2 (by rw [hp]; exact h.2.2), h.2.1⟩⟩, mem_pull.2 h.2.1, mem_pull.2 h.1⟩⟩
  have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) p, f z ∈ W p → gm f z (W p) (u p) =
      gw w' (f ≫ π₁) z p.2.2 p.1 * (gw v (f ≫ π₀) z p.2.2 p.2.1)⁻¹ * (gw w f z p.2.1 (fun _ => p.1))⁻¹ := by
    intro Z f z p h
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)) ?_)
    · exact (gm_res f z _ h _).trans (gm_pull f π₁ z _ h.1.1 _)
    · exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z _ h _).trans (gm_pull f π₀ z _ h.1.2 _)))
    · exact (map_inv _ _).trans (congrArg (·⁻¹) (gm_res f z _ h _))
  obtain ⟨ρ, hρ⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π₁ x)
      obtain ⟨m₀, h₀⟩ := exists_chart hM₀ (π₀ x)
      obtain ⟨m₁, h₁⟩ := exists_chart hM₁ (β (π₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, m₀, m₁), (hW x _).2 ⟨hj, h₀, h₁⟩⟩) u (fun p q x hx => by
      obtain ⟨a₁, a₂, a₃⟩ := (hW x p).1 hx.1
      obtain ⟨b₁, b₂, b₃⟩ := (hW x q).1 hx.2
      rw [hu _ _ x p hx.1, hu _ _ x q hx.2,
        (isGen_iff w').1 hw' _ (𝟙 B' ≫ π₁) x p.2.2 q.2.2 p.1 q.1 a₃ b₃ a₁ b₁,
        (isGen_iff v).1 hv _ (𝟙 B' ≫ π₀) x p.2.2 q.2.2 p.2.1 q.2.1 ((hp x).symm ▸ a₃) ((hp x).symm ▸ b₃) a₂ b₂,
        (isGen_iff w).1 hw _ (𝟙 B') x p.2.1 q.2.1 (fun _ => p.1) (fun _ => q.1) a₂ b₂ (mem_pull.2 a₁) (mem_pull.2 b₁),
        gm_pull_g L π₁ (𝟙 B') x (fun _ => p.1) (fun _ => q.1) (mem_pull.2 a₁) (mem_pull.2 b₁)]
      simp only [Category.assoc, hκ₀]
      simp only [mul_inv, inv_inv]
      generalize gm (𝟙 B' ≫ π₁ ≫ β) x _ _ = s
      generalize gm (𝟙 B' ≫ π₁) x _ _ = t
      generalize gm (𝟙 B' ≫ π₀) x _ _ = r
      rw [show ∀ a b c, s * t⁻¹ * a * (s⁻¹ * r * b) * (r⁻¹ * t * c) = (s * s⁻¹) * (t * t⁻¹) * (r * r⁻¹) * (a * b * c) from
        fun a b c => by ac_rfl]
      simp)
  refine ⟨ρ, fun Z f z j m₀ m₁ h₁ h₂ h₃ => ?_⟩
  have hm : f z ∈ W (j, m₀, m₁) := (hW _ _).2 ⟨h₁, h₂, h₃⟩
  rw [← gm_res f z le_top hm ρ, hρ, hu Z f z _ hm]
  rw [mul_right_comm _ _ (gw v _ _ _ _), inv_mul_cancel_right, inv_mul_cancel_right]

theorem gm_const {S S₀ : Scheme.{0}} (i : S ⟶ S₀) (B₀ : Over S₀) [GrpObj B₀] (B' : Over S) [GrpObj B']
    (h₀ : IsAbelianScheme B₀) {π₀ : B'.left ⟶ B₀.left} (p₀ : IsGrpPullback B' B₀ i π₀) (ρ : Γ(B'.left, ⊤)ˣ) (z : S)
    (c c' : S ⟶ B'.left) (hc : c ≫ B'.hom = 𝟙 _) (hc' : c' ≫ B'.hom = 𝟙 _) : gm c z ⊤ ρ = gm c' z ⊤ ρ := by
  obtain ⟨e, -, -⟩ := grpPullback_iso (isGrpPullback_pullback B₀ i) p₀
  obtain ⟨κ, hκ⟩ := TLinPf.const_pullback GlobalTheory.globalFns_holds i B₀ h₀ (e.hom.left.appTop.hom ρ.val)
  have hρ : ρ.val = B'.hom.appTop.hom κ := by
    have h1 : e.inv.left.appTop.hom (e.hom.left.appTop.hom ρ.val) = ρ.val := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
      simp
    rw [← h1, ← hκ, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w]
  have key : ∀ d : S ⟶ B'.left, d ≫ B'.hom = 𝟙 _ → d.appTop.hom ρ.val = κ := fun d hd => by
    rw [hρ, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hd]
    simp
  apply Units.ext
  rw [gm_val c z ⊤ trivial, gm_val c' z ⊤ trivial]
  exact (congrArg (S.presheaf.germ ⊤ z trivial).hom ((key c hc).trans (key c' hc').symm))

private theorem inv_mul_cancel_left' {G : Type} [Group G] (a s b : G) : a * s⁻¹ * (s * b) = a * b := by group

theorem exists_const {K : Type} [Field K] (k₀ : Subfield K) {B₀ B₁ : Scheme.{0}} {M₀ : LB B₀} {M₁ : LB B₁} (hM₀ : M₀.IsLB)
    (hM₁ : M₁.IsLB) {κ₀ : B₀ ⟶ B₁} {v : LB.Iso M₀ (M₁.pull κ₀)} (hv : v.IsGen) (p : Fin 4 → (Sp k₀ ⟶ B₀))
    (τ₁ : LB.Gen (LB.LinComb M₀ p ![-1, 1, 1, -1])) (hτ : τ₁.IsGen) (z : Sp K) (m : Fin 4 → M₁.ι)
    (hm : ∀ k, κ₀ (p k (spMap k₀.subtype z)) ∈ M₁.U (m k)) (t : ((Sp K).presheaf.stalk z)ˣ)
    (ht : t ∈ (gm (spMap k₀.subtype) z ⊤).range) :
    ∃ x : k₀ˣ, ∀ J₀, Good M₀ z J₀ →
      gw v (spMap k₀.subtype ≫ p 0) z (m 0) (J₀ (spMap k₀.subtype ≫ p 0)) *
        (gw v (spMap k₀.subtype ≫ p 1) z (m 1) (J₀ (spMap k₀.subtype ≫ p 1)))⁻¹ *
        (gw v (spMap k₀.subtype ≫ p 2) z (m 2) (J₀ (spMap k₀.subtype ≫ p 2)))⁻¹ *
        gw v (spMap k₀.subtype ≫ p 3) z (m 3) (J₀ (spMap k₀.subtype ≫ p 3)) * t =
      gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  have : Subsingleton (Sp k₀) := inferInstanceAs (Subsingleton (PrimeSpectrum k₀))
  set i : Sp K ⟶ Sp k₀ := spMap k₀.subtype with hi
  have rg : ∀ (U : (Sp k₀).Opens) (a : Γ(Sp k₀, U)ˣ), i z ∈ U → gm i z U a ∈ (gm i z ⊤).range := fun U a h => by
    obtain ⟨x, hx⟩ := SepBModel.gm_field i z U h a
    exact ⟨_, hx.symm⟩
  choose I hI using fun χ : Sp K ⟶ B₀ => exists_chart hM₀ (χ z)
  have rw' : ∀ k, gw v (i ≫ p k) z (m k) (I (i ≫ p k)) ∈ (gm i z ⊤).range := fun k => by
    have h : p k (i z) ∈ (M₁.pull κ₀).U (fun _ => m k) ⊓ M₀.U (I (i ≫ p k)) := ⟨mem_pull.2 (hm k), hI (i ≫ p k)⟩
    obtain ⟨c, hc⟩ := rg _ (pullU (p k) _ (v.s (fun _ => m k, I (i ≫ p k)))) h
    exact ⟨c, hc.trans (gm_pull i (p k) z _ h _)⟩
  have rv : val τ₁ i z I ∈ (gm i z ⊤).range := rg _ _ (Good.mem hI p i)
  obtain ⟨c, hc⟩ := mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (rw' 0) (inv_mem (rw' 1))) (inv_mem (rw' 2))) (rw' 3)) ht)
    (inv_mem rv)
  obtain ⟨x, hx⟩ := SepBModel.gm_field i z ⊤ trivial c
  refine ⟨x, fun J₀ hJ₀ => ?_⟩
  have ch : ∀ k, gw v (i ≫ p k) z (m k) (J₀ (i ≫ p k)) =
      (gm (i ≫ p k) z _ (M₀.g (J₀ (i ≫ p k)) (I (i ≫ p k))))⁻¹ * gw v (i ≫ p k) z (m k) (I (i ≫ p k)) := fun k => by
    rw [(isGen_iff v).1 hv _ (i ≫ p k) z (m k) (m k) _ _ (hm k) (hm k) (hJ₀ _) (hI _),
      gm_self hM₁ ((i ≫ p k) ≫ κ₀) z (hm k), _root_.one_mul]
  have cv : val τ₁ i z J₀ = _ * val τ₁ i z I := gen_trans hτ i z (hJ₀.mem p i) (Good.mem hI p i)
  rw [← SepBModel.gm_spMap, ← hx, hc, ch, ch, ch, ch, cv]
  simp only [trF, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_neg, zpow_one,
    mul_inv, inv_inv]
  generalize val τ₁ i z I = s
  rw [mul_comm _ s, inv_mul_cancel_left' _ s]
  ac_rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  intro R _ _ Q τ₀ K _ _ ev k₀ hk W₀ _ ιb hF hι B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' h₀ hM₀ p₁ p₀ hw hc a b τ₁ hτ
  obtain ⟨B₁, _, M₁, c₁, τ', β, w', h₁, hM₁, pβ, hw', -, -, hv'⟩ := hF
  let i : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let e₀ : W₀ →+* k₀ := (ev.comp ιb).codRestrict k₀ hι
  have he : spMap ev ≫ spMap ιb = i ≫ spMap e₀ :=
    (Spec.map_comp _ _).symm.trans (Spec.map_comp (CommRingCat.ofHom e₀) (CommRingCat.ofHom k₀.subtype))
  obtain ⟨κ₀, hκ⟩ := exists_descent k₀ (spMap e₀) B₀ B₁ B' h₀ h₁ p₀ ((p₁.comp pβ).congr he rfl)
  obtain ⟨v, hv⟩ := exists_lbIso k₀ B₀ B' h₀ p₀ hκ Q.P.isLB hM₀ hM₁ ⟨w, hw⟩ ⟨w', hw'⟩
  obtain ⟨ρ, hρ⟩ := exists_unit hκ Q.P.isLB hM₀ hM₁ hw hw' hv
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let z₀ : Sp K := (default : PrimeSpectrum K)
  choose J₁ hJ₁ using fun χ : Sp K ⟶ B₁.left => exists_chart hM₁ (χ z₀)
  have gJ₁ : Good M₁ (spMap ev z₀) (fun χ => J₁ (spMap ev ≫ χ)) := fun χ => hJ₁ (spMap ev ≫ χ)
  let m : Q.X → M₁.ι := fun y => J₁ (spMap ev ≫ cpt Q y ≫ β)
  have hm₁ : ∀ y, β (π₁ (c' y z₀)) ∈ M₁.U (m y) := fun y => by
    have := hJ₁ (spMap ev ≫ cpt Q y ≫ β)
    rw [← Category.assoc] at this
    exact (congrArg (fun q : Sp K ⟶ _ => β (q z₀) ∈ M₁.U (m y)) (hc y).2.1).mpr this
  have hm₀ : ∀ y, κ₀ (c₀ y (i z₀)) ∈ M₁.U (m y) := fun y => by
    have e : i ≫ c₀ y ≫ κ₀ = c' y ≫ π₁ ≫ β := by rw [← hκ, ← Category.assoc, ← (hc y).2.2, Category.assoc]
    exact (congrArg (fun q : Sp K ⟶ _ => q z₀ ∈ M₁.U (m y)) e).mpr (hm₁ y)
  have mτ := gJ₁.mem ![c₁ (a + b), c₁ a, c₁ b, c₁ 0] (spMap ιb)
  let t := Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
    (val (τ' a b) (spMap ιb) (spMap ev z₀) (fun χ => J₁ (spMap ev ≫ χ)))
  have ht : t ∈ (gm i z₀ ⊤).range := by
    have hp : spMap ιb (spMap ev z₀) = spMap e₀ (i z₀) := congrArg (fun q : Sp K ⟶ Sp W₀ => q z₀) he
    have hm' := Eq.mp (congrArg (· ∈ _) hp) mτ
    have e₄ : t = _ := SepBModel.stalkMap_gm (spMap ev) (spMap ιb) z₀ _ mτ _
    rw [he] at e₄
    replace e₄ := e₄.trans (gm_pull _ _ z₀ _ hm' _).symm
    obtain ⟨x, hx⟩ := SepBModel.gm_field i z₀ _ hm' (pullU (spMap e₀) _ ((τ' a b).s _))
    exact ⟨_, (e₄.trans hx).symm⟩
  obtain ⟨x, hx⟩ := exists_const k₀ hM₀ hM₁ hv _ τ₁ hτ z₀ ![m (a + b), m a, m b, m 0]
    (fun k => by fin_cases k <;> exact hm₀ _) t ht
  refine ⟨x, fun z J J₀ hJ hJ₀ => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim _ _
  have gJ : Good Q.P.L (spMap ev z₀) (fun χ => J (spMap ev ≫ χ)) := fun χ => hJ (spMap ev ≫ χ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom) (hv' a b _ _ _ gJ gJ₁)
  have l : Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
      (val (τ₀ a b) (𝟙 (Sp R)) (spMap ev z₀) (fun χ => J (spMap ev ≫ χ))) = val (τ₀ a b) (spMap ev) z₀ J := by
    refine (SepBModel.stalkMap_gm (spMap ev) (𝟙 _) z₀ _ (gJ.mem _ _) _).trans ?_
    rw [Category.comp_id]
    exact (val_of _ _ _ _ _ fun k => by rw [Category.id_comp]).symm
  have key : ∀ y, Units.map ((spMap ev).stalkMap z₀).hom.toMonoidHom
      (gm (cpt Q y) (spMap ev z₀) _ (w'.s (fun _ => J₁ (spMap ev ≫ cpt Q y ≫ β), J (spMap ev ≫ cpt Q y)))) =
      gm (c' 0) z₀ ⊤ ρ * gw v (i ≫ c₀ y) z₀ (m y) (J₀ (i ≫ c₀ y)) *
        gw w (c' y) z₀ (J₀ (c' y ≫ π₀)) (fun _ => J (c' y ≫ π₁)) := fun y => by
    have hmem : cpt Q y (spMap ev z₀) ∈ (M₁.pull β).U (fun _ => m y) ⊓ Q.P.L.U (J (spMap ev ≫ cpt Q y)) :=
      ⟨mem_pull.2 (gJ₁ (cpt Q y ≫ β)), gJ (cpt Q y)⟩
    refine (SepBModel.stalkMap_gm (spMap ev) (cpt Q y) z₀ _ hmem _).trans ?_
    have r := hρ _ (c' y) z₀ (J (c' y ≫ π₁)) (J₀ (c' y ≫ π₀)) (m y) (hJ (c' y ≫ π₁)) (hJ₀ (c' y ≫ π₀)) (hm₁ y)
    rw [gm_const i B₀ B' h₀ p₀ ρ z₀ (c' y) (c' 0) (hc y).1 (hc 0).1] at r
    have e₁ : c' y ≫ π₁ = spMap ev ≫ cpt Q y := (hc y).2.1
    have e₂ : c' y ≫ π₀ = i ≫ c₀ y := (hc y).2.2
    rw [← e₂, ← r, e₁]
    rfl
  rw [l, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at E
  have E' := E.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (key _)
    (congrArg (·⁻¹) (key _))) (congrArg (·⁻¹) (key _))) (key _)) (rfl : _ = t))
  have hx' := hx J₀ hJ₀
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hx'
  rw [E', _root_.mul_assoc (lamUnit _ _ _ _ _ _ _), ← hx', lamUnit]
  generalize gm (c' 0) z₀ ⊤ ρ = s
  simp only [mul_inv]
  rw [show ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ u, s * a₁ * b₁ * (s⁻¹ * a₂ * b₂) * (s⁻¹ * a₃ * b₃) * (s * a₄ * b₄) * u =
    (s * s⁻¹) * (s * s⁻¹) * (b₁ * b₂ * b₃ * b₄ * (a₁ * a₂ * a₃ * a₄ * u)) from fun _ _ _ _ _ _ _ _ _ => by ac_rfl]
  simp only [mul_inv_cancel, _root_.one_mul]
  rfl

end GlobalTheory.UCanon.BaseDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  first | exact @GlobalTheory.UCanon.BaseDescent.main | exact GlobalTheory.UCanon.BaseDescent.main | (intros; apply GlobalTheory.UCanon.BaseDescent.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.ScaleTorus

theorem unitOn_mul' {R : Type} [CommRing R] (x y : Rˣ) : unitOn (x * y) = unitOn x * unitOn y := by
  apply Units.ext
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (x : R) (y : R)

theorem isUnitTau_scaleGen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C N s ε τ₀ hs hε hτ u hu a b
  obtain ⟨hgen, k, hk, hval⟩ := hτ a b
  set w : Rˣ := ∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) with hw
  let w' : (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom w
  have hw' : (w' : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s (.inr k)) ^
      ((l.M' : ℤ) • (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b := by
    simp only [w', hw, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      LinearMap.smul_apply, smul_eq_mul, ← hu]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen _ _ hgen, k * w'⁻¹, ?_, fun zz J hJ => ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ w'.ne_zero, hk, hw']
    refine (finSumFinEquiv.symm.prod_comp fun k => algebraMap R (FractionRing R) (s k) ^
      ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [hs, hε]
  · have e₁ : val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen (unitOn w) (τ₀ a b)) (toUnit (TK R)).left zz J =
        gm (toUnit (TK R)).left zz ⊤ (unitOn w) * val (τ₀ a b) (toUnit (TK R)).left zz J :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ zz le_top (hJ.mem _ _) _) rfl)
    have e₂ : gm (toUnit (TK R)).left zz ⊤ (unitOn w) = gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      have e : (toUnit (TK R)).left = spMap (algebraMap R (FractionRing R)) := by simp
      rw [e]
      exact SepBModel.gm_spMap _ zz w
    have e₃ : gm (𝟙 (TK R).left) zz ⊤ (unitOn k) =
        gm (𝟙 (TK R).left) zz ⊤ (unitOn (k * w'⁻¹)) * gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      refine Eq.trans ?_ (map_mul _ _ _)
      refine congrArg _ (Eq.trans ?_ (unitOn_mul' _ _))
      rw [inv_mul_cancel_right]
    refine (hval zz J hJ).trans (Eq.trans ?_ (congrArg _ e₁.symm))
    rw [e₂, ← _root_.mul_assoc, ← e₃]

end GlobalTheory.UCanon.ScaleTorus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  first | exact @GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | exact GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen | (intros; apply GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomials
namespace GlobalTheory

theorem mem_subfield_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by
  have h1 : (u : K) ^ m.natAbs ∈ k₀ := by
    rw [Units.val_zpow_eq_zpow_val] at h
    rcases Int.natAbs_eq m with h2 | h2
    · rw [h2, zpow_natCast] at h; exact h
    · rw [h2, zpow_neg, zpow_natCast] at h
      simpa using k₀.inv_mem h
  have hint : IsIntegral k₀ (u : K) := by
    apply IsIntegral.of_pow (Int.natAbs_pos.mpr hm)
    exact isIntegral_algebraMap (R := k₀) (x := ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (u : K)
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint))
  rw [← hy]
  exact y.2

def monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) : Submodule ℤ (I → ℤ) :=
  AddSubgroup.toIntSubmodule
  { carrier := {v | ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀}
    zero_mem' := by simp [k₀.one_mem]
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq, Pi.add_apply, zpow_add, Finset.prod_mul_distrib,
        Units.val_mul] at *
      exact k₀.mul_mem ha hb
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib,
        Units.val_inv_eq_inv_val] at *
      exact k₀.inv_mem ha }

theorem mem_monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := Iff.rfl

theorem mem_monomialExponents_of_smul {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by
  rw [mem_monomialExponents] at h ⊢
  apply mem_subfield_of_zpow_mem k₀ _ m hm
  convert h using 2
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem mem_subfield_of_bilinForm_monomials :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  intro X _ S I _ ε K _ k₀ hk n hn t h k
  classical
  set P := monomialExponents k₀ t with hP
  have hv : ∀ a b : X, (fun k => (ε k : LinearMap.BilinForm ℤ X) a b) ∈ P := fun a b =>
    mem_monomialExponents_of_smul k₀ t _ n hn (h a b)
  haveI : NoZeroSMulDivisors ℤ ((I → ℤ) ⧸ P) := by
    refine ⟨fun {c x} hx => ?_⟩
    obtain ⟨v, rfl⟩ := P.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact mem_monomialExponents_of_smul k₀ t v c hc hx
  haveI : Module.Free ℤ ((I → ℤ) ⧸ P) := Module.free_of_finite_type_torsion_free'
  have key : P.mkQ (Pi.single k 1) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro φ
    have hz : ∑ j, φ (P.mkQ (Pi.single j 1)) • ε j = 0 := by
      apply Subtype.ext
      ext a b
      have h0 : φ (P.mkQ (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hv a b), map_zero]
      have h1 : (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)
          = ∑ j, (ε j : LinearMap.BilinForm ℤ X) a b • (Pi.single j 1 : I → ℤ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact Fintype.linearIndependent_iff.mp ε.linearIndependent _ hz k
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, mem_monomialExponents] at key
  convert key using 2
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomialsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials : ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  first | exact @GlobalTheory.mem_subfield_of_bilinForm_monomials | exact GlobalTheory.mem_subfield_of_bilinForm_monomials | (intros; apply GlobalTheory.mem_subfield_of_bilinForm_monomials <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtRigid

theorem pointRigid_of_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C hC
  obtain ⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩ := hC
  intro K _ _ ev k₀ hk hemb hsep
  apply hPR K ev k₀ hk hemb
  obtain ⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩ := hsep
  refine ⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩
  intro W₀ _ ιb hFB hιb j
  let u : Fin N → Rˣ := fun k => (hu k).unit
  have hu' : ∀ k, (u k : R) = s (.inr k) := fun k => (hu k).unit_spec
  let t : Fin C.m ⊕ Fin N → Kˣ := Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))
  have key : ∀ a b : C.P.D.toPre.X,
      ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀ := by
    intro a b
    have hτ' := GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b
    obtain ⟨τ₁, hτ₁, hv⟩ := hrel a b _ hτ'
    obtain ⟨x, hx⟩ := GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc
      a b τ₁ hτ₁
    let z : Sp K := IsLocalRing.closedPoint K
    choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)
    choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)
    have gJ : Good C.P.D.toPre.P.L z J := hJ
    have gJ₀ : Good M₀ z J₀ := hJ₀
    have e₁ := hv z J J₀ gJ gJ₀
    have e₂ := hx z J J₀ gJ gJ₀
    have vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J =
        gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J := fun cc =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)
    rw [vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂] at e₁
    set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))
    set x' := Units.map k₀.subtype.toMonoidHom x
    set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)
    set L := lamUnit w c' a b z J J₀
    set V := val τ₁ (spMap k₀.subtype) z J₀
    have e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by
      have h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) =
          (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x')) := by ac_rfl
      have h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by ac_rfl
      rw [h₁, h₂] at e₁
      exact mul_left_cancel e₁
    have e₄ : U' * x' = A := GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by
      rw [show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]; exact e₃)
    have e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹ := by
      rw [Fintype.prod_sum_type]
      have hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹ := by
        simp only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]
      have hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U' := by
        simp only [t, Sum.elim_inr, U', map_prod, map_zpow]
      rw [hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]
    rw [e₅]
    exact (x⁻¹ : k₀ˣ).val.2
  have := GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M')
    (by exact_mod_cast (level_pos l).ne') t key (.inr j)
  simpa [t, u] using this

end GlobalTheory.PtRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  first | exact @GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | exact GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | (intros; apply GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem isTautB_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi k _ m e C hC hms
  obtain ⟨hm, hs⟩ := hms
  have hB : GlobalTheory.Mum.Base (ChartRing k m e) := GlobalTheory.ChartQF.base_chartRing C.toFam
  have hR : HasRigidCoords C := GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates Xo c φ (ChartRing k m e) hB C hC
  obtain ⟨hft, hdim⟩ := GlobalTheory.T.canonicalChart_residueField_dimension Xo c φ C hC
  obtain ⟨N, s, ε, τ₀, h1, h2, h3, h4, -⟩ := id hR
  exact ⟨⟨hm, hs, GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ _ hB C, GlobalTheory.T.canonicalFamily_localInjections_eq_same_point Xo c φ hpq hfan hnsi _ hB C hC,
    ⟨GlobalTheory.T.canonical_data_rigid_along_stratum Xo c φ _ hB C hC, GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates Xo c φ _ C hR, hft⟩, ⟨N, s, ε, τ₀, h1, h2, h3, h4⟩, hdim⟩, hR⟩

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  first | exact @GlobalTheory.UCanon.isTautB_of_canon | exact GlobalTheory.UCanon.isTautB_of_canon | (intros; apply GlobalTheory.UCanon.isTautB_of_canon <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersality
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem spMap_isDominant_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : IsDominant (spMap f) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]
    exact bot_le)⟩

theorem spMap_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] {S : Scheme.{0}} [S.IsSeparated]
    (f : A →+* B) (hf : Function.Injective f) {a b : Sp A ⟶ S} (h : spMap f ≫ a = spMap f ≫ b) : a = b := by
  haveI := spMap_isDominant_of_injective f hf
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap f) h

theorem isSeparated_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    X.IsSeparated := by
  obtain ⟨N, ci, hci, hcis⟩ := h
  haveI := hci
  have : IsSeparated f := by
    rw [← hcis, PSpace.str]
    infer_instance
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem exists_taut_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep V _ _ _ hB hac C ξV hnt hCV
  obtain ⟨k, hk, m, e, C₁, θ, ⟨hcan⟩, hpar, hθ, hthr⟩ := GlobalTheory.T.exists_canonical_family_through_degenerating_family Xo c φ V hB hac C hnt
  letI := hk
  have hT : IsTautB C₁ := GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart Xo c φ hpq hpf hns C₁ hcan hpar
  obtain ⟨ξ, hξ⟩ := GlobalTheory.UChart.taut_exists_map Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C₁ hT.1
  haveI : S.IsSeparated := isSeparated_of_projOver hU.2.2.2.2.1.2.1
  refine ⟨k, hk, m, e, C₁, ξ, θ, hT, hξ, hθ, ?_⟩
  obtain ⟨yo, κ, hgen, hκ, hκy⟩ := hthr

  obtain ⟨hm, hs⟩ := hpar
  have hne : (∏ i, C₁.s i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [hs i]
    exact bdParam_ne_zero k m e _
  set L := Localization.Away (∏ i, C₁.s i)
  have hle : Submonoid.powers (∏ i, C₁.s i) ≤ nonZeroDivisors (ChartRing k m e) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hne
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  have hu : IsUnit (algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) (∏ i, C₁.s i)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hne)
  let gR : L →+* FractionRing (ChartRing k m e) := IsLocalization.Away.lift (∏ i, C₁.s i) hu
  have hgR : gR.comp (algebraMap (ChartRing k m e) L) = algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) :=
    IsLocalization.Away.lift_comp (∏ i, C₁.s i) hu
  have hinj : Function.Injective gR := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective (ChartRing k m e) (FractionRing (ChartRing k m e))).eq_iff]
  have hg : spMap gR ≫ spMap (algebraMap (ChartRing k m e) L) = jK (ChartRing k m e) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgR]

  have hopen : spMap (algebraMap (ChartRing k m e) L) ≫ ξ = yo ≫ j := by
    refine spMap_ext_of_injective gR hinj ?_
    rw [← Category.assoc, hg, ← hξ, ← Category.assoc, hgen _ hg]
  refine spMap_ext_of_injective (algebraMap V (FractionRing V)) (IsFractionRing.injective _ _) ?_
  change jK V ≫ _ = jK V ≫ _
  rw [← Category.assoc, ← hκ, Category.assoc, hopen, ← Category.assoc, hκy, hCV]

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersalityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tautological_chart_versality : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  first | exact @GlobalTheory.UCanon.exists_taut_through | exact GlobalTheory.UCanon.exists_taut_through | (intros; apply GlobalTheory.UCanon.exists_taut_through <;> assumption)
end
