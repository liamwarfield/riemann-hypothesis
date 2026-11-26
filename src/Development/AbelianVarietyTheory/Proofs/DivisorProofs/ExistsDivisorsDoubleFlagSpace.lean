module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominant
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem exists_isPull : ∀ (Z V : Scheme.{0}) [IsIntegral Z] [IsIntegral V] (q : Z ⟶ V) [IsDominant q]
    (E : CartierDiv V), ∃ D : CartierDiv Z, IsPull q D E := by
  intro Z V _ _ q _ E
  obtain ⟨D, -, hD⟩ := GlobalTheory.Cartier.exists_pullback_cartierDiv V Z q E
  exact ⟨D, fun y b hb x hx => hD x b (hx ▸ hb)⟩

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorPullbackOfDominantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant : ∀ (Z V : Scheme.{0}) [IsIntegral Z] [IsIntegral V] (q : Z ⟶ V) [IsDominant q] (E : CartierDiv V), ∃ D : CartierDiv Z, IsPull q D E := by
  first | exact @GlobalTheory.FlagPush.exists_isPull | exact GlobalTheory.FlagPush.exists_isPull | (intros; apply GlobalTheory.FlagPush.exists_isPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem isEqn_diag_of_frame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  intro F _ Y ι m E' gr B hB H y A hA
  have par : ∀ {z : Y.X} {A : Mat m Y.Fn}, A ∈ E'.S z → Par m ⊤ (B * A⁻¹) := fun {z A} h =>
    ((Fr.mem_iff (Fr.mem_genericPoint h)).1 hB).mono le_rfl le_top
  refine ⟨par hA, fun x => ?_⟩
  obtain ⟨A', hA', t', ht', heq⟩ := H y x
  have hP : Par m ((ratOf Y).O y).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have e : B * A⁻¹ = (B * A'⁻¹) * (A' * A⁻¹) := by
    rw [← mul_assoc, mul_assoc B, Mat.inv_mul (Fr.det_ne hA'), mul_one]
  obtain ⟨hu0, hui, -, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn _ (A' * A⁻¹) hP x
  obtain ⟨-, -, -, hmul⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A'⁻¹) (par hA') x
  obtain ⟨ht0, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A⁻¹) (par hA) x
  have hd : (B * A⁻¹) x.1 x.2 x.2 = t' * (A' * A⁻¹) x.1 x.2 x.2 := by
    rw [e, hmul _ (hP.mono le_rfl le_top), ht']
  refine ⟨Units.mk0 _ ht0, rfl, heq.iff_unitAt.2 ?_⟩
  have hu : UnitAt y ((A' * A⁻¹) x.1 x.2 x.2) := (unitAt_iff hu0).2
    ⟨mem_O_ratOf.1 ((hP x.1).1 x.2 x.2), mem_O_ratOf.1 hui⟩
  convert hu using 1
  rw [Units.val_mk0, hd]
  exact mul_div_cancel_left₀ _ t'.ne_zero

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  first | exact @GlobalTheory.FlagPush.isEqn_diag_of_frame | exact GlobalTheory.FlagPush.isEqn_diag_of_frame | (intros; apply GlobalTheory.FlagPush.isEqn_diag_of_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.OnSection

theorem not_unitAt_of_eq {F : Type} [Field F] {X Y : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) (W : Dbl Y)
    (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) (τ : ι) (a b : Fin (m τ)) (hab : a ≠ b) {k : Type} [Field k]
    (w : Sp k ⟶ W.Z) (hw : w ≫ W.p₁ = w ≫ W.p₂) (A : Mat m Y.Fn)
    (hA : A ∈ E'.S (W.p₁ (w (IsLocalRing.closedPoint k)))) :
    ¬ UnitAt (w (IsLocalRing.closedPoint k)) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  have hp : W.p₂ (w (IsLocalRing.closedPoint k)) = W.p₁ (w (IsLocalRing.closedPoint k)) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp k ⟶ Y.X => q (IsLocalRing.closedPoint k)) hw.symm).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨A₀, hA₀⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hM := hf.sub _ A hA A₀ hA₀
  have hd : ∀ σ, (A₀.map φ σ).det ≠ 0 := fun σ => by
    have := Mat.det_map A₀ (φ : X.Fn →+* Y.Fn) σ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA₀ σ))
  generalize hB : A₀.map φ = B at hM hd
  have hB12 : B.map W.α₁ = B.map W.α₂ := by
    subst hB
    funext σ
    ext i j
    exact hα _
  have h1 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₁ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => hq W.p₁ u (mem_O_ratOf.1 hu)
  have h2 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₂ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => by
    obtain ⟨h, e⟩ := hq W.p₂ u (by rw [hp]; exact mem_O_ratOf.1 hu)
    exact ⟨h, e.trans (congrArg (fun q => (ratOf Y).val q u) hw.symm)⟩
  have hN₁ := hM.map W.α₁ fun u hu => (h1 u hu).choose
  have hN₂ := hM.map W.α₂ fun u hu => (h2 u hu).choose
  have hd₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => (Mat.det_map B W.α₂ σ).trans_ne ((map_ne_zero _).2 (hd σ))
  have hg : A.map W.α₁ * (A.map W.α₂)⁻¹ = (A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hB12, Mat.mul_inv_rev, Mat.inv_inv hd₂, mul_assoc,
      ← mul_assoc _ (B.map W.α₂), Mat.inv_mul hd₂, one_mul]
  rw [hg]
  have hG := hN₁.mul hN₂.inv
  let v : W.Z.functionField → k := fun u => if h : u ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k)))
    W.Z.functionField).range then ev ⟨u, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v (x : W.Z.functionField) = ev x := fun x => dif_pos x.2
  have e1 := Par.map_mul_of hG hN₂ v ev hv
  rw [mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one] at e1
  have e2 : ((A * B⁻¹).map W.α₁).map v = ((A * B⁻¹).map W.α₂).map v := by
    funext σ
    ext i j
    obtain ⟨p, hp⟩ := h1 _ ((hM σ).1 i j)
    obtain ⟨q, hq⟩ := h2 _ ((hM σ).1 i j)
    exact ((hv ⟨_, p⟩).trans hp).trans ((hv ⟨_, q⟩).trans hq).symm
  have hV := (Par.map_of hN₂ v ev hv).det_ne
  have e3 : ((A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹).map v = 1 := by
    have := congrArg (· * (((A * B⁻¹).map W.α₂).map v)⁻¹) (e1.symm.trans e2)
    simpa only [mul_assoc, Mat.mul_inv hV, mul_one] using this
  intro hu
  refine (hev ⟨_, (hG τ).1 a b⟩).2 hu ((hv ⟨_, (hG τ).1 a b⟩).symm.trans ?_)
  exact (congrFun (congrFun (congrFun e3 τ) a) b).trans (Matrix.one_apply_ne hab)

end GlobalTheory.FlagPush.OnSection

theorem GlobalTheory.FlagPush.not_unitAt_section : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b hab y A hA
  let w₀ : Sp (Y.X.residueField y) ⟶ Y.X := Y.X.fromSpecResidueField y
  have h0 : w₀ (IsLocalRing.closedPoint _) = y := Scheme.fromSpecResidueField_apply _ _
  have h1 : (w₀ ≫ W.δ) (IsLocalRing.closedPoint _) = W.δ y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h0)
  have h2 : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
  have := OnSection.not_unitAt_of_eq hf W hα τ a b hab (w₀ ≫ W.δ)
    (by rw [Category.assoc, Category.assoc, W.δ₁, W.δ₂]) A (by rw [h1, h2]; exact hA)
  rwa [h1] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  first | exact @GlobalTheory.FlagPush.not_unitAt_section | exact GlobalTheory.FlagPush.not_unitAt_section | (intros; apply GlobalTheory.FlagPush.not_unitAt_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntry
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem mem_range_section_of_not_unitAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b z
  obtain ⟨k, _, w, rfl⟩ : ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ W.Z), w (IsLocalRing.closedPoint k) = z :=
    ⟨W.Z.residueField z, inferInstance, W.Z.fromSpecResidueField z, Scheme.fromSpecResidueField_apply _ _⟩
  intro A₁ hA₁ A₂ hA₂ hlow hnu
  have hbase : W.p₁ ≫ f = W.p₂ ≫ f := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hf.hom W hα
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  refine W.diag k w ?_
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hff : f (W.p₂ (w (IsLocalRing.closedPoint k))) = f (W.p₁ (w (IsLocalRing.closedPoint k))) := by
    rw [← Scheme.Hom.comp_apply W.p₂ f, ← hbase, Scheme.Hom.comp_apply]
  have hM₁ := hf.sub _ A₁ hA₁ A hA
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun y => A ∈ E.S y) hff).mpr hA)
  let v : W.Z.functionField → k := fun x =>
    if h : x ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range then ev ⟨x, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v x = ev x := fun x => dif_pos x.2
  have hN₁ := hM₁.map W.α₁ fun x hx => (hq W.p₁ x (mem_O_ratOf.1 hx)).1
  have hN₂ := hM₂.map W.α₂ fun x hx => (hq W.p₂ x (mem_O_ratOf.1 hx)).1
  have e₁ : ((A₁ * (A.map φ)⁻¹).map W.α₁).map v = (A₁ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₁)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₁ _ (mem_O_ratOf.1 ((hM₁ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have e₂ : ((A₂ * (A.map φ)⁻¹).map W.α₂).map v = (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₂)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₂ _ (mem_O_ratOf.1 ((hM₂ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have hC : (A.map φ).map W.α₁ = (A.map φ).map W.α₂ := by
    funext σ
    ext i j
    exact hα _
  have hCd : ∀ σ, (((A.map φ).map W.α₂)⁻¹ σ).det ≠ 0 := fun σ => by
    have h := hN₂.det_ne σ
    rw [Mat.map_mul, Mat.map_inv, Pi.mul_apply, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  have hg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      (A₁ * (A.map φ)⁻¹).map W.α₁ * ((A₂ * (A.map φ)⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hC, Mat.mul_inv_rev, mul_assoc, ← mul_assoc _ _ (A₂.map W.α₂)⁻¹,
      Mat.mul_inv hCd, one_mul]
  have hG := hN₁.mul hN₂.inv
  rw [hg] at hlow hnu
  generalize hN1 : (A₁ * (A.map φ)⁻¹).map W.α₁ = N₁ at *
  generalize hN2 : (A₂ * (A.map φ)⁻¹).map W.α₂ = N₂ at *
  have hb₁ := hN₁.map_of v ev hv
  have hb₂ := hN₂.map_of v ev hv
  have hbG := hG.map_of v ev hv
  have hmul : (N₁ * N₂⁻¹).map v * N₂.map v = N₁.map v := by
    rw [← hG.map_mul_of hN₂ v ev hv, mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one]
  have hv0 : v 0 = 0 := (hv 0).trans (map_zero ev)
  have hlowv : Par m ⊤ ((N₁ * N₂⁻¹).map v) := fun σ => by
    refine ⟨(hbG σ).1, (hbG σ).2.1, (hbG σ).2.2.1, fun i j _ hij => ?_⟩
    show v ((N₁ * N₂⁻¹) σ i j) = 0
    by_cases hc : (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩
    · obtain ⟨h1, h2⟩ := hc
      cases h1
      have h3 : j = b := eq_of_heq (Sigma.mk.inj h2).2
      subst h3
      by_contra h0
      exact hnu ((hev ⟨_, (hG τ).1 a j⟩).1 fun h => h0 ((hv ⟨_, (hG τ).1 a j⟩).trans h))
    · rw [hlow.2.2 σ i j hij hc, hv0]
  have hA' : A ∈ E.S ((w ≫ W.p₁ ≫ f) (IsLocalRing.closedPoint k)) :=
    (congrArg (fun y => A ∈ E.S y) ((Scheme.Hom.comp_apply w (W.p₁ ≫ f) _).trans
      (Scheme.Hom.comp_apply W.p₁ f _))).mpr hA
  refine (hf.lifts k (w ≫ W.p₁ ≫ f) A hA' (N₁.map v) hb₁).unique ⟨Category.assoc _ _ _, A₁, ?_, ?_⟩
    ⟨(Category.assoc _ _ _).trans (congrArg (w ≫ ·) hbase.symm), A₂, ?_, ?_⟩
  · exact (congrArg (fun y => A₁ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₁ _)).mpr hA₁
  · have : Par m ⊤ (N₁.map v * (N₁.map v)⁻¹) := by rw [Mat.mul_inv hb₁.det_ne]; exact Par.one
    exact e₁ ▸ this
  · exact (congrArg (fun y => A₂ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₂ _)).mpr hA₂
  · have : Par m ⊤ (N₁.map v * (N₂.map v)⁻¹) := by
      rw [← hmul, mul_assoc, Mat.mul_inv hb₂.det_ne, mul_one]; exact hlowv
    exact e₂ ▸ this

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeDiagonalOfNotUnitTransitionEntryStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  first | exact @GlobalTheory.FlagPush.mem_range_section_of_not_unitAt | exact GlobalTheory.FlagPush.mem_range_section_of_not_unitAt | (intros; apply GlobalTheory.FlagPush.mem_range_section_of_not_unitAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.Dbl.transition_par_stalk : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  intro F _ X Y ι _ m E E' φ f hR W hW z A₁ hA₁ A₂ hA₂
  have hbase := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hR.hom W hW
  have hf : f (W.p₁ z) = f (W.p₂ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbase]
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ z))
  have hA' : A ∈ E.S (f (W.p₂ z)) := hf ▸ hA
  have h₁ := hR.sub _ A₁ hA₁ A hA
  have h₂ := hR.sub _ A₂ hA₂ A hA'
  have reg : ∀ (p : W.Z ⟶ Y.X) [IsDominant p], ∀ x ∈ ((ratOf Y).O (p z)).toSubring,
      functionFieldMap p x ∈ (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range := by
    intro p _ x hx
    obtain ⟨a, rfl⟩ := mem_O_ratOf.1 hx
    exact ⟨_, (functionFieldMap_algebraMap p z a).symm⟩
  have k₁ := h₁.map W.α₁ (reg W.p₁)
  have k₂ := h₂.map W.α₂ (reg W.p₂)
  set B : Mat m Y.Fn := A.map φ with hBdef
  have hB : ∀ τ, (B τ).det ≠ 0 := fun τ => by
    intro h
    exact Fr.det_ne hA τ ((map_eq_zero (φ : X.Fn →+* Y.Fn)).1 (((φ : X.Fn →+* Y.Fn).map_det (A τ)).trans h))
  have hB₂ : ∀ τ, (B.map W.α₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hB τ)
  have e12 : B.map W.α₁ = B.map W.α₂ := by
    funext τ; ext i j; exact hW (A τ i j)
  have d₁ : A₁ = A₁ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have d₂ : A₂ = A₂ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have key : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ = (A₁ * B⁻¹).map W.α₁ * ((A₂ * B⁻¹).map W.α₂)⁻¹ := by
    conv_lhs => rw [d₁, d₂]
    rw [Mat.map_mul _ _ W.α₁, Mat.map_mul _ _ W.α₂, e12, Mat.mul_inv_rev, mul_assoc, ← mul_assoc (B.map W.α₂),
      Mat.mul_inv hB₂, one_mul]
  rw [key]
  exact k₁.mul k₂.inv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFramesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  first | exact @GlobalTheory.FlagPush.Dbl.transition_par_stalk | exact GlobalTheory.FlagPush.Dbl.transition_par_stalk | (intros; apply GlobalTheory.FlagPush.Dbl.transition_par_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush.LowMul

variable {K : Type} [Field K] {n : ℕ}

def Lo (L : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → L i j = 0

def AL (E : Fin n → Fin n → Prop) (C : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → ¬ E i j → C i j = 0

theorem al_mul {E : Fin n → Fin n → Prop} (hE : ∀ i j k, E k j → k ≤ i → i < j → E i j)
    {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C) : AL E (L * C) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hL i k h, zero_mul]
  · rw [hC k j (lt_of_le_of_lt h hij) (fun he => hn (hE i j k he h hij)), mul_zero]

theorem mul_al {E : Fin n → Fin n → Prop} (hE : ∀ i j l, E i l → j ≤ l → i < j → E i j)
    {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R) : AL E (C * R) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l j with h | h
  · rw [hR l j h, mul_zero]
  · rw [hC i l (lt_of_lt_of_le hij h) (fun he => hn (hE i j l he h hij)), zero_mul]

theorem diag_mul {E : Fin n → Fin n → Prop} {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C)
    (x : Fin n) (hx : ∀ k, k < x → ¬ E k x) : (L * C) x x = L x x * C x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hC k x h (hx k h), mul_zero]
  · rw [hL x k h, zero_mul]

theorem mul_diag {E : Fin n → Fin n → Prop} {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R)
    (x : Fin n) (hx : ∀ l, x < l → ¬ E x l) : (C * R) x x = C x x * R x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun l hl => ?_
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hR l x h, mul_zero]
  · rw [hC x l h (hx l h), zero_mul]

theorem lo_diag_ne {M : Matrix (Fin n) (Fin n) K} (hM : Lo M) (hd : M.det ≠ 0) (i : Fin n) : M i i ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular M (fun i j h => hM i j (OrderDual.toDual_lt_toDual.1 h))] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

section Pair
variable {a b : Fin n} {L C R : Matrix (Fin n) (Fin n) K}

theorem lower_index_pair_unique (hab : (b : ℕ) = a + 1) : ∀ i j k : Fin n, (k = a ∧ j = b) → k ≤ i → i < j → (i = a ∧ j = b) := by
  rintro i j k ⟨rfl, rfl⟩ h1 h2
  refine ⟨Fin.ext ?_, rfl⟩
  rw [Fin.le_iff_val_le_val] at h1; rw [Fin.lt_iff_val_lt_val] at h2; omega

theorem l_aa (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a a = L a a * C a a :=
  diag_mul hL hC a fun _ _ e => absurd (congrArg Fin.val e.2) (by omega)

theorem l_ab (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a b = L a a * C a b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single a fun k hk => ?_
  have hk' : (k : ℕ) ≠ a := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hk' with h | h
  · rw [hC k b (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hk e.1), mul_zero]
  · rw [hL a k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_ba (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b a = L b a * C a a + L b b * C b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k a (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_bb (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b b = L b a * C a b + L b b * C b b := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k b h (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem r_aa (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a a = C a a * R a a + C a b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 h) (fun e => hlb e.2), zero_mul]

theorem r_ab (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a b = C a b * R b b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single b fun l hl => ?_
  have hl' : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hR l b (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hl e.2), zero_mul]

theorem r_ba (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b a = C b a * R a a + C b b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC b l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hne e.1.symm), zero_mul]

theorem r_bb (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b b = C b b * R b b :=
  mul_diag hC hR b fun _ _ e => absurd (congrArg Fin.val e.1) (by omega)

end Pair

section Root
variable {ι : Type} {m : ι → ℕ} {τ : ι} {a b : Fin (m τ)}

theorem root_lower_pair_unique_left (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j k : Fin (m σ),
    ((⟨σ, k⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → k ≤ i → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j k ⟨h1, h2⟩ hki hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨congrArg (Sigma.mk _) (Fin.ext ?_), rfl⟩
  rw [Fin.le_iff_val_le_val] at hki; rw [Fin.lt_iff_val_lt_val] at hij; omega

theorem root_lower_pair_unique_right (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j l : Fin (m σ),
    ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, l⟩ : Root m) = ⟨τ, b⟩) → j ≤ l → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j l ⟨h1, h2⟩ hjl hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨rfl, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
  rw [Fin.le_iff_val_le_val] at hjl; rw [Fin.lt_iff_val_lt_val] at hij; omega

end Root

end GlobalTheory.FlagPush.LowMul

namespace GlobalTheory.FlagPush


open LowMul in
theorem almostLow_mul_entries : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  intro ι m τ a b hab K _ S T C hS hT hC
  have hSl : ∀ σ, Lo (S σ) := fun σ i j h => (hS σ).2.2.2 i j i.isLt h
  have hTl : ∀ σ, Lo (T σ) := fun σ i j h => (hT σ).2.2.2 i j i.isLt h
  have hCr : ∀ σ, AL (fun i j => (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) (C σ) :=
    fun σ => hC.2.2 σ
  have hCt : AL (fun i j => i = a ∧ j = b) (C τ) := fun i j h hn =>
    hC.2.2 τ i j h fun e => hn ⟨eq_of_heq (Sigma.mk.inj_iff.1 e.1).2, eq_of_heq (Sigma.mk.inj_iff.1 e.2).2⟩
  have hP : AL (fun i j => i = a ∧ j = b) (S τ * C τ) := al_mul (lower_index_pair_unique hab) (hSl τ) hCt
  have h3 : (S * C * T) τ a b = S τ a a * C τ a b * T τ b b := by
    show (S τ * C τ * T τ) a b = _
    rw [r_ab hab hP (hTl τ), l_ab hab (hSl τ) hCt]
  refine ⟨⟨fun σ => ?_, ?_, fun σ => ?_⟩, fun x hxa hxb => ?_, h3, ?_⟩
  · show (S σ * C σ * T σ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hS.det_ne σ) (hC.1 σ)) (hT.det_ne σ)
  · rw [h3]
    exact mul_ne_zero (mul_ne_zero (lo_diag_ne (hSl τ) (hS.det_ne τ) a) hC.2.1) (lo_diag_ne (hTl τ) (hT.det_ne τ) b)
  · exact mul_al (root_lower_pair_unique_right hab σ) (al_mul (root_lower_pair_unique_left hab σ) (hSl σ) (hCr σ)) (hTl σ)
  · show (S x.1 * C x.1 * T x.1) x.2 x.2 = _
    rw [mul_diag (al_mul (root_lower_pair_unique_left hab x.1) (hSl x.1) (hCr x.1)) (hTl x.1) x.2 (fun _ _ e => hxa e.1),
      diag_mul (hSl x.1) (hCr x.1) x.2 (fun _ _ e => hxb e.2)]
  · show (S τ * C τ * T τ) a a * (S τ * C τ * T τ) b b - (S τ * C τ * T τ) a b * (S τ * C τ * T τ) b a =
      S τ a a * S τ b b * (C τ a a * C τ b b - C τ a b * C τ b a) * (T τ a a * T τ b b)
    rw [r_aa hab hP (hTl τ), r_bb hab hP (hTl τ), r_ab hab hP (hTl τ), r_ba hab hP (hTl τ),
      l_aa hab (hSl τ) hCt, l_bb hab (hSl τ) hCt, l_ab hab (hSl τ) hCt, l_ba hab (hSl τ) hCt]
    ring

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProductStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_two_by_two_triangular_product : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  first | exact @GlobalTheory.FlagPush.almostLow_mul_entries | exact GlobalTheory.FlagPush.almostLow_mul_entries | (intros; apply GlobalTheory.FlagPush.almostLow_mul_entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnit
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.AlmostLowUnits

theorem det_almost {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hb : (b : ℕ) = a + 1) (hab : A a b ≠ 0)
    (hl : ∀ i j : Fin n, i < j → ¬ (i = a ∧ j = b) → A i j = 0) :
    A.det = (A a a * A b b - A a b * A b a) * ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_iff_val_lt_val]; omega
  set c := A a a / A a b with hc
  set U := A.updateCol a (fun k => A k a + (-c) • A k b) with hU
  set N := U.submatrix id (Equiv.swap a b) with hN
  have hdetU : U.det = A.det := Matrix.det_updateCol_add_smul_self A hne (-c)
  have hdetN : N.det = - A.det := by
    rw [hN, Matrix.det_permute', Equiv.Perm.sign_swap hne, hdetU]; simp
  have hUapp : ∀ i j, U i j = if j = a then A i a - c * A i b else A i j := by
    intro i j
    rw [hU, Matrix.updateCol_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  have hNapp : ∀ i j, N i j = U i (Equiv.swap a b j) := fun _ _ => rfl
  have htri : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hNapp]
    by_cases hja : j = a
    · rw [hja, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
      rw [hja] at hij'
      exact hl i b (lt_trans hij' hlt) (fun h => (ne_of_lt hij') h.1)
    · by_cases hjb : j = b
      · rw [hjb, Equiv.swap_apply_right, hUapp, if_pos rfl]
        rw [hjb] at hij'
        by_cases hia : i = a
        · rw [hia, hc, div_mul_cancel₀ _ hab, sub_self]
        · have hia' : i < a := by
            have h1 : (i : ℕ) < b := hij'
            have h2 : (i : ℕ) ≠ a := fun h => hia (Fin.ext h)
            rw [Fin.lt_iff_val_lt_val]; omega
          rw [hl i a hia' (fun h => hia h.1), hl i b (lt_trans hia' hlt) (fun h => hia h.1)]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, hUapp, if_neg hja]
        exact hl i j hij' (fun h => hjb h.2)
  have hprod := Matrix.det_of_lowerTriangular N htri
  have hmb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hmb] at hprod
  have hNa : N a a = A a b := by rw [hNapp, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
  have hNb : N b b = A b a - c * A b b := by rw [hNapp, Equiv.swap_apply_right, hUapp, if_pos rfl]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, N i i = ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hib := (Finset.mem_erase.1 hi).1
    have hia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [hNapp, Equiv.swap_apply_of_ne_of_ne hia hib, hUapp, if_neg hia]
  rw [hNa, hNb, hrest, hdetN] at hprod
  have e : A a b * (A b a - c * A b b) = A a b * A b a - A a a * A b b := by
    rw [hc]; field_simp
  rw [← mul_assoc, e] at hprod
  linear_combination (-1 : K) * hprod

theorem units_of_det {K α : Type} [Field K] [DecidableEq α] (O : Subring K) {s : Finset α} (x : α → K) (y d : K)
    (hd : d = y * ∏ i ∈ s, x i) (hd0 : d ≠ 0) (hdi : d⁻¹ ∈ O) (hy : y ∈ O) (hx : ∀ i ∈ s, x i ∈ O) :
    (y ≠ 0 ∧ y⁻¹ ∈ O) ∧ ∀ i ∈ s, x i ≠ 0 ∧ (x i)⁻¹ ∈ O := by
  have hP : ∏ i ∈ s, x i ∈ O := O.prod_mem hx
  rw [hd] at hd0
  refine ⟨⟨left_ne_zero_of_mul hd0, ?_⟩, fun i hi => ?_⟩
  · have e : y⁻¹ = d⁻¹ * ∏ i ∈ s, x i := by
      rw [hd, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul hd0), mul_one]
    rw [e]; exact O.mul_mem hdi hP
  · have e : d = x i * (y * ∏ j ∈ s.erase i, x j) := by
      rw [hd, ← Finset.mul_prod_erase s x hi]; ring
    have h0 : x i * (y * ∏ j ∈ s.erase i, x j) ≠ 0 := by rw [← e, hd]; exact hd0
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have e' : (x i)⁻¹ = d⁻¹ * (y * ∏ j ∈ s.erase i, x j) := by
      rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul h0), mul_one]
    rw [e']
    exact O.mul_mem hdi (O.mul_mem hy (O.prod_mem fun j hj => hx j (Finset.mem_of_mem_erase hj)))

end GlobalTheory.FlagPush.AlmostLowUnits


open GlobalTheory.FlagPush.AlmostLowUnits in
theorem GlobalTheory.FlagPush.almostLow_units : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g →
    (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧
      minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  intro ι m τ a b hb K _ O g hg hp
  have hlτ : ∀ i j : Fin (m τ), i < j → ¬ (i = a ∧ j = b) → g τ i j = 0 := fun i j hij h =>
    hg.2.2 τ i j hij (fun h' => h ⟨eq_of_heq (Sigma.mk.inj h'.1).2, eq_of_heq (Sigma.mk.inj h'.2).2⟩)
  have hdetτ := det_almost (g τ) a b hb hg.2.1 hlτ
  have hmO : minor τ a b g ∈ O :=
    O.sub_mem (O.mul_mem ((hp τ).1 a a) ((hp τ).1 b b)) (O.mul_mem ((hp τ).1 a b) ((hp τ).1 b a))
  have hτ := units_of_det O (fun i => g τ i i) (minor τ a b g) ((g τ).det) hdetτ (hp τ).2.1 (hp τ).2.2.1 hmO
    (fun i _ => (hp τ).1 i i)
  refine ⟨?_, hτ.1⟩
  rintro ⟨σ, i⟩ h1 h2
  by_cases hσ : σ = τ
  · subst hσ
    have hia : i ≠ a := fun e => h1 (by rw [e])
    have hib : i ≠ b := fun e => h2 (by rw [e])
    exact hτ.2 i (Finset.mem_erase.2 ⟨hib, Finset.mem_erase.2 ⟨hia, Finset.mem_univ _⟩⟩)
  · have htri : (g σ).BlockTriangular OrderDual.toDual := fun i j hij =>
      hg.2.2 σ i j (OrderDual.toDual_lt_toDual.1 hij) (fun h' => hσ (congrArg Sigma.fst h'.1))
    have hdet := Matrix.det_of_lowerTriangular (g σ) htri
    have h := units_of_det O (s := Finset.univ) (fun j => g σ j j) 1 ((g σ).det) (by rw [one_mul]; exact hdet)
      (hp σ).2.1 (hp σ).2.2.1 O.one_mem (fun j _ => (hp σ).1 j j)
    exact h.2 i (Finset.mem_univ _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnitStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g → (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧ minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  first | exact @GlobalTheory.FlagPush.almostLow_units | exact GlobalTheory.FlagPush.almostLow_units | (intros; apply GlobalTheory.FlagPush.almostLow_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpace
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.DivOn

theorem unitAt_of {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {u : Z.functionField} (h0 : u ≠ 0)
    (h : u ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range)
    (h' : u⁻¹ ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range) : UnitAt z u :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem key {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) {gr : Root m → Y.Dv}
    {B : Mat m Y.Fn} (hB : B ∈ E'.S (genericPoint Y.X))
    (hgr : ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t)
    (W : Dbl Y) (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) {τ : ι} {a b : Fin (m τ)} (hab : (b : ℕ) = a + 1)
    (hC : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)) {D₁ D₂ : Root m → CartierDiv W.Z}
    (hD₁ : ∀ x, IsPull W.p₁ (D₁ x) (gr x)) (hD₂ : ∀ x, IsPull W.p₂ (D₂ x) (gr x)) (z : W.Z)
    {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) :
    ∃ t₁ t₂ : Root m → W.Z.functionFieldˣ, (∀ x, (D₁ x).IsEqn z (t₁ x)) ∧ (∀ x, (D₂ x).IsEqn z (t₂ x)) ∧
      AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∧
      (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ →
        UnitAt z ((t₁ x : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) x.1 x.2 x.2 * t₂ x)) ∧
      UnitAt z ((t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (t₁ ⟨τ, b⟩ : W.Z.functionField)⁻¹ *
        minor τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) * (t₂ ⟨τ, a⟩ * t₂ ⟨τ, b⟩)) ∧
      (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b =
        (t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) τ a b * t₂ ⟨τ, b⟩ ∧
      RegAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨hP₁, h₁⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₁ hA₁
  obtain ⟨hP₂, h₂⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₂ hA₂
  choose s₁ e₁ q₁ using h₁
  choose s₂ e₂ q₂ using h₂
  have hT₁ : Par m ⊤ ((B * A₁⁻¹).map W.α₁) := hP₁.map W.α₁ fun _ _ => trivial
  have hT₂ : Par m ⊤ ((B * A₂⁻¹).map W.α₂) := hP₂.map W.α₂ fun _ _ => trivial
  have hloc := GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames F X Y ι m E E' φ f hf W hα z A₁ hA₁ A₂ hA₂
  have dB₁ : ∀ σ, (B.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dB₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dA₁ : ∀ σ, (A₁.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₁ σ)
  have eg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      ((B * A₁⁻¹).map W.α₁)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) * (B * A₂⁻¹).map W.α₂ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, Mat.mul_inv_rev, Mat.inv_inv dA₁, mul_assoc, mul_assoc,
      mul_assoc, ← mul_assoc (B.map W.α₂)⁻¹, Mat.inv_mul dB₂, one_mul, ← mul_assoc (B.map W.α₁)⁻¹, Mat.inv_mul dB₁,
      one_mul]
  obtain ⟨hal, hd, hab', hmin⟩ := GlobalTheory.T.minor_two_by_two_triangular_product ι m τ a b hab _ _ _ _ hT₁.inv hT₂ hC
  rw [← eg] at hal hd hab' hmin
  obtain ⟨hu, hm0, hm1⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ _ _ hal hloc
  have i₁ : ∀ x : Root m, ((B * A₁⁻¹).map W.α₁)⁻¹ x.1 x.2 x.2 = (W.α₁ (s₁ x))⁻¹ := fun x => by
    rw [(GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m _ ⊤ _ hT₁ x).2.2.1, ← e₁ x]; rfl
  have i₂ : ∀ x : Root m, ((B * A₂⁻¹).map W.α₂) x.1 x.2 x.2 = W.α₂ (s₂ x) := fun x => by
    rw [← e₂ x]; rfl
  refine ⟨fun x => Units.map W.α₁.toMonoidHom (s₁ x), fun x => Units.map W.α₂.toMonoidHom (s₂ x),
    fun x => hD₁ x _ _ (q₁ x) z rfl, fun x => hD₂ x _ _ (q₂ x) z rfl, hal, fun x hxa hxb => ?_, ?_, ?_,
    (hloc τ).1 a b⟩
  · have := unitAt_of (hu x hxa hxb).1 ((hloc x.1).1 x.2 x.2) (hu x hxa hxb).2
    rw [hd x hxa hxb, i₁, i₂] at this
    exact this
  · have hmem : minor τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∈
        (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range :=
      sub_mem (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _)) (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _))
    have := unitAt_of hm0 hmem hm1
    rw [hmin, i₁ ⟨τ, a⟩, i₁ ⟨τ, b⟩, i₂ ⟨τ, a⟩, i₂ ⟨τ, b⟩] at this
    exact this
  · rw [hab', i₁ ⟨τ, a⟩, i₂ ⟨τ, b⟩]
    rfl

theorem exists_divisors : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection F X Y ι m E E' φ f hf W hα τ a b hne y A hA

end GlobalTheory.FlagPush.DivOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisors_doubleFlagSpace : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    GlobalTheory.FlagPush.DivOn.key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection F X Y ι m E E' φ f hf W hα τ a b hne y A hA
end
