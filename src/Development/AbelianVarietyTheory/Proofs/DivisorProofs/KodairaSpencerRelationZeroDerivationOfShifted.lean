module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocVal

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_mul {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_add {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq x U h, map_add (f := _)]

theorem valR_pow {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) (n : ℕ) : valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_eq x U h, map_pow]

theorem valR_one {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR_eq x U h, map_one]

theorem valR_res {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  rw [valR_eq x V h, valR_eq x U (h.trans (x.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_field_of_le : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z),
    ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) →
    (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) →
    ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  intro Z U hU F _ ξ _ d hd D _ hDm hDU O hOU hξO h
  obtain ⟨p₀⟩ : Nonempty (Sp F) := inferInstance
  have hp₀ : ξ.base p₀ ∈ O := hξO (Set.mem_univ p₀)
  obtain ⟨g, hgO, hg⟩ := hU.exists_basicOpen_le (V := O) ⟨_, hp₀⟩ (hOU hp₀)
  set B := Z.basicOpen g
  have hBU : B ≤ U := hgO.trans hOU
  have hξB : ⊤ ≤ ξ ⁻¹ᵁ B := by
    intro p _
    have : p = p₀ := Subsingleton.elim _ _
    subst this
    exact hg
  have := hU.isLocalization_basicOpen g
  obtain ⟨m, f, hf⟩ := IsLocalization.Away.surj g (resG Z hgO h)
  have hf' : resG Z hgO h * resG Z hBU g ^ m = resG Z hBU f := hf

  have hgu : IsUnit (resG Z hBU g) := Z.toRingedSpace.isUnit_res_basicOpen g
  have hg0 : valR ξ U g ≠ 0 := by
    obtain ⟨u, hu⟩ := hgu
    intro h0
    have e1 := congrArg (valR ξ B) u.mul_inv
    rw [valR_mul ξ B hξB, valR_one ξ B hξB, hu, valR_res ξ hBU hξB, h0, zero_mul] at e1
    exact zero_ne_one e1

  have hL := congrArg (d B) hf'
  rw [hd.2.1 B hBU, ← map_pow, hd.2.2 U B hBU le_rfl, hd.2.2 U B hBU le_rfl, hd.2.2 O B hgO hOU] at hL
  have hV := congrArg (valR ξ B) hL
  rw [valR_add ξ B hξB, valR_mul ξ B hξB, valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB,
    valR_res ξ hBU hξB, valR_res ξ hBU hξB, hDU, hDU] at hV
  have hfv : valR ξ U f = valR ξ O h * valR ξ U g ^ m := by
    have := congrArg (valR ξ B) hf'
    rw [valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB, valR_pow ξ B hξB, valR_res ξ hBU hξB] at this
    exact this.symm
  rw [hfv, hDm, valR_pow ξ U (hξB.trans (ξ.preimage_mono hBU))] at hV
  have key : valR ξ U g ^ m * (valR ξ B (resG Z hgO (d O h)) - D (valR ξ O h)) = 0 := by
    linear_combination hV
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (pow_eq_zero_iff'.1 h1).1 hg0
  · rw [← valR_res ξ hgO hξB]
    exact sub_eq_zero.1 h1

end GlobalTheory.LocVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorField_follows_derivation_on_smaller_open_at_fieldPoint : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z), ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) → ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  first | exact @GlobalTheory.LocVal.valR_field_of_le | exact GlobalTheory.LocVal.valR_field_of_le | (intros; apply GlobalTheory.LocVal.valR_field_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecValLC

theorem valR_def' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := by
  unfold valR; rw [dite_eq_left h]

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_def' x U h, map_mul]

theorem valR_map' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_def' x V h, valR_def' x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]

theorem valR_id_app {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) (f : Γ(X, U)) :
    valR x ((𝟙 X) ⁻¹ᵁ U) ((Scheme.Hom.app (𝟙 X) U).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h
  rw [valR_def' x _ h, valR_def' x U hU]
  congr 1

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_def' x U h, map_pow]

theorem secM_valR_transition : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  intro X L k σ F _ ξ j j' hj hj'
  set LC := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k:ℤ)) with hLC
  have hW : ∀ i : L.ι, L.U i ≤ LC.U (fun _ => i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have h1 : ⊤ ≤ ξ ⁻¹ᵁ (LC.U (fun _ => j) ⊓ LC.U (fun _ => j')) := by
    intro x hx
    exact ⟨hW j (hj hx), hW j' (hj' hx)⟩
  have h2 : ⊤ ≤ ξ ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j')) := fun x hx => ⟨hj hx, hj' hx⟩
  have hle : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ (𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
  have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
      Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) =
      (X.presheaf.map (homOfLE hle).op).hom ((Scheme.Hom.app (𝟙 X) (L.U j ⊓ L.U j')).hom
        (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k := by
    show Units.val (∏ _i : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (k:ℤ)) = _
    rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  have hc := σ.compat (fun _ => j) (fun _ => j')
  have := congrArg (valR ξ _) hc
  rw [valR_map' _ _ h1, valR_mul' _ _ h1, valR_map' _ _ h1] at this
  rw [this, hg, valR_pow' _ _ h1, valR_map' _ _ h1, valR_id_app _ _ h2]

end GlobalTheory.SecValLC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionPowerValue_chart_change_by_transition_pow : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  first | exact @GlobalTheory.SecValLC.secM_valR_transition | exact GlobalTheory.SecValLC.secM_valR_transition | (intros; apply GlobalTheory.SecValLC.secM_valR_transition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CocVal

theorem valR_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_map_le {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE hVU).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono hVU)
  rw [valR_pos x V h, valR_pos x U hU]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_mul_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_pos x U h, map_mul]

theorem top_le_inf {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun p _ => ⟨hU trivial, hV trivial⟩

theorem valR_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X)
    (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' →
    valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val =
      valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  intro X L hL F _ ξ j j' j'' h1 h2 h3
  have h123 : ⊤ ≤ ξ ⁻¹ᵁ (L.U j ⊓ L.U j' ⊓ L.U j'') := top_le_inf ξ (top_le_inf ξ h1 h2) h3
  have e := congrArg (fun u : Γ(X, L.U j ⊓ L.U j' ⊓ L.U j'')ˣ => valR ξ _ u.val) (hL.cocycle j j' j'')
  simp only [Units.val_mul] at e
  rw [valR_mul_pos ξ _ h123] at e
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at e
  rw [valR_map_le ξ _ h123, valR_map_le ξ _ h123, valR_map_le ξ _ h123] at e
  exact e

end GlobalTheory.CocVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transitionUnit_pointValue_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' → valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val = valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  first | exact @GlobalTheory.CocVal.valR_cocycle | exact GlobalTheory.CocVal.valR_cocycle | (intros; apply GlobalTheory.CocVal.valR_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShifted
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.ZeroKS

theorem valR_res' {F : Type} [CommRing F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ V) (a : Γ(Z, U)) : valR ξ V (resG Z e a) = valR ξ U a := by
  rw [WtAlg.valR_eq' ξ V h, WtAlg.valR_eq' ξ U (h.trans (ξ.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_sum' {F : Type} [CommRing F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    {β : Type} (s : Finset β) (f : β → Γ(Z, O)) : valR ξ O (∑ i ∈ s, f i) = ∑ i ∈ s, valR ξ O (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [WtAlg.valR_eq' _ _ h, map_sum]

theorem valR_inv' {F : Type} [Field F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    (u : Γ(Z, O)ˣ) : valR ξ O (↑u⁻¹ : Γ(Z, O)) = (valR ξ O (u : Γ(Z, O)))⁻¹ := by
  have e : valR ξ O (u : Γ(Z, O)) * valR ξ O (↑u⁻¹ : Γ(Z, O)) = 1 := by
    rw [← WtAlg.valR_mul'' _ _ h, Units.mul_inv, WtAlg.valR_eq' _ _ h, map_one, map_one]
  exact eq_inv_of_mul_eq_one_right e

theorem valR_unit_ne {F : Type} [Field F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    (u : Γ(Z, O)ˣ) : valR ξ O (u : Γ(Z, O)) ≠ 0 := by
  intro h0
  have e : valR ξ O (u : Γ(Z, O)) * valR ξ O (↑u⁻¹ : Γ(Z, O)) = 1 := by
    rw [← WtAlg.valR_mul'' _ _ h, Units.mul_inv, WtAlg.valR_eq' _ _ h, map_one, map_one]
  rw [h0, zero_mul] at e
  exact zero_ne_one e

theorem alg_val {F : Type} [Field F] {n : ℕ} (δ : Fin n → Derivation ℤ F F) (lam' : Fin n → Fin n → F) (k : ℕ)
    (hk : (k : F) ≠ 0) (G S : F) (hG : G ≠ 0) (hS : S ≠ 0) (y0 x : F) :
    y0 - (k : F)⁻¹ * ∑ a, ∑ e, lam' a e * (δ a (G ^ k * S) / (G ^ k * S)) * δ e x +
      ∑ e, ((k : F)⁻¹ * ∑ a, lam' a e * δ a S * S⁻¹) * δ e x =
    y0 - ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x := by
  have hl : ∀ a, δ a (G ^ k * S) / (G ^ k * S) = k * (δ a G / G) + δ a S / S := by
    intro a
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact absurd (by rw [h0]; simp) hk
      · omega⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
    ring
  have h3 : ∑ e, ((k : F)⁻¹ * ∑ a, lam' a e * δ a S * S⁻¹) * δ e x =
      (k : F)⁻¹ * ∑ a, ∑ e, lam' a e * (δ a S / S) * δ e x := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [div_eq_mul_inv]; ring
  have key : ∑ a, ∑ e, lam' a e * ((k : F) * (δ a G / G) + δ a S / S) * δ e x =
      (k : F) * ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x + ∑ a, ∑ e, lam' a e * (δ a S / S) * δ e x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h3]
  simp only [hl]
  rw [key, mul_add, ← _root_.mul_assoc, inv_mul_cancel₀ hk, _root_.one_mul]
  ring

theorem alg_diff {F : Type} [Field F] {n : ℕ} (δ : Fin n → Derivation ℤ F F) (lam' : Fin n → Fin n → F)
    (hsym : ∀ a b, lam' a b = lam' b a) (G G' H : F) (hG : G ≠ 0) (hH : H ≠ 0) (e : G * H = G') (y0 x : F) :
    (y0 - ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x) - (y0 - ∑ a, ∑ e, lam' a e * (δ a G' / G') * δ e x) =
      ∑ a, ∑ b, lam' a b * (δ b H * H⁻¹) * δ a x := by
  subst e
  have hl : ∀ a, δ a (G * H) / (G * H) = δ a G / G + δ a H / H := by
    intro a
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    field_simp
    ring
  simp only [hl]
  rw [Finset.sum_comm (f := fun a b => lam' a b * (δ b H * H⁻¹) * δ a x)]
  rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [div_eq_mul_inv]
  rw [hsym a b]; ring

end GlobalTheory.Heat.ZeroKS

namespace GlobalTheory.Heat.ZeroKS

theorem isField_mono {Z : Scheme.{0}} {U V : Z.Opens} {d : Fld Z} (h : IsField U d) (hVU : V ≤ U) : IsField V d :=
  ⟨fun W hW => h.1 W (hW.trans hVU), fun W hW => h.2.1 W (hW.trans hVU), fun W W' h' hW => h.2.2 W W' h' (hW.trans hVU)⟩

theorem ksRel_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (lam : Matrix (Fin n) (Fin n) K), lamᵀ = lam → (∀ r, δ₀ (ψ r) = 0) → ∀ (k : ℕ), 1 ≤ k → ∀ (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), ⨆ i, Out.nonzeroLocus (s i) = ⊤ → (∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i)) → (∀ i, (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (valR ξ _ ((s i).f fun _ => j₀)) / valR ξ _ ((s i).f fun _ => j₀)) * δ e (valR ξ _ f))) → KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) lam := by
  intro K _ _ P₀ n v dd hinv F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ lam hlam hδ₀ k hk I s hcov haff hξs hf'
  have hk0 : (k : F) ≠ 0 := by
    rw [← map_natCast ψ]
    exact (map_ne_zero ψ).2 (Nat.cast_ne_zero.2 (by omega))
  have heq : ∀ O (h : ⊤ ≤ ξ ⁻¹ᵁ O) (f g : Γ(P₀.A.left, O)), valR ξ O f = valR ξ O g → f = g := by
    intro O h f g e
    exact sub_eq_zero.1 (hinj O _ h (by rw [WtAlg.valR_sub' _ _ h, e, sub_self]))
  have hsub : ∀ O : P₀.A.left.Opens, ¬ ⊤ ≤ ξ ⁻¹ᵁ O → Subsingleton Γ(P₀.A.left, O) := by
    intro O hO
    have hb : O = ⊥ := by
      by_contra hne
      refine hO (GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hinj O ?_)
      rw [Set.nonempty_iff_ne_empty]
      intro he
      exact hne (TopologicalSpace.Opens.ext (by simpa using he))
    exact CommRingCat.subsingleton_of_isTerminal (P₀.A.left.sheaf.isTerminalOfEqEmpty hb)
  have hδψ : ∀ a r, δ a (ψ r) = 0 := by
    intro a r
    have h1 := hδ a ⊤ (constFn P₀.A.hom ⊤ r) (fun _ _ => trivial)
    rw [Adjust.inv_constFn P₀.A (v a) (dd a) (hinv a), WtAlg.valR_zero',
      Adjust.valR_const P₀.A.hom ψ ξ hξ ⊤ (fun _ _ => trivial) r] at h1
    exact h1.symm
  let S0 : I → F := fun i => valR ξ _ ((s i).f fun _ => j₀)
  let Tm : I → F → F := fun i x => ∑ a, ∑ e, ψ (lam a e) * (δ a (S0 i) / S0 i) * δ e x
  let Dv : I → F → F := fun i x => δ₀ x - (k : F)⁻¹ * Tm i x
  have Tm_add : ∀ i x y, Tm i (x + y) = Tm i x + Tm i y := by
    intro i x y
    simp only [Tm, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have Tm_mul : ∀ i x y, Tm i (x * y) = x * Tm i y + y * Tm i x := by
    intro i x y
    simp only [Tm, Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have Dv_add : ∀ i x y, Dv i (x + y) = Dv i x + Dv i y := by
    intro i x y
    simp only [Dv, map_add (f := _), Tm_add]; ring
  have Dv_mul : ∀ i x y, Dv i (x * y) = x * Dv i y + y * Dv i x := by
    intro i x y
    simp only [Dv, Derivation.leibniz, smul_eq_mul, Tm_mul]; ring
  have hd : ∀ i, ∃ d : Fld P₀.A.left, IsField (Out.nonzeroLocus (s i)) d ∧ ∀ O, O ≤ Out.nonzeroLocus (s i) →
      ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h, valR ξ O (d O h) = Dv i (valR ξ O h) := by
    intro i
    have hξi := hξs i
    choose f' hf'' using hf' i
    let δf : Γ(P₀.A.left, Out.nonzeroLocus (s i)) → Γ(P₀.A.left, Out.nonzeroLocus (s i)) :=
      fun f => constFn P₀.A.hom _ ((k : K)⁻¹) * f' f
    have hval : ∀ f, valR ξ _ (δf f) = Dv i (valR ξ _ f) := by
      intro f
      simp only [δf]
      rw [WtAlg.valR_mul'' _ _ hξi, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξi, hf'' f, map_inv₀, map_natCast]
      simp only [Dv, Tm]
      rw [mul_sub, ← _root_.mul_assoc, inv_mul_cancel₀ hk0, _root_.one_mul]
    obtain ⟨d, hdF, hdU⟩ := GlobalTheory.DerFieldExt.exists_field P₀.A.left _ (haff i) δf
      (fun a b => heq _ hξi _ _ (by
        rw [hval, WtAlg.valR_add' ξ _ hξi (δf a) (δf b), hval, hval, WtAlg.valR_add' ξ _ hξi a b, Dv_add]))
      (fun a b => heq _ hξi _ _ (by
        rw [hval, WtAlg.valR_add' ξ _ hξi, WtAlg.valR_mul'' ξ _ hξi a (δf b), WtAlg.valR_mul'' ξ _ hξi b (δf a),
          hval, hval, WtAlg.valR_mul'' ξ _ hξi a b, Dv_mul]))
    refine ⟨d, hdF, GlobalTheory.T.vectorField_follows_derivation_on_smaller_open_at_fieldPoint P₀.A.left _ (haff i) F ξ hξi d hdF (Dv i) (Dv_add i) (Dv_mul i) (fun f => ?_)⟩
    rw [hdU]; exact hval f
  choose d hdF hdv using hd
  let Wo : I × P₀.L.ι → P₀.A.left.Opens := fun p => P₀.A.left.basicOpen ((s p.1).f fun _ => p.2)
  have hWD : ∀ p, Wo p ≤ Out.nonzeroLocus (s p.1) := fun p =>
    le_iSup (fun κ => P₀.A.left.basicOpen ((s p.1).f κ)) (fun _ => p.2)
  have hWU : ∀ p, Wo p ≤ 𝟙 P₀.A.left ⁻¹ᵁ P₀.L.U p.2 := fun p =>
    (P₀.A.left.basicOpen_le _).trans (LB.wchart_le P₀.L (fun _ : Fin 1 => 𝟙 P₀.A.left) (fun _ => p.2) 0)
  let u : ∀ p, Γ(P₀.A.left, Wo p)ˣ := fun p =>
    (P₀.A.left.toRingedSpace.isUnit_res_basicOpen ((s p.1).f fun _ => p.2)).unit
  let y : ∀ p, Fin n → Γ(P₀.A.left, Wo p) := fun p e =>
    constFn P₀.A.hom _ ((k : K)⁻¹) *
      ∑ a, constFn P₀.A.hom _ (lam a e) * dd a (Wo p) (u p).val * ((u p)⁻¹).val
  let dk : I × P₀.L.ι → Fld P₀.A.left := fun p O f => d p.1 O f + ∑ e, rsT (y p e) O * dd e O f
  let Gv : P₀.L.ι → F := fun j => valR ξ (P₀.L.U j₀ ⊓ P₀.L.U j) (P₀.L.g j₀ j).val
  have hUj : ∀ p O, O ≤ Wo p → ⊤ ≤ ξ ⁻¹ᵁ O → ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U p.2 := fun p O hOW hO q hq => hWU p (hOW (hO hq))
  have hGv : ∀ j, ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j → Gv j ≠ 0 := fun j hj =>
    valR_unit_ne ξ (O := P₀.L.U j₀ ⊓ P₀.L.U j) (fun q hq => ⟨hj₀ hq, hj hq⟩) (P₀.L.g j₀ j)
  have hval : ∀ p O, O ≤ Wo p → ∀ (hO : ⊤ ≤ ξ ⁻¹ᵁ O) f, valR ξ O (dk p O f) =
      δ₀ (valR ξ O f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (Gv p.2) / Gv p.2) * δ e (valR ξ O f) := by
    intro p O hOW hO f
    have hW : ⊤ ≤ ξ ⁻¹ᵁ Wo p := fun q hq => hOW (hO hq)
    have hS : valR ξ (Wo p) (u p : Γ(P₀.A.left, Wo p)) = valR ξ _ ((s p.1).f fun _ => p.2) :=
      valR_res' ξ _ hW _
    have hy : ∀ e, valR ξ (Wo p) (y p e) = (k : F)⁻¹ *
        ∑ a, ψ (lam a e) * δ a (valR ξ _ ((s p.1).f fun _ => p.2)) * (valR ξ _ ((s p.1).f fun _ => p.2))⁻¹ := by
      intro e
      simp only [y]
      rw [WtAlg.valR_mul'' _ _ hW, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hW, map_inv₀, map_natCast, valR_sum' ξ hW]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [WtAlg.valR_mul'' _ _ hW, WtAlg.valR_mul'' _ _ hW, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hW, hδ a _ _ hW,
        valR_inv' ξ hW, hS]
    have hSne : valR ξ _ ((s p.1).f fun _ => p.2) ≠ 0 := hS ▸ valR_unit_ne ξ hW (u p)
    have hE : S0 p.1 = Gv p.2 ^ k * valR ξ _ ((s p.1).f fun _ => p.2) :=
      GlobalTheory.T.sectionPowerValue_chart_change_by_transition_pow P₀.A.left P₀.L k (s p.1) F ξ j₀ p.2 hj₀ (hUj p O hOW hO)
    simp only [dk]
    rw [WtAlg.valR_add' _ _ hO, hdv p.1 O (hOW.trans (hWD p)) hO f, valR_sum' ξ hO]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [WtAlg.valR_mul'' _ _ hO, GlobalTheory.LogKSBal.valR_rsT ξ hOW hO, hy e, hδ e O f hO])]
    simp only [Dv, Tm]
    rw [hE]
    exact alg_val δ (fun a e => ψ (lam a e)) k hk0 (Gv p.2) _ (hGv _ (hUj p O hOW hO)) hSne _ _
  refine ⟨I × P₀.L.ι, Wo, fun p => p.2, dk, ?_, hWU, fun p => ⟨?_, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨κ, hκ⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    obtain ⟨j, rfl⟩ : ∃ j, κ = fun _ => j := ⟨κ 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hκ⟩
  · exact Adjust.isField_add_comb (d p.1) dd (y p) (isField_mono (hdF p.1) (hWD p)) (fun a => (hinv a).1)
  · intro O hO r
    by_cases hξO : ⊤ ≤ ξ ⁻¹ᵁ O
    · apply heq O hξO
      rw [hval p O hO hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO]
      simp [hδ₀, hδψ]
    · exact (hsub O hξO).elim _ _
  · intro p p' O hO f
    by_cases hξO : ⊤ ≤ ξ ⁻¹ᵁ O
    · apply heq O hξO
      have hO1 : O ≤ Wo p := hO.trans inf_le_left
      have hO2 : O ≤ Wo p' := hO.trans inf_le_right
      have hU1 := hUj p O hO1 hξO
      have hU2 := hUj p' O hO2 hξO
      have hU12 : ⊤ ≤ ξ ⁻¹ᵁ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) := fun q hq => ⟨hU1 hq, hU2 hq⟩
      have hOg : O ≤ 𝟙 P₀.A.left ⁻¹ᵁ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) := fun q hq => ⟨hWU p (hO1 hq), hWU p' (hO2 hq)⟩
      have hsym : ∀ a b, ψ (lam a b) = ψ (lam b a) := fun a b => by
        rw [← congrFun (congrFun hlam a) b, Matrix.transpose_apply]
      have hR : valR ξ O (∑ a, ∑ b, constFn P₀.A.hom O (lam a b) * dlg P₀.A (𝟙 P₀.A.left) P₀.L (dd b) p.2 p'.2 O *
          dd a O f) = ∑ a, ∑ b, ψ (lam a b) * (δ b (valR ξ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) (P₀.L.g p.2 p'.2).val) *
            (valR ξ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) (P₀.L.g p.2 p'.2).val)⁻¹) * δ a (valR ξ O f) := by
        rw [valR_sum' ξ hξO]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [valR_sum' ξ hξO]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [WtAlg.valR_mul'' _ _ hξO, WtAlg.valR_mul'' _ _ hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO,
          hδ a O f hξO, dlg, WtAlg.valR_mul'' _ _ hξO, hδ b O _ hξO, GlobalTheory.LogKSBal.valR_pbT ξ _ hOg hξO,
          GlobalTheory.LogKSBal.valR_pbT ξ _ hOg hξO, Category.comp_id, valR_inv' ξ hU12]
      rw [WtAlg.valR_sub' _ _ hξO, hval p O hO1 hξO f, hval p' O hO2 hξO f, hR]
      exact alg_diff δ (fun a e => ψ (lam a e)) hsym (Gv p.2) (Gv p'.2) _ (hGv _ hU1) (valR_unit_ne ξ hU12 _)
        (GlobalTheory.T.transitionUnit_pointValue_cocycle P₀.A.left P₀.L P₀.isLB F ξ j₀ p.2 p'.2 hj₀ hU1 hU2) _ _
    · exact (hsub O hξO).elim _ _

end GlobalTheory.Heat.ZeroKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShiftedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (lam : Matrix (Fin n) (Fin n) K), lamᵀ = lam → (∀ r, δ₀ (ψ r) = 0) → ∀ (k : ℕ), 1 ≤ k → ∀ (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), ⨆ i, Out.nonzeroLocus (s i) = ⊤ → (∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i)) → (∀ i, (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (valR ξ _ ((s i).f fun _ => j₀)) / valR ξ _ ((s i).f fun _ => j₀)) * δ e (valR ξ _ f))) → KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) lam := by
  first | exact @GlobalTheory.Heat.ZeroKS.ksRel_zero | exact GlobalTheory.Heat.ZeroKS.ksRel_zero | (intros; apply GlobalTheory.Heat.ZeroKS.ksRel_zero <;> assumption)
end
