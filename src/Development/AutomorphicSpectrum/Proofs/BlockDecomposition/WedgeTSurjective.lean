module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section Defs

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev QC : Type := C1 F ⧸ LinearMap.range (d0 F)

def iotaQ : H1 F →ₗ[R] QC F :=
  Submodule.mapQ _ _ (Z1 F).subtype (by
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩)

theorem iotaQ_mk (f : Z1 F) : iotaQ F (H1.mk F f) = Submodule.Quotient.mk f.1 := rfl

theorem iotaQ_injective : Function.Injective (iotaQ F) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [iotaQ_mk, Submodule.Quotient.mk_eq_zero] at hc
  obtain ⟨g, hg⟩ := hc
  exact H1.mk_eq_zero.2 ⟨g, hg⟩

def crossB : H1 F →ₗ[R] H1 F →ₗ[R] H2 (box F) :=
  (cup (box F)).compl₁₂ (boxL F).pull1 (boxR F).pull1

theorem crossB_apply (a b : H1 F) : crossB F a b = cup (box F) ((boxL F).pull1 a) ((boxR F).pull1 b) := rfl

end Defs

section Wedge

variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

private theorem upd0 {X : Type} (a b c : X) : Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> simp

private theorem upd1 {X : Type} (a b c : X) : Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> simp

def wedgeT : V ⊗[R] V →ₗ[R] ⋀[R]^2 V :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 0 a a'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 0 r a
      simpa only [upd0, upd1] using this)
    (fun a b b' ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 1 b b'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 1 r b
      simpa only [upd0, upd1] using this))

theorem wedgeT_tmul (a b : V) : wedgeT (R := R) V (a ⊗ₜ b) = exteriorPower.ιMulti R 2 ![a, b] := rfl

end Wedge

end GlobalTheory.CompanionTheory.WedgeOf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishing
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle

theorem exists_tensorPi (R : Type) [CommRing R] (I J : Type) [Finite I] [Finite J] (A : I → Type) (B : J → Type)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)] :
    ∃ Φ : (∀ i, A i) ⊗[R] (∀ j, B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2,
      ∀ (f : ∀ i, A i) (g : ∀ j, B j) (x : I × J), Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g x.2 := by
  classical
  haveI := Fintype.ofFinite I
  haveI := Fintype.ofFinite J
  let e : (∀ j, ∀ i, A i ⊗[R] B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2 :=
    { toFun := fun g x ↦ g x.2 x.1
      invFun := fun h j i ↦ h (i, j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨(TensorProduct.piRight R R (∀ i, A i) B) ≪≫ₗ
    (LinearEquiv.piCongrRight fun j ↦ (TensorProduct.comm R _ _) ≪≫ₗ (TensorProduct.piRight R R (B j) A) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R _ _)) ≪≫ₗ e, fun f g x ↦ ?_⟩
  simp [e]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev Ar (C : Type) [Category.{0} C] : Type := Σ T : C, Σ T' : C, (T ⟶ T')

theorem finite_ar [Finite C] [Quiver.IsThin C] : Finite (Ar C) := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  infer_instance

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ x : Ar C, F.obj x.2.1 where
  toFun f x := f x.1 x.2.1 x.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

abbrev E : Type := ∀ x : Ar C × Ar C, F.obj x.1.2.1 ⊗[R] F.obj x.2.2.1

def shuffle : C2 (box F) →ₗ[R] E F where
  toFun z x := z (x.1.1, x.2.1) (x.1.2.1, x.2.1) (x.1.2.1, x.2.2.1) (x.1.2.2, 𝟙 _) (𝟙 _, x.2.2.2)
    - z (x.1.1, x.2.1) (x.1.1, x.2.2.1) (x.1.2.1, x.2.2.1) (𝟙 _, x.2.2.2) (x.1.2.2, 𝟙 _)
  map_add' z z' := by
    funext x
    simp only [Pi.add_apply]
    abel
  map_smul' r z := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem mp_box {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') (t : F.obj a ⊗[R] F.obj b) :
    (mp (box F) (T := (a, b)) (T' := (a', b')) (φ, ψ)) t =
      TensorProduct.map (mp F φ).toLinearMap (mp F ψ).toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem shuffle_cup (f h : Z1 F) (x : Ar C × Ar C) :
    shuffle F (cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h)).1 x =
      f.1 _ _ x.1.2.2 ⊗ₜ h.1 _ _ x.2.2.2 := by
  obtain ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩ := x
  change (mp (box F) (T := (a', b)) (T' := (a', b')) (𝟙 a', ψ)) (f.1 a a' φ ⊗ₜ 1) * (1 ⊗ₜ h.1 b b' ψ) -
    (mp (box F) (T := (a, b')) (T' := (a', b')) (φ, 𝟙 b')) (f.1 a a (𝟙 a) ⊗ₜ 1) * (1 ⊗ₜ h.1 b' b' (𝟙 b')) = _
  rw [Z1.id f a, mp_box]
  simp [mp_id]

theorem shuffle_mk (z : C2 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F z (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      z (a, b) (a', b) (a', b') (φ, 𝟙 b) (𝟙 a', ψ) - z (a, b) (a, b') (a', b') (𝟙 a, ψ) (φ, 𝟙 b') := rfl

theorem shuffle_coboundary_one (w : C1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F (d1 (box F) w) (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      (TensorProduct.map LinearMap.id (mp F ψ).toLinearMap (w (a, b) (a', b) (φ, 𝟙 b)) - w (a, b') (a', b') (φ, 𝟙 b')) +
      (w (a', b) (a', b') (𝟙 a', ψ) -
        TensorProduct.map (mp F φ).toLinearMap LinearMap.id (w (a, b) (a, b') (𝟙 a, ψ))) := by
  have e : CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a', b)) (Z := (a', b')) (φ, 𝟙 b) (𝟙 a', ψ) =
      CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a, b')) (Z := (a', b')) (𝟙 a, ψ) (φ, 𝟙 b') := by
    simp
  have i1 : (mp F (𝟙 a')).toLinearMap = LinearMap.id := by ext u; exact mp_id F a' u
  have i2 : (mp F (𝟙 b')).toLinearMap = LinearMap.id := by ext u; exact mp_id F b' u
  rw [shuffle_mk, d1_apply, d1_apply, e, mp_box, mp_box, i1, i2]
  abel

theorem exists_one_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F, ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) (Ar C) (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_one_zero_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2,
      ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) C (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (LinearEquiv.refl R _) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_zero_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1,
      ∀ f g x, Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R C (Ar C) (fun x ↦ F.obj x) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (LinearEquiv.refl R _) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

variable {F}

theorem phi_right (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₁ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2)
    (hΦ₁ : ∀ f g x, Φ₁ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2) (u : C1 F ⊗[R] C0 F) (x y : Ar C) :
    Φ (TensorProduct.map LinearMap.id (d0 F) u) (x, y) =
      Φ₁ u (x, y.2.1) - TensorProduct.map LinearMap.id (mp F y.2.2).toLinearMap (Φ₁ u (x, y.1)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₁, amitsur_d0_apply, TensorProduct.tmul_sub]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Pi.add_apply, hu, hv]
    abel

theorem phi_left (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₂ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1)
    (hΦ₂ : ∀ f g x, Φ₂ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2) (v : C0 F ⊗[R] C1 F) (x y : Ar C) :
    Φ (TensorProduct.map (d0 F) LinearMap.id v) (x, y) =
      Φ₂ v (x.2.1, y) - TensorProduct.map (mp F x.2.2).toLinearMap LinearMap.id (Φ₂ v (x.1, y)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₂, amitsur_d0_apply, TensorProduct.sub_tmul]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Pi.add_apply, hu, hv]
    abel

variable (F)

def crossZ : Z1 F ⊗[R] Z1 F →ₗ[R] Z2 (box F) :=
  TensorProduct.lift ((cupZ (box F)).compl₁₂ (boxL F).pullbackOneCocycle (boxR F).pullbackOneCocycle)

theorem crossZ_tmul (f h : Z1 F) :
    crossZ F (f ⊗ₜ h) = cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h) := rfl

theorem mk_crossZ (s : Z1 F ⊗[R] Z1 F) :
    H2.mk (box F) (crossZ F s) = TensorProduct.lift (crossB F) (TensorProduct.map (H1.mk F) (H1.mk F) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h => rfl
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem shuffle_crossZ (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2) (s : Z1 F ⊗[R] Z1 F) :
    shuffle F (crossZ F s).1 = Φ (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h =>
    funext x
    rw [crossZ_tmul, shuffle_cup, TensorProduct.map_tmul, hΦ]
    rfl
  | add u v hu hv =>
    simp only [map_add (f := _), Submodule.coe_add, hu, hv]

theorem exists_boundary [Finite C] [Quiver.IsThin C] (s : Z1 F ⊗[R] Z1 F) (w : C1 (box F))
    (hw : d1 (box F) w = (crossZ F s).1) :
    ∃ (u : C1 F ⊗[R] C0 F) (v : C0 F ⊗[R] C1 F), TensorProduct.map (Z1 F).subtype (Z1 F).subtype s =
      TensorProduct.map (d0 F) LinearMap.id v - TensorProduct.map LinearMap.id (d0 F) u := by
  obtain ⟨Φ, hΦ⟩ := exists_one_one_cochain_tensor_equiv F
  obtain ⟨Φ₁, hΦ₁⟩ := exists_one_zero_cochain_tensor_equiv F
  obtain ⟨Φ₂, hΦ₂⟩ := exists_zero_one_cochain_tensor_equiv F
  refine ⟨Φ₁.symm fun x ↦ w (x.1.1, x.2) (x.1.2.1, x.2) (x.1.2.2, 𝟙 _),
    Φ₂.symm fun x ↦ w (x.1, x.2.1) (x.1, x.2.2.1) (𝟙 _, x.2.2.2), Φ.injective ?_⟩
  rw [← shuffle_crossZ F Φ hΦ, ← hw]
  funext ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩
  rw [shuffle_coboundary_one, map_sub, Pi.sub_apply, phi_right Φ hΦ Φ₁ hΦ₁, phi_left Φ hΦ Φ₂ hΦ₂]
  simp only [LinearEquiv.apply_symm_apply]
  abel

theorem map_iotaQ_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F) (ht : TensorProduct.lift (crossB F) t = 0) :
    TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by
  obtain ⟨s, rfl⟩ := TensorProduct.map_surjective (H1.mk_surjective F) (H1.mk_surjective F) t
  rw [← mk_crossZ] at ht
  obtain ⟨w, hw⟩ := H2.mk_eq_zero.1 ht
  obtain ⟨u, v, huv⟩ := exists_boundary F s w hw
  let q := (LinearMap.range (d0 F)).mkQ
  have hq : ∀ g, q (d0 F g) = 0 := fun g ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨g, rfl⟩
  have h1 : ∀ s : Z1 F ⊗[R] Z1 F, TensorProduct.map (iotaQ F) (iotaQ F) (TensorProduct.map (H1.mk F) (H1.mk F) s) =
      TensorProduct.map q q (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := fun s ↦ by
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ v : C0 F ⊗[R] C1 F, TensorProduct.map q q (TensorProduct.map (d0 F) LinearMap.id v) = 0 := fun v ↦ by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  have h3 : ∀ u : C1 F ⊗[R] C0 F, TensorProduct.map q q (TensorProduct.map LinearMap.id (d0 F) u) = 0 := fun u ↦ by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  rw [h1, huv, map_sub, h2, h3, sub_zero]

end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishingStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.cross_product_kernel_quotient_vanishing := GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRank
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem bijective_of_surjective_of_VB : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B,
    Function.Surjective f → Function.Bijective f := by
  intro R A B _ _ _ _ _ n hA hB f hf
  obtain ⟨fA, pA, rA⟩ := hA
  obtain ⟨fB, pB, rB⟩ := hB
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hg' : ∀ b, f (g b) = b := fun b => LinearMap.congr_fun hg b

  let s : A →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g ∘ₗ f) (fun a => by
      simp [LinearMap.mem_ker, hg'])
  have hs : s ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    have hx : f x.1 = 0 := x.2
    simp [s, hx]
  have hsurj : Function.Surjective s := fun x => ⟨x.1, LinearMap.congr_fun hs x⟩
  haveI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective s hsurj
  haveI : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype s hs

  let E : (LinearMap.ker f × B) ≃ₗ[R] A :=
    LinearEquiv.ofLinear ((LinearMap.ker f).subtype.coprod g) (s.prod f)
      (by
        ext a <;> simp [s, hg'])
      (by
        ext x <;> simp [s, hg'])
  have hsub : Subsingleton (LinearMap.ker f) := by
    rw [← Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)]
    funext p
    have h1 := congrFun (Module.rankAtStalk_prod (R := R) (LinearMap.ker f) B) p
    have h2 := Module.rankAtStalk_eq_of_equiv (R := R) E
    have h3 := congrFun h2 p
    simp only [Pi.add_apply] at h1
    rw [h1, rA p, rB p] at h3
    simpa using h3
  refine ⟨?_, hf⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have : (⟨a, ha⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

end GlobalTheory.CompanionTheory.WedgeOf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRankStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.bijective_of_surjective_same_rank := GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCross
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCross
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a', rfl⟩ := H1.mk_surjective F a
  obtain ⟨b', rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add (f := _), H2.mk_eq_zero]
  refine ⟨-(fun T T' φ => a'.1 T T' φ * b'.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [map_neg, Pi.neg_apply, d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp, map_mul]
  ring

theorem hopf_pull_lift_cup {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R)
    (π : CoefMap (RingHom.id R) (box F) G) (m : CoefMap (RingHom.id R) F G)
    (hm : ∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c))
    (t : H1 F ⊗[R] H1 F) :
    m.pull2 (TensorProduct.lift (cup F) t) =
      π.pull2 ((boxL F).pull2 (TensorProduct.lift (cup F) t) +
        (boxR F).pull2 (TensorProduct.lift (cup F) t) +
        TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.lift.tmul, CoefMap.pullCohomologyTwo_cup m a b, hm a, hm b, ← CoefMap.pullCohomologyTwo_cup π _ _]
    refine congrArg (fun x => π.pull2 x) ?_
    rw [CoefMap.pullCohomologyTwo_cup (boxL F) a b, CoefMap.pullCohomologyTwo_cup (boxR F) a b, TensorProduct.comm_tmul, map_sub,
      TensorProduct.lift.tmul, TensorProduct.lift.tmul, crossB_apply, crossB_apply]
    simp only [map_add (f := _), LinearMap.add_apply]
    have h := cup_add_cup_swap (box F) ((boxL F).pull1 b) ((boxR F).pull1 a)
    have h3 : cup (box F) ((boxR F).pull1 a) ((boxL F).pull1 b) =
        -cup (box F) ((boxL F).pull1 b) ((boxR F).pull1 a) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    rw [h3]
    abel
  | add x y hx hy =>
    simp only [map_add (f := _), map_sub, hx, hy]
    abel

theorem hopf_cross_antisymm : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  intro hLow R _ C _ F hH t ht
  obtain ⟨D, _, G, π, m, hq, hm, -⟩ := hH
  have h2 := hopf_pull_lift_cup F G π m hm t
  simp only [ht, map_zero, zero_add] at h2
  obtain ⟨-, hinj, -⟩ := hLow R (C × C) D (box F) G π hq
  apply hinj.1
  rw [map_zero]
  exact h2.symm

end GlobalTheory.CompanionTheory.WedgeOf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCrossStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.cup_vanishing_antisymmetric_cross := GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZero
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.CompanionTheory.WedgeOf

section SymmWedge

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem wedgeT_tmul_self (a : V) : wedgeT (R := R) V (a ⊗ₜ[R] a) = 0 := by
  rw [wedgeT_tmul]
  exact (exteriorPower.ιMulti R (M := V) 2).map_eq_zero_of_eq ![a, a]
    (i := 0) (j := 1) rfl (by decide)

theorem wedgeT_tmul_add_swap (a b : V) :
    wedgeT (R := R) V (a ⊗ₜ[R] b) + wedgeT (R := R) V (b ⊗ₜ[R] a) = 0 := by
  have h := wedgeT_tmul_self (R := R) (a + b)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add (f := _), map_add (f := _),
    map_add, wedgeT_tmul_self, wedgeT_tmul_self, zero_add, add_zero] at h
  exact h

theorem sum_sum_eq_zero_of_antisymm {ι M : Type} [DecidableEq ι] [AddCommGroup M]
    (f : ι → ι → M) (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.sum_add_distrib, ih, hd, zero_add, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ ha a i

theorem wedgeT_eq_zero_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (t : V ⊗[R] V) (ht : TensorProduct.comm R V V t = t) : wedgeT (R := R) V t = 0 := by
  set B := b.tensorProduct b with hB
  have hsym : ∀ i j, B.repr t (i, j) = B.repr t (j, i) := by
    have key : ∀ (i j : ι) (s : V ⊗[R] V),
        B.repr (TensorProduct.comm R V V s) (i, j) = B.repr s (j, i) := by
      intro i j s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp [hB, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add x y hx hy => simp [map_add (f := _), hx, hy]
    intro i j
    rw [← key i j t, ht]
  have hexp : t = ∑ i, ∑ j, B.repr t (i, j) • (b i ⊗ₜ[R] b j) := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_prod_type]
    simp [hB, Module.Basis.tensorProduct_apply]
  rw [hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  refine sum_sum_eq_zero_of_antisymm
    (fun i j ↦ B.repr t (i, j) • wedgeT (R := R) V (b i ⊗ₜ[R] b j)) ?_ ?_ Finset.univ
  · intro i
    simp [wedgeT_tmul_self]
  · intro i j
    show B.repr t (i, j) • _ + B.repr t (j, i) • _ = 0
    rw [hsym j i, ← smul_add, wedgeT_tmul_add_swap, smul_zero]

theorem map_wedgeT {W : Type} [AddCommGroup W] [Module R W] (r : W →ₗ[R] V) (s : W ⊗[R] W) :
    exteriorPower.map 2 r (wedgeT (R := R) W s) = wedgeT (R := R) V (TensorProduct.map r r s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, wedgeT_tmul, wedgeT_tmul, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem wedgeT_eq_zero_of_symm (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V)
    (ht : t - TensorProduct.comm R V V t = 0) : wedgeT (R := R) V t = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R V
  obtain ⟨i, hi⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hri : ∀ v, r (i v) = v := fun v ↦ LinearMap.congr_fun hi v
  have hcomm : TensorProduct.comm R V V t = t := (sub_eq_zero.1 ht).symm
  have hmap : ∀ s : V ⊗[R] V, TensorProduct.comm R (Fin n → R) (Fin n → R) (TensorProduct.map i i s)
      = TensorProduct.map i i (TensorProduct.comm R V V s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hback : ∀ s : V ⊗[R] V, TensorProduct.map r r (TensorProduct.map i i s) = s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hri]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hW : wedgeT (R := R) (Fin n → R) (TensorProduct.map i i t) = 0 :=
    wedgeT_eq_zero_of_basis (Pi.basisFun R (Fin n)) _ (by rw [hmap, hcomm])
  have := map_wedgeT r (TensorProduct.map i i t)
  rw [hW, map_zero, hback] at this
  exact this.symm

end SymmWedge

end GlobalTheory.CompanionTheory.WedgeOf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZeroStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.wedge_of_symmetric_tensor_zero := GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']

@[reducible] def bcF : C ⥤ CommAlgCat.{0} R' where
  obj T := CommAlgCat.of R' (R' ⊗[R] F.obj T)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_id F T b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_comp F φ ψ b))

def bcM : BC F (bcF F R') where
  α T := (Algebra.TensorProduct.includeRight : F.obj T →ₐ[R] R' ⊗[R] F.obj T).toRingHom
  naturality _ _ := rfl
  smul T r b := by
    change (1 : R') ⊗ₜ[R] (r • b) = algebraMap R R' r • ((1 : R') ⊗ₜ[R] b)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  bij T := ⟨LinearEquiv.refl _ _, fun _ ↦ rfl⟩

variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')

def ev0 : M ⊗[R] C0 F →ₗ[R] ∀ T : C, R' ⊗[R] F.obj T :=
  LinearMap.pi fun T ↦ TensorProduct.map j (LinearMap.proj T)

def ev1 : M ⊗[R] C1 F →ₗ[R] ∀ (T T' : C) (_ : T ⟶ T'), R' ⊗[R] F.obj T' :=
  LinearMap.pi fun T ↦ LinearMap.pi fun T' ↦ LinearMap.pi fun φ ↦
    TensorProduct.map j ((LinearMap.proj φ) ∘ₗ (LinearMap.proj T') ∘ₗ (LinearMap.proj T))

theorem evaluation_zero_tmul (n : M) (g : C0 F) (T : C) : ev0 F j (n ⊗ₜ g) T = j n ⊗ₜ g T := rfl

theorem realTensorEvalAlgHom_tmul (n : M) (f : C1 F) {T T' : C} (φ : T ⟶ T') :
    ev1 F j (n ⊗ₜ f) T T' φ = j n ⊗ₜ f T T' φ := rfl

theorem evaluation_coboundary_zero_tensor (y : M ⊗[R] C0 F) :
    ev1 F j ((d0 F).lTensor M y) = d0 (bcF F R') (ev0 F j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n g =>
    funext T T' φ
    show ev1 F j (n ⊗ₜ d0 F g) T T' φ = ev0 F j (n ⊗ₜ g) T' - mp (bcF F R') φ (ev0 F j (n ⊗ₜ g) T)
    rw [realTensorEvalAlgHom_tmul, evaluation_zero_tmul, evaluation_zero_tmul, amitsur_d0_apply]
    show j n ⊗ₜ (g T' - mp F φ (g T)) =
      j n ⊗ₜ g T' - (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ)) (j n ⊗ₜ g T)
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.tmul_sub]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_cocycle (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul n c =>
    refine ⟨j n • (bcM F R').coef.pullbackOneCocycle c, ?_, ?_⟩
    · funext T T' φ
      show j n • ((1 : R') ⊗ₜ[R] (c.1 T T' φ)) = ev1 F j (n ⊗ₜ c.1) T T' φ
      rw [realTensorEvalAlgHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rw [map_smul, ← CoefMap.pullCohomologyOne_class]
      show j n • (bcM F R').coef.pull1 (H1.mk F c) = e (j n ⊗ₜ H1.mk F c)
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨z1, h1, h1'⟩ := hx
    obtain ⟨z2, h2, h2'⟩ := hy
    refine ⟨z1 + z2, ?_, ?_⟩
    · simp only [Submodule.coe_add, h1, h2, map_add (f := _)]
    · simp only [map_add (f := _), h1', h2']

theorem lTensor_iotaQ_injective_of_retract (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by
  obtain ⟨e, he⟩ := h R' (bcF F R') (bcM F R')
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective M (H1.mk_surjective F) x
  have hcomp : iotaQ F ∘ₗ H1.mk F = (LinearMap.range (d0 F)).mkQ ∘ₗ (Z1 F).subtype :=
    LinearMap.ext fun f => iotaQ_mk F f
  have hx' : ((LinearMap.range (d0 F)).mkQ).lTensor M ((Z1 F).subtype.lTensor M t) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, ← hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (LinearMap.exact_map_mkQ_range (d0 F))
    (Submodule.mkQ_surjective _) ((Z1 F).subtype.lTensor M t)).1 hx'
  obtain ⟨z, hz1, hz2⟩ := exists_cocycle F j e he t
  have hz0 : H1.mk (bcF F R') z = 0 := by
    apply iotaQ_injective (bcF F R')
    rw [iotaQ_mk, map_zero, Submodule.Quotient.mk_eq_zero, hz1, ← hy, evaluation_coboundary_zero_tensor]
    exact LinearMap.mem_range_self _ _
  have hx0 : j.rTensor (H1 F) ((H1.mk F).lTensor M t) = 0 := by
    rw [← e.map_eq_zero_iff, ← hz2, hz0]
  calc (H1.mk F).lTensor M t = (p ∘ₗ j).rTensor (H1 F) ((H1.mk F).lTensor M t) := by
        rw [hp, LinearMap.rTensor_id_apply]
    _ = p.rTensor (H1 F) (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := LinearMap.rTensor_comp_apply _ _ _ _
    _ = 0 := by rw [hx0, map_zero]

end BaseChange

theorem iotaQ_lTensor_injective (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact lTensor_iotaQ_injective_of_retract F (TrivSqZeroExt.inrHom R M) h (TrivSqZeroExt.sndHom R M)
    (LinearMap.ext fun m => by simp)

end GlobalTheory.CompanionTheory.WedgeOf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjectiveStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.first_cohomology_inclusion_tensor_injective := GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRank
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem vb_exteriorPower_two : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  intro R V _ _ _ g h
  obtain ⟨hf, hp, hr⟩ := h
  have hproj : Module.Projective R (⋀[R]^2 V) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hp
    haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2
    refine Module.Projective.of_split (exteriorPower.map 2 s)
      (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hb := LocalizedModule.isBaseChange p.asIdeal.primeCompl V
  have hb2 := GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule p.asIdeal.primeCompl V
  let q : PrimeSpectrum S := IsLocalRing.closedPoint S
  have hq : PrimeSpectrum.comap (algebraMap R S) q = p :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := p.asIdeal))
  have h1 := Module.rankAtStalk_isBaseChange hb q
  have h2 := Module.rankAtStalk_isBaseChange hb2 q
  rw [hq] at h1 h2
  haveI : Module.Finite S M := Module.Finite.equiv hb.equiv
  haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  have h3 : Module.finrank S M = g := by
    rw [← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S (⋀[S]^2 M) = _
  rw [exteriorPower.finrank_eq, h3]

end GlobalTheory.CompanionTheory.WedgeOf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRankStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
alias GlobalTheory.T.exterior_square_vector_bundle_rank := GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem wedgeT_surjective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] :
    Function.Surjective (wedgeT (R := R) V) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span (R := R) (n := 2) (M := V),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ v 1, ?_⟩
  rw [wedgeT_tmul]
  congr 1
  funext i; fin_cases i <;> rfl

theorem wedgeOf_of_low : LowSt → WedgeOfSt := by
  intro hL R _ P _ _ F g hH hV hBC hV2 hspan
  have : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  have hV' := hV
  obtain ⟨hf, hp, -⟩ := hV'
  have hκ : Function.Surjective (TensorProduct.lift (cup F)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1 ⊗ₜ x.2, rfl⟩
  have hinj : Function.Injective (TensorProduct.map (iotaQ F) (iotaQ F)) := by
    have e : TensorProduct.map (iotaQ F) (iotaQ F) =
        ((iotaQ F).lTensor (QC F)) ∘ₗ ((iotaQ F).rTensor (H1 F)) := by
      rw [LinearMap.lTensor_comp_rTensor]
    rw [e, LinearMap.coe_comp]
    exact (GlobalTheory.T.first_cohomology_inclusion_tensor_injective R _ F hBC (QC F)).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (iotaQ_injective F))
  have hker : LinearMap.ker (TensorProduct.lift (cup F)) ≤ LinearMap.ker (wedgeT (R := R) (H1 F)) := by
    intro t ht
    have h1 := GlobalTheory.T.cup_vanishing_antisymmetric_cross hL R _ F hH t ht
    have h2 := GlobalTheory.T.cross_product_kernel_quotient_vanishing R _ F _ h1
    have h3 := hinj (h2.trans (map_zero _).symm)
    exact GlobalTheory.T.wedge_of_symmetric_tensor_zero R _ t h3
  let s : H2 F →ₗ[R] ⋀[R]^2 (H1 F) :=
    (LinearMap.ker (TensorProduct.lift (cup F))).liftQ (wedgeT (R := R) (H1 F)) hker ∘ₗ
      (LinearMap.quotKerEquivOfSurjective _ hκ).symm.toLinearMap
  have hs : ∀ t, s (TensorProduct.lift (cup F) t) = wedgeT (R := R) (H1 F) t := by
    intro t
    have : (LinearMap.quotKerEquivOfSurjective _ hκ).symm (TensorProduct.lift (cup F) t) =
        Submodule.Quotient.mk t := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun y ↦ by
    obtain ⟨t, rfl⟩ := wedgeT_surjective R (H1 F) y
    exact ⟨_, hs t⟩
  have hb := GlobalTheory.T.bijective_of_surjective_same_rank R _ _ _ hV2 (GlobalTheory.T.exterior_square_vector_bundle_rank R _ g hV) s hsurj
  refine ⟨(LinearEquiv.ofBijective s hb).symm, fun a b ↦ ?_⟩
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  have := hs (a ⊗ₜ b)
  rw [wedgeT_tmul] at this
  exact this.symm

end GlobalTheory.CompanionTheory.WedgeOf
