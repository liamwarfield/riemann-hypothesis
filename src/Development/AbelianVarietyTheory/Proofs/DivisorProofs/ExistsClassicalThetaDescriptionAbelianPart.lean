module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieComb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.TanLinComb

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

abbrev TP (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (P : Type) [CommRing P] [Algebra ℂ P] :
    Over (Sp R) :=
  Over.mk (spMap (algebraMap ℂ P) ≫ (TF (R := R) ℂ).hom)

def mapP {P P' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] (φ : P →ₐ[ℂ] P') :
    TP R P' ⟶ TP R P :=
  Over.homMk (spMap φ.toRingHom) (by
    show spMap _ ≫ spMap _ ≫ _ = spMap _ ≫ _
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact RingHom.ext fun x => φ.commutes x)

def toTF (P : Type) [CommRing P] [Algebra ℂ P] : TP R P ⟶ TF (R := R) ℂ :=
  Over.homMk (spMap (algebraMap ℂ P)) rfl

def homF {P : Type} [CommRing P] [Algebra ℂ P] (a : P →ₐ[ℂ] ℂ) : TF (R := R) ℂ ⟶ TP R P :=
  Over.homMk (spMap a.toRingHom) (by
    show spMap _ ≫ spMap _ ≫ _ = _
    rw [← Category.assoc, spMap_comp']
    have : a.toRingHom.comp (algebraMap ℂ P) = RingHom.id ℂ := RingHom.ext fun x => a.commutes x
    rw [this, spMap_id', Category.id_comp])

variable {P P' P'' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] [CommRing P''] [Algebra ℂ P'']

theorem specMap_comp₃ (f : P →ₐ[ℂ] P') (g : P' →ₐ[ℂ] P'') :
    mapP (R := R) g ≫ mapP f = mapP (g.comp f) := by
  apply Over.OverMorphism.ext
  exact spMap_comp' _ _

theorem specMap_id₃ : mapP (R := R) (AlgHom.id ℂ P) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact spMap_id' _

theorem specMap_comp_toTF (f : P →ₐ[ℂ] P') : mapP (R := R) f ≫ toTF P = toTF P' := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  rw [spMap_comp']
  congr 1
  exact RingHom.ext fun x => f.commutes x

theorem homF_mapP (a : P' →ₐ[ℂ] ℂ) (f : P →ₐ[ℂ] P') : homF (R := R) a ≫ mapP f = homF (a.comp f) := by
  apply Over.OverMorphism.ext
  exact spMap_comp' _ _

theorem homF_toTF (a : P →ₐ[ℂ] ℂ) : homF (R := R) a ≫ toTF P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = 𝟙 _
  rw [spMap_comp']
  have : a.toRingHom.comp (algebraMap ℂ P) = RingHom.id ℂ := RingHom.ext fun x => a.commutes x
  rw [this, spMap_id']

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

def IsT (x : TP R (DualNumber ℂ) ⟶ G) : Prop := homF (Chart.fstD ℂ) ≫ x = 1

abbrev L {P : Type} [CommRing P] [Algebra ℂ P] (z : TP R P ⟶ G) : TP R P ⟶ TF (R := R) ℂ ⊗ G := lift (toTF P) z

abbrev x0 (G : Over (Sp R)) [GrpObj G] : Sp ℂ ⟶ (TF (R := R) ℂ ⊗ G).left := (lift (𝟙 (TF (R := R) ℂ)) (1 : TF (R := R) ℂ ⟶ G)).left

theorem isT_one : IsT (1 : TP R (DualNumber ℂ) ⟶ G) := MonObj.comp_one _

theorem isT_mul {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) : IsT (x * y) := by
  unfold IsT at *
  rw [MonObj.comp_mul, hx, hy, _root_.mul_one]

theorem isT_scale (c : ℂ) {x : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) : IsT (mapP (Chart.scaleD c) ≫ x) := by
  unfold IsT at *
  have : (Chart.fstD ℂ).comp (Chart.scaleD c) = Chart.fstD ℂ := by
    ext
    exact TrivSqZeroExt.fst_map _ _
  rw [← Category.assoc, homF_mapP, this, hx]

theorem specMap_scaleD_zero : mapP (R := R) (Chart.scaleD (0 : ℂ)) = toTF (DualNumber ℂ) ≫ homF (Chart.fstD ℂ) := by
  apply Over.OverMorphism.ext
  show spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp', Chart.scaleD_zero]
  rfl

theorem scale_zero_comp {x : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) : mapP (Chart.scaleD (0 : ℂ)) ≫ x = 1 := by
  rw [specMap_scaleD_zero, Category.assoc, hx, MonObj.comp_one]

theorem scale_one_comp (x : TP R (DualNumber ℂ) ⟶ G) : mapP (Chart.scaleD (1 : ℂ)) ≫ x = x := by
  rw [Chart.scaleD_one, specMap_id₃, Category.id_comp]

theorem homF_L {P : Type} [CommRing P] [Algebra ℂ P] (a : P →ₐ[ℂ] ℂ) (z : TP R P ⟶ G) :
    homF a ≫ L z = lift (𝟙 _) (homF a ≫ z) := by
  rw [comp_lift, homF_toTF]

theorem mapP_L {P P' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] (φ : P →ₐ[ℂ] P') (z : TP R P ⟶ G) :
    mapP φ ≫ L z = L (mapP φ ≫ z) := by
  rw [comp_lift, specMap_comp_toTF]

theorem valR_spMap_comp {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (φ : A →+* B) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR (spMap φ ≫ x) U f = φ (TangentOrigin.evalPt x U h f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, dite_eq_left h']
  exact TangentOrigin.evalPt_spMap_comp φ x U h h' f

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

theorem val_comb {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) (U : (TF (R := R) ℂ ⊗ G).left.Opens)
    (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) :
    ∃ t : TrivSqZeroExt ℂ (ℂ × ℂ), ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ,
      valR (L ((mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y))).left U f =
        TrivSqZeroExt.map l t := by
  let P : TP R (Chart.JetR ℂ (Fin 2) 1) ⟶ G := (mapP (Chart.qD 0) ≫ x) * (mapP (Chart.qD 1) ≫ y)
  have hP : homF (Chart.jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homF_mapP, homF_mapP, Chart.jetAug_comp_qD,
      Chart.jetAug_comp_qD]
    unfold IsT at hx hy
    rw [hx, hy, _root_.mul_one]
  have hred : spMap (Chart.jetAug ℂ (Fin 2) 1).toRingHom ≫ (L P).left = x0 G := by
    have := congrArg CommaMorphism.left (homF_L (Chart.jetAug ℂ (Fin 2) 1) P)
    rw [hP] at this
    exact this
  have hPU : ⊤ ≤ (L P).left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := UnifLieBasis.spMap_jetAug_surjective p
    rw [← hred] at h0
    exact h0 (Set.mem_univ q)
  refine ⟨Chart.deltaJ (TangentOrigin.evalPt (L P).left U hPU f), fun l => ?_⟩
  have hval : mapP (Chart.rD l) ≫ P =
      (mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y) := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specMap_comp₃, specMap_comp₃, Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  rw [← hval, ← mapP_L]
  exact valR_spMap_comp (Chart.rD l).toRingHom (L P).left U hPU f

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

def Dg (z : TP R (DualNumber ℂ) ⟶ G) (δ : ∀ U : (TF (R := R) ℂ ⊗ G).left.Opens, Γ((TF (R := R) ℂ ⊗ G).left, U) → ℂ) :
    Prop :=
  IsT z ∧ ∀ U f, ⊤ ≤ x0 G ⁻¹ᵁ U → valR (L z).left U f = TrivSqZeroExt.inl (valF (x0 G) U f) + TrivSqZeroExt.inr (δ U f)

theorem val_one (U : (TF (R := R) ℂ ⊗ G).left.Opens) (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) :
    valR (L (1 : TP R (DualNumber ℂ) ⟶ G)).left U f = TrivSqZeroExt.inl (valF (x0 G) U f) := by
  have e : L (1 : TP R (DualNumber ℂ) ⟶ G) = toTF (DualNumber ℂ) ≫ lift (𝟙 _) (1 : TF (R := R) ℂ ⟶ G) := by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  rw [e, Over.comp_left]
  show valR (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x0 G) U f = _
  rw [valR_spMap_comp _ _ U h0, valF, dite_eq_left h0, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem dg_one : Dg (1 : TP R (DualNumber ℂ) ⟶ G) (fun _ _ => 0) := by
  refine ⟨isT_one, fun U f h0 => ?_⟩
  rw [val_one U f h0, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comb {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) (U : (TF (R := R) ℂ ⊗ G).left.Opens)
    (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) (t : TrivSqZeroExt ℂ (ℂ × ℂ))
    (ht : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ,
      valR (L ((mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y))).left U f =
        TrivSqZeroExt.map l t) : t.fst = valF (x0 G) U f := by
  have := ht 0
  simp only [LinearMap.zero_apply] at this
  rw [scale_zero_comp hx, scale_zero_comp hy, _root_.mul_one, val_one U f h0] at this
  have := congrArg TrivSqZeroExt.fst this
  rw [TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_map] at this
  exact this.symm

theorem dg_mul {x y : TP R (DualNumber ℂ) ⟶ G} {δ δ'} (hx : Dg x δ) (hy : Dg y δ') : Dg (x * y) (δ + δ') := by
  refine ⟨isT_mul hx.1 hy.1, fun U f h0 => ?_⟩
  obtain ⟨t, ht⟩ := val_comb hx.1 hy.1 U f h0
  have h1 := fst_comb hx.1 hy.1 U f h0 t ht
  have ha := ht (LinearMap.fst ℂ ℂ ℂ)
  have hb := ht (LinearMap.snd ℂ ℂ ℂ)
  have hc := ht (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at ha hb hc
  rw [scale_one_comp, scale_zero_comp hy.1, _root_.mul_one, hx.2 U f h0] at ha
  rw [scale_one_comp, scale_zero_comp hx.1, _root_.one_mul, hy.2 U f h0] at hb
  rw [scale_one_comp, scale_one_comp] at hc
  rw [hc]
  have ha2 := congrArg TrivSqZeroExt.snd ha
  have hb2 := congrArg TrivSqZeroExt.snd hb
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_map,
    LinearMap.fst_apply, LinearMap.snd_apply, zero_add] at ha2 hb2
  ext
  · simp [TrivSqZeroExt.fst_map, h1]
  · simp [TrivSqZeroExt.snd_map, ha2, hb2]

theorem dg_scale (c : ℂ) {x : TP R (DualNumber ℂ) ⟶ G} {δ} (hx : Dg x δ) :
    Dg (mapP (Chart.scaleD c) ≫ x) (c • δ) := by
  refine ⟨isT_scale c hx.1, fun U f h0 => ?_⟩
  obtain ⟨t, ht⟩ := val_comb hx.1 isT_one U f h0
  have h1 := fst_comb hx.1 isT_one U f h0 t ht
  have ha := ht (LinearMap.fst ℂ ℂ ℂ)
  have hc := ht (c • LinearMap.fst ℂ ℂ ℂ)
  simp only [LinearMap.fst_apply, LinearMap.smul_apply, smul_eq_mul, _root_.mul_one, MulZeroClass.mul_zero] at ha hc
  rw [scale_one_comp, scale_zero_comp isT_one, _root_.mul_one, hx.2 U f h0] at ha
  rw [scale_zero_comp isT_one, _root_.mul_one] at hc
  rw [hc]
  have ha2 := congrArg TrivSqZeroExt.snd ha
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_map,
    LinearMap.fst_apply, zero_add] at ha2
  ext
  · simp [TrivSqZeroExt.fst_map, h1]
  · simp [TrivSqZeroExt.snd_map, ha2]

theorem dg_prod : ∀ {n : ℕ} (z : Fin n → (TP R (DualNumber ℂ) ⟶ G)) (δ : Fin n → ∀ U : (TF (R := R) ℂ ⊗ G).left.Opens,
    Γ((TF (R := R) ℂ ⊗ G).left, U) → ℂ), (∀ i, Dg (z i) (δ i)) → Dg (List.ofFn z).prod (∑ i, δ i)
  | 0, z, δ, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact dg_one
  | n + 1, z, δ, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact dg_mul (h 0) (dg_prod (fun i => z i.succ) (fun i => δ i.succ) fun i => h i.succ)

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

theorem toUnit_left' (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

abbrev fC (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] : R →+* ℂ :=
  (algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))

theorem tf_hom : (TF (R := R) ℂ).hom = spMap (fC R) := by
  show spMap _ ≫ spMap _ = _
  rw [spMap_comp']

def dm (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] : TP R (DualNumber ℂ) ⟶ epsR R :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (fC R))) (by
    show spMap _ ≫ spMap _ = spMap _ ≫ (TF (R := R) ℂ).hom
    rw [tf_hom, spMap_comp', spMap_comp']
    congr 1
    refine RingHom.ext fun a => ?_
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl])

variable {G : Over (Sp R)} [GrpObj G]

theorem comp_prod {T T' : Over (Sp R)} (h : T' ⟶ T) : ∀ {n : ℕ} (u : Fin n → (T ⟶ G)),
    h ≫ (List.ofFn u).prod = (List.ofFn fun i => h ≫ u i).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.comp_one _
  | n + 1, u => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h]

theorem isT_of_tangent {v : epsR R ⟶ G} (hv : IsTangent v) {b : TP R (DualNumber ℂ) ⟶ G}
    (hb : b.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (fC R)) ≫ v.left) : IsT b := by
  unfold IsT
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hb, Hom.one_def, Over.comp_left, toUnit_left', tf_hom]
  show spMap _ ≫ spMap _ ≫ _ = _
  rw [← Category.assoc, spMap_comp']
  have e : (Chart.fstD ℂ).toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap (fC R)) = (fC R).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, Chart.fstD]
  rw [e, ← spMap_comp', Category.assoc]
  unfold IsTangent at hv
  rw [hv]

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

theorem dm_scale (c : R) {v u : epsR R ⟶ G} (hu : u.left = spMap (epsScaleR c) ≫ v.left) {b : TP R (DualNumber ℂ) ⟶ G}
    (hb : b.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (fC R)) ≫ v.left) : dm R ≫ u = mapP (Chart.scaleD (fC R c)) ≫ b := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, hu, hb]
  show spMap _ ≫ spMap _ ≫ _ = spMap _ ≫ spMap _ ≫ _
  rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp']
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [epsScaleR, GlobalTheory.CompanionTheory.Ar.dualMap, Chart.scaleD, smul_smul, _root_.mul_comm]

end GlobalTheory.TanLinComb

namespace GlobalTheory


open GlobalTheory.TanLinComb in
theorem isD_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  open TanLinComb in
  intro R _ _ D _ N ν g d n c v w W b bw hv hc hb hbw hD
  have hx0 : ptB ν d 0 = x0 D.P.A := by
    have e1 : ν.eA (d.ex 0) = 1 := by
      have h1 := d.ex_add 0 0
      rw [add_zero] at h1
      have h2 := congrArg ν.eA h1
      rw [map_mul] at h2
      exact mul_eq_left.1 h2.symm
    unfold ptB
    rw [e1]
  let δW : (Fin g → ℂ) → ∀ U : (TF (R := R) ℂ ⊗ D.P.A).left.Opens, Γ((TF (R := R) ℂ ⊗ D.P.A).left, U) → ℂ :=
    fun W U f => fderiv ℂ (fun z => valF (ptB ν d z) U f) 0 W
  have hDg : ∀ j, Dg (b j) (δW (W j)) := fun j => ⟨isT_of_tangent (hv j) (hb j), fun U f h0 => by
    rw [← hx0] at h0 ⊢
    exact hD j U f h0⟩
  obtain ⟨u, hu, rfl⟩ := hc
  have hbw' : bw = (List.ofFn fun i => mapP (Chart.scaleD (fC R (c i))) ≫ b i).prod := by
    have e : bw = dm R ≫ (List.ofFn u).prod := Over.OverMorphism.ext hbw
    rw [e, comp_prod]
    exact congrArg (fun F : Fin n → (TE R ℂ ⟶ D.P.A) => (List.ofFn F).prod) (funext fun i => dm_scale (c i) (hu i) (hb i))
  have key := dg_prod _ _ (fun i => dg_scale (fC R (c i)) (hDg i))
  rw [← hbw'] at key
  intro U f h0
  rw [hx0] at h0 ⊢
  refine (key.2 U f h0).trans ?_
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [δW, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
  rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieCombStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  intro R _ _ D _ N ν g d n c v w W b bw hv hw hb hbw hW
  exact GlobalTheory.isD_lieComb R D N ν g d n c v w W b bw hv hw hb hbw hW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatum
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MBLow.Cl

namespace GlobalTheory.MBLow.Cl

theorem exists_NF : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  intro g x hg
  subst hg
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, u, h₁, h₂, h₃, h₄, h₅, h₆⟩, -⟩ :=
    GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  exact ⟨u, τ, a, b, c, fun i => (2 * Real.pi * Complex.I : ℂ)⁻¹ • M i, h₁, h₂, hab.1, hab.2, hc, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  first | exact @GlobalTheory.MBLow.Cl.exists_NF | exact GlobalTheory.MBLow.Cl.exists_NF | (intros; apply GlobalTheory.MBLow.Cl.exists_NF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.KeyLieChg

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem lieComb_of_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left)
    (hu'v' : ∀ i, (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left) (i : Fin m) :
    IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i) := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).1 (hu'v' i)

theorem constFn_one {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    Geo.Tor.constFn p U (1 : R) = 1 := by
  simp [Geo.Tor.constFn]

theorem exists_keyPB_det : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  intro κ hκ R _ y x f hxy v' hv' M hM
  obtain ⟨φ, he, w, hg, F, hp, hw, hrig, hsec, hF, hε, hlie⟩ := hxy
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  subst hF'
  haveI := y.P.isAb.comm
  haveI := x.P.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R ℂ f y.P.A x.P.A φ hp y.P.isAb.smooth y.P.g v' hv'
  have hb : IsLieBasis (fun i : Fin x.P.g => u (i.cast hg)) := isLieBasis_cast hg hu
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, fun i => u (i.cast hg), hb⟩,
    ⟨φ, he, w, hg, Chart.dualMapR f, hp, hw, hrig, hsec, hF, hε, fun i => huv (i.cast hg)⟩, ?_⟩
  have hc := lieComb_of_over f hp hg M y.v v' x.v (fun i => u (i.cast hg)) hM hlie (fun i => huv (i.cast hg))
  have k := hκ ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne (fun i => u (i.cast hg)) hb 1
    (fun i j => f (M (i.cast hg) (j.cast hg))) (fun i => by rw [constFn_one, _root_.one_mul]) hc
  have hd : (Matrix.of fun i j : Fin x.P.g => f (M (i.cast hg) (j.cast hg))).det = (M.map f).det :=
    Matrix.det_submatrix_equiv_self (finCongr hg) (M.map f)
  simp only [Nat.mul_one, one_pow, _root_.one_mul] at k
  rw [k]
  exact congrArg (· ^ 4 * (κ ℂ x : ℂ)) hd

end GlobalTheory.KeyLieChg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  first | exact @GlobalTheory.KeyLieChg.exists_keyPB_det | exact GlobalTheory.KeyLieChg.exists_keyPB_det | (intros; apply GlobalTheory.KeyLieChg.exists_keyPB_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.DegTheta

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (z : Γ(X, U)) :
    resG X h (resG X h' z) = resG X (h.trans h') z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (z : Γ(X, U)) : resG X h z = z := by
  change (X.presheaf.map (homOfLE h).op).hom z = z
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

theorem basicOpen_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (z : Γ(X, U)) :
    X.basicOpen (resG X h z) = V ⊓ X.basicOpen z :=
  Scheme.basicOpen_res X z (homOfLE h).op

def secOfSecOn {X : Scheme.{0}} {L : LB X} {V : X.Opens} (hV : ∀ x : X, x ∈ V) (θ : ∀ i, Γ(X, V ⊓ L.U i))
    (hθ : θ ∈ secOn L V) : L.Sec where
  f i := resG X (le_inf (fun x _ => hV x) le_rfl) (θ i)
  compat i j := by
    have e := congrArg (resG X (le_inf (le_inf (fun x _ => hV x) inf_le_left) inf_le_right : L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
    simp only [map_mul, resG_resG] at e
    change resG X _ (resG X _ (θ i)) = _ * resG X _ (resG X _ (θ j))
    rw [resG_resG, resG_resG, e, resG_self]

end GlobalTheory.DegTheta

namespace GlobalTheory.DegTheta

theorem exists_sec_nonvanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), ∃ th : D.P.L.Sec, (∀ s : Sp R, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i) := by
  intro R _ _ _ _ D F _ _ N ν
  obtain ⟨V, θ, hxV, hθ, H⟩ := GlobalTheory.SecFamily.exists_secOn_nonvanishing GlobalTheory.abelianSchemeLaws_all.1 (Sp R) D.P
    (IsLocalRing.closedPoint R)
  have hVtop : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hxV
  have hV : ∀ a : D.P.A.left, a ∈ D.P.A.hom ⁻¹ᵁ V := fun a => by rw [hVtop]; trivial
  let θ' : D.P.L.Sec := secOfSecOn hV θ hθ
  obtain ⟨r, hr⟩ := ν.th_gen (DVR.toH0 θ')
  refine ⟨DVR.secOfH0 ν.th, fun s => ?_, fun i h => ?_⟩
  · obtain ⟨a, i, has, ha⟩ := H s (by rw [hVtop]; trivial)
    refine ⟨a, has, ?_⟩
    have haU : a ∈ D.P.L.U i := (D.P.A.left.basicOpen_le (θ i) ha).2
    have e := hr (fun _ => i)
    have h1 : a ∈ D.P.A.left.basicOpen ((DVR.toH0 θ').f (fun _ => i)) := by
      have eq1 : (DVR.toH0 θ').f (fun _ => i) = resG _ ((DVR.h0_le (fun _ => i)).trans
          (le_inf (fun x _ => hV x) le_rfl)) (θ i) := resG_resG _ _ _
      rw [eq1]
      exact (basicOpen_resG _ (θ i)).ge ⟨DVR.chart_le_weighted_chart_single i haU, ha⟩
    rw [e, Scheme.basicOpen_mul] at h1
    have h2 : a ∈ D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f i) := by
      have eq2 : (DVR.secOfH0 ν.th).f i = resG _ (DVR.chart_le_weighted_chart_single i) (ν.th.f (fun _ => i)) := rfl
      rw [eq2]
      exact (basicOpen_resG (DVR.chart_le_weighted_chart_single i) _).ge ⟨haU, h1.2⟩
    exact (le_iSup (fun k => D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f k)) i) h2
  · exact ((resG_resG h (DVR.chart_le_weighted_chart_single i) _).trans (resG_self _ _)).symm

end GlobalTheory.DegTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationThetaSection_nonvanishingFibres : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), ∃ th : D.P.L.Sec, (∀ s : Sp R, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i) := by
  first | exact @GlobalTheory.DegTheta.exists_sec_nonvanishing | exact GlobalTheory.DegTheta.exists_sec_nonvanishing | (intros; apply GlobalTheory.DegTheta.exists_sec_nonvanishing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.AbCl

theorem exists_te {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] (v : epsR R ⟶ D.P.A) :
    ∃ bb : TE R ℂ ⟶ D.P.A, bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left := by
  refine ⟨Over.homMk (spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left) ?_, rfl⟩
  rw [Category.assoc, Over.w v]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isD_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {ν : NumOf D ℂ N} {g : ℕ} {d : AB N.toNumB g} {b₀ b : TE R ℂ ⟶ D.P.A} {W₀ W₁ W₂ : Fin g → ℂ}
    (h₀ : ∀ W', IsD ν d W' b₀ ↔ W' = W₀) (h₁ : IsD ν d W₁ b) (h₂ : IsD ν d W₂ b) : W₁ = W₂ := by
  have key : IsD ν d (W₀ + (W₁ - W₂)) b₀ := by
    intro U f hU
    rw [(h₀ W₀).2 rfl U f hU]
    have e := congrArg TrivSqZeroExt.snd ((h₁ U f hU).symm.trans (h₂ U f hU))
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e
    rw [map_add (f := _), map_sub, e, sub_self, add_zero]
  have := (h₀ _).1 key
  have h3 : W₁ - W₂ = 0 := by simpa using this
  exact sub_eq_zero.1 h3

theorem exists_ab_keyOK : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ hκ R _ _ _ _ D hψ hτ _ N ν hg
  obtain ⟨th, hth, hcomp⟩ := GlobalTheory.T.exists_degenerationThetaSection_nonvanishingFibres R D ℂ N ν
  obtain ⟨vB₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.P.A D.P.smoothDim
  let y₀ : KeyIn R := ⟨D.P, hg, D.rig, D.rig_gen, th, hth, vB₀, hv₀⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB y₀ ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))
  have hg₀ : x₀.P.g = D.P.g := by obtain ⟨_, _, _, hgg, _⟩ := hx₀; exact hgg
  obtain ⟨u, τ, a, b, c, W, hNF⟩ := GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum D.P.g x₀ hg₀
  obtain ⟨d, G, hdc, huniq⟩ := GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm R D hψ hτ N ν y₀ rfl HEq.rfl ⟨th, HEq.rfl, hcomp⟩ x₀ hg₀ rfl u τ a b c W hx₀ hNF
  refine ⟨d, G, ?_⟩
  intro vB bs MB k₀ hv hbs hIsD hBK
  have hM : ∀ i, ∃ c : Fin D.P.g → R, IsLieComb c vB₀ (vB i) := fun i => (hv₀.2 (vB i) (hv.1 i)).exists
  choose M' hMc using hM
  let M : Matrix (Fin D.P.g) (Fin D.P.g) R := Matrix.of M'
  obtain ⟨x, hKx, hκx⟩ := GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow κ hκ.1 R y₀ x₀ _ hx₀ vB hv M hMc
  have hk : (κ ℂ x : ℂ) = k₀ := hBK.2 hg D.rig_gen th hth hv x hcomp hKx
  choose b₀ hb₀ using fun j => exists_te (D := D) (vB₀ j)
  have hW : ∀ j, ∀ W', IsD ν d W' (b₀ j) ↔ W' = W j := fun j => huniq vB₀ (fun i => HEq.rfl) j (b₀ j) (hb₀ j)
  have hlin : ∀ i, IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j) (bs i) :=
    fun i => GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb R D N ν D.P.g d D.P.g (M i) vB₀ (vB i) W b₀ (bs i) hv₀.1 (hMc i) hb₀ (hbs i) (fun j => (hW j _).2 rfl)
  have hrow : ∀ i, (2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i =
      ∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j :=
    fun i => isD_unique (hW ⟨0, hg⟩) (hIsD i) (hlin i)
  have h2π : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Mx : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := Matrix.of fun j k => (2 * Real.pi * Complex.I : ℂ) * W j k
  have hNF' : NF x₀ hg₀ u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
    have e : (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) = W := by
      funext j k
      show (2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * W j k) = W j k
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h2π, _root_.one_mul]
    rw [e]; exact hNF
  obtain ⟨hdet, hval⟩ := GlobalTheory.T.thetaKeyRule_value_classicalNormalForm κ hκ.1 hκ.2.2.1 D.P.g x₀ hg₀ u τ a b c Mx hNF'
  have hMB : MB = (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) * Mx := by
    ext i k
    have e := congrFun (hrow i) k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at e
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Mx, Matrix.of_apply, RingHom.comp_apply]
    calc MB i k = (2 * Real.pi * Complex.I : ℂ) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * MB i k) := by field_simp
      _ = _ := by rw [e, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp [M]; ring
  have hne : (κ ℂ x : ℂ) ≠ 0 := Units.ne_zero _
  rw [hMB, Matrix.det_mul]
  rw [hκx] at hk hne
  have hf : (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))).det ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  refine ⟨mul_ne_zero hf hdet, ?_⟩
  rw [← hk, hdc, _root_.mul_assoc, hval]
  ring

end GlobalTheory.MBLow.AbCl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalThetaDescription_abelianPart : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  first | exact @GlobalTheory.MBLow.AbCl.exists_ab_keyOK | exact GlobalTheory.MBLow.AbCl.exists_ab_keyOK | (intros; apply GlobalTheory.MBLow.AbCl.exists_ab_keyOK <;> assumption)
end
