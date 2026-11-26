module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThickeningGroupHomExtends
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SurjectiveLeftOfFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationThickeningCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernel
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

section Identity
variable {R : Type} [CommRing R]

def toIdMk (Y : Over (Spec (CommRingCat.of R))) : Y ⟶ Over.mk (Y.hom ≫ 𝟙 _) :=
  Over.homMk (𝟙 _) (by simp)

def ofIdMk (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ⟶ Y :=
  Over.homMk (𝟙 _) (by simp)

theorem ofIdMk_toIdMk (Y : Over (Spec (CommRingCat.of R))) : ofIdMk Y ≫ toIdMk Y = 𝟙 _ := by
  ext
  simp [ofIdMk, toIdMk]

end Identity

theorem exists_qfGroup_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  intro R _ _ _ _ B _ hB N hN A _ _ j _ hp hpt
  have := hB.smooth
  have := hB.separated
  have := hB.quasiCompact
  have := hB.comm
  have := GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have := GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have hm := mono_of_pullback hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := kernel_props hp
  have := kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)
  haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd A.hom (genPt R).hom)
  have hv : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ B) (y : Y ⟶ A),
      y.left ≫ j.left = g.left → y ≫ j = toIdMk Y ≫ g := fun {Y} g y h => by
    ext
    simpa [toIdMk] using h
  refine ⟨genPt R ⟶ A, inferInstance,
    { G := A, flat := h1, quasiFinite := h2, separated := h3, quasiCompact := h4, finPres := h5,
      pt := MonoidHom.id _, pt_inj := ?_, pt_onto := hpt, gen_reduced := hred }, Iso.refl _, ?_, ?_⟩
  · intro s t u v h
    exact Over.OverMorphism.ext (eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h)
  · show IsMonHom (𝟙 A)
    infer_instance
  · refine { isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }
    · show (𝟙 _ ≫ j.left) ≫ B.hom = A.hom ≫ 𝟙 _
      simpa using Over.w j
    · intro Y y z y₀ z₀ hy hz
      have hy' : y ≫ j = toIdMk Y ≫ y₀ := hv y₀ y (by rw [hy]; simp)
      have hz' : z ≫ j = toIdMk Y ≫ z₀ := hv z₀ z (by rw [hz]; simp)
      have e : (y * z) ≫ j = toIdMk Y ≫ (y₀ * z₀) := by
        rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
      have e' := congrArg (fun w => w.left) e
      simpa [toIdMk] using e'.symm
    · intro Y y z h
      rw [← cancel_mono j]
      ext
      simpa using h
    · intro Y g
      constructor
      · intro h
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by
          rw [← MonObj.comp_pow, h, MonObj.comp_one]
        obtain ⟨y, hy⟩ := lift_of_torsion hp _ h'
        refine ⟨y, ?_⟩
        have e := congrArg (fun w => w.left) hy
        simpa [toIdMk] using e
      · rintro ⟨y, hy⟩
        have e : y ≫ j = toIdMk Y ≫ g := hv g y (by rw [← hy]; simp)
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by rw [← e]; exact torsion_of_comp hp y
        have e2 : ofIdMk Y ≫ toIdMk Y ≫ g = g := by
          rw [← Category.assoc, ofIdMk_toIdMk, Category.id_comp]
        rw [← e2, ← MonObj.comp_pow, h', MonObj.comp_one]

end GlobalTheory.CompanionTheory.Ar.BT.Tors
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernelStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_torsion_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEq
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEq
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.EqRed
open GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem eq_zero_of_forall_mem_map (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (x : A)
    (h : ∀ e : ℕ, x ∈ (I ^ (e + 1)).map (algebraMap R A)) : x = 0 := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := A) I
    (by simpa only [Ideal.jacobson_bot] using hI)
  have hx : x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule R A)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have h1 : x ∈ (I ^ (i + 1) • (⊤ : Submodule R A)) := by
      rw [Ideal.smul_top_eq_map]
      exact h i
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h1
  rw [key] at hx
  simpa using hx

theorem eq_of_reductions (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) : f = g := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom

  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  have : Module.Finite R Γ(X.left, ⊤) := hfin'

  let u : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom
  let v : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ g.left ≫ Y.left.isoSpec.hom
  have hu : Spec.map (Spec.preimage u) = u := Spec.map_preimage _
  have hv : Spec.map (Spec.preimage v) = v := Spec.map_preimage _

  have hred : ∀ e : ℕ, Spec.preimage u ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) = Spec.preimage v ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) := by
    intro e
    let J := (I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤))
    let m : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec Γ(X.left, ⊤) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let q : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap R Γ(X.left, ⊤)) Ideal.le_comap_map))
    have hcond : (m ≫ X.left.isoSpec.inv) ≫ X.hom = q ≫ thick R I e := by
      rw [Category.assoc, ← hψ]
      simp only [m, q, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
    let t : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ (thickObj R I e X).left :=
      pullback.lift (m ≫ X.left.isoSpec.inv) q hcond
    have ht : t ≫ thickι I e X = m ≫ X.left.isoSpec.inv := pullback.lift_fst _ _ _
    have hfg : thickι I e X ≫ f.left = thickι I e X ≫ g.left := by
      have hl : thickHom I e f = thickHom I e g := congrArg (fun φ => φ.left) (h e)
      rw [← thickHom_ι, ← thickHom_ι, hl]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hu, hv]
    change m ≫ u = m ≫ v
    simp only [u, v]
    rw [← Category.assoc m, ← Category.assoc m, ← ht, Category.assoc t, Category.assoc t,
      reassoc_of% hfg]
  have hpre : Spec.preimage u = Spec.preimage v := by
    ext b
    refine sub_eq_zero.1 (eq_zero_of_forall_mem_map I Γ(X.left, ⊤) _ fun e => ?_)
    exact Ideal.Quotient.eq.1 (congrArg (fun φ => φ.hom b) (hred e))
  have huv : u = v := by rw [← hu, ← hv, hpre]
  apply Over.OverMorphism.ext
  have h1 : f.left ≫ Y.left.isoSpec.hom = g.left ≫ Y.left.isoSpec.hom := (cancel_epi X.left.isoSpec.inv).1 huv
  exact (cancel_mono Y.left.isoSpec.hom).1 h1

end GlobalTheory.CompanionTheory.Ar.BT.EqRed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEqStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_map_eq_of_thickenings_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y), (∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | exact GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsion
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsion
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext

section General
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def pre {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) : (Y ⟶ A) →* (Y' ⟶ A) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

def post {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] : (Y ⟶ A) →* (Y ⟶ A') where
  toFun x := x ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

theorem pre_pow {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) (n : ℕ) : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n :=
  map_pow (pre ρ) x n

theorem post_pow {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n :=
  map_pow (post φ) x n

theorem post_inv {Y A A' : C} [GrpObj A] [GrpObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) :
    x⁻¹ ≫ φ = (x ≫ φ)⁻¹ :=
  map_inv (post φ) x

theorem pre_inv {Y Y' A : C} [GrpObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  map_inv (pre ρ) x

theorem isPullback_of_lift {Z P G B : C} {f : Z ⟶ P} {g : Z ⟶ G} {h : P ⟶ B} {k : G ⟶ B}
    (w : f ≫ h = g ≫ k) (hm : ∀ {Y : C} {a b : Y ⟶ Z}, a ≫ f = b ≫ f → a ≫ g = b ≫ g → a = b)
    (hl : ∀ {Y : C} (x : Y ⟶ P) (y : Y ⟶ G), x ≫ h = y ≫ k → ∃ l : Y ⟶ Z, l ≫ f = x ∧ l ≫ g = y) :
    IsPullback f g h k :=
  ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst s.snd s.condition).choose)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.2)
    (fun s m h1 h2 => hm (h1.trans (hl s.fst s.snd s.condition).choose_spec.1.symm)
      (h2.trans (hl s.fst s.snd s.condition).choose_spec.2.symm))⟩⟩

end General

theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; rfl

section Main
variable {S : Scheme.{0}} {T Gt B : Over S} [GrpObj T] [IsCommMonObj T] [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B]
  [IsCommMonObj B] {u : T ⟶ Gt} {q : Gt ⟶ B} [IsMonHom u] [IsMonHom q] {N : ℕ}
  {TN GN BN : Over S} {jT : TN ⟶ T} {jG : GN ⟶ Gt} {jB : BN ⟶ B} {eB : 𝟙_ _ ⟶ BN}

theorem mono_of_ext (hu : IsPullback u (toUnit _) q η[B]) : Mono u :=
  ⟨fun _ _ h => hu.hom_ext h (toUnit_unique _ _)⟩

theorem lift_of_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (y : Y ⟶ Gt) (hy : y ≫ q = 1) :
    ∃ z : Y ⟶ T, z ≫ u = y :=
  ⟨hu.lift y (toUnit Y) (by rw [hy, Hom.one_def]), hu.lift_fst _ _ _⟩

theorem comp_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (z : Y ⟶ T) : (z ≫ u) ≫ q = 1 := by
  rw [Category.assoc, hu.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit T) (toUnit Y)]

theorem isPullback_kernel (hu : IsPullback u (toUnit _) q η[B])
    (hT : IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[T]) (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt])
    (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B]) (he : eB ≫ jB = η[B])
    {a : TN ⟶ GN} {b : GN ⟶ BN} (ha : a ≫ jG = jT ≫ u) (hb : b ≫ jB = jG ≫ q) :
    IsPullback a (toUnit TN) b eB := by
  have := mono_of_ext hu
  have := mono_of_pullback hT
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift S ?_ (fun {Y} x y h => ?_) (fun {Y} t ht => ?_)
  · rw [← cancel_mono jB, Category.assoc, hb, reassoc_of% ha, Category.assoc, he]
    have := comp_ext hu jT
    rw [Category.assoc] at this
    rw [this, Hom.one_def]
  · rw [← cancel_mono jG, Category.assoc, Category.assoc, ha] at h
    rw [← cancel_mono (jT ≫ u)]
    simpa using h
  · have h1 : (t ≫ jG) ≫ q = 1 := by
      have : t ≫ b ≫ jB = t ≫ jG ≫ q := by rw [hb]
      rw [Category.assoc, ← this, ← Category.assoc, ht, Category.assoc, he, Hom.one_def]
    obtain ⟨v, hv⟩ := lift_of_ext hu _ h1
    have h2 : v ^ N = 1 := by
      rw [← cancel_mono u, post_pow, hv, torsion_of_comp hG, MonObj.one_comp]
    obtain ⟨w, hw⟩ := lift_of_torsion hT v h2
    refine ⟨w, ?_⟩
    rw [← cancel_mono jG, Category.assoc, ha, reassoc_of% hw, hv]

theorem exists_isPullback_cover (hu : IsPullback u (toUnit _) q η[B])
    (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt]) (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B])
    {b : GN ⟶ BN} (hb : b ≫ jB = jG ≫ q) {P : Over S} {pG : P ⟶ Gt} {pB : P ⟶ BN} (hP : pG ≫ q = pB ≫ jB) :
    ∃ (φ : P ⟶ T) (c : pullback φ ((𝟙 T) ^ N) ⟶ GN), IsPullback (pullback.fst _ _) c pB b := by
  have := mono_of_ext hu
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  have h0 : (pG ^ N)⁻¹ ≫ q = 1 := by
    rw [post_inv, post_pow, hP, torsion_of_comp hB, inv_one]
  obtain ⟨φ, hφ⟩ := lift_of_ext hu _ h0
  have key : ∀ {Y : Over S} (y : Y ⟶ P), (y ≫ φ) ≫ u = ((y ≫ pG) ^ N)⁻¹ := fun y => by
    rw [Category.assoc, hφ, pre_inv, pre_pow]
  have hz : ∀ {Y : Over S} (z : Y ⟶ T), z ≫ ((𝟙 T) ^ N) = z ^ N := fun z => by
    rw [pre_pow, Category.comp_id]
  have tor : ((pullback.snd φ ((𝟙 T) ^ N) ≫ u) * (pullback.fst φ ((𝟙 T) ^ N) ≫ pG)) ^ N = 1 := by
    rw [mul_pow, ← post_pow u, ← hz (pullback.snd φ ((𝟙 T) ^ N)), ← pullback.condition, key, inv_mul_cancel]
  obtain ⟨c, hc⟩ := lift_of_torsion hG _ tor
  refine ⟨φ, c, isPullback_of_lift ?_ (fun {Y} a a' h1 h2 => ?_) (fun {Y} x k hxk => ?_)⟩
  · rw [← cancel_mono jB, Category.assoc, Category.assoc, hb, ← hP, reassoc_of% hc, MonObj.mul_comp,
      comp_ext hu, _root_.one_mul, Category.assoc]
  · refine pullback.hom_ext h1 ?_
    have h3 : a ≫ c ≫ jG = a' ≫ c ≫ jG := by rw [reassoc_of% h2]
    rw [hc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc a (pullback.fst _ _) pG,
      ← Category.assoc a' (pullback.fst _ _) pG, h1, mul_left_inj] at h3
    rw [← cancel_mono u, Category.assoc, Category.assoc]
    exact h3
  · have e : (k ≫ jG) ≫ q = (x ≫ pG) ≫ q := by
      rw [Category.assoc, Category.assoc, ← hb, hP, reassoc_of% hxk]
    have hw : ((k ≫ jG) * (x ≫ pG)⁻¹) ≫ q = 1 := by
      rw [MonObj.mul_comp, post_inv, e, mul_inv_cancel]
    obtain ⟨s, hs⟩ := lift_of_ext hu _ hw
    have hsN : x ≫ φ = s ≫ ((𝟙 T) ^ N) := by
      rw [← cancel_mono u, key x, hz, post_pow, hs, mul_pow, torsion_of_comp hG, _root_.one_mul, inv_pow]
    refine ⟨pullback.lift x s hsN, pullback.lift_fst _ _ _, ?_⟩
    rw [← cancel_mono jG, Category.assoc, hc, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      pullback.lift_fst, pullback.lift_snd, hs, inv_mul_cancel_right]

end Main

theorem torsion_exact : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  intro S X _ _ _ Gt B _ _ _ _ u q _ _ hfl hsu hqc hu N hN TN GN BN jT jG jB eB hT hG hB he a b ha hb
  have hN' : N ≠ 0 := by omega
  have hP := IsPullback.of_hasPullback q jB
  obtain ⟨φ, c, sq⟩ := exists_isPullback_cover hu hG hB hb hP.w
  have sql : IsPullback (pullback.fst φ ((𝟙 _) ^ N)).left c.left (pullback.snd q jB).left b.left :=
    sq.map (Over.forget S)
  have hPl : IsPullback (pullback.fst q jB).left (pullback.snd q jB).left q.left jB.left :=
    hP.map (Over.forget S)
  have hZl : IsPullback (pullback.snd φ ((𝟙 _) ^ N)).left (pullback.fst φ ((𝟙 _) ^ N)).left
      ((𝟙 (splitTorus S X)) ^ N).left φ.left :=
    (IsPullback.of_hasPullback φ ((𝟙 _) ^ N)).flip.map (Over.forget S)
  have f1 : Flat ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.flat_mulN S X hN'
  have s1 : Surjective ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.surjective_mulN S X hN'
  have f2 : Flat (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl f1
  have s2 : Surjective (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl s1
  have f3 : Flat (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hfl
  have s3 : Surjective (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hsu
  have c3 : QuasiCompact (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hqc
  refine ⟨?_, ?_, isPullback_kernel hu hT hG hB he ha hb⟩
  · haveI := GlobalTheory.flat_descendsAlong_fpqc
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sql ⟨⟨s3, f3⟩, c3⟩ f2
  · have : Surjective (c.left ≫ b.left) := by
      rw [← sql.w]; infer_instance
    exact Surjective.of_comp c.left b.left

end GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsionStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_extension_torsion : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext.torsion_exact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupOpenImmersionLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupOpenImmersionLift
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinPart

theorem thick_apply (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ)
    (q : Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)))) :
    thick R (IsLocalRing.maximalIdeal R) e q = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal =
    IsLocalRing.maximalIdeal R
  have hp : (Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal).IsPrime :=
    q.isPrime.comap _
  have hle : IsLocalRing.maximalIdeal R ≤
      Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) q.asIdeal := by
    intro a ha
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) (a ^ (e + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow ha _)
    have h1 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)) a) ^ (e + 1) ∈ q.asIdeal := by
      rw [← map_pow, h0]
      exact zero_mem _
    exact q.isPrime.mem_of_pow_mem _ h1
  exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.ne_top hle).symm

section Points
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}

def unitIso (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ≅ Y :=
  Over.isoMk (Iso.refl _) (by simp)

theorem mul_left_eq (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (y z : Y ⟶ Γ.G) (a b : Y ⟶ G) (ha : a.left = y.left ≫ i) (hb : b.left = z.left ≫ i) :
    (a * b).left = (y * z).left ≫ i := by
  have h := ht.mul Y y z ((unitIso Y).hom ≫ a) ((unitIso Y).hom ≫ b)
    (by simpa [unitIso] using ha) (by simpa [unitIso] using hb)
  rw [← MonObj.comp_mul] at h
  simpa [unitIso] using h

theorem pow_eq_one_iff (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (g : Y ⟶ G) : g ^ N = 1 ↔ ∃ y : Y ⟶ Γ.G, y.left ≫ i = g.left := by
  have h := ht.kernel Y ((unitIso Y).hom ≫ g)
  have e : ((unitIso Y).hom ≫ g) ^ N = (unitIso Y).hom ≫ g ^ N := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id]
  have e1 : (unitIso Y).hom ≫ g ^ N = 1 ↔ g ^ N = 1 := by
    constructor
    · intro h1
      have := congrArg (fun w => (unitIso Y).inv ≫ w) h1
      simpa [MonObj.comp_one] using this
    · intro h1
      rw [h1, MonObj.comp_one]
  rw [e, e1] at h
  rw [h]
  simp [unitIso]

end Points

section Pow
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

theorem comp_pow_id' {B Y : C} [MonObj B] (y : Y ⟶ B) (n : ℕ) : y ≫ (𝟙 B) ^ n = y ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end Pow

section Main
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {N : ℕ} {T : Type} [CommGroup T] {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left}
  {H : Type} [CommGroup H] {Γf : QFGroup R H} {u : Γf.G ⟶ Γ.G} [IsMonHom u]

def finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) (u : Γf.G ⟶ Γ.G) : Γf.G ⟶ G :=
  Over.homMk (u.left ≫ i) (by
    have h := ht.isOver
    have hu := Over.w u
    simp only [Category.comp_id] at h
    simp [h, hu])

theorem finMap_left (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : (finMap ht u).left = u.left ≫ i := rfl

theorem comp_finMap_mul (ht : Γ.IsTorsionAlong G (𝟙 _) N i) {Y : Over (Spec (CommRingCat.of R))}
    (a b : Y ⟶ Γf.G) : (a * b) ≫ finMap ht u = (a ≫ finMap ht u) * (b ≫ finMap ht u) := by
  ext1
  have h := mul_left_eq ht (a ≫ u) (b ≫ u) (a ≫ finMap ht u) (b ≫ finMap ht u)
    (by simp [finMap_left]) (by simp [finMap_left])
  rw [h, ← MonObj.mul_comp]
  simp [finMap_left]

instance isMonHom_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : IsMonHom (finMap ht u) := by
  have hone : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) ≫ finMap ht u = 1 := by
    have h := comp_finMap_mul (u := u) ht (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γf.G) 1
    rw [_root_.mul_one] at h
    exact left_eq_mul.1 h
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h := comp_finMap_mul (u := u) ht (fst Γf.G Γf.G) (snd Γf.G Γf.G)
    rw [Hom.mul_def, Hom.mul_def] at h
    simpa using h

theorem mono_finMap (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsOpenImmersion u.left] : Mono (finMap ht u) := by
  have hu : Mono u := by
    constructor
    intro Z a b h
    ext1
    rw [← cancel_mono u.left]
    simpa using congrArg (fun w => w.left) h
  constructor
  intro Z a b h
  rw [← cancel_mono u]
  apply ht.inj
  simpa [finMap_left] using congrArg (fun w => w.left) h

theorem finMap_pow (ht : Γ.IsTorsionAlong G (𝟙 _) N i) : finMap ht u ^ N = 1 :=
  (pow_eq_one_iff ht _).2 ⟨u, rfl⟩

theorem isPullback_thick (ht : Γ.IsTorsionAlong G (𝟙 _) N i) [IsLocalRing R] [IsOpenImmersion u.left]
    (hcl : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) (e : ℕ) :
    IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map (finMap ht u)) (toUnit _)
      ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N)
      η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  set x := thick R (IsLocalRing.maximalIdeal R) e with hx
  have := mono_finMap (u := u) ht
  have hF : (𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N = (Over.pullback x).map ((𝟙 G) ^ N) :=
    (GlobalTheory.CompanionTheory.Ar.BT.Tors.map_pow_id (Over.pullback x) G N).symm
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift _ ?_ ?_ ?_
  · rw [hF, ← Functor.map_comp, GlobalTheory.CompanionTheory.Ar.BT.Tors.comp_pow_id, finMap_pow, Functor.map_one, ← Hom.one_def]
  · intro Z a b h
    exact (cancel_mono _).1 h
  · intro Z t h
    have htN : t ^ N = 1 := by
      rw [← Hom.one_def] at h
      rw [← comp_pow_id', h]
    let g := GlobalTheory.CompanionTheory.Ar.BT.Tors.ofPull x G t
    have hg : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g = t := GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_ofPull x G t
    have hgN : g ^ N = 1 := by
      apply (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_inj (x := x) (G := G))
      have h1 := map_pow (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z) g N
      have h2 : GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z g = GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x G g := rfl
      have h3 := map_one (GlobalTheory.CompanionTheory.Ar.BT.Tors.toPullHom x G Z)
      exact h1.trans ((by rw [h2, hg, htN]; exact h3.symm))
    obtain ⟨y, hy⟩ := (pow_eq_one_iff ht g).1 hgN
    have hrange : Set.range y.left ⊆ Set.range u.left := by
      rintro _ ⟨z, rfl⟩
      apply hcl
      rw [← Scheme.Hom.comp_apply, Over.w y]
      show x (Z.hom z) = _
      exact thick_apply R e _
    let l := IsOpenImmersion.lift u.left y.left hrange
    have hl : l ≫ u.left = y.left := IsOpenImmersion.lift_fac _ _ _
    let w : Over.mk (Z.hom ≫ x) ⟶ Γf.G := Over.homMk l (by
      have hu := Over.w u
      have hyw := Over.w y
      rw [← hu, ← Category.assoc, hl, hyw])
    refine ⟨GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull x Γf.G w, ?_⟩
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.hom_ext_pull
    have h1 : ((Over.pullback x).map (finMap ht u)).left ≫ pullback.fst G.hom x =
        pullback.fst _ x ≫ (finMap ht u).left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, h1, ← Category.assoc, GlobalTheory.CompanionTheory.Ar.BT.Tors.toPull_fst]
    show l ≫ u.left ≫ i = g.left
    rw [← Category.assoc, hl, hy]

end Main

theorem finite_part_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (N : ℕ) (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ v : Γf.G ⟶ G, v.left = u.left ≫ i ∧ IsMonHom v ∧ Mono v ∧ ∀ e, IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v) (toUnit _) ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N) η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  intro R _ _ _ G _ _ N T _ Γ i ht H _ Γf u _ hu hcl
  have := hu
  exact ⟨finMap ht u, rfl, inferInstance, mono_finMap ht, isPullback_thick ht hcl⟩

end GlobalTheory.CompanionTheory.Ar.BT.FinPart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupOpenImmersionLiftStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_open_immersion_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (N : ℕ) (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ v : Γf.G ⟶ G, v.left = u.left ≫ i ∧ IsMonHom v ∧ Mono v ∧ ∀ e, IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v) (toUnit _) ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N) η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroup
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.BT.RatKer

theorem exists_section_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  intro R _ _ H _ Γf A E a b e ha hP g hg
  have hwa : Γf.G.hom (a.left g) = A.hom g := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨t, x, hx⟩ := Γf.11 (a.left g) (by rw [hwa]; exact hg)
  have hgen : (GlobalTheory.CompanionTheory.Ar.BT.genPt R).hom x = A.hom g := by
    rw [← Over.w (Γf.9 t), Scheme.Hom.comp_apply, hx, hwa]
  have hab := congrArg (fun φ => φ.left g) hP.w
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at hab
  have hpt : Γf.9 t ≫ b = toUnit (GlobalTheory.CompanionTheory.Ar.BT.genPt R) ≫ e := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.eq_of_same_point E.hom _ _ (Over.w _) (Over.w _) x x
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left]
    rw [hx, hab, hgen]
  refine ⟨hP.lift (Γf.9 t) (toUnit _) hpt, x, ?_⟩
  apply a.left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hP.lift_fst, hx]

end GlobalTheory.CompanionTheory.Ar.BT.RatKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroupStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_closed_subgroup : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | exact GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Stight.D1

section Unit
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

theorem kernel_map [PreservesLimitsOfShape WalkingCospan F] {A B : C} [GrpObj B] {N : ℕ} {j : A ⟶ B}
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback (F.map j) (toUnit (F.obj A)) ((𝟙 (F.obj B)) ^ N) η[F.obj B] := by
  have h := hp.map F
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso F).symm (Iso.refl _)
    (by simp) (toUnit_unique _ _) ?_ ?_
  · simp [Tors.map_pow_id]
  · simp [Functor.obj.η_def]

theorem isPullback_map_unit {A E B : C} {a : A ⟶ E} {b : E ⟶ B} {e : 𝟙_ C ⟶ B}
    (h : IsPullback (F.map a) (toUnit (F.obj A)) (F.map b) (Functor.LaxMonoidal.ε F ≫ F.map e)) :
    IsPullback (F.map a) (F.map (toUnit A)) (F.map b) (F.map e) := by
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso F) (Iso.refl _)
    (by simp) (by rw [← cancel_mono (Functor.Monoidal.εIso F).inv]; exact toUnit_unique _ _) (by simp) (by simp)

end Unit

section Iso
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem kernel_iso {A B B' : C} [GrpObj B] [GrpObj B'] {N : ℕ} {j : A ⟶ B} (β : B ≅ B') [IsMonHom β.hom]
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback (j ≫ β.hom) (toUnit A) ((𝟙 B') ^ N) η[B'] := by
  refine IsPullback.of_iso hp (Iso.refl _) β (Iso.refl _) β (by simp) (by simp) ?_ (by simp)
  rw [MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem factor_of_kernel [BraidedCategory C] {P P' Q Q' : C} [GrpObj P'] [IsCommMonObj P'] [GrpObj Q'] [IsCommMonObj Q']
    {N : ℕ} {jP : P ⟶ P'} {jQ : Q ⟶ Q'}
    (hP : IsPullback jP (toUnit P) ((𝟙 P') ^ N) η[P']) (hQ : IsPullback jQ (toUnit Q) ((𝟙 Q') ^ N) η[Q'])
    (φ : P' ⟶ Q') [IsMonHom φ] : ∃ w : P ⟶ Q, w ≫ jQ = jP ≫ φ := by
  refine Tors.lift_of_torsion hQ _ ?_
  have h := Tors.torsion_of_comp hP (𝟙 _)
  rw [Category.id_comp] at h
  rw [← MonObj.pow_comp, h]
  simp

end Iso

theorem kernel_pull {S' S : Scheme.{0}} (x : S' ⟶ S) {A B : Over S} [GrpObj B] {N : ℕ} {j : A ⟶ B}
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback ((Over.pullback x).map j) (toUnit ((Over.pullback x).obj A))
      ((𝟙 ((Over.pullback x).obj B)) ^ N) η[(Over.pullback x).obj B] :=
  kernel_map (Over.pullback x) hp

theorem comp_left_of_map {S' S : Scheme.{0}} (x : S' ⟶ S) {P G B : Over S} (v : P ⟶ G) (c : P ⟶ B)
    (qq : (Over.pullback x).obj G ⟶ (Over.pullback x).obj B)
    (h : (Over.pullback x).map c = (Over.pullback x).map v ≫ qq) {Y : Scheme.{0}} (y : Y ⟶ P.left)
    (y' : Y ⟶ ((Over.pullback x).obj G).left) (hy : y' ≫ pullback.fst G.hom x = y ≫ v.left) :
    y ≫ c.left = y' ≫ qq.left ≫ pullback.fst B.hom x := by
  have hc : y ≫ P.hom = y' ≫ pullback.snd G.hom x ≫ x := by
    rw [← pullback.condition, ← Category.assoc, hy, Category.assoc, Over.w]
  let w : Y ⟶ ((Over.pullback x).obj P).left := pullback.lift y (y' ≫ pullback.snd G.hom x) (by simpa using hc)
  have hw1 : w ≫ pullback.fst P.hom x = y := pullback.lift_fst _ _ _
  have hw2 : w ≫ ((Over.pullback x).map v).left = y' := by
    refine pullback.hom_ext ?_ ?_
    · have h1 : ((Over.pullback x).map v).left ≫ pullback.fst G.hom x = pullback.fst P.hom x ≫ v.left :=
        pullback.lift_fst _ _ _
      rw [Category.assoc, h1, ← Category.assoc, hw1, hy]
    · have h2 : ((Over.pullback x).map v).left ≫ pullback.snd G.hom x = pullback.snd P.hom x :=
        pullback.lift_snd _ _ _
      rw [Category.assoc, h2]
      exact pullback.lift_snd _ _ _
  have h3 : ((Over.pullback x).map c).left ≫ pullback.fst B.hom x = pullback.fst P.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  calc y ≫ c.left = w ≫ pullback.fst P.hom x ≫ c.left := by rw [← Category.assoc, hw1]
    _ = w ≫ ((Over.pullback x).map c).left ≫ pullback.fst B.hom x := by rw [h3]
    _ = y' ≫ qq.left ≫ pullback.fst B.hom x := by
      rw [h, Over.comp_left, Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, hw2,
        Category.assoc]

theorem mulN_eq_pow {S : Scheme.{0}} (P : Over S) [GrpObj P] (n : ℕ) : mulN P n = (𝟙 P) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih, mulN, Hom.mul_def]

theorem finiteMulTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ), 1 ≤ N → IsFinite ((𝟙 (splitTorus S X)) ^ N).left := by
  intro S X _ _ _ N hN
  rw [← mulN_eq_pow]
  exact GlobalTheory.Diag.isFinite_mulN S X (by omega)

theorem kernelOf : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Over S) [GrpObj P], IsSemiAbelian P → ∀ N : ℕ, 1 ≤ N → IsFinite ((𝟙 P) ^ N).left → ∃ (A : Over S) (_ : GrpObj A) (_ : IsCommMonObj A) (j : A ⟶ P), IsMonHom j ∧ IsPullback j (toUnit A) ((𝟙 P) ^ N) η[P] ∧ IsFinite A.hom ∧ Flat A.hom := by
  intro S _ P _ hP N hN hfin
  have := hP.comm
  have := hP.smooth
  have := hP.separated
  have := hP.quasiCompact
  have := GlobalTheory.T.power_map_flat_semiabelian S P hP N hN
  have := GlobalTheory.T.power_map_locally_quasi_finite S P hP N hN
  have hp : IsPullback (pullback.fst ((𝟙 P) ^ N) η[P]) (toUnit (pullback ((𝟙 P) ^ N) η[P])) ((𝟙 P) ^ N) η[P] := by
    have h := IsPullback.of_hasPullback ((𝟙 P) ^ N) η[P]
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  obtain ⟨g1, g2, g3⟩ := Tors.exists_kernel_grp hp
  obtain ⟨h1, -⟩ := Tors.kernel_props hp
  refine ⟨_, g1, g2, _, g3, hp, ?_, h1⟩
  have hl := hp.map (Over.forget S)
  have hA : (toUnit (pullback ((𝟙 P) ^ N) η[P])).left = (pullback ((𝟙 P) ^ N) η[P]).hom := by
    simpa using Over.w (toUnit (pullback ((𝟙 P) ^ N) η[P]))
  have hl' : IsPullback (pullback.fst ((𝟙 P) ^ N) η[P]).left (pullback ((𝟙 P) ^ N) η[P]).hom ((𝟙 P) ^ N).left (η[P]).left := by
    rw [← hA]; exact hl
  exact MorphismProperty.of_isPullback hl' hfin

theorem gt_q_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ), thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.toPre.P.A := by
  intro R _ _ I D A G _ _ U e
  refine pullback.hom_ext ?_ ?_
  · have h := U.gt_q e
    have h1 : thickMap R I e D.toPre.P.A ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
    simp only [Category.assoc]
    rw [h1]
    exact h
  · have w1 := Over.w (U.gt (e + 1)).q
    have w2 := Over.w (U.gt e).q
    have s1 : thickMap R I e D.toPre.P.A ≫ pullback.snd _ _ = pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    have s2 : thickMap R I e G ≫ pullback.snd _ _ = pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    simp only [Over.pullback_obj_hom] at w1 w2
    simp only [Category.assoc]
    rw [w1, s1, s2, ← Category.assoc, w2]

theorem finiteMulAbelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ N : ℕ, 1 ≤ N → IsFinite ((𝟙 B) ^ N).left := by
  intro S _ B _ hB N hN
  have := hB.proper
  have := GlobalTheory.T.power_map_locally_quasi_finite S B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hB) N hN
  have hw : ((𝟙 B) ^ N).left ≫ B.hom = B.hom := Over.w _
  have : IsProper ((𝟙 B) ^ N).left := by
    have h : IsProper (((𝟙 B) ^ N).left ≫ B.hom) := by rw [hw]; infer_instance
    exact IsProper.of_comp _ B.hom
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem finitePart_extension_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (G B : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : ∀ e, thickObj R (IsLocalRing.maximalIdeal R) e G ⟶ thickObj R (IsLocalRing.maximalIdeal R) e B) (ii : ∀ e, splitTorus (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)))) X ⟶ thickObj R (IsLocalRing.maximalIdeal R) e G), IsAbelianScheme B → (∀ e, IsMonHom (q e)) → (∀ e, IsMonHom (ii e)) → (∀ e, thickMap R (IsLocalRing.maximalIdeal R) e G ≫ (q (e + 1)).left = (q e).left ≫ thickMap R (IsLocalRing.maximalIdeal R) e B) → (∀ e, thickMap R (IsLocalRing.maximalIdeal R) e (splitTorus (Spec (CommRingCat.of R)) X) ≫ (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) (e + 1)) X).hom.left ≫ (ii (e + 1)).left = (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom.left ≫ (ii e).left ≫ thickMap R (IsLocalRing.maximalIdeal R) e G) → (∀ e, ii e ≫ q e = toUnit _ ≫ η[thickObj R (IsLocalRing.maximalIdeal R) e B]) → Flat (q 0).left → Surjective (q 0).left → QuasiCompact (q 0).left → IsPullback (ii 0) (toUnit _) (q 0) η[thickObj R (IsLocalRing.maximalIdeal R) 0 B] → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → IsFinite Γf.G.hom → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ (M C : Type) (_ : CommGroup M) (_ : CommGroup C) (ΓM : QFGroup R M) (ΓB : QFGroup R C) (iM : ΓM.G.left ⟶ (splitTorus (Spec (CommRingCat.of R)) X).left) (iB : ΓB.G.left ⟶ B.left) (a : ΓM.G ⟶ Γf.G) (b : Γf.G ⟶ ΓB.G), ΓM.IsTorsionAlong _ (𝟙 _) N iM ∧ ΓB.IsTorsionAlong B (𝟙 _) N iB ∧ IsMonHom a ∧ IsMonHom b ∧ IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit _) b η[ΓB.G] ∧ ∀ (e : ℕ) (Y : Scheme.{0}) (y : Y ⟶ Γf.G.left) (y' : Y ⟶ (thickObj R (IsLocalRing.maximalIdeal R) e G).left), y' ≫ (fstG (IsLocalRing.maximalIdeal R) e G).left = y ≫ u.left ≫ i → y ≫ b.left ≫ iB = y' ≫ (q e).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) e) := by
  intro R _ _ _ _ _ _ G B _ _ _ _ X _ _ _ q ii hBab qhom ihom hcq hci hiq hfl hsu hqc hk0 N hN T _ Γ i hi H _ Γf u _ hop hfin hcl
  have hBs : IsSemiAbelian B := GlobalTheory.isSemiAbelian_of_isAbelianScheme B hBab
  obtain ⟨AB, _, _, jB, _, hpB, finB, flatB⟩ := kernelOf (Spec (CommRingCat.of R)) B hBs N hN
    (finiteMulAbelian _ B hBab N hN)
  obtain ⟨AT, _, _, jT, _, hpT, finT, flatT⟩ := kernelOf (Spec (CommRingCat.of R)) (splitTorus (Spec (CommRingCat.of R)) X) inferInstance N hN
    (finiteMulTorus _ X N hN)
  obtain ⟨v, hvl, _, _, hker⟩ := GlobalTheory.T.torsion_group_open_immersion_lift R G N T Γ i hi H Γf u hop hcl
  have monoB : Mono jB := Tors.mono_of_pullback hpB
  have hfb : ∀ e, ∃ w : thickObj R (IsLocalRing.maximalIdeal R) e Γf.G ⟶ thickObj R (IsLocalRing.maximalIdeal R) e AB,
      w ≫ (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB = (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v ≫ q e := fun e => by
    have := qhom e
    have h1 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpB
    have h2 := hker e
    exact factor_of_kernel h2 h1 (q e)
  haveI := hfin
  obtain ⟨b, _, hb⟩ := GlobalTheory.T.thickening_group_hom_extends R (IsLocalRing.maximalIdeal R) Γf.G AB G B v jB q qhom hcq hfb
  have hfa : ∀ e, ∃ w : thickObj R (IsLocalRing.maximalIdeal R) e AT ⟶ thickObj R (IsLocalRing.maximalIdeal R) e Γf.G,
      w ≫ (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v = (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jT ≫
        ((GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom ≫ ii e) := fun e => by
    have := ihom e
    have h1 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpT
    have h2 := hker e
    exact factor_of_kernel h1 h2 _
  obtain ⟨a, _, ha⟩ := GlobalTheory.T.thickening_group_hom_extends R (IsLocalRing.maximalIdeal R) AT Γf.G (splitTorus (Spec (CommRingCat.of R)) X) G jT v
    (fun e => (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom ≫ ii e)
    (fun e => by have := ihom e; infer_instance)
    (fun e => by simpa [Over.comp_left] using hci e) hfa
  have hb0 := hb 0
  have ha0 := ha 0
  rw [Functor.map_comp] at hb0 ha0
  have hk1 := kernel_iso (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) 0) X) (kernel_pull (thick R (IsLocalRing.maximalIdeal R) 0) hpT)
  have hk2 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) 0) hpB
  have hk3 := hker 0
  have := qhom 0
  have := ihom 0
  obtain ⟨hf, hs, hpk⟩ := GlobalTheory.T.split_torus_extension_torsion _ X (thickObj R (IsLocalRing.maximalIdeal R) 0 G) (thickObj R (IsLocalRing.maximalIdeal R) 0 B) (ii 0) (q 0) hfl hsu hqc hk0 N hN _ _ _ _ _ _ η[(Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj AB] hk1 hk3 hk2 (IsMonHom.one_hom _) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) (by rw [ha0, Category.assoc]) hb0
  rw [Functor.obj.η_def AB] at hpk
  have flatG : Flat Γf.G.hom := Γf.flat
  have hab : a ≫ b = toUnit AT ≫ η[AB] := by
    refine GlobalTheory.T.finite_map_eq_of_thickenings_eq R (IsLocalRing.maximalIdeal R) AT AB _ _ (fun e => ?_)
    have hm : Mono ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB) :=
      Tors.mono_of_pullback (kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpB)
    rw [← cancel_mono ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB)]
    have e1 := ha e
    have e2 := hb e
    rw [Functor.map_comp] at e1 e2
    have e3 : η[thickObj R (IsLocalRing.maximalIdeal R) e B] =
        Functor.LaxMonoidal.ε (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)) ≫
          (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map η[B] := Functor.obj.η_def B
    rw [Functor.map_comp, Category.assoc, e2, ← Category.assoc, e1, Category.assoc, Category.assoc, hiq e, e3,
      ← Functor.map_comp, Category.assoc, IsMonHom.one_hom, Functor.map_comp]
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.Monoidal.εIso (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e))).inv]
    exact toUnit_unique _ _
  obtain ⟨hcl', hfb', hsb', hpb'⟩ := GlobalTheory.CompanionTheory.Ar.BT.FinFlat.exact_of_closedFibre R AT Γf.G AB a b η[AB] hab (isPullback_map_unit _ hpk) hf hs
  obtain ⟨C, _, ΓB, φB, _, htB⟩ := GlobalTheory.T.generic_points_of_torsion_kernel R B hBs N hN AB jB hpB (fun g hg => by
    obtain ⟨w, rfl⟩ := hsb'.surj g
    have hw : (Γf.G.hom w).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, Over.w b] at hg
      exact hg
    obtain ⟨t, x, hx⟩ := Γf.pt_onto w hw
    exact ⟨Γf.pt t ≫ b, x, by simp [hx]⟩)
  obtain ⟨M, _, ΓM, φM, _, htM⟩ := GlobalTheory.T.generic_points_of_torsion_kernel R _ inferInstance N hN AT jT hpT (GlobalTheory.T.generic_points_of_closed_subgroup R H Γf AT AB a b η[AB] hcl' hpb')
  have hinv : IsMonHom φB.inv := inferInstance
  have isoL : IsIso φB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map φB.inv))
  have isoM : IsIso φM.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φM.hom))
  refine ⟨M, C, _, _, ΓM, ΓB, φM.hom.left ≫ jT.left, φB.hom.left ≫ jB.left, φM.hom ≫ a, b ≫ φB.inv, htM, htB,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · refine IsPullback.of_iso hpb' φM.symm (Iso.refl _) (Iso.refl _) φB.symm (by simp) (toUnit_unique _ _) (by simp) ?_
    simp
  · intro e Y y y' h
    have hv : y' ≫ pullback.fst G.hom (thick R (IsLocalRing.maximalIdeal R) e) = y ≫ v.left := by
      rw [hvl]; exact h
    have key := comp_left_of_map (thick R (IsLocalRing.maximalIdeal R) e) v (b ≫ jB) (q e) (hb e) y y' hv
    rw [← key]
    simp [Over.comp_left]

theorem finitePart_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal R) D A G) (N : ℕ), 1 ≤ N → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] [Finite H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → IsFinite Γf.G.hom → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ (M C : Type) (_ : CommGroup M) (_ : CommGroup C) (ΓM : QFGroup R M) (ΓB : QFGroup R C) (iM : ΓM.G.left ⟶ (splitTorus (Spec (CommRingCat.of R)) D.toPre.X).left) (iB : ΓB.G.left ⟶ D.toPre.P.A.left) (a : ΓM.G ⟶ Γf.G) (b : Γf.G ⟶ ΓB.G), ΓM.IsTorsionAlong _ (𝟙 _) N iM ∧ ΓB.IsTorsionAlong D.toPre.P.A (𝟙 _) N iB ∧ IsMonHom a ∧ IsMonHom b ∧ IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit _) b η[ΓB.G] ∧ ∀ (e : ℕ) (Y : Scheme.{0}) (y : Y ⟶ Γf.G.left) (y' : Y ⟶ (thickObj R (IsLocalRing.maximalIdeal R) e G).left), y' ≫ (fstG (IsLocalRing.maximalIdeal R) e G).left = y ≫ u.left ≫ i → y ≫ b.left ≫ iB = y' ≫ (U.gt e).pG.left := by
  intro R _ _ _ _ _ _ D A G _ _ U N hN T _ _ Γ i hi H _ _ Γf u _ hop hfin hcl
  have hq0 : QuasiCompact (U.gt 0).q.left := by
    have := (U.gt 0).q_affine
    infer_instance
  exact finitePart_extension_core R G D.toPre.P.A D.toPre.X (fun e => (U.gt e).q) (fun e => (U.gt e).i) D.toPre.P.isAb
    (fun e => (U.gt e).q_hom) (fun e => (U.gt e).i_hom) (gt_q_compat R _ D A G U)
    (GlobalTheory.T.uniformization_thickening_compat R _ D A G U) (fun e => (U.gt e).isKernel.w) (U.gt 0).q_flat (U.gt 0).q_surj hq0 (U.gt 0).isKernel N hN T Γ i hi H Γf u hop hfin hcl

end PositivityTheory.HtPt.Stight.D1
