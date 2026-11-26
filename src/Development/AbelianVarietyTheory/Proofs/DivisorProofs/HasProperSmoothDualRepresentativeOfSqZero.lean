module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBases
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBases
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

def pairFun (φ : X' ⟶ X) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) : T ⥤ (Pair φ)ᵒᵖ where
  obj t := Opposite.op ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  map {t t'} a := (homOfLE (show (⟨((H.obj t').unop, (G.obj (K.obj t')).unop), le t'⟩ : Pair φ) ≤
      ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩ from
    ⟨leOfHom (H.map a).unop, leOfHom (G.map (K.map a)).unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def pairTo {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (G : D ⥤ AffOp X) (H : T ⥤ AffOp X')
    (K : T ⥤ D) (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R') (OPair φ s') (H ⋙ OAff s') where
  G := pairFun φ G H K le
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_pairRes (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s'))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairRes φ s')).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 H) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem pairTo_pairPull {φ : X' ⟶ X} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) (c : H2 (ext R₁ (OAff s))) :
    (extMap R₁ (pairTo φ s' G H K le)).pull2 ((extMap R₁ (pairPull w)).pull2 c) =
      (extMap R₁ (pullMap w G H K le)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s) G)).pull2 c) := by
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
  refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 (K ⋙ G)) (fun t b ↦ ?_) c
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end GlobalTheory.PrimBasis

namespace GlobalTheory.PrimBasis

variable {R : Type} [CommRing R] (R₁ : Type) [CommRing R₁] [Algebra R R₁]
variable {X X' : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

theorem pairTo_injective (φ : X' ⟶ X) (s' : X' ⟶ Sp R) (G : D ⥤ AffOp X) (H : T ⥤ AffOp X') (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1)
    (hr : Function.Surjective (extMap R₁ (pairRes φ s')).pull2)
    (hH : Function.Injective (extMap R₁ (CoefMap.restrict (OAff s') H)).pull2) :
    Function.Injective (extMap R₁ (pairTo φ s' G H K le)).pull2 := by
  intro x y e
  obtain ⟨x, rfl⟩ := hr x
  obtain ⟨y, rfl⟩ := hr y
  rw [pairTo_pairRes, pairTo_pairRes] at e
  rw [hH e]

end GlobalTheory.PrimBasis


open GlobalTheory.PrimBasis in
theorem GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  intro hP R R₁ _ _ _ q hq A _ g hA hg D T _ _ _ _ G H K₀ K₁ K₂ le₀ le₁ le₂ hGb hHb c hc
  have hG := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ A.left A.hom D G hGb.cover hGb.dir).2
  have hH := (GlobalTheory.Obs.BasisExt.restrict_ext_bijective R R₁ (A ⊗ A).left (A ⊗ A).hom T H hHb.cover hHb.dir).2
  have hr : ∀ φ : (A ⊗ A).left ⟶ A.left, Function.Bijective (extMap R₁ (pairRes φ (A ⊗ A).hom)).pull2 :=
    fun φ ↦ (GlobalTheory.T.cechPairRestrict_baseChange_bijective R R₁ A.left (A ⊗ A).left (A ⊗ A).hom φ).1.2
  obtain ⟨c', rfl⟩ := hG.2 c
  obtain ⟨c₁, hc₁⟩ := (hr (fst A A).left).2 ((extMap R₁ (pairPull (overW (fst A A)))).pull2 c')
  obtain ⟨c₂, hc₂⟩ := (hr (snd A A).left).2 ((extMap R₁ (pairPull (overW (snd A A)))).pull2 c')
  suffices h : c' = 0 by rw [h, map_zero]
  refine hP R R₁ q hq A g hA hg c' c₁ c₂ ?_ hc₁.symm hc₂.symm
  refine pairTo_injective R₁ _ _ G H K₀ le₀ (hr _).2 hH.1 ?_
  rw [pairTo_pairPull, pairTo_pairRes, map_add (f := _), hc, ← pairTo_pairPull R₁ (overW (fst A A)) G H K₁ le₁,
    ← pairTo_pairPull R₁ (overW (snd A A)) G H K₂ le₂, ← hc₁, ← hc₂, pairTo_pairRes, pairTo_pairRes]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBasesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  first | exact @GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | exact GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | (intros; apply GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoefficientExtensionH2Class
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoefficientExtensionH2Class
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimIdeal

variable {R : Type} [CommRing R] (I : Ideal R)

section Lin

variable (B : Type) [CommRing B] [Algebra R B]

def iota : I ⊗[R] B →ₗ[R] TrivSqZeroExt R I ⊗[R] B := (TrivSqZeroExt.inrHom R I).rTensor B

def tau : I ⊗[R] B →ₗ[R] B := TensorProduct.lid R B ∘ₗ I.subtype.rTensor B

def sig : TrivSqZeroExt R I ⊗[R] B →ₗ[R] B := tau I B ∘ₗ (TrivSqZeroExt.sndHom R I).rTensor B

theorem tau_tmul (i : I) (b : B) : tau I B (i ⊗ₜ b) = (i : R) • b := by
  simp [tau]

theorem sig_iota (y : I ⊗[R] B) : sig I B (iota I B y) = tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [sig, iota]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tau_mem (y : I ⊗[R] B) : tau I B y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b =>
    rw [tau_tmul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
  | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy

theorem sig_mem (x : TrivSqZeroExt R I ⊗[R] B) : sig I B x ∈ I.map (algebraMap R B) := tau_mem I B _

theorem tau_mulLeft (b : B) (y : I ⊗[R] B) : tau I B ((LinearMap.mulLeft R b).lTensor I y) = b • tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i c => simp [tau_tmul, Algebra.smul_def]; ring
  | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]

theorem exists_tau {x : B} (hx : x ∈ I.map (algebraMap R B)) : ∃ y, tau I B y = x := by
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨⟨i, hi⟩ ⊗ₜ 1, by simp [tau_tmul, Algebra.smul_def]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, rfl⟩ := hx; obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩
  | smul b x _ hx =>
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(LinearMap.mulLeft R b).lTensor I y, tau_mulLeft I B b y⟩

theorem tau_injective (hB : Module.Flat R B) : Function.Injective (tau I B) :=
  (TensorProduct.lid R B).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective)

variable {B} {B' : Type} [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')

theorem iota_nat (y : I ⊗[R] B) :
    extHom (TrivSqZeroExt R I) φ (iota I B y) = iota I B' (φ.toLinearMap.lTensor I y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [iota]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tau_nat (y : I ⊗[R] B) : tau I B' (φ.toLinearMap.lTensor I y) = φ (tau I B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [tau_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sig_nat (x : TrivSqZeroExt R I ⊗[R] B) :
    sig I B' (extHom (TrivSqZeroExt R I) φ x) = φ (sig I B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sig, tau_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Lin

end GlobalTheory.PrimIdeal

namespace GlobalTheory.PrimIdeal

theorem primI_of_ext : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁)
    (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧
    ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R)
      (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) →
      (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F),
        (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) →
      PrimI I n₀ n₁ n₂ := by
  intro R _ I
  refine ⟨TrivSqZeroExt R I, inferInstance, inferInstance, TrivSqZeroExt.fstHom R R I, ?_, ?_⟩
  · intro y y' hy hy'
    have h1 : y.fst = 0 := hy
    have h2 : y'.fst = 0 := hy'
    ext
    · simp [h1, h2]
    · simp [h1, h2]
  intro D T _ _ F F' n₀ n₁ n₂ hF hF' hc z f hz hf hrel
  choose y hy using fun (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t'') ↦ exists_tau I (F.obj t'') (hz t t' t'' a b)
  choose y' hy' using fun (t t' : T) (a : t ⟶ t') ↦ exists_tau I (F'.obj t') (hf t t' a)
  let zh : C2 (ext (TrivSqZeroExt R I) F) := fun t t' t'' a b ↦ iota I (F.obj t'') (y t t' t'' a b)
  have hzc : zh ∈ Z2 (ext (TrivSqZeroExt R I) F) := by
    intro t t' t'' t''' φ ψ χ
    have key : (mp F χ).toLinearMap.lTensor I (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ =
        y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ := by
      apply tau_injective I (F.obj t''') (hF t''')
      simp only [map_add (f := _), AlgHom.toLinearMap_apply, tau_nat, hy]
      exact z.2 φ ψ χ
    have := congrArg (iota I _) key
    simp only [map_add (f := _), ← iota_nat] at this
    exact this
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 (hc (H2.mk _ ⟨zh, hzc⟩) (by
    show H2.mk _ ((extMap _ n₀).pullbackTwoCocycle ⟨zh, hzc⟩) =
      H2.mk _ ((extMap _ n₁).pullbackTwoCocycle ⟨zh, hzc⟩) + H2.mk _ ((extMap _ n₂).pullbackTwoCocycle ⟨zh, hzc⟩)
    rw [← LinearMap.map_add (H2.mk _), H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ iota I (F'.obj t') (y' t t' a), ?_⟩
    funext t t' t'' a b
    simp only [d1_apply, Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply, CoefMap.pullCocycleTwo_apply]
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hrel t) t') t'') a) b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply] at e
    have key : (mp F' b).toLinearMap.lTensor I (y' _ _ a) - y' _ _ (a ≫ b) + y' _ _ b =
        (coefHom n₀ t'').toLinearMap.lTensor I (y _ _ _ (n₀.G.map a) (n₀.G.map b)) -
          ((coefHom n₁ t'').toLinearMap.lTensor I (y _ _ _ (n₁.G.map a) (n₁.G.map b)) +
            (coefHom n₂ t'').toLinearMap.lTensor I (y _ _ _ (n₂.G.map a) (n₂.G.map b))) := by
      apply tau_injective I (F'.obj t'') (hF' t'')
      simp only [map_add (f := _), map_sub, AlgHom.toLinearMap_apply, tau_nat, hy, hy']
      rw [e]
      rw [sub_sub]; rfl
    have := congrArg (iota I _) key
    simp only [map_add (f := _), map_sub, ← iota_nat] at this
    exact this))
  refine ⟨fun t t' a ↦ sig I (F.obj t') (g t t' a), fun t t' a ↦ sig_mem I _ _, ?_⟩
  funext t t' t'' a b
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hg t) t') t'') a) b
  simp only [d1_apply] at e ⊢
  rw [← sig_nat, ← map_sub, ← map_add (f := _)]
  change sig I (F.obj t'') (mp (ext (TrivSqZeroExt R I) F) b (g t t' a) - g t t'' (a ≫ b) + g t' t'' b) = _
  rw [e]
  exact (sig_iota I _ _).trans (hy t t' t'' a b)

end GlobalTheory.PrimIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoefficientExtensionH2ClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_coefficient_extension_H2_class : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧ ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) → (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F), (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) → PrimI I n₀ n₁ n₂ := by
  first | exact @GlobalTheory.PrimIdeal.primI_of_ext | exact GlobalTheory.PrimIdeal.primI_of_ext | (intros; apply GlobalTheory.PrimIdeal.primI_of_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBGlue

variable {R : Type} [CommRing R] {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

abbrev UU (t : (Small i L)ᵒᵖ) : X.Opens := t.unop.1.1.1

theorem le_of_hom {t t' : (Small i L)ᵒᵖ} (a : t ⟶ t') : UU t' ≤ UU t := leOfHom a.unop

theorem hom_eq {t t' : (Small i L)ᵒᵖ} (a b : t ⟶ t') : a = b :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def homOf {t t' : (Small i L)ᵒᵖ} (h : UU t' ≤ UU t) : t ⟶ t' :=
  (homOfLE (show t'.unop ≤ t.unop from h)).op

variable (u : C1 (smallG i L ⋙ OAff s)) (hu : ∀ t t' a, IsUnit (u t t' a))

def uu (t t' : (Small i L)ᵒᵖ) (a : t ⟶ t') : Γ(X, UU t')ˣ := (hu t t' a).unit

variable {u hu}

theorem uu_comp (hm : mdef _ u = 0) {t t' t'' : (Small i L)ᵒᵖ} (a : t ⟶ t') (b : t' ⟶ t'') :
    res (le_of_hom b) (uu u hu t t' a) * uu u hu t' t'' b = uu u hu t t'' (a ≫ b) := by
  apply Units.ext
  have := congrFun (congrFun (congrFun (congrFun (congrFun hm t) t') t'') a) b
  exact sub_eq_zero.1 this

theorem gm_uu (hm : mdef _ u = 0) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {t t' r : (Small i L)ᵒᵖ}
    (a : t ⟶ t') (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t') (uu u hu t t' a) =
      gm f y (UU r) (uu u hu t r (a ≫ b)) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  rw [← uu_comp hm a b, map_mul, gm_res f y _ hy, mul_inv_cancel_right]

theorem exists_g (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) (t t' : (Small i L)ᵒᵖ) :
    ∃ g : Γ(X, UU t ⊓ UU t')ˣ, ∀ p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r),
      res (le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) g = uu u hu t p.1 p.2.1 * (uu u hu t' p.1 p.2.2)⁻¹ := by
  refine glue_unit _ (fun p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r) ↦ UU p.1)
    (fun p ↦ le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) (fun x hx ↦ ?_) _ (fun p q x hx ↦ ?_)
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, homOf (hle.trans inf_le_left), homOf (hle.trans inf_le_right)⟩, hr⟩
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    have c : p.1 ⟶ r := homOf (hle.trans inf_le_left)
    have d : q.1 ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, map_mul, map_inv, map_inv, gm_uu hm (𝟙 X) x p.2.1 c hr, gm_uu hm (𝟙 X) x p.2.2 c hr,
      gm_uu hm (𝟙 X) x q.2.1 d hr, gm_uu hm (𝟙 X) x q.2.2 d hr, hom_eq (q.2.1 ≫ d) (p.2.1 ≫ c),
      hom_eq (q.2.2 ≫ d) (p.2.2 ≫ c)]
    group

variable (u hu)

def glueLB (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : LB X :=
  ⟨(Small i L)ᵒᵖ, UU, fun t t' ↦ Classical.choose (exists_g (hu := hu) hm hB t t')⟩

variable {u hu}

theorem gm_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
    {t t' r : (Small i L)ᵒᵖ} (a : t ⟶ r) (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t ⊓ UU t') ((glueLB u hu hm hB).g t t') =
      gm f y (UU r) (uu u hu t r a) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  have := Classical.choose_spec (exists_g (hu := hu) hm hB t t') ⟨r, a, b⟩
  show gm f y _ (Classical.choose (exists_g (hu := hu) hm hB t t')) = _
  rw [← gm_res f y (le_inf (le_of_hom a) (le_of_hom b)) hy, this, map_mul, map_inv]

theorem isLB_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : (glueLB u hu hm hB).IsLB := {
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨r, hr, -⟩ := hB.cover x ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩
  g_self := fun (t : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t) hx
    rw [gm_res _ x _ hx, map_one]
    exact (gm_glue hm hB (𝟙 X) x (homOf hle) (homOf hle) hr).trans (mul_inv_cancel _)
  cocycle := fun (t t' t'' : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t ⊓ UU t' ⊓ UU t'') hx
    have a : t ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_left))
    have b : t' ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_right))
    have c : t'' ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    refine (congrArg₂ (· * ·) (gm_glue hm hB (𝟙 X) x a b hr) (gm_glue hm hB (𝟙 X) x b c hr)).trans
      ((?_ : _ = _).trans (gm_glue hm hB (𝟙 X) x a c hr).symm)
    group }

theorem gm_lift (hl : IsLift s i L u) {t r : (Small i L)ᵒᵖ} (a : t ⟶ r) (y : X₀) (hy : i y ∈ UU r) :
    gm i y (UU r) (uu u hu t r a) = gm (𝟙 X₀) y _ (L.g t.unop.1.2 r.unop.1.2) := by
  have e := gm_pull (𝟙 X₀) i y (UU r) hy (uu u hu t r a)
  rw [Category.id_comp] at e
  have e' : pullU i (UU r) (uu u hu t r a) = res (Small.le_inf a) (L.g t.unop.1.2 r.unop.1.2) :=
    Units.ext (hl t r a)
  rw [← e, e', gm_res (𝟙 X₀) y _ hy]

def chart (hL : L.IsLB) (hl : IsLift s i L u) (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) :
    ChartPull ((glueLB u hu hm hB).pull i) L (𝟙 X₀) where
  idx J := (J PUnit.unit).unop.1.2
  le J y hy := (J PUnit.unit).unop.2 (mem_pull.1 hy)
  g y J J' hj hj' := by
    have hx : i y ∈ UU (J PUnit.unit) := mem_pull.1 hj
    have hx' : i y ∈ UU (J' PUnit.unit) := mem_pull.1 hj'
    obtain ⟨r, hr, hle⟩ := hB.cover (i y) (UU (J PUnit.unit) ⊓ UU (J' PUnit.unit)) ⟨hx, hx'⟩
    let t₁ : (Small i L)ᵒᵖ := J PUnit.unit
    let t₂ : (Small i L)ᵒᵖ := J' PUnit.unit
    have a : t₁ ⟶ r := homOf (hle.trans inf_le_left)
    have b : t₂ ⟶ r := homOf (hle.trans inf_le_right)
    have e := gm_pull_g (glueLB u hu hm hB) i (𝟙 X₀) y J J' hj hj'
    rw [Category.id_comp] at e
    refine e.trans ((gm_glue hm hB i y a b hr).trans ?_)
    rw [gm_lift hl a y hr, gm_lift hl b y hr]
    have hjr : (𝟙 X₀) y ∈ L.U r.unop.1.2 := r.unop.2 hr
    have hj₁ : (𝟙 X₀) y ∈ L.U (J PUnit.unit).unop.1.2 := (J PUnit.unit).unop.2 hx
    have hj₂ : (𝟙 X₀) y ∈ L.U (J' PUnit.unit).unop.1.2 := (J' PUnit.unit).unop.2 hx'
    rw [← gm_cocycle hL (𝟙 X₀) y hj₁ hj₂ hjr, mul_inv_cancel_right]

end GlobalTheory.LBGlue


open GlobalTheory.LBGlue in
theorem GlobalTheory.LBLift.exists_pic_of_strict_lift : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R)
    (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) →
    IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 →
    ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  intro R _ X X₀ s i L hL u hB hl hu hm
  refine ⟨cls _ (isLB_glue (hu := hu) hm hB), ?_⟩
  rw [← cls_pull (isLB_glue (hu := hu) hm hB) i (pull_isLB (isLB_glue (hu := hu) hm hB) i)]
  exact (cls_eq_iff _ hL).2 (iso_of_chart hL (chart hL hl hm hB))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) → IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 → ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  first | exact @GlobalTheory.LBLift.exists_pic_of_strict_lift | exact GlobalTheory.LBLift.exists_pic_of_strict_lift | (intros; apply GlobalTheory.LBLift.exists_pic_of_strict_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift.IsoRel

section Rel

variable {X X₀ Y Y₀ : Scheme.{0}}

abbrev Quad (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : Type :=
  {p : Y.affineOpens × Small i L × Small i L × Small i L //
    p.1.1 ≤ φ₀ ⁻¹ᵁ p.2.1.1.1.1 ∧ p.1.1 ≤ φ₁ ⁻¹ᵁ p.2.2.1.1.1.1 ∧ p.1.1 ≤ φ₂ ⁻¹ᵁ p.2.2.2.1.1.1}

variable {i : X₀ ⟶ X} {L : LB X₀} {φ₀ φ₁ φ₂ : Y ⟶ X}

theorem Quad.le_W {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1

theorem Quad.le_K₀ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.1 ≤ q.1.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).1

theorem Quad.le_K₁ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.2.1 ≤ q.1.2.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2).1

theorem Quad.le_K₂ {p q : Quad i L φ₀ φ₁ φ₂} (h : p ≤ q) : p.1.2.2.2 ≤ q.1.2.2.2 :=
  (Prod.le_def.1 (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2).2

theorem Quad.le_of {p q : Quad i L φ₀ φ₁ φ₂} (hW : p.1.1 ≤ q.1.1) (h₀ : p.1.2.1 ≤ q.1.2.1) (h₁ : p.1.2.2.1 ≤ q.1.2.2.1)
    (h₂ : p.1.2.2.2 ≤ q.1.2.2.2) : p ≤ q :=
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨hW, Prod.le_def.2 ⟨h₀, Prod.le_def.2 ⟨h₁, h₂⟩⟩⟩)

def quadW (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ AffOp Y :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.1) fun _ _ h ↦ Quad.le_W h).op

def quadK₀ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.1) fun _ _ h ↦ Quad.le_K₀ h).op

def quadK₁ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.2.1) fun _ _ h ↦ Quad.le_K₁ h).op

def quadK₂ (i : X₀ ⟶ X) (L : LB X₀) (φ₀ φ₁ φ₂ : Y ⟶ X) : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ⥤ (Small i L)ᵒᵖ :=
  (Monotone.functor (f := fun p : Quad i L φ₀ φ₁ φ₂ ↦ p.1.2.2.2) fun _ _ h ↦ Quad.le_K₂ h).op

end Rel

section SlopeTestRemainingChoices

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem appLE_eq_of_eq {f g : Y ⟶ X} (e : f = g) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e; rfl

theorem app_appLE {i : X₀ ⟶ X} {i' : Y₀ ⟶ Y} {φ : Y ⟶ X} {ψ : Y₀ ⟶ X₀} (h : ψ ≫ i = i' ≫ φ) {U : X.Opens}
    {W : Y.Opens} (le : W ≤ φ ⁻¹ᵁ U) {V₀ : X₀.Opens} (hV : i ⁻¹ᵁ U ≤ V₀) (hle : i' ⁻¹ᵁ W ≤ ψ ⁻¹ᵁ V₀) (b : Γ(X, U))
    (c : Γ(X₀, V₀)) (hc : (i.app U).hom b = (X₀.presheaf.map (homOfLE hV).op).hom c) :
    (i'.app W).hom ((φ.appLE U W le).hom b) = (ψ.appLE V₀ (i' ⁻¹ᵁ W) hle).hom c := by
  have hle' : i' ⁻¹ᵁ W ≤ (ψ ≫ i) ⁻¹ᵁ U := fun y hy ↦ by
    show (ψ ≫ i) y ∈ U
    rw [h, Scheme.Hom.comp_apply]; exact le hy
  have e1 : φ.appLE U W le ≫ i'.app W = (ψ ≫ i).appLE U (i' ⁻¹ᵁ W) hle' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq h.symm _ _ _ _
  have e2 := congrArg (fun q ↦ q.hom b) e1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2, Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, hc]
  have e3 := congrArg (fun q ↦ q.hom c) (Scheme.Hom.map_appLE ψ (U := i ⁻¹ᵁ U) (U' := V₀) hle' (homOfLE hV).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  exact e3

theorem map_res_val {U V V' : X.Opens} (h : V ≤ U) (h' : V' ≤ V) (a : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (res h a).val = (res (h'.trans h) a).val := by
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀) (hp : Function.Surjective p)
    (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K) (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem gm_one_res_pull (f : Y ⟶ X) (y : Y) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U) (h : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res hle (pullU f U a)) = gm f y U a := by
  rw [gm_res (𝟙 Y) y hle h, gm_pull (𝟙 Y) f y U (hle h), Category.id_comp]

theorem commGroup_mul_eq_mul_of_eq_mul_inv_mul {G : Type} [CommGroup G] (a b w w' : G) (h : w = a * b⁻¹ * w') : a * w' = b * w := by
  rw [h, mul_comm a b⁻¹, _root_.mul_assoc b⁻¹, mul_inv_cancel_left]

end SlopeTestRemainingChoices

theorem mulRel_of_iso : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  intro R _ I hI X X₀ Y Y₀ s s' i i' φ₀ φ₁ φ₂ w₀ w₁ w₂ ψ₀ ψ₁ ψ₂ L hL u hT hB hu h₀ h₁ h₂ hcls
  have hcls' : cls (tens (L.pull ψ₁) (L.pull ψ₂)) (isLB_tens (pull_isLB hL ψ₁) (pull_isLB hL ψ₂)) =
      cls (L.pull ψ₀) (pull_isLB hL ψ₀) := hcls.symm
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hcls'
  have mem : ∀ (ψ : Y₀ ⟶ X₀) (φ : Y ⟶ X), ψ ≫ i = i' ≫ φ → ∀ (q : Small i L) (W : Y.Opens),
      W ≤ φ ⁻¹ᵁ q.1.1.1 → ∀ y, i' y ∈ W → ψ y ∈ L.U q.1.2 := fun ψ φ h q W hW y hy ↦
    q.2 (show i (ψ y) ∈ q.1.1.1 by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]; exact hW hy)
  let c : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ → (LB.div (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂))).ι := fun t ↦
    ((fun _ ↦ t.unop.1.2.1.1.2), ((fun _ ↦ t.unop.1.2.2.1.1.2), (fun _ ↦ t.unop.1.2.2.2.1.2)))
  have hc : ∀ t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ,
      i' ⁻¹ᵁ t.unop.1.1.1 ≤ (LB.div (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂))).U (c t) := fun t y hy ↦
    ⟨mem_pull.2 (mem ψ₀ φ₀ h₀ _ _ t.unop.2.1 y hy), mem_pull.2 (mem ψ₁ φ₁ h₁ _ _ t.unop.2.2.1 y hy),
      mem_pull.2 (mem ψ₂ φ₂ h₂ _ _ t.unop.2.2.2 y hy)⟩
  have surj := fun t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ ↦ hT.app_surj t.unop.1.1
  let v : C0 (quadW i L φ₀ φ₁ φ₂ ⋙ OAff s') := fun t ↦ Function.surjInv (surj t) (res (hc t) (w.s (c t))).val
  have hv : ∀ t : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ, (i'.app t.unop.1.1.1).hom (v t) = (res (hc t) (w.s (c t))).val :=
    fun t ↦ Function.surjInv_eq (surj t) _
  refine ⟨(Quad i L φ₀ φ₁ φ₂)ᵒᵖ, inferInstance, inferInstance, quadW i L φ₀ φ₁ φ₂, quadK₀ i L φ₀ φ₁ φ₂,
    quadK₁ i L φ₀ φ₁ φ₂, quadK₂ i L φ₀ φ₁ φ₂, fun t ↦ t.unop.2.1, fun t ↦ t.unop.2.2.1, fun t ↦ t.unop.2.2.2, v,
    ?_, ?_, ?_⟩
  · constructor
    · intro y U hy
      obtain ⟨a₀, ha₀, -⟩ := hB.cover (φ₀ y) ⊤ trivial
      obtain ⟨a₁, ha₁, -⟩ := hB.cover (φ₁ y) ⊤ trivial
      obtain ⟨a₂, ha₂, -⟩ := hB.cover (φ₂ y) ⊤ trivial
      obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (show y ∈ U ⊓ (φ₀ ⁻¹ᵁ ((smallG i L).obj a₀).unop.1 ⊓ (φ₁ ⁻¹ᵁ ((smallG i L).obj a₁).unop.1 ⊓
          φ₂ ⁻¹ᵁ ((smallG i L).obj a₂).unop.1)) from ⟨hy, ha₀, ha₁, ha₂⟩)
      exact ⟨Opposite.op ⟨(⟨W, hW⟩, a₀.unop, a₁.unop, a₂.unop), fun z hz ↦ (hWU hz).2.1,
        fun z hz ↦ (hWU hz).2.2.1, fun z hz ↦ (hWU hz).2.2.2⟩, hyW, fun z hz ↦ (hWU hz).1⟩
    · intro t₁ t₂ y U hy hy₁ hy₂
      obtain ⟨b₀, ⟨f₀⟩, ⟨g₀⟩, hb₀, -⟩ := hB.dir ((quadK₀ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₀ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₀ y) ⊤ trivial (t₁.unop.2.1 hy₁) (t₂.unop.2.1 hy₂)
      obtain ⟨b₁, ⟨f₁⟩, ⟨g₁⟩, hb₁, -⟩ := hB.dir ((quadK₁ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₁ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₁ y) ⊤ trivial (t₁.unop.2.2.1 hy₁) (t₂.unop.2.2.1 hy₂)
      obtain ⟨b₂, ⟨f₂⟩, ⟨g₂⟩, hb₂, -⟩ := hB.dir ((quadK₂ i L φ₀ φ₁ φ₂).obj t₁) ((quadK₂ i L φ₀ φ₁ φ₂).obj t₂)
        (φ₂ y) ⊤ trivial (t₁.unop.2.2.2 hy₁) (t₂.unop.2.2.2 hy₂)
      obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (show y ∈ U ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1) ⊓ (φ₀ ⁻¹ᵁ ((smallG i L).obj b₀).unop.1 ⊓
          (φ₁ ⁻¹ᵁ ((smallG i L).obj b₁).unop.1 ⊓ φ₂ ⁻¹ᵁ ((smallG i L).obj b₂).unop.1)) from
          ⟨⟨hy, hy₁, hy₂⟩, hb₀, hb₁, hb₂⟩)
      let t₃ : (Quad i L φ₀ φ₁ φ₂)ᵒᵖ := Opposite.op ⟨(⟨W, hW⟩, b₀.unop, b₁.unop, b₂.unop),
        fun z hz ↦ (hWU hz).2.1, fun z hz ↦ (hWU hz).2.2.1, fun z hz ↦ (hWU hz).2.2.2⟩
      refine ⟨t₃, ⟨(homOfLE (Quad.le_of (p := t₃.unop) (q := t₁.unop) (fun z hz ↦ (hWU hz).1.2.1) (leOfHom f₀.unop)
          (leOfHom f₁.unop) (leOfHom f₂.unop))).op⟩,
        ⟨(homOfLE (Quad.le_of (p := t₃.unop) (q := t₂.unop) (fun z hz ↦ (hWU hz).1.2.2) (leOfHom g₀.unop)
          (leOfHom g₁.unop) (leOfHom g₂.unop))).op⟩, hyW, fun z hz ↦ (hWU hz).1.1⟩
  · intro t
    refine isUnit_of_sqZero (i'.app t.unop.1.1.1).hom (surj t) (I.map (algebraMap R (Sec s' t.unop.1.1.1)))
      (by have e := Ideal.map_pow (algebraMap R (Sec s' t.unop.1.1.1)) I 2; rw [hI, Ideal.map_bot] at e; exact e.symm) (fun a ha ↦ (hT.ker t.unop.1.1 a).1 ha) (v t) ?_
    rw [hv t]; exact Units.isUnit _
  · intro t t' a
    have le : t'.unop ≤ t.unop := leOfHom a.unop
    have hWle : t'.unop.1.1.1 ≤ t.unop.1.1.1 := Quad.le_W le
    have hV : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ i' ⁻¹ᵁ t.unop.1.1.1 := fun y hy ↦ hWle hy
    refine (hT.ker t'.unop.1.1 _).1 ?_
    have ek : ∀ (ψ : Y₀ ⟶ X₀) (φ : Y ⟶ X) (hψ : ψ ≫ i = i' ≫ φ) (p q : (Small i L)ᵒᵖ) (f : p ⟶ q)
        (le' : t'.unop.1.1.1 ≤ φ ⁻¹ᵁ q.unop.1.1.1)
        (hle : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ ⁻¹ᵁ (L.U p.unop.1.2 ⊓ L.U q.unop.1.2)),
        (i'.app t'.unop.1.1.1).hom ((φ.appLE _ t'.unop.1.1.1 le').hom (u p q f)) =
          (res hle (pullU ψ _ (L.g p.unop.1.2 q.unop.1.2))).val := fun ψ φ hψ p q f le' hle ↦
      (app_appLE hψ le' (Small.le_inf f) hle _ _ (hu p q f)).trans rfl
    have hle₀ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₀ ⁻¹ᵁ (L.U t.unop.1.2.1.1.2 ⊓ L.U t'.unop.1.2.1.1.2) := fun y hy ↦
      ⟨mem ψ₀ φ₀ h₀ _ _ t.unop.2.1 y (hV hy), mem ψ₀ φ₀ h₀ _ _ t'.unop.2.1 y hy⟩
    have hle₁ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₁ ⁻¹ᵁ (L.U t.unop.1.2.2.1.1.2 ⊓ L.U t'.unop.1.2.2.1.1.2) := fun y hy ↦
      ⟨mem ψ₁ φ₁ h₁ _ _ t.unop.2.2.1 y (hV hy), mem ψ₁ φ₁ h₁ _ _ t'.unop.2.2.1 y hy⟩
    have hle₂ : i' ⁻¹ᵁ t'.unop.1.1.1 ≤ ψ₂ ⁻¹ᵁ (L.U t.unop.1.2.2.2.1.2 ⊓ L.U t'.unop.1.2.2.2.1.2) := fun y hy ↦
      ⟨mem ψ₂ φ₂ h₂ _ _ t.unop.2.2.2 y (hV hy), mem ψ₂ φ₂ h₂ _ _ t'.unop.2.2.2 y hy⟩
    have e₀ := ek ψ₀ φ₀ h₀ _ _ ((quadK₀ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.1) hle₀
    have e₁ := ek ψ₁ φ₁ h₁ _ _ ((quadK₁ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.2.1) hle₁
    have e₂ := ek ψ₂ φ₂ h₂ _ _ ((quadK₂ i L φ₀ φ₁ φ₂).map a) (t'.unop.2.2.2) hle₂
    have emp : (i'.app t'.unop.1.1.1).hom (mp (quadW i L φ₀ φ₁ φ₂ ⋙ OAff s') a (v t)) =
        (res (hV.trans (hc t)) (w.s (c t))).val := by
      have n := congrArg (fun q ↦ q.hom (v t)) (i'.naturality (homOfLE hWle).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
      refine n.trans ?_
      show (Y₀.presheaf.map _).hom ((i'.app t.unop.1.1.1).hom (v t)) = _
      rw [hv t]
      exact map_res_val (hc t) hV _
    have key : res hle₀ (pullU ψ₀ _ (L.g t.unop.1.2.1.1.2 t'.unop.1.2.1.1.2)) * res (hc t') (w.s (c t')) =
        res hle₁ (pullU ψ₁ _ (L.g t.unop.1.2.2.1.1.2 t'.unop.1.2.2.1.1.2)) *
          res hle₂ (pullU ψ₂ _ (L.g t.unop.1.2.2.2.1.2 t'.unop.1.2.2.2.1.2)) * res (hV.trans (hc t)) (w.s (c t)) := by
      refine unit_ext fun y hy ↦ ?_
      have hp := hc t (hV hy)
      have hq := hc t' hy
      have g := (isGen_iff_germ w).1 hw y (c t) (c t') hp hq
      rw [gm_div' (L.pull ψ₀) (tens (L.pull ψ₁) (L.pull ψ₂)) (𝟙 Y₀) y (c t) (c t') hp hq,
        gm_pull_g L ψ₀ (𝟙 Y₀) y _ _ hp.1 hq.1,
        gm_tens (L.pull ψ₁) (L.pull ψ₂) (𝟙 Y₀) y _ _ hp.2 hq.2, gm_pull_g L ψ₁ (𝟙 Y₀) y _ _ hp.2.1 hq.2.1,
        gm_pull_g L ψ₂ (𝟙 Y₀) y _ _ hp.2.2 hq.2.2, Category.id_comp, Category.id_comp, Category.id_comp] at g
      simp only [map_mul, gm_one_res_pull _ y _ hy, gm_res (𝟙 Y₀) y _ hy]
      exact commGroup_mul_eq_mul_of_eq_mul_inv_mul _ _ _ _ g
    have kv := congrArg Units.val key
    simp only [Units.val_mul] at kv
    beta_reduce
    refine (map_sub (i'.app t'.unop.1.1.1).hom _ _).trans (sub_eq_zero.2 ?_)
    refine ((map_mul (i'.app t'.unop.1.1.1).hom _ _).trans ?_).trans (((map_mul (i'.app t'.unop.1.1.1).hom _ _).trans
      (congrArg (· * _) (map_mul (i'.app t'.unop.1.1.1).hom _ _))).symm)
    erw [emp, hv t', e₀, e₁, e₂]
    exact kv

end GlobalTheory.LBLift.IsoRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  first | exact @GlobalTheory.LBLift.IsoRel.mulRel_of_iso | exact GlobalTheory.LBLift.IsoRel.mulRel_of_iso | (intros; apply GlobalTheory.LBLift.IsoRel.mulRel_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem app_presheaf_map {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem presheaf_map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₂).op).hom ((Y.presheaf.map (homOfLE h₁).op).hom y) =
      (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isBasis_smallG (hi : IsThick I s i) (hL : L.IsLB) : IsBasis (smallG i L) := by
  haveI := hi.closed
  have hind : Topology.IsInducing i.base := i.isClosedEmbedding.isInducing
  have cov : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : (Small i L)ᵒᵖ,
      x ∈ ((smallG i L).obj t).unop.1 ∧ ((smallG i L).obj t).unop.1 ≤ U := by
    intro x U hx
    obtain ⟨x₀, rfl⟩ := hi.surj.surj x
    have hx₀ : x₀ ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨V, hV, hVe⟩ := hind.isOpen_iff.1 (L.U j).isOpen
    have hxV : i.base x₀ ∈ (⟨V, hV⟩ : X.Opens) ⊓ U := ⟨show x₀ ∈ i.base ⁻¹' V from hVe ▸ hj, hx⟩
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
    have hsm : i ⁻¹ᵁ W ≤ L.U j := fun y hy ↦ by
      show y ∈ (L.U j : Set X₀)
      rw [← hVe]
      exact (hWle hy).1
    exact ⟨Opposite.op ⟨(⟨W, hW⟩, j), hsm⟩, hxW, fun y hy ↦ (hWle hy).2⟩
  refine ⟨cov, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t₃, hx₃, hle⟩ := cov x (U ⊓ ((smallG i L).obj t₁).unop.1 ⊓ ((smallG i L).obj t₂).unop.1)
    ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨t₃, ⟨(homOfLE (show t₃.unop ≤ t₁.unop from fun y hy ↦ (hle hy).1.2)).op⟩,
    ⟨(homOfLE (show t₃.unop ≤ t₂.unop from fun y hy ↦ (hle hy).2)).op⟩, hx₃, fun y hy ↦ (hle hy).1.1⟩

theorem exists_isLift (hi : IsThick I s i) : ∃ u, IsLift s i L u :=
  ⟨fun p q a ↦ (hi.app_surj q.unop.1.1 (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val).choose,
    fun p q a ↦ (hi.app_surj q.unop.1.1 _).choose_spec⟩

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift
variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp v
  have hn : x * y - 1 ∈ K := hker _ (by simp [hv])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem lift_isUnit (hI : I ^ 2 = ⊥) (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (p q : (Small i L)ᵒᵖ) (a : p ⟶ q) : IsUnit (u p q a) := by
  have hK : ∀ (A : Type) [CommRing A] [Algebra R A], (I.map (algebraMap R A)) ^ 2 = ⊥ := fun A _ _ ↦ by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  exact isUnit_of_sqZero (A := Γ(X, q.unop.1.1.1)) (i.app q.unop.1.1.1).hom (hi.app_surj q.unop.1.1)
    (I.map (algebraMap R (Sec s q.unop.1.1.1))) (hK (Sec s q.unop.1.1.1)) (fun b hb ↦ (hi.ker q.unop.1.1 b).1 hb) (u p q a)
    ((hu p q a).symm ▸ Units.isUnit _)

theorem lift_mdef (hi : IsThick I s i) (hL : L.IsLB) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u) :
    In2 I _ (mdef _ u) := by
  intro t t' t'' a b
  refine (hi.ker t''.unop.1.1 _).1 ?_
  have hb : t''.unop.1.1.1 ≤ t'.unop.1.1.1 := leOfHom b.unop
  have h2 : i ⁻¹ᵁ t''.unop.1.1.1 ≤ L.U t.unop.1.2 ⊓ L.U t'.unop.1.2 ⊓ L.U t''.unop.1.2 :=
    le_inf ((i.preimage_mono hb).trans (Small.le_inf a)) t''.unop.2
  have hc := congrArg (fun w ↦ (X₀.presheaf.map (homOfLE h2).op).hom w.val)
    (hL.cocycle t.unop.1.2 t'.unop.1.2 t''.unop.1.2)
  simp only [Units.val_mul, map_mul, res, Units.coe_map, MonoidHom.coe_coe,
    presheaf_map_map] at hc
  have k : ∀ (x : Γ(X, t'.unop.1.1.1)) (y z : Γ(X, t''.unop.1.1.1)),
      (i.app t'.unop.1.1.1).hom x = (res (Small.le_inf a) (L.g t.unop.1.2 t'.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom y = (res (Small.le_inf b) (L.g t'.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom z = (res (Small.le_inf (a ≫ b)) (L.g t.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom ((X.presheaf.map (homOfLE hb).op).hom x * y - z) = 0 := by
    intro x y z hx hy hz
    rw [map_sub, map_mul, app_presheaf_map, hx, hy, hz, sub_eq_zero]
    simp only [res, Units.coe_map, MonoidHom.coe_coe, presheaf_map_map]
    exact hc
  exact k _ _ _ (hu t t' a) (hu t' t'' b) (hu t t'' (a ≫ b))

theorem isLiftOfTransitionUnits_of_ideal_cochain_change (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (u' : C1 (smallG i L ⋙ OAff s)) (h : In1 I _ (u' - u)) : IsLift s i L u' := by
  intro p q a
  have h0 := (hi.ker q.unop.1.1 _).2 (h p q a)
  have e : u' p q a = u p q a + (u' - u) p q a := by simp
  rw [e]
  exact (map_add (i.app q.unop.1.1.1).hom (u p q a) ((u' - u) p q a)).trans
    ((congrArg₂ (· + ·) (hu p q a) h0).trans (add_zero _))

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift

theorem small_basis_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  intro R _ I hI X X₀ s i L hi hL
  exact ⟨isBasis_smallG hi hL, exists_isLift hi, fun u hu ↦
    ⟨lift_isUnit hI hi hu, lift_mdef hi hL hu, fun u' h ↦ isLiftOfTransitionUnits_of_ideal_cochain_change hi hu u' h⟩⟩

end GlobalTheory.LBLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLiftStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_affine_basis_and_transition_units_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  first | exact @GlobalTheory.LBLift.small_basis_lift | exact GlobalTheory.LBLift.small_basis_lift | (intros; apply GlobalTheory.LBLift.small_basis_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZero
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

section
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.Obs

theorem abLift_of_prim (hP : PrimitiveExtendedDegTwoVanish) : AbLift := by
  intro R _ I hI A _ g hA hg X₀ Y₀ i i' ψ₀ ψ₁ ψ₂ hi hi' e₀ e₁ e₂ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨hB, ⟨u, hu⟩, hall⟩ := GlobalTheory.T.small_affine_basis_and_transition_units_lift R I hI _ _ A.hom i L hi hL
  obtain ⟨hun, hdef, hnear⟩ := hall u hu
  obtain ⟨T, _, _, H, K₀, K₁, K₂, le₀, le₁, le₂, v, hH, hv, hrel⟩ := GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening R I hI _ _ _ _ A.hom (A ⊗ A).hom i i'
    _ _ _ (overW μ[A]) (overW (fst A A)) (overW (snd A A)) ψ₀ ψ₁ ψ₂ L hL u hi' hB hu e₀ e₁ e₂ hc
  obtain ⟨R₁, _, _, q, hq, hprim⟩ := GlobalTheory.T.flat_coefficient_extension_H2_class R I
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A ⊗ A).hom := by
    rw [← Over.w (fst A A)]
    haveI : Smooth (fst A A).left := inferInstanceAs (Smooth (pullback.fst A.hom A.hom))
    infer_instance
  have hpi := hprim _ _ _ _ (pullMap (overW μ[A]) _ H K₀ le₀) (pullMap (overW (fst A A)) _ H K₁ le₁)
    (pullMap (overW (snd A A)) _ H K₂ le₂)
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine A.hom ((smallG i L).obj t).unop
      inferInstanceAs (Module.Flat R (Sec A.hom ((smallG i L).obj t).unop.1)))
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine (A ⊗ A).hom (H.obj t).unop
      inferInstanceAs (Module.Flat R (Sec (A ⊗ A).hom (H.obj t).unop.1)))
    (GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt hP R R₁ q hq A g hA hg _ T _ H K₀ K₁ K₂ le₀ le₁ le₂ hB hH)
  obtain ⟨u', h1, h2⟩ := GlobalTheory.T.exists_cocycle_correction_square_zero_ideal R I hI _ _ _ _ _ _ _ hpi u v hun hdef hv hrel
  exact GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle R _ _ A.hom i L hL u' hB (hnear u' h1) (hall u' (hnear u' h1)).1 h2

theorem abLift : AbLift :=
  abLift_of_prim (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish fun R _ A _ g hA hg ↦
    ⟨(GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).1, (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).2.1⟩))

end

theorem exists_fac_quot {R K : Type} [CommRing R] [Field K] (J : Ideal R) (hJ : J ^ 2 = ⊥) (s : Sp K ⟶ Sp R) :
    ∃ s' : Sp K ⟶ Sp (R ⧸ J), s' ≫ spMap (Ideal.Quotient.mk J) = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have h : ∀ a ∈ J, φ.hom a = 0 := fun a ha ↦ by
    have h2 : a ^ 2 = 0 := by simpa [hJ] using Ideal.pow_mem_pow ha 2
    have := congrArg φ.hom h2
    rw [map_pow, map_zero] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨spMap (Ideal.Quotient.lift J φ.hom h), ?_⟩
  rw [← Spec.map_comp]
  rfl

theorem exists_fam {S : Scheme.{0}} {A U T : Over S} [GrpObj A] [IsLocallyNoetherian U.left] (hA : IsAbelianScheme A)
    (p : T ⟶ U) (hp : ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ U), ∃ t' : Over.mk s ⟶ T, t' ≫ p = t)
    {N : LB (A ⊗ T).left} (hN : N.IsLB) (ha : IsAdditive N) (c : Pic (A ⊗ U).left)
    (hc : CechPic.pull (A ◁ p).left c = cls N hN) :
    ∃ (M : LB (A ⊗ U).left) (hM : M.IsLB), IsAdditive M ∧
      ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := by
  obtain ⟨M, hM, e⟩ := cls_surj (c - CechPic.pull (lift 1 (snd A U)).left c)
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t =
      CechPic.pull (lift a t).left c - CechPic.pull (lift (1 : Y ⟶ A) t).left c := fun Y a t ↦ by
    rw [evc, e, map_sub, ← CechPic.pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, lift_snd]
  have k' : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), CechPic.pull (lift a (t ≫ p)).left c = evc hN a t :=
    fun Y a t ↦ by
    rw [evc, ← hc, ← CechPic.pull_comp, ← Over.comp_left, lift_whiskerLeft]
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := fun Y a t ↦ by
    rw [k, k', k', ha.evc_one hN, sub_zero]
  refine ⟨M, hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [k, sub_self])) fun K _ _ s t ↦ ?_, key⟩
  obtain ⟨t', rfl⟩ := hp K s t
  refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
  simp only [evc_ev hM, lift_fst, lift_snd_assoc]
  simp only [← Category.assoc, key]
  exact (isAdditive_iff hN).1 ha Y a a' _

theorem hasRep_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg J hJ ⟨B, b, P, hP, hb⟩
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B _ b P ?_ ?_ hP hb fun x ↦ ?_
  · haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk J)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact inferInstanceAs (IsFinite (spMap (Ideal.Quotient.mk J)))
  · exact GlobalTheory.LiftSys.surjective_spMap_sqZero _ Ideal.Quotient.mk_surjective hJ
      fun _ h ↦ Ideal.Quotient.eq_zero_iff_mem.1 h
  obtain ⟨C, _, σ, j, hs, hj, ho, hx⟩ := GlobalTheory.T.exists_affine_chart_smooth_lift_sqZero R J hJ g B b hb.smooth x
  have hN : (ev P (fst A _) (snd A _ ≫ j)).IsLB := pull_isLB hP.fam.isLB _
  have ha : IsAdditive (ev P (fst A _) (snd A _ ≫ j)) := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    simp only [evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP.fam.isLB).1 hP.fam.add Y a a' _
  obtain ⟨c, hc⟩ := GlobalTheory.T.additiveFamily_reduction_lifts_lineBundle abLift R J hJ A g hA hg C σ _ hN ha
  haveI : Smooth (spMap σ) := SmoothOfRelativeDimension.smooth g _
  haveI : IsLocallyNoetherian (Over.mk (spMap σ)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (spMap σ)
  obtain ⟨M, hM, hMa, key⟩ := exists_fam hA (fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J))))
    (fun K _ s t ↦ by
      obtain ⟨s', hs'⟩ := exists_fac_quot J hJ s
      exact ⟨lift t (Over.homMk s' hs'), lift_fst _ _⟩) hN ha c hc
  refine ⟨_, M, j, ⟨hM, hMa⟩, hs, hj, ho, hx, (same_iff hM hP.fam.isLB _ _).2 ?_⟩
  rw [key, evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]

end GlobalTheory.LBLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.LBLift.hasRep_of_sqZero | exact GlobalTheory.LBLift.hasRep_of_sqZero | (intros; apply GlobalTheory.LBLift.hasRep_of_sqZero <;> assumption)
end
