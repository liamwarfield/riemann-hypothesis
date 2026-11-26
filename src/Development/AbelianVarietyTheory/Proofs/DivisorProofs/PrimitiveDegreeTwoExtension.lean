module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.BaseChg

section Nat
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}

def ofNat (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := sm

theorem ofNat_pull2_bijective (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) (hb : ∀ T, Function.Bijective (α T)) :
    Function.Bijective (ofNat α nat sm).pull2 := by
  let e : ∀ T, F.obj T ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (e T).symm.toRingHom
  have hβα : ∀ T b, β T (α T b) = b := fun T b ↦ (e T).symm_apply_apply b
  have hαβ : ∀ T b, α T (β T b) = b := fun T b ↦ (e T).apply_symm_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := fun a b ↦ by
    apply (hb _).1; rw [hαβ, nat, hαβ]
  have smβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := fun T r b ↦ by
    apply (hb T).1; rw [hαβ, sm, hαβ]
  have h1 : ∀ c, (ofNat β natβ smβ).pull2 ((ofNat α nat sm).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F T b).trans (hβα T b).symm) c
  have h2 : ∀ c, (ofNat α nat sm).pull2 ((ofNat β natβ smβ).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F' T b).trans (hαβ T b).symm) c
  exact ⟨fun x y hxy ↦ by rw [← h1 x, hxy, h1], fun y ↦ ⟨_, h2 y⟩⟩

end Nat

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

theorem isAffineHom_of_isPullback (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance

abbrev pre (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : X₁.affineOpens :=
  haveI := isAffineHom_of_isPullback hp
  ⟨pr ⁻¹ᵁ U.1, U.2.preimage pr⟩

def preF (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : AffOp X₀ ⥤ AffOp X₁ :=
  (Monotone.functor (f := pre hp) fun _ _ h ↦ (show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from
    fun _ hx ↦ (Subtype.coe_le_coe.2 h) hx)).op

abbrev pairOf (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : Pair pr :=
  ⟨(pre hp U, U), le_rfl⟩

def secP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull s₀ s₁ (pairOf hp U)

theorem pullbackSection_smul₂ (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₀)
    (b : Sec s₀ U.1) : secP hp U (r • b) = algebraMap R₀ R₁ r • secP hp U b :=
  semiHom_secPull hp.w (pairOf hp U) r b

def beta (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    R₁ ⊗[R₀] Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { toRingHom := secP hp U
      commutes' := fun r ↦ by
        have := pullbackSection_smul₂ hp U r 1
        rw [map_one] at this
        change secP hp U (algebraMap R₀ _ r) = _
        rw [Algebra.algebraMap_eq_smul_one r, this, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          Algebra.algebraMap_eq_smul_one r]
        exact (Algebra.algebraMap_eq_smul_one _).symm }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

theorem beta_tmul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (b : Sec s₀ U.1) : beta hp U (r ⊗ₜ b) = algebraMap R₁ _ r * secP hp U b := by
  simp [beta]

theorem beta_smul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (x : R₁ ⊗[R₀] Sec s₀ U.1) : beta hp U (r • x) = r • beta hp U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, beta_tmul, beta_tmul, map_mul, _root_.mul_assoc, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem beta_nat (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {U V : AffOp X₀} (a : U ⟶ V)
    (x : (ext R₁ (OAff s₀)).obj U) :
    beta hp V.unop (mp (ext R₁ (OAff s₀)) a x) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop x) := by
  revert x
  change ∀ x : R₁ ⊗[R₀] Sec s₀ U.unop.1, _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (map_zero _).symm
  | tmul r b =>
    have hn := (pairPull hp.w).naturality
      (homOfLE (show pairOf hp V.unop ≤ pairOf hp U.unop from
        Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨fun _ hx ↦ (Subtype.coe_le_coe.2 (leOfHom a.unop) : V.unop.1 ≤ U.unop.1) hx,
          leOfHom a.unop⟩))).op b
    change beta hp V.unop (r ⊗ₜ mp (OAff s₀) a b) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop (r ⊗ₜ b))
    rw [beta_tmul, beta_tmul]
    erw [map_mul]
    congr 1
    all_goals first | exact ((Sec.res s₁ _).commutes r).symm | exact hn
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy]
    exact (map_add _ _ _).symm

def fwd (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preF hp ⋙ OAff s₁) :=
  ofNat (fun U ↦ beta hp U.unop) (fun a x ↦ beta_nat hp a x) (fun U r x ↦ beta_smul hp U.unop r x)

section PairMaps
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem comp_base_eq (hf : f₁ ≫ pr = pr' ≫ f₀) (y : Y₁) : pr.base (f₁.base y) = f₀.base (pr'.base y) := by
  have := congrArg (fun g : Y₁ ⟶ X₀ ↦ g.base y) hf
  simpa using this

abbrev preP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(pre hp' p.1.1, pre hp p.1.2), fun y hy ↦ by
    show pr.base (f₁.base y) ∈ p.1.2.1
    rw [comp_base_eq hf]; exact p.2 hy⟩

def preFP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ :=
  (Monotone.functor (f := preP hp hp' hf) fun _ _ h ↦ Subtype.coe_le_coe.1 (Prod.le_def.2
    ⟨show pr' ⁻¹ᵁ _ ≤ pr' ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_fst h)) hx,
     show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_snd h)) hx⟩)).op

def zMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preF hp ⋙ OAff s₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((preFP hp hp' hf).obj p)
  naturality a b := (pairPull h₁).naturality ((preFP hp hp' hf).map a) b
  smul p r b := (pairPull h₁).smul ((preFP hp hp' hf).obj p) r b

def zRes (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (preF hp' ⋙ OAff t₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (preFP hp hp' hf ⋙ OPair f₁ t₁) :=
  ofNat (fun p ↦ beta hp' p.unop.1.1) (fun a x ↦ beta_nat hp' ((pairFst f₀).map a) x)
    (fun p r x ↦ beta_smul hp' _ r x)

end PairMaps

section Pointwise
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem preF_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (x : X₁) (U : X₁.Opens) (hx : x ∈ U) :
    ∃ t : AffOp X₀, x ∈ ((preF hp).obj t).unop.1 ∧ ((preF hp).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x) (U := W₀) hx
  exact ⟨Opposite.op ⟨V, hV⟩, hxV, fun y hy ↦ hVW hy⟩

theorem preF_dir (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (t₁ t₂ : AffOp X₀) (x : X₁) (U : X₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preF hp).obj t₁).unop.1) (h₂ : x ∈ ((preF hp).obj t₂).unop.1) :
    ∃ t₃ : AffOp X₀, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((preF hp).obj t₃).unop.1 ∧
      ((preF hp).obj t₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x)
    (U := W₀ ⊓ t₁.unop.1 ⊓ t₂.unop.1) ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨Opposite.op ⟨V, hV⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₁.unop from fun y hy ↦ (hVW hy).1.2)).op⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₂.unop from fun y hy ↦ (hVW hy).2)).op⟩,
    hxV, fun y hy ↦ (hVW hy).1.1⟩

theorem preFP_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (x : Y₁) (U : Y₁.Opens) (hx : x ∈ U) :
    ∃ t : (Pair f₀)ᵒᵖ, x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ∧
      ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := (⊤ : X₀.Opens)) trivial
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ f₀ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩, hxV', fun z hz ↦ (hV'W hz).1⟩

theorem preFP_directed (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (a₁ a₂ : (Pair f₀)ᵒᵖ) (x : Y₁) (U : Y₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₁).unop.1)
    (h₂ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₂).unop.1) :
    ∃ a₃ : (Pair f₀)ᵒᵖ, Nonempty (a₁ ⟶ a₃) ∧ Nonempty (a₂ ⟶ a₃) ∧
      x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ∧ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  have g₁ : f₀.base (pr'.base x) ∈ a₁.unop.1.2.1 := a₁.unop.2 h₁
  have g₂ : f₀.base (pr'.base x) ∈ a₂.unop.1.2.1 := a₂.unop.2 h₂
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := a₁.unop.1.2.1 ⊓ a₂.unop.1.2.1) ⟨g₁, g₂⟩
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ a₁.unop.1.1.1 ⊓ a₂.unop.1.1.1 ⊓ f₀ ⁻¹ᵁ V) ⟨⟨⟨hx, h₁⟩, h₂⟩, hxV⟩
  let a₃ : Pair f₀ := ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩
  refine ⟨Opposite.op a₃, ⟨(homOfLE (show a₃ ≤ a₁.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.1.2, fun z hz ↦ (hVW hz).1⟩))).op⟩,
    ⟨(homOfLE (show a₃ ≤ a₂.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.2, fun z hz ↦ (hVW hz).2⟩))).op⟩, hxV', fun z hz ↦ (hV'W hz).1.1.1⟩

end Pointwise

end GlobalTheory.Obs.BaseChg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentation
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_opens_preimage_eq_of_sqZero_aug (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
    (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀)
    (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (W : X₁.Opens) :
    ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  have hcomp : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun r ↦ q.commutes r
  have hsp : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  let i : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀))
    (by rw [Category.id_comp, Category.assoc, hsp, Category.comp_id])
  have hi1 : i ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hi2 : i ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (i ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hi1, hsp]; exact IsPullback.id_horiz s₀
  have hsq : IsPullback i s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hi2 hp
  have hsurj : Function.Surjective (q : R₁ →+* R₀) := fun r ↦ ⟨algebraMap R₀ R₁ r, q.commutes r⟩
  have hI : (RingHom.ker (q : R₁ →+* R₀)) ^ 2 = 0 := by
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro y hy y' hy'
    exact (Ideal.mem_bot).2 (hq y y' (RingHom.mem_ker.1 hy) (RingHom.mem_ker.1 hy'))
  have hisurj : Surjective i := surjective_of_isPullback_sqZero hI hsurj rfl hsq
  have key : ∀ x : X₁, i.base (pr.base x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hisurj.surj x
    have h : pr.base (i.base y) = y := by rw [← Scheme.Hom.comp_apply, hi1]; rfl
    rw [h]
  refine ⟨i ⁻¹ᵁ W, ?_⟩
  ext x
  change i.base (pr.base x) ∈ W ↔ x ∈ W
  rw [key]

end GlobalTheory.LiftSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentationStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  first | exact @GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | exact GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | (intros; apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsComparisonHomBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsComparisonHomBijective
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BaseChg

theorem beta_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀)
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens),
    Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) U.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.1)))
      (CommRingCat.ofHom (algebraMap R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)))) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R₀)) (Scheme.ΓSpecIso (CommRingCat.of R₁))
      (Iso.refl (CommRingCat.of (Sec s₀ U.1))) (Iso.refl (CommRingCat.of (Sec s₁ (pr ⁻¹ᵁ U.1)))) ?_ ?_ ?_ ?_
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · ext r
      change (s₀.appLE ⊤ U.1 le_top).hom r = (s₀.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom r))
      congr 1
      simp
    · ext r
      change (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) _).hom r = (s₁.appLE ⊤ (pr ⁻¹ᵁ U.1) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom r))
      congr 1
      simp
    · rfl
  have h1 := CommRingCat.isPushout_tensorProduct R₀ R₁ (Sec s₀ U.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (beta hp U) := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext r
      change algebraMap R₁ _ r = beta hp U (r ⊗ₜ 1)
      rw [beta_tmul, map_one, _root_.mul_one]
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext b
      change (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl).hom b = beta hp U (1 ⊗ₜ b)
      refine Eq.trans ?_ (beta_tmul hp U 1 b).symm
      rw [map_one, _root_.one_mul]
      rfl
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory.Obs.BaseChg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsComparisonHomBijectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeSectionsComparisonHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens), Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  first | exact @GlobalTheory.Obs.BaseChg.beta_bijective | exact GlobalTheory.Obs.BaseChg.beta_bijective | (intros; apply GlobalTheory.Obs.BaseChg.beta_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2Bijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2Bijective
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem restrict_pull2_bijective_of_basis (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X)
    (h1 : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U)
    (h2 : ∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 →
      x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
        x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) :
    Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let B : Set Γ(X, T.unop.1) :=
      {f | ∃ t : C', X.basicOpen f ≤ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t, hxt, htT⟩ := h1 x T.unop.1 hx
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := (G.obj t).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨t, hf, htT⟩⟩, hxf⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, T.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S u hu
      obtain ⟨t, hft, htT⟩ := hFB (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op f) at hu
      have hSf : S.unop.1 ≤ X.basicOpen f := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      refine ⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op,
        (homOfLE (show S.unop ≤ (G.obj t).unop from hSf.trans hft)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS : IsAffineOpen S.unop.1 := S.unop.2
    have hS₁ : S.unop.1 ≤ (G.obj t₁).unop.1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G.obj t₂).unop.1 := leOfHom a₂.unop
    let B : Set Γ(X, S.unop.1) :=
      {g | ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ X.basicOpen g ≤ (G.obj t₃).unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hS.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t₃, e₁, e₂, hxt, -⟩ := h2 t₁ t₂ x S.unop.1 hx (hS₁ hx) (hS₂ hx)
      obtain ⟨g, hg, hxg⟩ := hS.exists_basicOpen_le (V := (G.obj t₃).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ⟨t₃, e₁, e₂, hg⟩⟩, hxg⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, S.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S' u hu
      obtain ⟨t₃, e₁, e₂, hgt⟩ := hFB (F.equivFin.symm i).2
      set g : Γ(X, S.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
      have hS'g : S'.unop.1 ≤ X.basicOpen g := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      exact ⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hS'g.trans hgt)).op⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) G H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2BijectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  first | exact @GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | exact GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis | (intros; apply GlobalTheory.AbCoh.restrict_pull2_bijective_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtension
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Obs.BaseChg in
theorem GlobalTheory.Obs.extCoef_two_equiv : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  intro R₀ R₁ _ _ _ q hq
  have hres : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))),
      Function.Bijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2 := fun {X₀ X₁ s₀ s₁ pr} hp ↦
    GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ X₁ s₁ _ (preF hp) (preF_cover hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
      (preF_dir hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
  have hfwd : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))), Function.Bijective (fwd hp).pull2 :=
    fun {X₀ X₁ s₀ s₁ pr} hp ↦ ofNat_pull2_bijective _ _ _ (fun U ↦ GlobalTheory.T.baseChangeSectionsComparisonHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop)
  refine ⟨fun X₀ X₁ s₀ s₁ pr hp ↦
    (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm, ?_⟩
  intro X₀ X₁ s₀ s₁ pr hp Y₀ Y₁ t₀ t₁ pr' hp' f₀ f₁ h₀ h₁ hf c c' hE
  set d := ((AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm) c with hd0
  set d' := ((AddEquiv.ofBijective (CoefMap.restrict (OAff t₁) (preF hp')).pull2.toAddMonoidHom (hres hp')).trans
      (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).symm) c' with hd0'
  have hd : (fwd hp).pull2 d = (CoefMap.restrict (OAff s₁) (preF hp)).pull2 c :=
    (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).apply_symm_apply _
  have hd' : (fwd hp').pull2 d' = (CoefMap.restrict (OAff t₁) (preF hp')).pull2 c' :=
    (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).apply_symm_apply _
  clear_value d d'
  have A : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairPull h₁).pull2 c) =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairPull h₀)).pull2 d) := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairPull h₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff s₁) (preF hp)).comp (zMap hp hp' hf h₁)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c]
    rw [CoefMap.pullCohomologyTwo_comp, ← hd, ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp).comp (zMap hp hp' hf h₁))
      ((extMap R₁ (pairPull h₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairPull h₀) p) b) =
      GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (beta hp p.unop.1.2 b)
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec s₀ p.unop.1.2.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
    | tmul r a =>
      change beta hp' p.unop.1.1 (r ⊗ₜ[R₀] (coefHom (pairPull h₀) p a)) = _
      rw [beta_tmul hp p.unop.1.2 r a]
      erw [beta_tmul hp' p.unop.1.1 r]
      rw [map_mul]
      have hr : GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (algebraMap R₁ _ r) = algebraMap R₁ _ r := by
        have := semiHom_secPull h₁ (preP hp hp' hf p.unop) r 1
        rw [map_one, RingHom.id_apply, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at this
        exact this
      have e1 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1
        (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl)
      have e2 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1
        (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl (preP hp hp' hf p.unop).2)
      have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (e e'),
          (g.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e).hom a = (g'.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e').hom a := by
        rintro g _ rfl _ _; rfl
      rw [hr]
      congr 1
      exact e1.trans ((key _ _ hf.symm _ _).trans e2.symm)
    | add x y hx hy =>
      exact ((congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))).trans
        ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm
  have B : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 c') =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 d') := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairRes f₁ t₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff t₁) (preF hp')).comp (zRes hp hp' hf)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c']
    rw [CoefMap.pullCohomologyTwo_comp, ← hd', ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp').comp (zRes hp hp' hf))
      ((extMap R₁ (pairRes f₀ t₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d'
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = beta hp' p.unop.1.1 b
    congr 1
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec t₀ p.unop.1.1.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul r a => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  have hinj : Function.Injective (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 x
    obtain ⟨y0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 y
    have key : ∀ z, (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 z) =
        (CoefMap.restrict (OAff t₁) (preFP hp hp' hf ⋙ pairFst f₁)).pull2 z := fun z ↦ by
      rw [← CoefMap.pullCohomologyTwo_comp]
      exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun p ↦ 𝟙 _ } (fun p b ↦ mp_id _ _ b) z
    rw [key, key] at hxy
    have hW' := GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp'
    rw [(GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ Y₁ t₁ _ (preFP hp hp' hf ⋙ pairFst f₁) (preFP_cover hp hp' hf hW')
      (preFP_directed hp hp' hf hW')).1 hxy]
  apply hinj
  rw [A, B]
  exact congrArg _ hE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtensionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  first | exact @GlobalTheory.Obs.extCoef_two_equiv | exact GlobalTheory.Obs.extCoef_two_equiv | (intros; apply GlobalTheory.Obs.extCoef_two_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_of_primO2 (hO : PrimitiveStructureSheafDegTwoVanish) : PrimitiveExtendedDegTwoVanish := by
  intro R₀ R₁ _ _ _ q hq A _ g hA hsm c c₁ c₂ hμ h₁ h₂
  obtain ⟨B, _, pr, pr', hB, hBs, hp, hp', eμ, ef, es, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hA hsm
  obtain ⟨e, he⟩ := GlobalTheory.T.h2_structure_base_change_extension R₀ R₁ q hq
  set eX := e A.left B.left A.hom B.hom pr hp
  set eY := e (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
  have hc : c = eX (eX.symm c) := (eX.apply_symm_apply c).symm
  have hc₁ : c₁ = eY (eY.symm c₁) := (eY.apply_symm_apply c₁).symm
  have hc₂ : c₂ = eY (eY.symm c₂) := (eY.apply_symm_apply c₂).symm
  have hsum : c₁ + c₂ = eY (eY.symm c₁ + eY.symm c₂) := by rw [map_add (f := _), ← hc₁, ← hc₂]
  have hd : eX.symm c = 0 := by
    refine hO R₁ B g hB hBs (eX.symm c) (eY.symm c₁) (eY.symm c₂) ?_ ?_ ?_
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (μ[A]).left (μ[B]).left (overW μ[A]) (overW μ[B]) eμ _ _ ?_
      rw [← hc, ← hsum]; exact hμ
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (fst A A).left (fst B B).left (overW (fst A A)) (overW (fst B B)) ef _ _ ?_
      rw [← hc, ← hc₁]; exact h₁
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (snd A A).left (snd B B).left (overW (snd A A)) (overW (snd B B)) es _ _ ?_
      rw [← hc, ← hc₂]; exact h₂
  rw [hc, hd, map_zero]

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_extension : PrimitiveStructureSheafDegTwoVanish → PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_of_primO2 | exact GlobalTheory.Obs.primE2_of_primO2 | (intros; apply GlobalTheory.Obs.primE2_of_primO2 <;> assumption)
end
