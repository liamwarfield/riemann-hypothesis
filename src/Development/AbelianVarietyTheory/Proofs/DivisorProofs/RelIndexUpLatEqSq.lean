module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

theorem relIndex_prod_prod {G G' : Type} [AddGroup G] [AddGroup G'] (H K : AddSubgroup G) (H' K' : AddSubgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

variable {L : Type} [Field L] {n : ℕ}

def skewPair (σ : L →+* L) (θ d : L) :
    Matrix (Fin n) (Fin n) L →+ Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L :=
  AddMonoidHom.mk' (fun X => (X - θ • (X + adjJ σ X), d • (X + adjJ σ X))) (fun X Y => by
    ext i j <;> simp [adjJ] <;> ring)

theorem skewPair_injective (σ : L →+* L) (θ : L) {d : L} (hd : d ≠ 0) :
    Function.Injective (skewPair (n := n) σ θ d) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro X hX
  have h1 : X - θ • (X + adjJ σ X) = 0 := congrArg Prod.fst hX
  have h2 : d • (X + adjJ σ X) = 0 := congrArg Prod.snd hX
  have h3 : X + adjJ σ X = 0 := (smul_eq_zero.1 h2).resolve_left hd
  simpa [h3] using h1

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem map_skewPair_upLat {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    {θ d : L} (hθ : Valued.v θ ≤ 1) (hθ1 : θ + σ θ = 1) (hd : Valued.v d = 1) (hd1 : σ d = -d)
    {c : Fin n → Fin n → ℤ} (hc : ∀ i j, c j.rev i.rev = c i j) :
    (upLat L c).map (skewPair σ θ d) = (upLat L c ⊓ skewJ σ n).prod (upLat L c ⊓ skewJ σ n) := by
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  have hσθ : σ θ = 1 - θ := by linear_combination hθ1
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    have hs : X + adjJ σ X ∈ upLat L c := add_mem hX (adjJ_mem_upLat hv hc hX)
    refine ⟨⟨(upLat L c).sub_mem hX (smul_mem_upLat hθ hs), ?_⟩, ⟨smul_mem_upLat hd.le hs, ?_⟩⟩
    · show adjJ σ (X - θ • (X + adjJ σ X)) = -(X - θ • (X + adjJ σ X))
      rw [adjJ_sub, adjJ_smul, adjJ_add, adjJ_adjJ hσ, hσθ]
      module
    · show adjJ σ (d • (X + adjJ σ X)) = -(d • (X + adjJ σ X))
      rw [adjJ_smul, adjJ_add, adjJ_adjJ hσ, hd1]
      module
  · rintro ⟨A, B⟩ ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩
    have hA2 : adjJ σ A = -A := hA'
    have hB2 : adjJ σ B = -B := hB'
    have hv' : Valued.v (θ * d⁻¹) ≤ 1 := by simpa [hd] using hθ
    refine ⟨A + (θ * d⁻¹) • B, add_mem hA (smul_mem_upLat hv' hB), ?_⟩
    have key : A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B) = d⁻¹ • B := by
      rw [adjJ_add, adjJ_smul, hA2, hB2, map_mul, map_inv₀, hd1, hσθ, inv_neg]
      module
    show (A + (θ * d⁻¹) • B - θ • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B)),
      d • (A + (θ * d⁻¹) • B + adjJ σ (A + (θ * d⁻¹) • B))) = (A, B)
    rw [key, smul_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul, add_sub_cancel_right]

theorem relIndex_upLat_eq_sq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, c j.rev i.rev = c i j) →
    (∀ i j, C j.rev i.rev = C i j) → (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ((upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n)) ^ 2 := by
  intro L _ _ ϖ σ q n h c C hc hC _
  obtain ⟨⟨θ, hθ, hθ1⟩, d, hd, hd1⟩ := exists_trace_one h
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (skewPair_injective σ θ hd0),
    map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hc, map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hC,
    relIndex_prod_prod, sq]

end GlobalTheory.BorelUMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.ScalarExt

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

abbrev liftHom : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

def ext : Shv R ⥤ Shv S :=
  Sheaf.composeAndSheafify Scheme.etaleTopology.{0}
    (ModuleCat.extendScalars (liftHom φ) : ModuleCat.{1} (ULift.{1} R) ⥤ ModuleCat.{1} (ULift.{1} S))

def adj : ext φ ⊣ restr φ :=
  Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (liftHom φ))

instance : (ext φ).IsLeftAdjoint := (adj φ).isLeftAdjoint

instance : (ext φ).PreservesZeroMorphisms := inferInstance

def extCx : Cx R ⥤ Cx S := (ext φ).mapHomologicalComplex _

variable {φ}

def semiHom {I : Cx R} {J : Cx S} (σ : SemiMap I J)
    (hl : ∀ (U : Scheme.{0}) (s : ℤ) (r : ULift.{1} R) (a : Sec (I.X s) U), σ.app U s (r • a) = liftHom φ r • σ.app U s a)
    (s : ℤ) : I.X s ⟶ (restr φ).obj (J.X s) where
  hom :=
    { app := fun U => ModuleCat.ofHom (X := (I.X s).obj.obj U) (Y := ((restr φ).obj (J.X s)).obj.obj U)
        { toFun := fun a => σ.app U.unop s a
          map_add' := map_add _
          map_smul' := fun r a => hl U.unop s r a }
      naturality := fun U V g => by
        ext a
        exact (σ.nat g.unop s a).symm }

def semiBar {I : Cx R} {J : Cx S} (σ : SemiMap I J)
    (hl : ∀ (U : Scheme.{0}) (s : ℤ) (r : ULift.{1} R) (a : Sec (I.X s) U), σ.app U s (r • a) = liftHom φ r • σ.app U s a) :
    (extCx φ).obj I ⟶ J where
  f s := ((adj φ).homEquiv _ _).symm (semiHom σ hl s)
  comm' s t _ := by
    change _ ≫ J.d s t = (ext φ).map (I.d s t) ≫ _
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext U a
    change Sec.map (J.d s t) (σ.app U.unop s a) = σ.app U.unop t (Sec.map (I.d s t) a)
    exact σ.comm U.unop s t a

def unitSemi (I : Cx R) : SemiMap I ((extCx φ).obj I) where
  app U s := (((adj φ).unit.app (I.X s)).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    have h := ((adj φ).unit.app (I.X s)).hom.naturality g.op
    exact (congrArg (fun f => ModuleCat.Hom.hom f a) h).symm
  comm U s t a := by
    have h := (adj φ).unit.naturality (I.d s t)
    exact (congrArg (fun f : I.X s ⟶ (ext φ ⋙ restr φ).obj (I.X t) => ModuleCat.Hom.hom (f.hom.app (op U)) a) h).symm

theorem semi_factor {I : Cx R} {J : Cx S} (σ : SemiMap I J)
    (hl : ∀ (U : Scheme.{0}) (s : ℤ) (r : ULift.{1} R) (a : Sec (I.X s) U), σ.app U s (r • a) = liftHom φ r • σ.app U s a)
    (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    σ.app U s a = Sec.map ((semiBar σ hl).f s) ((unitSemi I).app U s a) := by
  have h := (adj φ).homEquiv_unit (I.X s) (J.X s) (((adj φ).homEquiv _ _).symm (semiHom σ hl s))
  rw [Equiv.apply_symm_apply] at h
  refine Eq.trans ?_ ((congrArg (fun f => (f.hom.app (op U)).hom a) h).trans ?_)
  · rfl
  · rfl

theorem zmod_semilinear {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {I : Cx (ZMod Q)} {J : Cx (ZMod q)} (σ : SemiMap I J)
    (U : Scheme.{0}) (s : ℤ) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) :
    σ.app U s (r • a) = liftHom (ZMod.castHom h (ZMod q)) r • σ.app U s a := by
  have hr : r = ((r.down.val : ℕ) : ULift.{1} (ZMod Q)) := ULift.ext (by
    first
    | rw [ULift.natCast_down, ZMod.natCast_zmod_val]
    | rw [ULift.down_natCast, ZMod.natCast_zmod_val])
  rw [hr, map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

end GlobalTheory.EtC.ScalarExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.BaseChangeColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}}
  (g' : D.obj j ⟶ B')

noncomputable def mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout g' (D.map k.hom) ⟶ pushout g' (D.map k'.hom) :=
  pushout.desc (pushout.inl g' (D.map k'.hom)) (D.map f.right ≫ pushout.inr g' (D.map k'.hom))
    (by rw [pushout.condition, ← Category.assoc, ← D.map_comp, Under.w f])

@[reassoc]
lemma inl_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f = pushout.inl g' (D.map k'.hom) :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f = D.map f.right ≫ pushout.inr g' (D.map k'.hom) :=
  pushout.inr_desc _ _ _

noncomputable def diag : Under j ⥤ CommRingCat.{0} where
  obj k := pushout g' (D.map k.hom)
  map f := mapPush D j g' f
  map_id k := by
    apply pushout.hom_ext
    · rw [inl_mapPush, Category.comp_id]
    · rw [inr_mapPush, Category.comp_id, Under.id_right, D.map_id, Category.id_comp]
  map_comp f f' := by
    apply pushout.hom_ext
    · rw [inl_mapPush, inl_mapPush_assoc, inl_mapPush]
    · rw [inr_mapPush, inr_mapPush_assoc, inr_mapPush, Under.comp_right, D.map_comp,
        Category.assoc]

noncomputable def inrNat : Under.forget j ⋙ D ⟶ diag D j g' where
  app k := pushout.inr g' (D.map k.hom)
  naturality k k' f := by
    show D.map f.right ≫ pushout.inr g' (D.map k'.hom) = pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inr_mapPush]

noncomputable def inlNat : (Functor.const _).obj B' ⟶ diag D j g' where
  app k := pushout.inl g' (D.map k.hom)
  naturality k k' f := by
    show 𝟙 B' ≫ pushout.inl g' (D.map k'.hom) = pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inl_mapPush, Category.id_comp]

noncomputable def toB (c : Cocone D) {B : CommRingCat.{0}} (h : B' ⟶ B) (g : c.pt ⟶ B)
    (sq : g' ≫ h = c.ι.app j ≫ g) : diag D j g' ⟶ (Functor.const _).obj B where
  app k := pushout.desc h (c.ι.app k.right ≫ g) (by rw [sq, ← c.w k.hom, Category.assoc])
  naturality k k' f := by
    show mapPush D j g' f ≫ pushout.desc h (c.ι.app k'.right ≫ g) _ =
      pushout.desc h (c.ι.app k.right ≫ g) _ ≫ 𝟙 B
    apply pushout.hom_ext
    · rw [inl_mapPush_assoc, pushout.inl_desc, pushout.inl_desc_assoc, Category.comp_id]
    · rw [inr_mapPush_assoc, pushout.inr_desc, pushout.inr_desc_assoc, Category.comp_id,
        ← Category.assoc, c.w]

theorem exists_isColimit_pushout_under : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (B' B : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B) (g : c.pt ⟶ B), IsPushout g' (c.ι.app j) h g → ∃ (D' : Under j ⥤ CommRingCat.{0}) (ι : D' ⟶ (Functor.const _).obj B) (u : Under.forget j ⋙ D ⟶ D') (v : (Functor.const _).obj B' ⟶ D'), Nonempty (IsColimit (Cocone.mk B ι)) ∧ ∀ k : Under j, IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ι.app k = h ∧ u.app k ≫ ι.app k = c.ι.app k.right ≫ g := by
  intro J _ _ D c hc j B' B g' h g hsq
  refine ⟨diag D j g', toB D j g' c h g hsq.w, inrNat D j g', inlNat D j g', ⟨?_⟩,
    fun k => ⟨IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩⟩
  have hc' : IsColimit (c.whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  let k0 : Under j := Under.mk (𝟙 j)

  let e : ∀ (s : Cocone (diag D j g')) (k : Under j), pushout g' (D.map k.hom) ⟶ s.pt :=
    fun s k => s.ι.app k
  have he : ∀ (s : Cocone (diag D j g')) {k k' : Under j} (f : k ⟶ k'),
      mapPush D j g' f ≫ e s k' = e s k := fun s _ _ f => s.w f
  let r : Cocone (diag D j g') → Cocone (Under.forget j ⋙ D) := fun s =>
    { pt := s.pt, ι := inrNat D j g' ≫ s.ι }
  have hl : ∀ (s : Cocone (diag D j g')) (k : Under j),
      pushout.inl g' (D.map k.hom) ≫ e s k = pushout.inl g' (D.map k0.hom) ≫ e s k0 := by
    intro s k
    rw [← he s (Under.homMk k.hom (Category.id_comp k.hom) : k0 ⟶ k), inl_mapPush_assoc]
  have hfr : ∀ (s : Cocone (diag D j g')) (k : Under j),
      c.ι.app k.right ≫ hc'.desc (r s) = pushout.inr g' (D.map k.hom) ≫ e s k :=
    fun s k => hc'.fac (r s) k
  have hw : ∀ s : Cocone (diag D j g'),
      g' ≫ (pushout.inl g' (D.map k0.hom) ≫ e s k0) = c.ι.app j ≫ hc'.desc (r s) := by
    intro s
    rw [show c.ι.app j = c.ι.app k0.right from rfl, hfr, ← Category.assoc, pushout.condition,
      Category.assoc]
    exact (congrArg (· ≫ (pushout.inr g' (D.map k0.hom) ≫ e s k0)) (D.map_id j)).trans
      (Category.id_comp _)
  exact
    { desc := fun s => hsq.desc _ _ (hw s)
      fac := fun s k => by
        change pushout.desc _ _ _ ≫ _ = e s k
        apply pushout.hom_ext
        · rw [pushout.inl_desc_assoc, hsq.inl_desc, hl s k]
        · rw [pushout.inr_desc_assoc, Category.assoc, hsq.inr_desc, hfr]
      uniq := fun s m hm => by
        have hm' : ∀ k : Under j, pushout.desc h (c.ι.app k.right ≫ g)
            (by rw [hsq.w, ← c.w k.hom, Category.assoc]) ≫ m = e s k := hm
        apply hsq.hom_ext
        · rw [hsq.inl_desc, ← hm' k0, pushout.inl_desc_assoc]
        · rw [hsq.inr_desc]
          apply hc'.hom_ext
          intro k
          change c.ι.app k.right ≫ g ≫ m = c.ι.app k.right ≫ hc'.desc (r s)
          rw [hfr, ← hm' k, pushout.inr_desc_assoc, Category.assoc] }

end GlobalTheory.BaseChangeColim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrank
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.FundId

variable {k F : Type} [Field k] [Field F] [Algebra k F]

noncomputable def toRing (v : Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top := by
    intro h
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le

theorem valuation_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by
  refine GroundTheory.FunctionField.valuation_eq_of_isEquiv ?_ (toRing v).valuation_surjective v.2.1
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [GroundTheory.FunctionField.Place.valuation_le_one_iff]
  rfl

theorem ord_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by
  unfold ord
  rw [← valuation_toRing]
  rfl

theorem toRing_injective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := fun v w h =>
  Subtype.ext (by rw [← valuation_toRing, ← valuation_toRing, h])

theorem toRing_surjective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by
  intro w
  refine ⟨⟨w.valuation, w.valuation_surjective, fun c hc => ?_⟩, ?_⟩
  · exact w.valuation_algebraMap' hc
  · ext x
    exact w.valuation_le_one_iff x

theorem deg_eq_one [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by
  have h : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have e : k ≃ₗ[k] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField) h
  have := e.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm

theorem sum_ord_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hF ρ hρ v π _ hπ
  classical
  haveI : GroundTheory.FunctionField.IsFunctionField k F := ⟨hF⟩
  haveI : GroundTheory.FunctionField.IsFunctionField k E :=
    GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional (k := k) (K := F)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have key : ∀ p : Place k E, ρ p = v ↔ (toRing p).LiesOver (toRing v) := by
    intro p
    have h1 : (toRing p).LiesOver (toRing (ρ p)) := by
      ext x
      exact hρ p x
    constructor
    · rintro rfl; exact h1
    · intro h
      exact toRing_injective (GroundTheory.FunctionField.Place.ext (h1.symm.trans h))
  have hfin := (toRing v).finite_liesOver (K' := E)
  have hfin' : {p | ρ p = v}.Finite := by
    refine (hfin.preimage toRing_injective.injOn).subset fun p hp => (key p).1 hp
  refine ⟨hfin', ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← (toRing v).sum_ramificationIdx_mul_inertiaDeg (K' := E),
    Nat.cast_sum]
  refine Finset.sum_bij (fun p _ => toRing p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [key] using hp
  · intro p _ q _ h
    exact toRing_injective h
  · intro w hw
    obtain ⟨p, rfl⟩ := toRing_surjective w
    exact ⟨p, by simpa [key] using hw, rfl⟩
  · intro p hp
    have h : (toRing p).LiesOver (toRing v) := by simpa [key] using hp
    rw [← ord_toRing, h.ord_algebraMap, ord_toRing, hπ, GroundTheory.FunctionField.Place.inertiaDeg,
      deg_eq_one, deg_eq_one]
    simp

end GlobalTheory.Nef.FundId
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrankStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  first | exact @GlobalTheory.Nef.FundId.sum_ord_eq_finrank | exact GlobalTheory.Nef.FundId.sum_ord_eq_finrank | (intros; apply GlobalTheory.Nef.FundId.sum_ord_eq_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprod
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def biprodPresheaf (P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (P₁.obj U × P₂.obj U)
  map f := ModuleCat.ofHom ((P₁.map f).hom.prodMap (P₂.map f).hom)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

theorem secBiprod_total (M N : Shv R) (U : Scheme.{0}) (y : Sec (M ⊞ N) U) :
    y = Sec.map (biprod.inl : M ⟶ M ⊞ N) (Sec.map biprod.fst y) + Sec.map (biprod.inr : N ⟶ M ⊞ N) (Sec.map biprod.snd y) := by
  conv_lhs => rw [show y = (((𝟙 (M ⊞ N)) : M ⊞ N ⟶ M ⊞ N).hom.app (op U)).hom y from rfl, ← biprod.total]
  rfl

theorem secBiprod_inl_fst (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = a := by
  change ((biprod.inl ≫ biprod.fst : M ⟶ M).hom.app (op U)).hom a = a
  rw [biprod.inl_fst]; rfl

theorem secBiprod_inr_fst (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = 0 := by
  change ((biprod.inr ≫ biprod.fst : N ⟶ M).hom.app (op U)).hom b = 0
  rw [biprod.inr_fst]; rfl

theorem secBiprod_inl_snd (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = 0 := by
  change ((biprod.inl ≫ biprod.snd : M ⟶ N).hom.app (op U)).hom a = 0
  rw [biprod.inl_snd]; rfl

theorem secBiprod_inr_snd (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = b := by
  change ((biprod.inr ≫ biprod.snd : N ⟶ N).hom.app (op U)).hom b = b
  rw [biprod.inr_snd]; rfl

noncomputable section

def biprodPresheafMap {M N : Shv R} {P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ₁ : P₁ ⟶ M.obj) (φ₂ : P₂ ⟶ N.obj) :
    biprodPresheaf P₁ P₂ ⟶ (M ⊞ N).obj where
  app U := ModuleCat.ofHom (LinearMap.coprod (((biprod.inl : M ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₁.app U).hom)
    (((biprod.inr : N ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₂.app U).hom))
  naturality U V f := by
    ext ⟨a, b⟩
    have h1 := congrArg (fun g => ModuleCat.Hom.hom g a) (φ₁.naturality f)
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g b) (φ₂.naturality f)
    have h3 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₁.app U).hom a)) ((biprod.inl : M ⟶ M ⊞ N).hom.naturality f)
    have h4 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₂.app U).hom b)) ((biprod.inr : N ⟶ M ⊞ N).hom.naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1 h2 h3 h4
    change (((biprod.inl : M ⟶ M ⊞ N).hom).app V).hom ((φ₁.app V).hom ((P₁.map f).hom a)) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app V).hom ((φ₂.app V).hom ((P₂.map f).hom b)) =
      ((M ⊞ N).obj.map f).hom ((((biprod.inl : M ⟶ M ⊞ N).hom).app U).hom ((φ₁.app U).hom a) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app U).hom ((φ₂.app U).hom b))
    rw [map_add (f := _), h1, h2, h3, h4]

theorem secRes_secMap {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  exact h.symm

theorem flatS_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  intro R _ M N ⟨P₁, φ₁, s₁, i₁, f₁⟩ ⟨P₂, φ₂, s₂, i₂, f₂⟩
  refine ⟨biprodPresheaf P₁ P₂, biprodPresheafMap φ₁ φ₂, ?_, ?_, ?_⟩
  · intro U y
    obtain ⟨S, hS, hS'⟩ := s₁ U (Sec.map biprod.fst y)
    obtain ⟨T, hT, hT'⟩ := s₂ U (Sec.map biprod.snd y)
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    obtain ⟨x₁, hx₁⟩ := hS' V g hg.1
    obtain ⟨x₂, hx₂⟩ := hT' V g hg.2
    refine ⟨(x₁, x₂), ?_⟩
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op V)).hom x₁) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op V)).hom x₂) = Sec.res g y
    rw [hx₁, hx₂, ← secRes_secMap, ← secRes_secMap, ← map_add (f := _)]
    exact congrArg (Sec.res g) (secBiprod_total M N U y).symm
  · rintro U ⟨a, b⟩ hx
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op U)).hom a) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op U)).hom b) = 0 at hx
    have ha : (φ₁.app (op U)).hom a = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.fst : M ⊞ N ⟶ M) (x + y) =
          Sec.map biprod.fst x + Sec.map biprod.fst y := fun x y => map_add _ x y
      have z : Sec.map (biprod.fst : M ⊞ N ⟶ M) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.fst : M ⊞ N ⟶ M)) hx
      rwa [e, secBiprod_inl_fst, secBiprod_inr_fst, add_zero, z] at h
    have hb : (φ₂.app (op U)).hom b = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.snd : M ⊞ N ⟶ N) (x + y) =
          Sec.map biprod.snd x + Sec.map biprod.snd y := fun x y => map_add _ x y
      have z : Sec.map (biprod.snd : M ⊞ N ⟶ N) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.snd : M ⊞ N ⟶ N)) hx
      rwa [e, secBiprod_inl_snd, secBiprod_inr_snd, zero_add, z] at h
    obtain ⟨S, hS, hS'⟩ := i₁ U a ha
    obtain ⟨T, hT, hT'⟩ := i₂ U b hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    change ((P₁.map g.op).hom a, (P₂.map g.op).hom b) = 0
    rw [hS' V g hg.1, hT' V g hg.2]
    rfl
  · intro U hU
    haveI := f₁ U hU
    haveI := f₂ U hU
    exact GlobalTheory.flat_prod (R := ULift.{1} R) (A := P₁.obj (op U)) (B := P₂.obj (op U))

end

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  first | (exact @GlobalTheory.EtC.flatS_biprod) | (exact GlobalTheory.EtC.flatS_biprod) | (intros; apply GlobalTheory.EtC.flatS_biprod  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtaleCoverDescent


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout {R S T P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (H : IsPushout f g inl inr) (x : Spec S) (y : Spec T)
    (hxy : Spec.map f x = Spec.map g y) : ∃ z : Spec P, Spec.map inl z = x := by
  have hP := isPullback_SpecMap_of_isPushout f g inl inr H
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
  exact hw

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_of_filtered_colimit (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c) {B : CommRingCat.{0}}
    (g : c.pt ⟶ B) (hg : g.hom.Etale) :
    ∃ (j : J) (B' : CommRingCat.{0}) (a : D.obj j ⟶ B') (h : B' ⟶ B),
      a.hom.Etale ∧ IsPushout a (c.ι.app j) h g := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale c.pt B := hg
  obtain ⟨j, A, _, _, hA, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  refine ⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A),
    CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp
      Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr hA
  · refine (CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      rfl
    · ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact e.commutes x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_at_later_index_of_range {J : Type} [SmallCategory J]
    {D : J ⥤ CommRingCat.{0}} (c : Cocone D) {k k' : J} (f : k ⟶ k') {B B' : CommRingCat.{0}}
    {g : c.pt ⟶ B} {a : D.obj k ⟶ B'} {h : B' ⟶ B} (ha : a.hom.Etale)
    (H : IsPushout a (c.ι.app k) h g) :
    ∃ (B'' : CommRingCat.{0}) (a' : D.obj k' ⟶ B'') (h' : B'' ⟶ B),
      a'.hom.Etale ∧ IsPushout a' (c.ι.app k') h' g ∧
      ∀ p : Spec (D.obj k'), Spec.map (D.map f) p ∈ Set.range (Spec.map a) →
        p ∈ Set.range (Spec.map a') := by
  have hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h := by
    rw [H.w, ← c.w f, Category.assoc]
  refine ⟨pushout (D.map f) a, pushout.inl (D.map f) a,
    pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩
  · exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha
  · have top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a) :=
      (IsPushout.of_hasPushout (D.map f) a).flip
    have big : IsPushout a (D.map f ≫ c.ι.app k')
        (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g := by
      rw [c.w f, pushout.inr_desc]
      exact H
    exact big.of_top (pushout.inl_desc _ _ _) top
  · rintro p ⟨v, hv⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm
    exact ⟨z, hz⟩


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (ι : Type) [Finite ι] (B : ι → CommRingCat.{0}) (g : ∀ i, c.pt ⟶ B i), (∀ i, (g i).hom.Etale) → (∀ p : Spec c.pt, ∃ i v, Spec.map (g i) v = p) → ∀ j₀ : J, ∃ (j : J) (_ : j₀ ⟶ j) (B' : ι → CommRingCat.{0}) (g' : ∀ i, D.obj j ⟶ B' i) (h : ∀ i, B' i ⟶ B i), (∀ i, (g' i).hom.Etale ∧ IsPushout (g' i) (c.ι.app j) (h i) (g i)) ∧ ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g' i) v = p := by
  intro J _ _ D c hc ι _ B g hg hsurj j₀
  classical
  have := Fintype.ofFinite ι
  choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)
  let O : Finset J := insert j₀ (Finset.univ.image jm)
  let j1 := IsFiltered.sup O ∅
  have f0 : j₀ ⟶ j1 := IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)
  have fm : ∀ i, jm i ⟶ j1 := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)
  let W : Set (Spec (D.obj j1)) := {q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ := by
      ext q
      simp [W]
    rw [hWe, isClosed_compl_iff]
    refine isOpen_iUnion fun i => ?_
    have : Etale (Spec.map (a1 i)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact ha1 i
    exact (Spec.map (a1 i)).isOpenMap.isOpen_range
  have claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W := by
    by_contra hcon
    push_neg at hcon
    haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) :=
      fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))
    obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1)
      (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W)
      (fun i hij => hW.preimage (Spec.map _).continuous)
      (fun i hij => hcon _ hij.unop)
      (fun i hij => (hW.preimage (Spec.map _).continuous).isCompact)
      (fun i i' hi'i hij x hx => by
        change Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]
        exact hx)
    have hs1 : Spec.map (c.ι.app j1) s ∈ W := by
      have := hs (op j1) (𝟙 _)
      change Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this
      simpa [D.map_id, Spec.map_id] using this
    obtain ⟨i, v, rfl⟩ := hsurj s
    refine hs1 i ⟨Spec.map (h1 i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]
  obtain ⟨k, f, hk⟩ := claim
  choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)
  refine ⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩
  have hp := hk p
  simp only [W, Set.mem_setOf_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨v, hv⟩ := hpt i p hi
  exact ⟨i, v, hv⟩

end GlobalTheory.EtaleCoverDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod.UpLatIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ordBall (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (k : ℤ) : AddSubgroup L where
  carrier := {x | (Valued.v x : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-k)}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by simpa using hx

theorem mem_ordBall {k : ℤ} {x : L} : x ∈ ordBall L k ↔ Valued.v x ≤ WithZero.exp (-k) := Iff.rfl

theorem ordBall_mono {k K : ℤ} (h : k ≤ K) : ordBall L K ≤ ordBall L k :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.2 (neg_le_neg h))

theorem lt_one_iff (a : WithZero (Multiplicative ℤ)) : a < 1 ↔ a ≤ WithZero.exp (-1) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem relIndex_ordBall_succ {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (ordBall L (k + 1)).relIndex (ordBall L k) =
      Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hp : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := fun m => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  have hle : ∀ (x : L) (a m : ℤ), Valued.v (x * ϖ ^ m) ≤ WithZero.exp (-(a + m)) ↔ Valued.v x ≤ WithZero.exp (-a) :=
    fun x a m => by
      rw [map_mul, hp, neg_add, WithZero.exp_add]
      exact mul_le_mul_iff_left₀ (zero_lt_iff.2 WithZero.exp_ne_zero)
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hm : ∀ x : ordBall L k, x.1 * ϖ ^ (-k) ∈ O := fun x => by
    have := (hle x.1 k (-k)).2 x.2
    rw [add_neg_cancel, neg_zero, WithZero.exp_zero] at this
    exact this
  let g : ordBall L k →+ O :=
    { toFun := fun x => ⟨x.1 * ϖ ^ (-k), hm x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul] }
  let f : ordBall L k →+ O ⧸ IsLocalRing.maximalIdeal O :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).toAddMonoidHom.comp g
  have hf : Function.Surjective f := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y.1 * ϖ ^ k ∈ ordBall L k := by
      have := (hle y.1 0 k).2 (by rw [neg_zero, WithZero.exp_zero]; exact y.2)
      simpa [mem_ordBall] using this
    refine ⟨⟨_, hy⟩, ?_⟩
    change Ideal.Quotient.mk _ (g ⟨_, hy⟩) = _
    congr 1
    ext
    change y.1 * ϖ ^ k * ϖ ^ (-k) = y.1
    rw [mul_assoc, ← zpow_add₀ h0]; simp
  have hc : (ordBall L (k + 1)).addSubgroupOf (ordBall L k) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    change _ ↔ Ideal.Quotient.mk _ (g x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff, lt_one_iff, mem_ordBall,
      ← hle x.1 (k + 1) (-k)]
    have : -(k + 1 + -k) = -1 := by ring
    rw [this]; rfl
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top]

theorem relIndex_ordBall {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {k K : ℤ} (hk : k ≤ K) :
    (ordBall L K).relIndex (ordBall L k) = (q ^ 2) ^ (K - k).toNat := by
  obtain ⟨-, -, -, hϖ, -, -, hq⟩ := h
  obtain ⟨m, rfl⟩ := Int.le.dest hk
  have e : ∀ m : ℕ, (k + m - k).toNat = m := fun m => by omega
  rw [e]
  clear hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (ordBall L (k + m + 1)).relIndex (ordBall L (k + m)) = q ^ 2 :=
      (relIndex_ordBall_succ hϖ (k + m)).trans hq
    have h2 := AddSubgroup.relIndex_mul_relIndex (ordBall L (k + m + 1)) (ordBall L (k + m)) (ordBall L k)
      (ordBall_mono (by omega)) (ordBall_mono (by omega))
    rw [Nat.cast_succ, ← add_assoc, ← h2, h1, ih, pow_succ' (q ^ 2)]

theorem relIndex_upLat_eq_prod {n : ℕ} (c C : Fin n → Fin n → ℤ) :
    (upLat L C).relIndex (upLat L c) =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (ordBall L (C p.1.1 p.1.2)).relIndex (ordBall L (c p.1.1 p.1.2)) := by
  let f : upLat L c →+ (∀ p : {p : Fin n × Fin n // p.1 < p.2}, ordBall L (c p.1.1 p.1.2) ⧸
      (ordBall L (C p.1.1 p.1.2)).addSubgroupOf (ordBall L (c p.1.1 p.1.2))) :=
    { toFun := fun x p => QuotientAddGroup.mk ⟨x.1 p.1.1 p.1.2, x.2.2 _ _ p.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i j => if h : i < j then ((y ⟨(i, j), h⟩).out : L) else 0, fun i j h => dif_neg (not_lt.2 h),
      fun i j h => ?_⟩, funext fun p => ?_⟩
    · simp only [dif_pos h]
      exact (y ⟨(i, j), h⟩).out.2
    · refine Eq.trans ?_ (y p).out_eq
      exact congrArg QuotientAddGroup.mk (Subtype.ext (dif_pos p.2))
  have hc : (upLat L C).addSubgroupOf (upLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_upLat]
    constructor
    · intro h p
      exact (QuotientAddGroup.eq_zero_iff _).2 (h.2 _ _ p.2)
    · intro h
      exact ⟨x.2.1, fun i j e => (QuotientAddGroup.eq_zero_iff _).1 (h ⟨(i, j), e⟩)⟩
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem relIndex_upLat : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (q ^ 2) ^ (C p.1 p.2 - c p.1 p.2).toNat := by
  intro L _ _ ϖ σ q n h c C hc
  rw [relIndex_upLat_eq_prod, Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2) _ (by simp)]
  exact Finset.prod_congr rfl fun p _ => relIndex_ordBall h (hc _ _ p.2)

end GlobalTheory.BorelUMod.UpLatIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmul
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem map_mul_left_eq_norm_smul (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  obtain ⟨b, -, -⟩ := hE.basis
  have : FiniteDimensional F E := Module.Finite.of_basis b
  let T : E ≃ₗ[F] E :=
    { LinearMap.mulLeft F (z : E) with
      invFun := fun x => ((z⁻¹ : Eˣ) : E) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have hT : LinearEquiv.det T = Units.map (Algebra.norm F : E →* F) z := by
    ext
    rw [LinearEquiv.coe_det, Units.coe_map, Algebra.norm_apply]
    rfl
  rw [← hT]
  exact GlobalTheory.T.map_linearEquiv_addHaar_localField F E μ T

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmulStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ), μ.map (fun x => (z : E) * x) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_mul_left_eq_norm_smul | exact GlobalTheory.KSp.map_mul_left_eq_norm_smul | (intros; apply GlobalTheory.KSp.map_mul_left_eq_norm_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory.Nef

def symMat {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun a i => ((C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a

theorem symMat_mulVec {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by
  funext a
  simp only [Matrix.mulVec, dotProduct, symMat, Matrix.of_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm]

theorem symMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by
  ext a i
  simp only [symMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add (f := _)]

def twistAt {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : Place k F → Matrix (Fin n) (Fin n) F := by
  classical
  exact fun v => if v = v₀ then c • h v else h v

theorem twistAt_self {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : twistAt v₀ c h v₀ = c • h v₀ := by
  simp [twistAt]

theorem twistAt_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (v : Place k F) (hv : v ≠ v₀) :
    twistAt v₀ c h v = h v := by
  simp [twistAt, hv]

end GlobalTheory.Nef
end
end
