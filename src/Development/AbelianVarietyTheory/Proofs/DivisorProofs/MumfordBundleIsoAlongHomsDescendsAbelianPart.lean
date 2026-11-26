module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructures
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructures
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

namespace GlobalTheory.HomMumAdd

variable {S : Scheme.{0}}

theorem prod_mumford {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum G (x2 G) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift x y).left ≫ (psum G (x2 G) I.down).left =
      (psum G ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem prod_pair (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ I : MK, h ((lift x y).left ≫ mφ H₁ H₂ a b I) ^ mε I =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  refine prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_mumford (x ≫ a) (y ≫ b) fun q => h (q ≫ coprod.inr))
    have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) = lift (x ≫ a) (y ≫ b) := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
    refine congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) ?_
    rw [← e, Over.comp_left, Category.assoc, Category.assoc]
    rfl
  · refine Eq.trans ?_ (congrArg (·⁻¹) (prod_mumford x y fun q => h (q ≫ coprod.inl)))
    refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (Finset.prod_inv_distrib _)
    refine (zpow_neg _ _).trans (congrArg (fun q => (h q ^ ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹) ?_)
    exact (Category.assoc _ _ _).symm

theorem pair_add_of_surj : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ c₁ c₂ hL sj f g _ _ u hu T z J hJ x x' y
  let p₀ := x3 H₁ 0
  let p₁ := x3 H₁ 1
  let p₂ := x3 H₁ 2
  have mf : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have P₁ := isPart_inl L₁.L L₂.L
  have P₂ := isPart_inr L₁.L L₂.L
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J → ∀ a b : T ⟶ H₁,
      val (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let e : 𝟙_ (Over S) ⟶ G3 H₁ := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have he : e.left ≫ (H₁ ⊗ H₁ ⊗ H₁).hom = 𝟙 _ := Over.w e
  let ρ : T ⟶ G3 H₁ := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ : G3 H₁ ⟶ H₁) (l₁ l₂ l₃ : G3 H₁ ⟶ H₂),
      (∀ (V : Type) [CommGroup V] (k : (G3 H₁ ⟶ H₁) → V) (l : (G3 H₁ ⟶ H₂) → V),
        (l (l₁ * l₂ * l₃) * (l (l₁ * l₂))⁻¹ * (l (l₁ * l₃))⁻¹ * (l (l₂ * l₃))⁻¹ * l l₁ * l l₂ * l l₃ * (l 1)⁻¹) *
          (((l ((a₁ ≫ f) * (b₁ ≫ g)) * (l (a₁ ≫ f))⁻¹ * (l (b₁ ≫ g))⁻¹ * l 1) *
              (k (a₁ * b₁) * (k a₁)⁻¹ * (k b₁)⁻¹ * k 1)⁻¹) *
            ((l ((a₂ ≫ f) * (b₂ ≫ g)) * (l (a₂ ≫ f))⁻¹ * (l (b₂ ≫ g))⁻¹ * l 1) *
              (k (a₂ * b₂) * (k a₂)⁻¹ * (k b₂)⁻¹ * k 1)⁻¹)) =
        ((l ((a ≫ f) * (b ≫ g)) * (l (a ≫ f))⁻¹ * (l (b ≫ g))⁻¹ * l 1) *
              (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1)⁻¹) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 →
      val u (lift (ρ ≫ a) (ρ ≫ b)).left z J * cubV c₁ z (rl J) (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c₂ z (rr J) (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) *
          (val u (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J * val u (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H₁) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J →
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left)
          (P₁.gen (LB.pullGen L₁.L (thφ H₁ (x3 H₁)) thε c₁.t (lift k₁ (lift k₂ k₃)).left))) σ.left z J =
          val u (lift (σ ≫ a) (σ ≫ b)).left z J * cubV c₁ z (rl J) (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _
          (P₂.gen (LB.pullGen L₂.L (thφ H₂ (x3 H₂)) thε c₂.t (lift l₁ (lift l₂ l₃)).left))
          (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₁ b₁).left)
            (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c₂ z (rr J) (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val u (lift (σ ≫ a₁) (σ ≫ b₁)).left z J * val u (lift (σ ≫ a₂) (σ ≫ b₂)).left z J) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
          ((P₁.val_gen _ _ z hJ).trans (val_cub c₁ σ (P₁.good hJ) _ _ _))),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((P₂.val_gen _ _ z hJ).trans (val_cub c₂ σ (P₂.good hJ) _ _ _))
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (P₁.gen_isGen (pullGen_isGen _ _ _ _ c₁.isGen _)))
      (mulGen_isGen _ _ _ _ _ _ _ (P₂.gen_isGen (pullGen_isGen _ _ _ _ c₂.isGen _)) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ hu.1 _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (prod_sum₂ (K := thK) (K' := MK ⊕ MK) (U := V) _ (prod_cub l₁ l₂ l₃ fun q => k (q ≫ coprod.inr))
        (prod_sum₂ (K := MK) (K' := MK) (U := V) _ (prod_pair f g a₁ b₁ k) (prod_pair f g a₂ b₂ k))).trans
        ((hF V (fun q => k (q.left ≫ coprod.inl)) (fun q => k (q.left ≫ coprod.inr))).trans
          (prod_sum₂ (K := MK) (K' := thK) (U := V) _ (prod_pair f g a b k)
          (prod_cub k₁ k₂ k₃ fun q => k (q ≫ coprod.inl))).symm)
    · have C₁ : IsCub (cubV c₁ y (rl I)) := isCub_cubV c₁ (P₁.good hI)
      have C₂ : IsCub (cubV c₂ y (rr I)) := isCub_cubV c₂ (P₂.good hI)
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, hl, hu.2 y I hI, C₁.face, C₂.face]
      simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ p₂ (p₀ ≫ f) (p₁ ≫ f) (p₂ ≫ g) (fun V _ k l => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (by rw [← Category.assoc, e₀, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ f) (p₀ ≫ g) (p₁ ≫ g) (fun V _ k l => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (by rw [← Category.assoc, e₂, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

end GlobalTheory.HomMumAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructuresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homMumfordGenerator_additive_cubicalStructures : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  first | exact @GlobalTheory.HomMumAdd.pair_add_of_surj | exact GlobalTheory.HomMumAdd.pair_add_of_surj | (intros; apply GlobalTheory.HomMumAdd.pair_add_of_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomMumfordGeneratorNormalisedOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomMumfordGeneratorNormalisedOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem prod_alt_const {U : Type} [CommGroup U] (m : U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), m ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => m ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp

theorem lift_one_psum {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ psum G (x2 G) I = 1 := by
  rw [comp_psum]
  have e : (fun k => lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ x2 G k) = fun _ => (1 : T ⟶ G) := by
    funext k
    fin_cases k <;> simp [x2]
  rw [e]
  unfold psum
  induction ((List.finRange 2).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem kappa_comp_mφ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (k : MK) :
    (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₂).left ≫ coprod.inr) (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₁).left ≫ coprod.inl) k := by
  rcases k with I | I
  · simp only [mφ, Sum.elim_inl]
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc,
      lift_snd_assoc, MonObj.one_comp, MonObj.one_comp, lift_one_psum]
  · simp only [mφ, Sum.elim_inr]
    rw [← Category.assoc, ← Over.comp_left, lift_one_psum]

theorem exists_isNrm : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b]
    (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen →
    ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ hL a b _ _ t ht
  have p : ∀ (V : Type) [CommGroup V] (k : ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) → V),
      ∏ i : MK, k ((lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b i) ^ mε i = 1 := by
    intro V _ k
    rw [Fintype.prod_sum_type]
    simp only [kappa_comp_mφ, Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
    rw [prod_alt_const, prod_alt_const, inv_one, _root_.mul_one]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := mφ H₁ H₂ a b) (ε' := mε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := MK) (K' := MK) (U := V) _
        (c := ∏ i, k (mφ H₁ H₂ a b i) ^ mε i) rfl (DVR.prod_neg _ _ (p V k))) ?_
      simp)
    (LB.mulGen _ _ _ _ _ t (LB.invGen _ _ _ (LB.pullGen _ _ _ t (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  have e : (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left ≫ (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left =
      (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end GlobalTheory.HomMum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomMumfordGeneratorNormalisedOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homMumfordGenerator_normalised_origin : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen → ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  first | exact @GlobalTheory.HomMum.exists_isNrm | exact GlobalTheory.HomMum.exists_isNrm | (intros; apply GlobalTheory.HomMum.exists_isNrm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


open GlobalTheory.HomMum in
theorem GlobalTheory.HomMum.lbIso_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  intro R _ _ _ _ hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ f g fB gB _ _ _ _ of og H
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := hG₁.geomConnected
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht, -⟩ := exists_gen_of_iso (isPart_inr U₁.LG.L U₂.LG.L) (isPart_inl U₁.LG.L U₂.LG.L) w hw
  have hN := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_homMumfordGenerator_normalised_origin hN f g t ht
  have sj := (FamGerm.surjective_appTop_sq_cube U₁.toUnifPre).2
  have hP : AbLaw.IsProjBy D₁.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)
  obtain ⟨V, hV, t', ht'⟩ := GlobalTheory.EndRosati.loc_gen_of_thickenings hGF (maximalIdeal R) _
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D₁.toPre.P.isAb D₁.toPre.P.isAb)
    (AbLaw.isProjBy_tensor R _ _ hP hP) (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun e => by
      have := EndTorus.connectedSpace_thickening (maximalIdeal R) e
      have : GeometricallyConnected (thickObj R (maximalIdeal R) e G₁).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G₁.hom (thick R (maximalIdeal R) e)))
      have : ConnectedSpace (thickObj R (maximalIdeal R) e G₁).left :=
        GroupConn.connectedSpace_of_section (thickObj R (maximalIdeal R) e G₁).hom
          (η : 𝟙_ _ ⟶ thickObj R (maximalIdeal R) e G₁).left (Over.w _)
      exact GlobalTheory.T.exists_mumfordGenerator_abelianPart_at_level U₁.toUnifPre U₂.toUnifPre e (of e) (og e) u hu
        fun T z J hJ x x' y => GlobalTheory.T.homMumfordGenerator_additive_cubicalStructures U₁.cubG U₂.cubG hN sj f g u hu T z J hJ x x' y) (closedPoint R)
  have hall : ∀ p : PrimeSpectrum R, p ∈ V := fun p =>
    ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.isPrime.ne_top)).mem_open V.isOpen hV
  obtain ⟨t'', ht'', -⟩ := glue_gen (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun _ : Unit => (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom ⁻¹ᵁ V) (fun y => ⟨(), hall _⟩) (fun _ => t') (fun _ => ht')
    (fun _ _ Z r r' z J _ h => by
      obtain rfl := (cancel_mono _).1 h
      rfl)
  obtain ⟨w', hw', -⟩ := exists_iso_of_gen (isPart_inr D₁.toPre.P.L D₂.toPre.P.L) (isPart_inl D₁.toPre.P.L D₂.toPre.P.L)
    D₂.toPre.P.isLB D₁.toPre.P.isLB (snd_surjective D₁.toPre.P.isLB) (fst_surjective D₂.toPre.P.isLB) t'' ht''
  exact ⟨w', hw'⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  first | exact @GlobalTheory.HomMum.lbIso_descends | exact GlobalTheory.HomMum.lbIso_descends | (intros; apply GlobalTheory.HomMum.lbIso_descends <;> assumption)
end
