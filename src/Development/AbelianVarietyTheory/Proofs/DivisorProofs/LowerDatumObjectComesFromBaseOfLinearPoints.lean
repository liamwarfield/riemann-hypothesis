module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBala
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRingLinearHomSchemeLowerObject

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricBalancedGeneratorPsiZeroLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativ
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymTau
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem gen_eq₂ (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb Lr.L φ ε)} {u' : LB.Gen (LB.LinComb Lr.L φ' ε')}
    (hu : u.IsGen) (hu' : u'.IsGen) (h0 : ∀ y J, Good Lr.L y J → val u (zero2 A) y J = val u' (zero2 A) y J)
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val u (lift x y).left z J = val u' (lift x y).left z J := by
  have he : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
  have hp : Function.Surjective (A ⊗ A).hom.appTop.hom := by
    have := surj_comp (surj_snd hG hA A) ((hG _ _ hA).2)
    rwa [Over.w (snd A A)] at this
  exact gen_unique' Lr.isLB hF (A ⊗ A).hom (zero2 A) he hp hu hu' h0 T.left (lift x y).left z J hJ

omit [IsCommMonObj A] in
theorem val_zero2 {f g : A ⟶ A} (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {y : (𝟙_ (Over S)).left} {J}
    (hJ : Good Lr.L y J) : val u (zero2 A) y J = 1 := by
  have := val_corr hJ h₀ (𝟙 _)
  rwa [val_pull hJ, Category.id_comp, val_one] at this

theorem ros_swap (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A g f) rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ u' z J y x * val₂ u z J x y = 1 := by
  have hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (lift (snd A A) (fst A A)).left) u) (lift x y).left z J =
        val₂ u' z J y x * val₂ u z J x y := fun hJ x y => by
    refine (val_mul hJ _ _ _).trans ?_
    rw [val_pull hJ, ← Over.comp_left, comp_lift, lift_snd, lift_fst]; rfl
  refine (hv hJ x y).symm.trans ((gen_eq₂ hG hA (u' := LB.oneGen Lr.L) (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu' _) hu)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    (fun y I hI => ?_) hJ x y).trans (val_one _))
  · have p₁ := prod_ros g f (snd A A) (fst A A) h
    have p₂ := prod_ros f g (fst A A) (snd A A) h
    rw [lift_fst_snd] at p₂
    simp only [Over.id_left, Category.id_comp] at p₂
    refine (Fintype.prod_empty _).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)
    rw [mul_comm (snd A A ≫ g) (fst A A), mul_comm (snd A A) (fst A A ≫ f)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · have := hv hI η[A] η[A]
    simp only [val₂] at this
    rw [this, val_zero2 u' h₀' hI, val_zero2 u h₀ hI, _root_.mul_one, val_one]

theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f₁ g₁ f₂ g₂ : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁]
    [IsMonHom f₂] [IsMonHom g₂] (hf : f₁ * f₂ = 𝟙 A) (hg : g₁ * g₂ = 𝟙 A)
    (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (hu₁ : u₁.IsGen)
    (h₁ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L))
    (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)) (hu₂ : u₂.IsGen)
    (h₂ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (y w : T ⟶ A) :
    val₂ u₁ z J y w * val₂ u₂ z J y w = cubV c z J (w ≫ g₁) (w ≫ g₂) y * (cubV c z J (y ≫ f₁) (y ≫ f₂) w)⁻¹ := by
  let t := LB.mulGen Lr.L _ _ _ _
    (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (snd A A ≫ g₁) (lift (snd A A ≫ g₂) (fst A A))).left)
    (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left))
  have hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val t (lift x y).left z J = cubV c z J (y ≫ g₁) (y ≫ g₂) x * (cubV c z J (x ≫ f₁) (x ≫ f₂) y)⁻¹ := fun hJ x y => by
    refine (val_mul hJ _ _ _).trans ?_
    refine congrArg₂ (· * ·) ((val_cub c _ hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg _ ((val_cub c _ hJ _ _ _).trans ?_)))
    · simp only [lift_snd_assoc, lift_fst]
    · simp only [lift_fst_assoc, lift_snd]
  have hm : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ u₁ u₂) (lift x y).left z J = val₂ u₁ z J x y * val₂ u₂ z J x y :=
    fun hJ x y => val_mul hJ _ _ _
  refine (hm hJ y w).symm.trans ((gen_eq₂ hG hA (u' := t) (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₁ hu₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)))
    (fun y I hI => ?_) hJ y w).trans (hv hJ y w))
  · have p₁ := prod_ros f₁ g₁ (fst A A) (snd A A) h
    have p₂ := prod_ros f₂ g₂ (fst A A) (snd A A) h
    rw [lift_fst_snd] at p₁ p₂
    simp only [Over.id_left, Category.id_comp] at p₁ p₂
    refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := U) _ (prod_cub _ _ _ h)
      (DVR.prod_neg _ _ (prod_cub _ _ _ h))).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)
    have e₁ : (snd A A ≫ g₁) * (snd A A ≫ g₂) = snd A A := by rw [← MonObj.comp_mul, hg, Category.comp_id]
    have e₂ : (fst A A ≫ f₁) * (fst A A ≫ f₂) = fst A A := by rw [← MonObj.comp_mul, hf, Category.comp_id]
    rw [e₁, e₂, mul_comm (snd A A) (fst A A), mul_comm (snd A A ≫ g₁) (fst A A), mul_comm (snd A A ≫ g₂) (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have := hv hI η[A] η[A]
    rw [this]
    refine (val_mul hI _ _ _).trans ?_
    rw [val_zero2 u₁ h₁ hI, val_zero2 u₂ h₂ hI, _root_.mul_one]
    have C := isCub_cubV c hI
    have o : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
    simp only [o, MonObj.one_comp, C.face, inv_one, _root_.mul_one]

theorem exists_tauSum {T : Over S} (x a b w : T ⟶ A) (e : a * b = w)
    (t₁ : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts x a) GlobalTheory.PolDeg.negε)) (ht₁ : t₁.IsGen)
    (t₂ : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts b x) GlobalTheory.PolDeg.negε)) (ht₂ : t₂.IsGen) :
    ∃ t : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts x w) GlobalTheory.PolDeg.negε), t.IsGen ∧
      ∀ p J, Good Lr.L p J → val t (𝟙 _) p J = val t₁ (𝟙 _) p J * val t₂ (𝟙 _) p J * (cubV c p J a b x)⁻¹ := by
  subst e
  obtain ⟨t, ht, hv⟩ := exists_gen Lr.isLB (φ' := GlobalTheory.PolDeg.lamPts x (a * b)) (ε' := GlobalTheory.PolDeg.negε)
    (fun U _ h => by
      refine (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ rfl rfl) (DVR.prod_neg _ _ (prod_cub a b x h))).trans ?_
      simp only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      rw [mul_comm x a, mul_comm x (a * b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen Lr.L _ _ _ _ (LB.mulGen Lr.L _ _ _ _ t₁ t₂)
      (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift a (lift b x)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ ht₂)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)))
  refine ⟨t, ht, fun p J hJ => ?_⟩
  have hc := val_cub c (𝟙 T) hJ a b x
  simp only [Over.id_left, Category.id_comp] at hc
  refine (hv _ _ p J hJ).trans ((val_mul hJ _ _ _).trans ?_)
  rw [val_mul hJ]
  exact congrArg (_ * ·) ((val_inv (z := p) (J := J) _ _).trans (congrArg (·⁻¹) hc))

end GlobalTheory.SymTau

namespace GlobalTheory.SymTau

section Alg
variable {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (C : IsCub θ)
include C

theorem alg_first (Y Y' a b : G) (v₁ v₂ x₁ x₂ y₁ y₂ : U) (h₁ : v₁ * θ Y Y' a = x₁ * x₂) (h₂ : v₂ * θ Y Y' b = y₁ * y₂) :
    v₁ * v₂ * (θ a b (Y * Y'))⁻¹ * θ Y Y' (a * b) = x₁ * y₁ * (θ a b Y)⁻¹ * (x₂ * y₂ * (θ a b Y')⁻¹) := by
  have k := C.compat Y Y' a b
  have sA := (C.s12 a b (Y * Y')).trans (C.s01 _ _ _)
  have sB := (C.s12 a b Y).trans (C.s01 _ _ _)
  have sC := (C.s12 a b Y').trans (C.s01 _ _ _)
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁; have a₂ := congrArg Additive.ofMul h₂; have ak := congrArg Additive.ofMul k
  have aA := congrArg Additive.ofMul sA; have aB := congrArg Additive.ofMul sB; have aC := congrArg Additive.ofMul sC
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ak aA aB aC ⊢
  linear_combination (norm := abel) a₁ + a₂ - ak - aA + aB + aC

theorem alg_second (Y a a' b b' : G) (v₁ v₂ x₁ x₂ y₁ y₂ : U) (h₁ : v₁ * θ a a' Y = x₁ * x₂)
    (h₂ : v₂ * θ b b' Y = y₁ * y₂) :
    v₁ * v₂ * (θ (a * a') (b * b') Y)⁻¹ * θ (a * b) (a' * b') Y = x₁ * y₁ * (θ a b Y)⁻¹ * (x₂ * y₂ * (θ a' b' Y)⁻¹) := by
  have k₁ := C.coc (a * b) a' b' Y
  have k₂ := C.coc a b a' Y
  have k₃ := C.coc (a * a') b b' Y
  have k₄ := C.coc a a' b Y
  rw [mul_right_comm a b a'] at k₁
  rw [mul_comm b a'] at k₂
  have s := C.s01 b a' Y
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁; have a₂ := congrArg Additive.ofMul h₂
  have b₁ := congrArg Additive.ofMul k₁; have b₂ := congrArg Additive.ofMul k₂
  have b₃ := congrArg Additive.ofMul k₃; have b₄ := congrArg Additive.ofMul k₄; have bs := congrArg Additive.ofMul s
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ b₃ b₄ bs ⊢
  linear_combination (norm := abel) a₁ + a₂ - b₁ + b₂ + b₃ - b₄ + bs

theorem alg_bal (Y Ya a b p q : G) (v₁ v₂ w₁ w₂ uz ua ub ub' : U) (e₁ : v₁ * ua = w₁) (e₂ : w₂ * ub' = v₂)
    (ra : uz * θ Y p q = θ Ya a b * (ua * ub)) (sw : ub' * ub = 1) :
    v₁ * v₂ * (θ a b Ya)⁻¹ * uz = w₁ * w₂ * (θ p q Y)⁻¹ := by
  have s₁ := (C.s12 a b Ya).trans (C.s01 _ _ _)
  have s₂ := (C.s12 p q Y).trans (C.s01 _ _ _)
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁; have a₂ := congrArg Additive.ofMul e₂; have a₃ := congrArg Additive.ofMul ra
  have a₄ := congrArg Additive.ofMul sw; have c₁ := congrArg Additive.ofMul s₁; have c₂ := congrArg Additive.ofMul s₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ c₂ ⊢
  linear_combination (norm := abel) a₁ - a₂ + a₃ + a₄ - c₁ + c₂

theorem alg_symm (Y Z a b a' b' : G) (v₁ v₂ v₃ v₄ u₁ u₁' u₀ : U) (e₁ : v₄ * u₁ = v₁) (e₂ : v₂ * u₁' = v₃)
    (sw : u₁' * u₀ = 1) (sm : u₁ * u₀ = θ a b Y * (θ b' a' Z)⁻¹) :
    v₁ * v₂ * (θ a b Y)⁻¹ = v₃ * v₄ * (θ a' b' Z)⁻¹ := by
  have s := C.s01 b' a' Z
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁; have a₂ := congrArg Additive.ofMul e₂; have a₃ := congrArg Additive.ofMul sw
  have a₄ := congrArg Additive.ofMul sm; have c₁ := congrArg Additive.ofMul s
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ ⊢
  linear_combination (norm := abel) -a₁ + a₂ - a₃ + a₄ - c₁

end Alg

end GlobalTheory.SymTau

namespace GlobalTheory.SymTau

theorem symm_of_bal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') →
    (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    ∀ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ →
    ∃ τ' : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ' ∧
      ∀ y z p J, Good M.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J := by
  intro R _ _ B _ _ hA M cub O _ _ act hros X _ _ c cadd clin w0 hw τ hτ
  obtain ⟨hgen, hadd1, hadd2, hbal⟩ := hτ
  have hG := GlobalTheory.globalFns_holds
  have cw : ∀ z, c (w0 • z) * c (star w0 • z) = c z := fun z => by rw [← cadd, ← add_smul, hw, one_smul]
  choose τ' hτ'g hτ'v using fun y z => exists_tauSum cub (c y) (c (w0 • z)) (c (star w0 • z)) (c z) (cw z)
    (τ y (w0 • z)) (hgen _ _) (τ (star w0 • z) y) (hgen _ _)
  refine ⟨τ', ⟨hτ'g, ?_, ?_, ?_⟩, ?_⟩
  · intro y y' z p J hJ
    have ey : cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c (y + y')) =
        cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c y * c y') := by rw [cadd]
    have ez : cubV cub p J (c y) (c y') (c z) = cubV cub p J (c y) (c y') (c (w0 • z) * c (star w0 • z)) := by
      rw [cw z]
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, ey, ez]
    exact alg_first (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ (hadd1 y y' (w0 • z) p J hJ)
      (hadd2 (star w0 • z) y y' p J hJ)
  · intro y z z' p J hJ
    have v₁ : val (τ y (w0 • (z + z'))) (𝟙 _) p J = val (τ y (w0 • z + w0 • z')) (𝟙 _) p J := by rw [smul_add]
    have v₂ : val (τ (star w0 • (z + z')) y) (𝟙 _) p J = val (τ (star w0 • z + star w0 • z') y) (𝟙 _) p J := by
      rw [smul_add]
    have ea : cubV cub p J (c (w0 • (z + z'))) (c (star w0 • (z + z'))) (c y) =
        cubV cub p J (c (w0 • z) * c (w0 • z')) (c (star w0 • z) * c (star w0 • z')) (c y) := by
      rw [smul_add, smul_add, cadd, cadd]
    have ez : cubV cub p J (c z) (c z') (c y) =
        cubV cub p J (c (w0 • z) * c (star w0 • z)) (c (w0 • z') * c (star w0 • z')) (c y) := by rw [cw z, cw z']
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, v₁, v₂, ea, ez]
    exact alg_second (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ (hadd2 y (w0 • z) (w0 • z') p J hJ)
      (hadd1 (star w0 • z) (star w0 • z') y p J hJ)
  · intro a u hu hu0 y z p J hJ
    haveI := act.hom a
    haveI := act.hom (star a)
    obtain ⟨ub, hub, hub0⟩ := exists_ros hG hA M.isLB (act.act (star a)) (act.act a)
      (by simpa only [star_star] using hros (star a))
    have hb := hbal (star a)
    rw [star_star] at hb
    have q₁ : star a • w0 • z = w0 • star a • z := smul_comm _ _ _
    have q₂ : star a • star w0 • z = star w0 • star a • z := smul_comm _ _ _
    have e₁ := hbal a u hu hu0 y (w0 • z) p J hJ
    have e₂ := hb ub hub hub0 (star w0 • z) y p J hJ
    have ra := (ros_add cub hG hA (act.act a) (act.act (star a)) u hu hu0 hJ (c (w0 • z)) (c (star w0 • z)) (c y)).2
    have sw := ros_swap hG hA (act.act a) (act.act (star a)) u hu hu0 ub hub hub0 hJ (c y) (c (star w0 • z))
    simp only [val₂] at ra sw
    rw [← clin, ← clin, ← clin, q₁, q₂, cw z] at ra
    rw [q₁] at e₁
    rw [q₂] at e₂
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]
    exact alg_bal (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ ra sw
  · intro y z p J hJ
    haveI := act.hom w0
    haveI := act.hom (star w0)
    obtain ⟨u₀, hu₀, hu₀0⟩ := exists_ros hG hA M.isLB (act.act w0) (act.act (star w0)) (hros w0)
    obtain ⟨u₁, hu₁, hu₁0⟩ := exists_ros hG hA M.isLB (act.act (star w0)) (act.act w0)
      (by simpa only [star_star] using hros (star w0))
    have hb := hbal (star w0)
    rw [star_star] at hb
    have e₁ := hb u₁ hu₁ hu₁0 y z p J hJ
    have e₂ := hb u₁ hu₁ hu₁0 z y p J hJ
    have sw := ros_swap hG hA (act.act w0) (act.act (star w0)) u₀ hu₀ hu₀0 u₁ hu₁ hu₁0 hJ (c y) (c z)
    have hf : act.act (star w0) * act.act w0 = 𝟙 B := by
      rw [← act.map_one, ← hw, add_comm]; exact (act.map_add _ _).symm
    have hg : act.act w0 * act.act (star w0) = 𝟙 B := by
      rw [← act.map_one, ← hw]; exact (act.map_add _ _).symm
    have sm := ros_sum cub hG hA (act.act (star w0)) (act.act w0) (act.act w0) (act.act (star w0)) hf hg u₁ hu₁ hu₁0
      u₀ hu₀ hu₀0 hJ (c y) (c z)
    simp only [val₂] at sw sm
    rw [← clin, ← clin, ← clin, ← clin] at sm
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]
    exact alg_symm (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ sw sm

end GlobalTheory.SymTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') →
    (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    ∀ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ →
    ∃ τ' : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ' ∧
      ∀ y z p J, Good M.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J := by
  first | exact @GlobalTheory.SymTau.symm_of_bal | exact GlobalTheory.SymTau.symm_of_bal | (intros; apply GlobalTheory.SymTau.symm_of_bal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

namespace GenTr

theorem stalkMap_gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z)
    (J : (Z ⟶ X) → L.ι) :
    val t q z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) := by
  subst hq
  rw [val_of t g (r z) _ (fun k => J ((r ≫ g) ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (stalkMap_gm_comp r g z _ _).symm

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

end GenTr

open GenTr

theorem rlaws_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  intro R _ _ D₀ O _ _ _ onB hc w0 uw huw hnw ψ hR
  obtain ⟨hgen, h1, h2, h3, h4⟩ := hR
  have hL := D₀.P.isLB
  have htu := toUnit_TK_left R
  let Dn : DegPre R := { D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _ }
  have Fψ : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ y,
      val (Dn.psi y) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val (ψ y) (𝟙 _) ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ y => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp) _ _)
  have Frig : ∀ (z : (TK R).left) J, Good D₀.P.L z J →
      val Dn.rigK (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (rigV D₀ ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp [htu]) _ _)
  have Ftau : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a b : D₀.X,
      val (Dn.tau a b) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (tauV D₀ ψ ((jK R) z) (fun f => J (jK R ≫ f)) a b) := by
    intro z J hJ a b
    rw [val_tau Dn hJ, Fψ z J hJ, Fψ z J hJ, Fψ z J hJ, Frig z J hJ, tauV, map_mul, map_mul, map_mul, map_inv, map_inv,
      map_inv]
    rfl
  have Fx : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K] (φ : K → (D₀.P.A.left ⟶ D₀.P.A.left))
      (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.xK y)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val t (D₀.c y).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp]
    show _ = (toUnit (TK R) ≫ D₀.c y).left
    rw [Over.comp_left, htu]
  have F2 : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K]
      (φ : K → ((D₀.P.A ⊗ D₀.P.A).left ⟶ D₀.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y y' : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.pt2 y y')) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val t (lift (D₀.c y) (D₀.c y')).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y y'
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt2, ← htu, ← Over.comp_left, comp_lift]
  have Fcub : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a a' b : D₀.X,
      val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val D₀.cub.t (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ a a' b
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt3, ← htu, ← Over.comp_left, comp_lift, comp_lift]
  refine ⟨fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _, ⟨onB, hc, ?_⟩, rfl, ?_, ?_, ⟨uw, huw, hnw, ?_⟩, ?_⟩
  · intro a u hu hun y y'
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Ftau z J hJ, F2 z J hJ, Ftau z J hJ, ← map_mul]
    exact congrArg _ (h3 a u hu hun y y' _ _ fun f => hJ _)
  · intro χ
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Fψ z J hJ, Fx z J hJ, Fψ z J hJ, ← map_mul]
    exact congrArg _ (h2 χ _ _ fun f => hJ _)
  · intro a a' b
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau (a + a') b) (𝟙 _) z J *
        val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
          val (Dn.tau a b) (𝟙 _) z J * val (Dn.tau a' b) (𝟙 _) z J := by
      rw [Ftau z J hJ, Fcub z J hJ, Ftau z J hJ, Ftau z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h1 a a' b _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau y (w0 • y)) (𝟙 _) z J * val (LB.pullGen D₀.P.L _ _ uw (Dn.xK y)) (𝟙 _) z J =
        val (Dn.psi y) (𝟙 _) z J * val Dn.rigK (𝟙 _) z J := by
      rw [Ftau z J hJ, Fx z J hJ, Fψ z J hJ, Frig z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h4 y _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y j V _ _ hV h
    have hle : V ≤ LB.wchart D₀.P.L (fun _ : PUnit => (D₀.c y).left) j :=
      fun x hx => Set.mem_iInter.2 fun _ => hV hx
    refine ⟨(res hle ((ψ y).s j)).val, Units.isUnit _, ?_⟩
    have e := congrArg (fun q => q.hom ((ψ y).s j).val) ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.trans ?_
    show _ = ((TK R).left.presheaf.map (homOfLE h).op).hom (((TK R).left.presheaf.map (homOfLE _).op).hom
      (((jK R).app _).hom ((ψ y).s j).val))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.UTau0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationPreData_laws_of_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  first | exact @GlobalTheory.UTau0.rlaws_transfer | exact GlobalTheory.UTau0.rlaws_transfer | (intros; apply GlobalTheory.UTau0.rlaws_transfer <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

theorem exists_symmetric_balanced_generator_psi_zero_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O]
    [StarRing O] [Module O D₀.X] [Module.Projective O D₀.X] [Module.Finite O D₀.X] (onB : D₀.P.OAct O),
    (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    (∃ u : LB.Gen (LB.LinComb D₀.P.L (K := Fin 4) ![(padd D₀.P.A (𝟙 _) (onB.act w0)).left, 𝟙 D₀.P.A.left,
        (onB.act w0).left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left] ![1, -2, -1, 2]),
      u.IsGen ∧ LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (eSec D₀.P.A)) (LB.oneGen D₀.P.L)) →
    ∃ (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => ptK (D₀.c y)) (fun _ => -1)))
      (h : ∀ y, (ψ y).IsGen),
      letI : Module O ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).X := ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).OAct O, oa.onB = onB ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) y Set.univ := by
  intro R _ _ _ D₀ O _ _ _ _ _ onB hlin w0 hw ⟨uw, huw, huw0⟩
  have cadd : ∀ y y' : D₀.X, D₀.c (y + y') = D₀.c y * D₀.c y' := fun y y' => D₀.c_add y y'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_balanced_bimultiplicative_generator_lambda_inv R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O onB.toRingAct
    onB.rosati D₀.X D₀.c cadd hlin
  obtain ⟨τ', hτ', hτs⟩ := GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O
    onB.toRingAct onB.rosati D₀.X D₀.c cadd hlin w0 hw τ hτ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced R D₀ O onB hlin w0 hw uw huw huw0 τ' hτ' hτs
  obtain ⟨h, rest⟩ := GlobalTheory.T.degenerationPreData_laws_of_generator_values R D₀ O onB hlin w0 uw huw huw0 ψ hψ
  exact ⟨_, h, rest⟩

end GlobalTheory.UTau0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTriple
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBaseData

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  intro E _ _ _ H W _ _ _ t hp hA hK ⟨g, hg⟩ X _ _ _ _ x₀ hadd hlin
  letI := H.starRing
  let P := GlobalTheory.GenericPol.toPolAV t g hg hp hA hK
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ t.PP).1 t.sym
  have hψ0 : ∀ y : X, ∃ ψ : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (x₀ y)) (fun _ => -1)), ψ.IsGen :=
    fun y => ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := FractionRing W) P.L P.isLB _ _
  choose ψ hψ using hψ0
  let D₀ : DegPre W :=
    { P := P, rig := t.PP.rig, rig_gen := t.PP.rigGen, cub := t.cub, sym := sym, sym_gen := hsym, sym_rig := hsym',
      X := X, c := x₀, c_add := hadd, psi := ψ, psi_gen := hψ }
  letI : Module (𝓞 E) D₀.X := ‹Module (𝓞 E) X›
  haveI : Module.Projective (𝓞 E) D₀.X := GlobalTheory.PointStepCompare.projective_of_free E (X := X)
  haveI : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  have := t.act.hom H.w0
  let onB : D₀.P.OAct (𝓞 E) := ⟨t.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj t⟩
  obtain ⟨u, hu, hu0⟩ := GlobalTheory.ArcCM.CxFibre.exists_primGen t.PP (t.act.act H.w0) t.prim
  obtain ⟨ψ', hψ', oa, hoa, he, hb, hw, hU⟩ := GlobalTheory.UTau0.exists_symmetric_balanced_generator_psi_zero_localRing W D₀ (𝓞 E) onB hlin H.w0
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) ⟨u, hu, hu0⟩
  refine ⟨{ D₀ with psi := ψ', psi_gen := hψ' }, ‹Module (𝓞 E) X›, oa, 𝟙 _, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hb
  · exact hU
  · exact hw
  · refine ⟨GlobalTheory.PolDeg.Wit.grpPullback_id t.G, fun a => ?_, GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen t.PP.isLB⟩
    rw [hoa]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro y
    exact Category.comp_id _

end GlobalTheory.UBaseData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generating_degenerationData_principalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  first | exact @GlobalTheory.UBaseData.main | exact GlobalTheory.UBaseData.main | (intros; apply GlobalTheory.UBaseData.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem lowBase_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hadd hlin
  obtain ⟨W, _, _, _, b, o, x₀, θ₀, m, hft, hadd₀, hlin₀, hloc, hcomp, hx, ⟨fR, fE⟩, hdim⟩ :=
    GlobalTheory.T.exists_localRing_linearHomScheme_lowerObject D' c V bV o' X x hadd hlin
  haveI : IsProper o.t.G.hom := o.proper
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim W o.t.G
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper _ o.t.semi)
  obtain ⟨D, hmod, oa, φB, e, hev, hbi, hgen, hw0, hab, hc⟩ :=
    GlobalTheory.T.exists_generating_degenerationData_principalTriple W o.t o.proper o.ample o.ktriv ⟨g, hg⟩ X x₀ hadd₀ hlin₀
  letI := hmod
  haveI hiso : IsIso φB := hab.1.1.isIso_fst_of_isIso
  refine ⟨⟨W, b, hft, o, D, oa, hev, hbi, hgen, hw0, φB, hab, ?_, ?_, ?_⟩, θ₀, e, m, hloc, hcomp, ?_⟩
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z h₁ h₂ hz
    refine fR A f₁ f₂ hf o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · intro k _ f o'' m₁ m₂ z h₁ h₂ hz
    refine fE k f o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · obtain ⟨a, t, h1, h2, h3⟩ := hdim
    exact ⟨a, t, h1, h2, by rw [h3, LinearEquiv.finrank_eq e]⟩
  · intro y
    show (x y).left ≫ m.toSABMap.φ ≫ φB = spMap θ₀ ≫ (D.c (e y)).left
    rw [← hc y, ← Category.assoc, hx y, Category.assoc]

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  first | exact @GlobalTheory.UCanon.lowBase_of_linearPoints | exact GlobalTheory.UCanon.lowBase_of_linearPoints | (intros; apply GlobalTheory.UCanon.lowBase_of_linearPoints <;> assumption)
end
