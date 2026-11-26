module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierEqOfPrimitiveAdjointBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerDataTensorBundleIsoWithPsiValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem cPoint_sum (T : Over (Sp R)) {K : Type} [Fintype K] (n : K → ℤ) (b : K → D.X) :
    DVR.cP D T (∑ i, n i • b i) = ∏ i, DVR.cP D T (b i) ^ n i := by
  let f : D.X →+ Additive (T ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (DVR.cP D T a)) (fun a b => by
      rw [DVR.cPoint_add]; rfl)
  apply Additive.ofMul.injective
  have e : Additive.ofMul (DVR.cP D T (∑ i, n i • b i)) = ∑ i, n i • f (b i) :=
    (map_sum f (fun i => n i • b i) Finset.univ).trans (Finset.sum_congr rfl fun i _ => map_zsmul f _ _)
  rw [e, ofMul_prod]
  simp only [ofMul_zpow]
  rfl

theorem val_tau_zero_right (hB : D.TauBimult) (a : D.X) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) : val (D.tau a 0) (𝟙 _) z J = 1 := by
  have C : IsCub (DVR.th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB 0 0 a
  have c0 : DVR.cP D (TK R) 0 = 1 := by
    have := DVR.cPoint_add D (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have s := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a 0
  simp only [Over.id_left] at s e
  rw [add_zero, c0, C.face, _root_.mul_one] at e
  rw [s]
  exact mul_eq_left.1 e.symm

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

theorem oneGen_isGen' : (LB.oneGen D.P.L (Y := T.left)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem expand_zero (hB : D.TauBimult) : Expand D (0 : K → ℤ) x y := by
  obtain ⟨κ, hκ, hv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (0 : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((0 : K → ℤ) k.1 * Oε k.2)))
    (fun U _ h => by
      simp [Fintype.prod_sum_type, lamPts, Oε, Fin.prod_univ_four])
    (LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'
  refine ⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_one]
  have e0 : (∑ i, (0 : K → ℤ) i • b i) = 0 := by simp
  have e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (0 : K → ℤ) i) = 1 := by simp
  rw [e0, e1, _root_.mul_one]
  exact val_tau_zero_right hB a hJ

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

theorem prod_exp_add {U : Type} [CommGroup U] (f : K × Fin 4 → U) (w w' : K → ℤ) :
    ∏ k, f k ^ (-((w + w') k.1 * Oε k.2)) = (∏ k, f k ^ (-(w k.1 * Oε k.2))) * ∏ k, f k ^ (-(w' k.1 * Oε k.2)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add, Pi.add_apply]
  congr 1
  ring

theorem prod_zpow_add (w w' : K → ℤ) : ∏ i, y i ^ (w + w') i = (∏ i, y i ^ w i) * ∏ i, y i ^ w' i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]

theorem formEq_add (w w' : K → ℤ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)) k) =
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w k.1 * Oε k.2)) k) *
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)) k) *
      ∏ I : thK, h ((lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I := by
  rw [prod_cub, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_exp_add (fun k => h (lamPts x (y k.1) k.2)) w w', prod_zpow_add y w w']
  generalize (∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w k.1 * Oε k.2))) = P
  generalize (∏ k : K × Fin 4, h (lamPts x (y k.1) k.2) ^ (-(w' k.1 * Oε k.2))) = P'
  generalize (∏ i, y i ^ w i) = Y
  generalize (∏ i, y i ^ w' i) = Y'
  have e1 : x * (Y * Y') = Y * Y' * x := mul_comm _ _
  have e2 : x * Y = Y * x := mul_comm _ _
  have e3 : x * Y' = Y' * x := mul_comm _ _
  simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e1, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

theorem comp_prod_cP {p : TK R ⟶ T} {b : K → D.X} (hy : ∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) (w : K → ℤ) :
    p ≫ ∏ i, y i ^ w i = DVR.cP D (TK R) (∑ i, w i • b i) := by
  rw [comp_prod_zpow, cPoint_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [hy i]; rfl

theorem val_tau_add_right (hB : D.TauBimult) (a B B' : D.X) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    val (D.tau a (B + B')) (𝟙 _) z J * cubV D.cub z J (DVR.cP D (TK R) B) (DVR.cP D (TK R) B') (DVR.cP D (TK R) a) =
      val (D.tau a B) (𝟙 _) z J * val (D.tau a B') (𝟙 _) z J := by
  have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB B B' a
  have s1 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a (B + B')
  have s2 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B
  have s3 := GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a B'
  simp only [Over.id_left] at e s1 s2 s3
  rw [s1, s2, s3]
  exact e

theorem sum_add_smul (w w' : K → ℤ) (b : K → D.X) : ∑ i, (w + w') i • b i = ∑ i, w i • b i + ∑ i, w' i • b i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]

theorem expand_add (hB : D.TauBimult) {w w' : K → ℤ} (h₁ : Expand D w x y) (h₂ : Expand D w' x y) :
    Expand D (w + w') x y := by
  obtain ⟨κ, hκ, hv⟩ := h₁
  obtain ⟨κ', hκ', hv'⟩ := h₂
  obtain ⟨κ₂, hκ₂, hv₂⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)))
    (fun U _ h => by
      exact ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans
        (formEq_add x y w w' h).symm)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ κ')
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ hκ') (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
  refine ⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩
  have c := val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x
  rw [comp_prod_cP y hy w, comp_prod_cP y hy w', hx] at c
  have e := val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ
  have e₁ := hv p a b hx hy z J hJ
  have e₂ := hv' p a b hx hy z J hJ
  have hm : val κ₂ p.left z J = val κ p.left z J * val κ' p.left z J *
      cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a) :=
    (hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) c))
  rw [hm, sum_add_smul]
  have hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i =
      (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]
  rw [hp, ← e₁, ← e₂]
  calc _ = (val (D.tau a (∑ i, w i • b i + ∑ i, w' i • b i)) (𝟙 _) z J *
          cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a)) *
          val κ p.left z J * val κ' p.left z J := by ac_rfl
    _ = _ := by rw [e]; ac_rfl

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

theorem formEq_sub (w w' : K → ℤ) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ (w + w') i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -((w + w') k.1 * Oε k.2)) k) *
      (∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        (-Sum.elim Oε (fun k : K × Fin 4 => -(w k.1 * Oε k.2)) k)) *
      (∏ I : thK, h ((lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left ≫ thφ D.P.A (x3 D.P.A) I) ^ (-thε I)) =
    ∏ k, h (Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2) k) ^
        Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)) k := by
  rw [formEq_add x y w w' h]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem expand_sub (hB : D.TauBimult) {w w' : K → ℤ} (h₁ : Expand D w x y) (h₃ : Expand D (w + w') x y) :
    Expand D w' x y := by
  obtain ⟨κ, hκ, hv⟩ := h₁
  obtain ⟨κ₃, hκ₃, hv₃⟩ := h₃
  obtain ⟨κ₂, hκ₂, hv₂⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ w' i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -(w' k.1 * Oε k.2)))
    (fun U _ h => by
      exact ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _) rfl)).trans
        (formEq_sub x y w w' h))
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ κ₃ (LB.invGen D.P.L _ _ κ))
      (LB.invGen D.P.L _ _
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (∏ i, y i ^ w i) (lift (∏ i, y i ^ w' i) x)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hκ₃ (DVR.invGen_isGen _ _ _ _ hκ))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨κ₂, hκ₂, fun p a b hx hy z J hJ => ?_⟩
  have c := val_cub D.cub p hJ (∏ i, y i ^ w i) (∏ i, y i ^ w' i) x
  rw [comp_prod_cP y hy w, comp_prod_cP y hy w', hx] at c
  have e := val_tau_add_right hB a (∑ i, w i • b i) (∑ i, w' i • b i) hJ
  have e₁ := hv p a b hx hy z J hJ
  have e₃ := hv₃ p a b hx hy z J hJ
  have hm : val κ₂ p.left z J = val κ₃ p.left z J * (val κ p.left z J)⁻¹ *
      (cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i)) (DVR.cP D (TK R) a))⁻¹ :=
    (hv₂ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) ((val_inv _ _).trans (congrArg _ c))))
  have hp : ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (w + w') i =
      (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w i) * ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add]
  rw [sum_add_smul, hp, ← e₁] at e₃
  rw [hm]
  generalize val (D.tau a (∑ i, w i • b i + ∑ i, w' i • b i)) (𝟙 _) z J = t₃ at e e₃
  generalize val (D.tau a (∑ i, w i • b i)) (𝟙 _) z J = t₁ at e e₃
  generalize val (D.tau a (∑ i, w' i • b i)) (𝟙 _) z J = t₂ at e ⊢
  generalize cubV D.cub z J (DVR.cP D (TK R) (∑ i, w i • b i)) (DVR.cP D (TK R) (∑ i, w' i • b i))
    (DVR.cP D (TK R) a) = C at e ⊢
  generalize val κ₃ p.left z J = k₃ at e₃ ⊢
  generalize val κ p.left z J = k₁ at e₃ ⊢
  generalize ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ w' i = P at e₃ ⊢
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e
  have a₃ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv] at a₁ a₃ ⊢
  linear_combination (norm := abel) a₃ - a₁

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData.ExpandPf

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {K : Type} [Fintype K] {T : Over (Sp R)}
  (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A))

theorem expand_single [DecidableEq K] (hB : D.TauBimult) (j : K) : Expand D (Pi.single j (1 : ℤ)) x y := by
  have hY : ∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i = y j := by
    rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  have hK : ∀ {U : Type} [CommGroup U] (f : K × Fin 4 → U),
      ∏ k, f k ^ (-((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2)) = ∏ m, f (j, m) ^ (-Oε m) := by
    intro U _ f
    rw [Fintype.prod_prod_type, Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  obtain ⟨κ, hκ, hv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (lamPts x (∏ i, y i ^ (Pi.single j (1 : ℤ) : K → ℤ) i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
    (ε' := Sum.elim Oε (fun k : K × Fin 4 => -((Pi.single j (1 : ℤ) : K → ℤ) k.1 * Oε k.2)))
    (fun U _ h => by
      refine (Fintype.prod_empty _).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hK (fun k => h (lamPts x (y k.1) k.2)), hY]
      simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_prod]
      simp
      abel)
    (LB.oneGen D.P.L (Y := T.left)) oneGen_isGen'
  refine ⟨κ, hκ, fun p a b hx hy z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_one, _root_.mul_one]
  have e0 : (∑ i, (Pi.single j (1 : ℤ) : K → ℤ) i • b i) = b j := by
    rw [Fintype.sum_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  have e1 : (∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ (Pi.single j (1 : ℤ) : K → ℤ) i) = val (D.tau a (b j)) (𝟙 _) z J := by
    rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])]
    simp
  rw [e0, e1]

theorem expand_single_int [DecidableEq K] (hB : D.TauBimult) (j : K) (m : ℤ) : Expand D (Pi.single j m) x y := by
  induction m using Int.induction_on with
  | zero => rw [Pi.single_zero]; exact expand_zero x y hB
  | succ i ih =>
    rw [Pi.single_add]
    exact expand_add x y hB ih (expand_single x y hB j)
  | pred i ih =>
    refine expand_sub x y hB (expand_single x y hB j) ?_
    rw [← Pi.single_add]
    have e : (1 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) := by ring
    rw [e]
    exact ih

theorem expand_all (hB : D.TauBimult) (n : K → ℤ) : Expand D n x y := by
  classical
  have key : ∀ s : Finset K, Expand D (∑ j ∈ s, Pi.single j (n j)) x y := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact expand_zero x y hB
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact expand_add x y hB (expand_single_int x y hB j (n j)) ih
  have := key Finset.univ
  rwa [Finset.univ_sum_single] at this

end GlobalTheory.Mum.PowData.ExpandPf

namespace GlobalTheory.Mum.PowData

theorem expand_of_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (K : Type) [Fintype K]
    (n : K → ℤ) (T : Over (Sp R)) (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)), Expand D n x y :=
  fun _ _ _ _ hB _ _ n _ x y => ExpandPf.expand_all x y hB n

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimultStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (K : Type) [Fintype K] (n : K → ℤ) (T : Over (Sp R)) (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)), Expand D n x y := by
  first | exact @GlobalTheory.Mum.PowData.expand_of_tauBimult | exact GlobalTheory.Mum.PowData.expand_of_tauBimult | (intros; apply GlobalTheory.Mum.PowData.expand_of_tauBimult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianParts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianPartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  first | exact @GlobalTheory.Mum.PowData.over₀_prod_zpow | exact GlobalTheory.Mum.PowData.over₀_prod_zpow | (intros; apply GlobalTheory.Mum.PowData.over₀_prod_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowCharacterMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowCharacterMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem torusHomOf_iff_charUnit {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem charUnit_eq_pointsEquiv {S : Scheme.{0}} {X : Type} [AddCommGroup X] (χ : X) :
    charUnit S X χ = GlobalTheory.splitTorusPointsEquiv S X _ (𝟙 _) (Multiplicative.ofAdd χ) :=
  Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) χ).trans (GlobalTheory.SplitTorusHom.appTop_id _)).symm

theorem torusHomOf_prod_zpow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {K : Type}
    [Fintype K] (n : K → ℤ) (h : K → X' → X) (t : K → (splitTorus S X ⟶ splitTorus S X'))
    (ht : ∀ i, TorusHomOf (h i) (t i)) : TorusHomOf (fun χ => ∑ i, n i • h i χ) (∏ i, t i ^ n i) := by
  simp only [torusHomOf_iff_charUnit] at ht
  rw [torusHomOf_iff_charUnit]
  intro χ
  have e₁ : ∀ i, GlobalTheory.splitTorusPointsEquiv S X' _ (t i) (Multiplicative.ofAdd χ) = charUnit S X (h i χ) := fun i =>
    Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X' _ (t i) χ).trans (ht i χ))
  rw [← GlobalTheory.splitTorusPointsEquiv_val, map_prod]
  simp only [map_zpow]
  rw [charUnit_eq_pointsEquiv, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, ← charUnit_eq_pointsEquiv]
  congr 1
  change (MonoidHom.eval (Multiplicative.ofAdd χ)) (∏ x, GlobalTheory.splitTorusPointsEquiv S X' _ (t x) ^ n x) = _
  rw [map_prod]
  simp only [map_zpow, MonoidHom.eval, MonoidHom.flip_apply, MonoidHom.id_apply, e₁]

end GlobalTheory.Mum.PowData

theorem GlobalTheory.Mum.PowData.onTorus_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a h H e
  choose t ht et using fun i => H i e
  refine ⟨∏ i, t i ^ n i, torusHomOf_prod_zpow n h t ht, ?_⟩
  have := (U₀.gt e).i_hom
  have hm : (Over.pullback (thick R I e)).map (∏ i, a i ^ n i) = ∏ i, (Over.pullback (thick R I e)).map (a i) ^ n i :=
    (map_prod ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _).trans
      (Finset.prod_congr rfl fun i _ => map_zpow ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _)
  rw [hm, comp_prod_zpow, prod_zpow_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [et i]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowCharacterMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  first | exact @GlobalTheory.Mum.PowData.onTorus_prod_zpow | exact GlobalTheory.Mum.PowData.onTorus_prod_zpow | (intros; apply GlobalTheory.Mum.PowData.onTorus_prod_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData.CmpTwoProof

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem pull_cls_of_isPart {X X₁ : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}
    (h : IsPart N M e π) (hN : N.IsLB) (hM : M.IsLB) : CechPic.pull e (cls N hN) = cls M hM := by
  have h1 := LB.isLB_linComb hN (fun _ : PUnit.{1} => 𝟙 X₁ ≫ e) (fun _ => 1)
  have h2 := LB.isLB_linComb hM (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)
  have a := cls_linComb hN _ _ h1
  have b := cls_linComb hM _ _ h2
  have c := (cls_eq_iff h1 h2).2 (iso_of_chart h2 (h.up (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)))
  have := (a.symm.trans c).trans b
  simpa only [Fintype.sum_unique, one_smul, Category.id_comp, pull_id] using this

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

end GlobalTheory.Mum.PowData.CmpTwoProof

open GlobalTheory.Mum.PowData.CmpTwoProof in
theorem GlobalTheory.Mum.PowData.cmpTwo_of_adjCls : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  intro R _ _ D D₀ q j hq hj hadj
  haveI := hq
  haveI := hj
  have hN : (JN D D₀).IsLB := jn_isLB D D₀
  have hG := GlobalTheory.globalFns_holds
  have pl := pull_cls_of_isPart (isPart_inl D.P.L D₀.P.L) hN D.P.isLB
  have pr := pull_cls_of_isPart (isPart_inr D.P.L D₀.P.L) hN D₀.P.isLB
  let φΓ : Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) :=
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let εΓ : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim Oε Oinvε
  have hL1 := LB.isLB_linComb hN φΓ εΓ

  have h0 : cls _ hL1 = 0 := by
    rw [cls_linComb hN _ _ hL1, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, pull_comp, pl, pr]
    refine Eq.trans ?_ (sub_eq_zero.2 (hadj _ (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A)))
    simp only [lam, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨Γ₀, hΓ₀⟩ := (cls_eq_zero_iff hL1).1 h0

  let o : (D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A ⊗ D₀.P.A).left :=
    (toUnit (D.P.A ⊗ D₀.P.A) ≫ lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)).left
  have hz : ∀ k, o ≫ φΓ k = Sum.elim (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D.P.A).left ≫ coprod.inl)
      (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D₀.P.A).left ≫ coprod.inr) k := by
    rintro (k | k) <;> simp only [φΓ, Sum.elim_inl, Sum.elim_inr, ← Category.assoc] <;> congr 1 <;>
      fin_cases k <;>
      simp only [lamPts, o, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, ← Over.comp_left, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, comp_one_pt, one_comp_hom, _root_.mul_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have fe0 : FormEq (Sum.elim φΓ (fun k => o ≫ φΓ k)) (Sum.elim εΓ (fun k => - εΓ k)) φΓ εΓ := by
    intro U _ h
    have hQ : ∏ k, h (o ≫ φΓ k) ^ (- εΓ k) = 1 := by
      simp only [hz]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
      simp only [Sum.elim_inl, Sum.elim_inr, εΓ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      simp only [neg_neg, one_smul, neg_smul]
      abel
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hQ, _root_.mul_one]
  obtain ⟨Γ, hΓ, hΓv⟩ := exists_gen hN fe0 (LB.mulGen _ _ _ _ _ Γ₀ (LB.invGen _ _ _ (LB.pullGen _ _ _ Γ₀ o)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hΓ₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hΓ₀ o)))
  have hone : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D₀.P.A).left) (z : Z) (J), Good (JN D D₀) z J → r ≫ o = r →
      val Γ r z J = 1 := by
    intro Z r z J hJ hr
    rw [hΓv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hr, mul_inv_cancel]
  have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  let ι₀ : D₀.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)).left
  have fe1 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => ι₀ ≫ φΓ k) εΓ := by
    intro U _ h
    rw [Fintype.prod_empty, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ι₀, ← Category.assoc,
      ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, comp_one_pt, one_comp_hom, Category.id_comp,
      _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have e0 : (η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)) ≫ toUnit _ ≫
      lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) =
      η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A) := by
    rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, comp_lift, comp_one_pt,
      Category.comp_id, o₀]
  have key1 := gen_unique' hN (u := LB.pullGen _ _ _ Γ ι₀) (u' := LB.oneGen (JN D D₀) (Y := D₀.P.A.left)) fe1
    D₀.P.A.hom (eSec D₀.P.A) (Over.w η[D₀.P.A]) (hG _ _ D₀.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hΓ ι₀)
    (oneGen_isGen _) (fun y J hJ => by
      rw [val_pull hJ, val_one]
      refine hone _ _ y J hJ ?_
      have := congrArg (fun f => f.left) e0
      simpa only [eSec, ι₀, o, Over.comp_left] using this)
  have hΓ1 : ∀ (T : Over (Sp R)) (w : T ⟶ D₀.P.A) (y : T.left) (J), Good (JN D D₀) y J →
      val Γ (lift (1 : T ⟶ D.P.A) w).left y J = 1 := by
    intro T w y J hJ
    have := key1 T.left w.left y J hJ
    rw [val_pull hJ, val_one] at this
    rwa [show w.left ≫ ι₀ = (lift (1 : T ⟶ D.P.A) w).left by
      rw [← Over.comp_left, comp_lift, comp_one_pt, Category.comp_id]] at this
  refine ⟨Γ, hΓ, ?_⟩
  intro χ' χ hc u hu T x z J hJ
  let m : D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (𝟙 D.P.A) (toUnit D.P.A ≫ D₀.c χ)).left
  have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
  have fe2 : FormEq (fun k => m ≫ φΓ k) εΓ
      (Sum.elim (fun k => D.Oφ (𝟙 _) χ' k ≫ coprod.inl) (fun k => D₀.Oφ q χ k ≫ coprod.inr)) (Sum.elim Oε Oinvε) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four,
      Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, m, pm, ← Hom.one_def, hc,
      ← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, Category.comp_id, comp_one_pt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have ev2 : ∀ y I, Good (JN D D₀) y I → val u (eSec D.P.A) y I = val (LB.pullGen _ _ _ Γ m) (eSec D.P.A) y I := by
    intro y I hI
    rw [val_pull hI]
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    have e2 : eSec D.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D.P.A] ≫ toUnit _) (toUnit _), o']
    rw [c, e2, hΓ1 _ _ y I hI]
  have key := gen_unique' hN (u := u) (u' := LB.pullGen _ _ _ Γ m) fe2 D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 hu.1 (DVR.pullGen_isGen _ _ _ _ hΓ m) ev2 T.left x.left z J hJ
  rw [key, val_pull hJ]
  congr 1
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  first | exact @GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | exact GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | (intros; apply GlobalTheory.Mum.PowData.cmpTwo_of_adjCls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

section Power

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] {r : ℕ}

theorem isMonHom_prod_zpow {K : Type} [Fintype K] (a : K → (G ⟶ G₀)) (ha : ∀ i, IsMonHom (a i)) (n : K → ℤ) :
    IsMonHom (∏ i, a i ^ n i) :=
  isMonHom_of_mul _ fun T x z => by
    rw [comp_prod_zpow, comp_prod_zpow, comp_prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := ha i
    rw [MonObj.mul_comp, mul_zpow]

theorem comp_zpow' {T T' : Over S} (p : T' ⟶ T) (y : T ⟶ G) (n : ℤ) : p ≫ y ^ n = (p ≫ y) ^ n := by
  simpa using comp_prod_zpow (K := Unit) p (fun _ => y) (fun _ => n)

theorem prod_zpow_same {M K : Type} [CommGroup M] [Fintype K] (a : M) (f : K → ℤ) : ∏ i, a ^ f i = a ^ ∑ i, f i := by
  have h := map_prod (zpowersHom M a) (fun i => Multiplicative.ofAdd (f i)) Finset.univ
  rw [← ofAdd_sum] at h
  exact h.symm

theorem exists_vec (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u) (v : Fin r → ℤ) :
    ∃ i : G₀ ⟶ G, IsMonHom i ∧ ∀ b, i ≫ q b = 𝟙 G₀ ^ v b := by
  obtain ⟨i, hi, -⟩ := huniv G₀ fun b => 𝟙 G₀ ^ v b
  refine ⟨i, isMonHom_of_mul _ fun T x z => (huniv T fun b => (x * z) ^ v b).unique (fun b => ?_) (fun b => ?_), hi⟩
  · rw [Category.assoc, hi, comp_zpow', Category.comp_id]
  · have := hq b
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, comp_zpow', comp_zpow', Category.comp_id, Category.comp_id,
      mul_zpow]

theorem lam_of_tens {L₀ : LB G₀.left} (hL : L₀.IsLB) (hΘ : ∃ t : LB.Gen (Theta G₀ L₀), t.IsGen) (q : Fin r → (G ⟶ G₀))
    (hq : ∀ u, IsMonHom (q u)) (W : Matrix (Fin r) (Fin r) ℤ) {c : Pic G.left}
    (hc : c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (q a) (q b)) {T : Over S} (x y : T ⟶ G) :
    lam c x y = ∑ a, ∑ b, (W + W.transpose) a b • lam (cls L₀ hL) (x ≫ q a) (y ≫ q b) := by
  have hp : ∀ h : T ⟶ G, pull h.left c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (h ≫ q a) (h ≫ q b) := fun h => by
    rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, pull_lam]
  have hm : ∀ i, (x * y) ≫ q i = x ≫ q i * y ≫ q i := fun i => by
    have := hq i
    exact MonObj.mul_comp _ _ _
  have ho : ∀ i, (1 : T ⟶ G) ≫ q i = 1 := fun i => by
    have := hq i
    exact MonObj.one_comp _
  have e : ∑ i, ∑ j, W i j • lam (cls L₀ hL) (y ≫ q i) (x ≫ q j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls L₀ hL) (x ≫ q i) (y ≫ q j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (y ≫ _)]
  conv_lhs => rw [lam]
  simp only [hp, hm, ho, lam_one_left, lam_mul_left hL hΘ, RosatiTens.lam_mul_right hL hΘ, smul_add,
    Finset.sum_add_distrib, Matrix.add_apply, add_smul, smul_zero, Finset.sum_const_zero]
  rw [e]
  abel

end Power

theorem exists_tens (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D D₀ : DegData R (maximalIdeal R))
    (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀]
    (hG : IsSemiAbelian G) (hG₀ : IsSemiAbelian G₀) (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀)
    {r : ℕ} (W N : Matrix (Fin r) (Fin r) ℤ) (hN : (W + W.transpose) * N = 1) (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u)
    (hc : cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b))
    (h : Fin r → (D₀.toPre.X →+ D.toPre.X)) (hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (h u))
    (xe : D.toPre.X ≃+ (Fin r → D₀.toPre.X))
    (hxe : ∀ mu, xe.symm mu = ∑ u, h u (∑ v, (W + W.transpose) u v • mu v)) :
    ∃ T : Tens D₀.toPre D.toPre W, T.xe = xe := by
  have hA := hR.1
  set Sm := W + W.transpose with hSm
  have hSs : ∀ a b, Sm a b = Sm b a := fun a b => by simp [hSm, add_comm]
  have hN' : N * Sm = 1 := mul_eq_one_comm.1 hN
  have SN : ∀ a c, ∑ b, Sm a b * N b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN, Matrix.one_apply]
  have NS : ∀ a c, ∑ b, N a b * Sm b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN', Matrix.one_apply]
  have hΘ₀ : ∃ t : LB.Gen (Theta G₀ U₀.LG.L), t.IsGen := ⟨U₀.cubG.t, U₀.cubG.isGen⟩
  have hΘ : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have P := fun {T : Over (Sp R)} (x y : T ⟶ G) => lam_of_tens U₀.LG.isLB hΘ₀ q hq W hc x y
  rw [← hSm] at P
  have zr : ∀ {T : Over (Sp R)} (x z : T ⟶ G₀) (n : ℤ), lam (cls U₀.LG.L U₀.LG.isLB) x (z ^ n) =
      n • lam (cls U₀.LG.L U₀.LG.isLB) x z := fun x z n => by
    simpa using RosatiTens.lam_prod_right (κ := Unit) U₀.LG.isLB hΘ₀ x (fun _ => z) (fun _ => n)
  choose j hj jq using fun a => exists_vec q hq huniv fun b => N b a
  choose inc hinc iq using fun a => exists_vec q hq huniv fun b => if a = b then 1 else 0
  let rr' : Fin r → (G ⟶ G₀) := fun a => ∏ b, q b ^ Sm a b
  have hrr : ∀ a, IsMonHom (rr' a) := fun a => isMonHom_prod_zpow q hq _
  have iq₁ : ∀ a, inc a ≫ q a = 𝟙 _ := fun a => by rw [iq, if_pos rfl, zpow_one]
  have jr : ∀ a, j a ≫ rr' a = 𝟙 _ := fun a => by
    simp only [rr', comp_prod_zpow, jq, ← zpow_mul, prod_zpow_same, mul_comm (N _ _), SN]
    simp
  have adjq : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (q a) (j a) := fun a T x z => by
    simp only [P, Category.assoc, jq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, SN]
    simp
  have adjr : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (rr' a) (inc a) := fun a T x z => by
    simp only [P, Category.assoc, iq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, rr', comp_prod_zpow,
      RosatiTens.lam_prod_left U₀.LG.isLB hΘ₀]
    simp [hSs a]
  have hNs : ∀ a b, N a b = N b a := fun a b => by
    have e₁ : Sm.transpose = Sm := Matrix.ext fun a b => hSs b a
    have e₂ : N.transpose * Sm = 1 := by rw [← e₁, ← Matrix.transpose_mul, hN, Matrix.transpose_one]
    have e₃ : N.transpose = N := by rw [← Matrix.mul_one N.transpose, ← hN, ← Matrix.mul_assoc, e₂, Matrix.one_mul]
    exact congrFun (congrFun e₃ b) a
  let f : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.2 ≫ j ab.1) ^ W ab.1 ab.2
  let f' : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.1 ≫ j ab.2) ^ W ab.1 ab.2
  have hf : IsMonHom f := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have hf' : IsMonHom f' := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have ff : f * f' = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [f, f', MonObj.mul_comp, prod_zpow_comp, Category.assoc, jq, comp_zpow', Category.comp_id, ← zpow_mul]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm, ← Finset.prod_mul_distrib]
    simp only [prod_zpow_same, ← zpow_add, ← Finset.sum_add_distrib, ← mul_add]
    have : ∀ b, ∑ a, N c a * (W a b + W b a) = if c = b then 1 else 0 := fun b => NS c b
    simp [this]) (fun c => Category.id_comp _)
  have adjf : AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' := fun T x z => by
    simp only [f, f', comp_prod_zpow, RosatiTens.lam_prod_left U.LG.isLB hΘ, RosatiTens.lam_prod_right U.LG.isLB hΘ]
    refine Finset.sum_congr rfl fun ab _ => congrArg _ ?_
    rw [← Category.assoc, ← Category.assoc, adjq, lam_comm _ _ z, adjq, lam_comm]
  have primf : cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f := by
    simp only [f, RosatiTens.lam_prod_right U.LG.isLB hΘ, adjq _ _, Category.id_comp, Fintype.sum_prod_type]
    exact hc
  have idq : ∏ a, (q a ≫ inc a) ^ (1 : ℤ) = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [prod_zpow_comp, Category.assoc, iq, comp_zpow', Category.comp_id]
    simp) (fun c => Category.id_comp _)
  choose qB hqB oq using fun a => exists_abelian_hom R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre (q a) (hq a)
  choose jB hjB oj using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  choose iB hiB oi using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (inc a) (hinc a)
  choose k tk using fun a => unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  have un := over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have un₀ := over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have oz : ∀ m : ℤ, Over₀ U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (𝟙 _ ^ m) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.over_id
  have tz : ∀ m : ℤ, OnTorus U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (fun χ => m • χ) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.onTorus_id
  have iqB : ∀ a b, iB a ≫ qB b = 𝟙 _ ^ (if a = b then 1 else 0 : ℤ) := fun a b =>
    (un₀ _).1 _ _ (iq a b ▸ FactorPol.over_comp (oi a) (oq b)) (oz _)
  have jqB : ∀ a b, jB a ≫ qB b = 𝟙 _ ^ N b a := fun a b =>
    (un₀ _).1 _ _ (jq a b ▸ FactorPol.over_comp (oj a) (oq b)) (oz _)
  have idB : ∏ a, (qB a ≫ iB a) ^ (1 : ℤ) = 𝟙 _ := (un _).1 _ _
    (idq ▸ GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ (fun _ => 1) _ _ fun a => FactorPol.over_comp (oq a) (oi a))
    FactorPol.over_id
  have kh : ∀ a b χ, k a (h b χ) = N b a • χ := fun a b =>
    congrFun ((un₀ _).2 _ _ (jq a b ▸ FactorPol.onTorus_comp (tk a) (hh b)) (tz _))
  have xk : ∀ y a, xe y a = k a y := fun y a => by
    obtain ⟨mu, rfl⟩ := xe.symm.surjective y
    rw [AddEquiv.apply_symm_apply, hxe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, kh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hNs _ a, NS]
    simp
  have extB : ∀ {T : Over (Sp R)} (x x' : T ⟶ D.toPre.P.A), (∀ a, x ≫ qB a = x' ≫ qB a) → x = x' := fun x x' e => by
    rw [← Category.comp_id x, ← Category.comp_id x', ← idB, comp_prod_zpow, comp_prod_zpow]
    simp only [← Category.assoc, e]
  have per := fun a => GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (inc a) (j a) (hinc a) (hj a) (iq₁ a) (adjq a) (qB a) (h a)
    (k a) ⟨hq a, hqB a, oq a, hh a⟩ (tk a)
  have adjB := fun a => GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (rr' a) (inc a) (j a) (hq a) (hrr a) (hinc a) (hj a) (iq₁ a)
    (jr a) (adjq a) (adjr a) (qB a) (jB a) (hqB a) (hjB a) (oq a) (oj a)
  have cz : ∀ (m : ℤ) χ, D₀.toPre.c (m • χ) = D₀.toPre.c χ ^ m := fun m χ => by
    let φ : Multiplicative D₀.toPre.X →* (𝟙_ (Over (Sp R)) ⟶ D₀.toPre.P.A) :=
      MonoidHom.mk' (fun y => D₀.toPre.c y.toAdd) fun a b => D₀.toPre.c_add _ _
    exact map_zpow φ (Multiplicative.ofAdd χ) m
  have ch : ∀ a χ, D.toPre.c (h a χ) = D₀.toPre.c χ ≫ jB a := fun a χ => extB _ _ fun b => by
    rw [← (per b).1, kh, cz, Category.assoc, jqB, comp_zpow', Category.comp_id, hNs]
  obtain ⟨w, hw, hψ⟩ := GlobalTheory.T.powerData_tensorBundleIso_with_psi_values R D.toPre D₀.toPre r W qB jB (fun a => h a) (fun a => k a) ch (fun a => (per a).1)
    (fun a => (per a).2) (fun a => GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint R _ _ _ _ (hqB a) (hjB a) (adjB a)) (GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult R _ D.tau_bimult _ _ _ _ _)
    (GlobalTheory.T.thetaMultiplier_eq_of_primitive_adjoint_bundle R hR D A G hG U f f' hf hf' ff adjf primf _ _
      (GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.over_comp (oq ab.2) (oj ab.1))
      (GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.onTorus_comp (hh ab.1) (tk ab.2)))
  have lf : ∀ {T : Over (Sp R)} (y : Fin r → (T ⟶ D₀.toPre.P.A)) b, (∏ a, (y a ≫ iB a) ^ (1 : ℤ)) ≫ qB b = y b := fun y b => by
    simp only [prod_zpow_comp, Category.assoc, iqB, comp_zpow', Category.comp_id]
    simp
  exact ⟨{ pr := qB, pr_hom := hqB, xe := xe, w := w, w_gen := hw
           lim := Fan.IsLimit.mk _ (fun s => (∏ a, (s.proj a ≫ iB a) ^ (1 : ℤ) : s.pt ⟶ D.toPre.P.A)) (fun s b => lf _ b)
             (fun s m hm => extB _ _ fun b => (hm b).trans (lf _ b).symm)
           c_pr := fun z a => by rw [xk, (per a).1]
           psi := fun y z J J' hJ hJ' => (hψ y z J J' hJ hJ').trans (congrArg _ (Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => by rw [xk, xk])) }, rfl⟩

end GlobalTheory.Mum.PowData


open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
  ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Eq8 in
theorem GlobalTheory.Mum.PowData.sharpRef_of_characters : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN _ _ D₀ e₀ hRef G₀ _ _ A₀ U₀ y α α₂ hG₀ hα hsq hlb P c φc φ₂ hφ hφsq hφlb _ pr _ _
    hPL G _ _ hG D U q hq huniv hcomp ch hch e he
  have hR : Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  have hc := GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum g n o ζ F W V₁ hR D D₀ P A₀ G G₀ hG U U₀ y α α₂ hα hsq hlb c φc φ₂ hφ hφsq hφlb pr hPL q hq hcomp
  have hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (ch u) := fun u => by
    obtain ⟨h, th⟩ := unifPre_hom_character_const V₁ _ hR.1 D D₀ P A₀ G G₀ U.toUnifPre U₀.toUnifPre (q u) (hq u)
    rwa [torMatch_unique V₁ hR G₀ hG₀ D₀ A₀ U₀ V₁ hR G hG D P U _ _ Function.injective_id _ _ (hch u)
      (GlobalTheory.T.toricTorsionMatch_of_characterMap_on_torus V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ (q u) (hq u) h th)]
  obtain ⟨T, hT⟩ := GlobalTheory.Mum.PowData.exists_tens V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ W (W + W.transpose)⁻¹
    (Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)) q hq huniv hc ch hh
    (e.symm.trans (AddEquiv.piCongrRight fun _ => e₀.symm)) (fun mu => by
      show e (fun a => e₀ (mu a)) = _
      simp [he])
  refine GlobalTheory.T.sharpRef_of_refines_tensor W V Q V₁ ρ D₀.toPre D.toPre e₀ hRef T e fun mu a => ?_
  simp [hT]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_eighthPower_via_characterMaps : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_characters | exact GlobalTheory.Mum.PowData.sharpRef_of_characters | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_characters <;> assumption)
end
