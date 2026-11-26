module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ESecToUnit
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetPointZeroEqOne
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CocycleProductThree
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem act_zero : Xo.univ.t.act.act 0 = 1 := by
  have h := Xo.univ.t.act.add 0 0
  rw [add_zero] at h
  first
    | exact mul_eq_left.mp h.symm
    | exact mul_right_eq_self.mp h.symm
    | exact self_eq_mul_right.mp h
    | simpa using h

private theorem comp_psum_lemma {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G))
    (S : Finset (Fin n)) :
    f ≫ psum Xo.univ.t.G xs S = psum Xo.univ.t.G (fun i => f ≫ xs i) S := by
  unfold psum
  generalize (List.finRange n).filter (· ∈ S) = L
  induction L with
  | nil =>
    simp only [List.foldr_nil, pzero]
    first
      | simp
      | rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd]
    first
      | rw [CartesianMonoidalCategory.comp_lift_assoc]
      | simp

theorem comp_cφ {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) (I : ULift (Finset (Fin n))) :
    f.left ≫ cφ xs I = cφ (fun i => f ≫ xs i) I := by
  simp only [cφ]
  rw [← Over.comp_left, comp_psum_lemma]

theorem comp_thφ {T T' : Over Xo.X} (f : T' ⟶ T) (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) (I : thK) :
    f.left ≫ thφ Xo.univ.t.G xs I = thφ Xo.univ.t.G (fun i => f ≫ xs i) I := by
  simp only [thφ]
  rw [← Over.comp_left, comp_psum_lemma]

private theorem padd_eq_lemma_2 {T : Over Xo.X} (a b : T ⟶ Xo.univ.t.G) :
    padd Xo.univ.t.G a b = a * b := rfl

private theorem pzero_eq_lemma_3 (T : Over Xo.X) : pzero Xo.univ.t.G T = 1 := rfl


set_option maxHeartbeats 800000 in
theorem prod_cφ2 {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 2 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (cφ xs I) ^ cε 2 I =
      h (1 : T ⟶ Xo.univ.t.G).left * (h (xs 0 * 1).left)⁻¹ * (h (xs 1 * 1).left)⁻¹ * h (xs 0 * (xs 1 * 1)).left := by
  have hsum : ∀ F : ULift (Finset (Fin 2)) → U,
      ∏ I : ULift (Finset (Fin 2)), F I = ∏ s : Finset (Fin 2), F (ULift.up s) :=
    fun F => Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have f0 : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  have f1 : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  have f2 : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  have f3 : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  have c3 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [cφ, cε, psum, f0, f1, f2, f3, c3, List.foldr_cons, List.foldr_nil, padd_eq_lemma_2,
    pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 c3
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  rw [mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))),
    mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))), mul_assoc (h (xs 0 * 1).left)⁻¹]


set_option maxHeartbeats 800000 in
theorem cocycle_product_three {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : thK, h (thφ Xo.univ.t.G xs I) ^ thε I =
      (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹ * h (xs 0 * 1).left * h (xs 1 * 1).left * h (xs 2 * 1).left *
        (h (xs 0 * (xs 1 * 1)).left)⁻¹ * (h (xs 0 * (xs 2 * 1)).left)⁻¹ * (h (xs 1 * (xs 2 * 1)).left)⁻¹ *
          h (xs 0 * (xs 1 * (xs 2 * 1))).left := by
  have hsum : ∀ F : thK → U, ∏ I : thK, F I = ∏ s : Finset (Fin 3), F (ULift.up s) :=
    fun F => Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have f0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
  have f1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
  have f2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
  have f3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
  have f4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
  have f5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
  have f6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
  have f7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thφ, thε, psum, f0, f1, f2, f3, f4, f5, f6, f7, c4, c5, c6, c7, List.foldr_cons,
    List.foldr_nil, padd_eq_lemma_2, pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 f4 f5 f6 f7 c4 c5 c6 c7
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  repeat rw [mul_assoc (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * 1).left)]
  repeat rw [mul_assoc (h (xs 1 * 1).left)]
  repeat rw [mul_assoc (h (xs 2 * 1).left)]
  repeat rw [mul_assoc (h (xs 0 * (xs 1 * 1)).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * (xs 2 * 1)).left)⁻¹]
  all_goals exact (rfl : (0 : ℕ) = 0)

abbrev AdTy (Xo : Moduli Dw l) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
      (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

abbrev wPc (wP : PrimTy H Xo) (c : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ wP (Xo.univ.t.act.act c).left

abbrev cubAt (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) :=
  LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift p (lift q r)).left

def Bq (wP : PrimTy H Xo) (a : 𝓞 E) (wLa : AdTy Xo a) (wLb : AdTy Xo (H.bar a)) :=
  let A := Xo.univ.t.act.act
  let b := a * H.bar a
  LB.mulGen Xo.univ.t.PP.L _ _ _ _
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (wPc wP (1 + b))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))
          (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ wP)
        (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP b))))
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A 1) (A b) (A ((1 + b) * H.w0)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A H.w0) (A (b * H.w0)) (A 1))
          (cubAt (A H.w0) (A (b * H.w0)) (A b))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (A 1) (A (a * H.w0))).left)
        (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (A a) (A H.w0)).left))))

theorem Bq_isGen (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (wLa : AdTy Xo a) (hwa : wLa.IsGen)
    (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) : (Bq wP a wLa wLb).IsGen := by
  have hP := fun c => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ wP hwP (Xo.univ.t.act.act c).left
  have hC := fun (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ _ Xo.univ.t.cub.isGen (lift p (lift q r)).left
  unfold Bq
  refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hP _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))
          (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hwP)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _) (hC _ _ _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwa _)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwb _))))

theorem exists_betaRaw (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : AdTy Xo a) (hwa : wLa.IsGen) (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (Bq wP a wLa wLb) r z J := by
  have hL := Xo.univ.t.PP.isLB
  refine exists_gen hL ?_ _ (Bq_isGen wP hwP a wLa hwa wLb hwb)
  intro U _ hU
  unfold betaφ betaε
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Fin.prod_univ_four,
    comp_cφ, comp_thφ, Category.comp_id, zpow_neg, zpow_one, neg_neg, Finset.prod_inv_distrib, prod_cφ2, cocycle_product_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, x3, lift_fst, lift_snd_assoc, lift_snd, lift_fst_assoc, Category.id_comp]
  have h1 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p * Xo.univ.t.act.act q = Xo.univ.t.act.act (p + q) :=
    fun p q => (Xo.univ.t.act.add p q).symm
  have h2 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p ≫ Xo.univ.t.act.act q = Xo.univ.t.act.act (p * q) :=
    fun p q => (Xo.univ.t.act.mul p q).symm
  have h3 : (1 : Xo.univ.t.G ⟶ Xo.univ.t.G) = Xo.univ.t.act.act 0 := act_zero.symm
  have h4 : 𝟙 Xo.univ.t.G = Xo.univ.t.act.act 1 := Xo.univ.t.act.one.symm
  have h5 : 𝟙 Xo.univ.t.G.left = (Xo.univ.t.act.act 1).left := by rw [Xo.univ.t.act.one]; rfl
  simp only [h3, h1, h2, hbb, h4, h5]
  ring_nf
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_zero_hom_ext {S : Type} [CommRing S] {κ κ' : Type} (f g : Jet S κ 0 →ₐ[S] Jet S κ' 0) : f = g := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)
  rw [h0, map_zero, map_zero]

theorem comp_one' {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {T T' : Over X0} (f : T' ⟶ T) :
    f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem val_scale' {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (scaleGen φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  GermB.val_scale Xo.univ.t φ ε u g r z J hJ

theorem chart_at_zero_eq_one (C : ChartAt Xo c y) : C.x 0 = 1 := by
  have hz := C.chart.zero 0
  have hid : homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
      homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S) = 𝟙 _ := by
    rw [homAt_comp, jet_zero_hom_ext ((Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)).comp jetAug) (AlgHom.id S _), homAt_id]
  calc C.x 0 = 𝟙 _ ≫ C.x 0 := (Category.id_comp _).symm
    _ = (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
          homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)) ≫ C.x 0 := by rw [hid]
    _ = homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫ 1 := by rw [Category.assoc, hz]
    _ = 1 := comp_one' _

theorem jet_point_zero_eq_one (C : ChartAt Xo c y) {n : ℕ} (i : Fin n) : jpt y C.d C.x 0 i = 1 := by
  unfold jpt
  rw [chart_at_zero_eq_one C]
  exact comp_one' _

theorem const_ad (C : ChartAt Xo c y) (a : 𝓞 E) : MvPowerSeries.constantCoeff (C.B.ad a) = 1 := by
  have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0]
    (by intro p q; fin_cases p <;> simp [Germ.pt]) (C.B.ad a)
  rw [C.B.adjoint_zero_fst a, map_one] at e
  exact e.symm

def AdRel (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ, (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (C.B.ad a) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
        (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGen _ _ (unitΓ u)
        (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)]))

theorem exists_adRel (C : ChartAt Xo c y) (a : 𝓞 E) : ∃ wL : ExpGC.AdTy Xo a, wL.IsGen ∧ AdRel C a wL :=
  C.frame.ad a

theorem wL_zero (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) (hrel : AdRel C a wL) {Z : Scheme.{0}}
    (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (hJ : Good Xo.univ.t.PP.L z J) :
    val wL (r ≫ (lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G)).left) z J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel 0
  have hu1 : u = 1 := Units.ext (hu.trans (ExpGB.psJet_zero_of _ (const_ad C a)))
  have hι : homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S) ≫
      lift (jpt y C.d C.x 0 (0 : Fin 2)) (jpt y C.d C.x 0 (1 : Fin 2)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G) := by
    rw [jet_point_zero_eq_one C, jet_point_zero_eq_one C, comp_lift]
    exact congrArg₂ (fun p q => lift p q) (comp_one' _) (comp_one' _)
  have h1 := val_corr hJ hc (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left)
  rw [val_mul hJ, val_pull hJ, val_scale' _ _ _ _ _ z J hJ, hu1,
    show unitΓ (1 : (Jet S (Fin 2 × Fin C.d) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
    _root_.one_mul] at h1
  have hpe : val (pe y C.d C.x C.e 0 ![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J =
      val (pe y C.d C.x C.e 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)])
        (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J := by
    have hm : (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left =
        (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left := by
      rw [jet_zero_hom_ext (jetSubstP 0 _) (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)]
    unfold pe
    rw [hm]
  rw [hpe, mul_eq_right] at h1
  rw [Category.assoc, ← Over.comp_left, hι] at h1
  exact h1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem val_rigPow {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by
  unfold rigPow val
  exact map_zpow _ _ _

theorem eSec_act (c : 𝓞 E) : eSec Xo.univ.t.G ≫ (Xo.univ.t.act.act c).left = eSec Xo.univ.t.G := by
  haveI := Xo.univ.t.act.2 c
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem eSec_toUnit : eSec Xo.univ.t.G ≫ (toUnit Xo.univ.t.G).left = 𝟙 _ := by
  unfold eSec
  rw [← Over.comp_left]
  simp

theorem exists_beta (wP : PrimTy H Xo) (hwP : IsPrim wP) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : ExpGC.AdTy Xo a) (hwa : wLa.IsGen) (wLb : ExpGC.AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
          (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
  have hL := Xo.univ.t.PP.isLB
  have hrig := Xo.univ.t.PP.rigGen
  obtain ⟨β0, hβ0, hv0⟩ := ExpGC.exists_betaRaw wP hwP.1 a hbb wLa hwa wLb hwb
  have hg := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ β0 hβ0 (eSec Xo.univ.t.G))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig hrig))
  obtain ⟨g0, hg0, hv1⟩ := exists_gen hL (φ' := (PEmpty.elim : PEmpty.{1} → ((𝟙_ (Over Xo.X)).left ⟶ Xo.univ.t.G.left)))
    (ε' := PEmpty.elim) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, betaφ, betaε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, eSec_act, Category.comp_id, Finset.univ_unique, Finset.prod_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      abel) _ hg
  have hB := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hβ0
    (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen Xo.univ.t.PP.L _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ g0 hg0 (toUnit Xo.univ.t.G).left))
  obtain ⟨β, hβ, hv2⟩ := exists_gen hL (φ' := betaφ (Xo := Xo) a) (ε' := betaε) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_eq_empty, Finset.prod_empty,
        _root_.mul_one]) _ hB
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
      Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
        (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
    intro Z r z J hJ
    rw [hv2 Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hv1 Z _ z J hJ, val_mul hJ, val_pull hJ, val_mul hJ,
      val_mul hJ, hv0 Z r z J hJ, hv0 Z _ z J hJ, ← Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  refine ⟨β, hβ, corr_of_val hL fun z J hJ => ?_, hval⟩
  rw [val_pull hJ, hval _ _ z J hJ, val_rigPow]
  simp only [Category.id_comp]
  rw [← Category.assoc (eSec Xo.univ.t.G), eSec_toUnit, Category.id_comp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

theorem psJet_coe (m : ℕ) (P : MvPolynomial κ S) : psJet m (P : MvPowerSeries κ S) = Ideal.Quotient.mk _ P := by
  unfold psJet
  rw [psTrunc_eq]
  exact mk_trunc_coe m P

theorem jetSubstPS_X (m : ℕ) (P : κ → MvPowerSeries κ' S) (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (i : κ) : jetSubstPS (m := m) P (Ideal.Quotient.mk _ (X i)) = psJet m (P i) := by
  unfold jetSubstPS
  rw [jetMap_mk, MvPolynomial.aeval_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', hP i, map_zero, sub_zero]
  rfl

theorem jetSubstPS_eq_jetMap (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by
  unfold jetSubstPS
  congr 1
  funext i
  have h0 : MvPolynomial.constantCoeff (psTrunc m (Q i)) = 0 := by
    have hmem : (0 : κ' →₀ ℕ) ∈ degLE (ι := κ') m := by
      simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨fun _ => 0, ?_⟩, ?_⟩
      · ext j
        simp
      · simp
    rw [← hQ i]
    change AddMonoidAlgebra.coeff (psTrunc m (Q i)) 0 = _
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    rw [if_pos hmem]
    rfl
  rw [h0, map_zero, sub_zero]

theorem jetSubstPS_psJet (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) : jetSubstPS (m := m) Q (psJet m f) = psJet m (MvPowerSeries.subst Q f) := by
  rw [jetSubstPS_eq_jetMap m Q hQ, psJet_subst m Q hQ f]

theorem const_substPS (Q : κ' → MvPowerSeries κ'' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ' S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst Q f) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf

theorem jetSubstPS_comp (m : ℕ) (P : κ → MvPowerSeries κ' S) (Q : κ' → MvPowerSeries κ'' S)
    (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    (jetSubstPS (m := m) Q).comp (jetSubstPS (m := m) P) =
      jetSubstPS (m := m) (fun i => MvPowerSeries.subst Q (P i)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m P hP i, jetSubstPS_psJet m Q hQ,
    jetSubstPS_X m _ (fun i => const_substPS Q hQ (P i) (hP i)) i]

theorem jetSubstP_eq_jetSubstPS (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by
  have hσ' : ∀ i, MvPowerSeries.constantCoeff ((σ i : MvPowerSeries κ' S)) = 0 := fun i => by
    show MvPowerSeries.coeff (0 : κ' →₀ ℕ) ((σ i : MvPowerSeries κ' S)) = 0
    rw [MvPolynomial.coeff_coe]
    exact hσ i
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ hσ' i, psJet_coe]
  unfold jetSubstP
  rw [jetMap_mk, MvPolynomial.aeval_X, hσ i, map_zero, sub_zero]

theorem jetCopy_eq_PS {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]
  unfold jetCopy
  rw [jetMap_mk, MvPolynomial.aeval_X]

theorem psJet_subst_trunc (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) :
    psJet m (MvPowerSeries.subst Q ((psTrunc m f : MvPolynomial κ S) : MvPowerSeries κ S)) =
      psJet m (MvPowerSeries.subst Q f) := by
  rw [psJet_subst m Q hQ, psJet_subst m Q hQ, psJet_coe]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BqOriginSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

def BqOriginSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E)
      (wLa : ExpGC.AdTy Xo a), ExpGD.AdRel C a wLa → ∀ (wLb : ExpGC.AdTy Xo (H.bar a)), ExpGD.AdRel C (H.bar a) wLb →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J →
        val (ExpGC.Bq C.wP a wLa wLb) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
end
end
