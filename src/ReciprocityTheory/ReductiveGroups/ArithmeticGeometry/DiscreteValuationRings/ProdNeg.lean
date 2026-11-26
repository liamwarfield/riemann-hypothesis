module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Cube

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def cQ (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

theorem cQ_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cQ D T (a + b) = cQ D T a * cQ D T b := by
  unfold cQ
  rw [D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]

theorem cQ_nsmul (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (a : D.X) : cQ D T (k • a) = cQ D T a ^ k := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero]
    have h0 : cQ D T 0 * cQ D T 0 = cQ D T 0 := by rw [← cQ_add, add_zero]
    simpa using h0
  | succ k ih => rw [succ_nsmul, cQ_add, ih, pow_succ]

theorem comp_cQ {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cQ D T a = cQ D T' a := by
  unfold cQ
  rw [← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left := Category.comp_id _
  have e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left := by
    rw [← Over.comp_left]
    congr 1
    rw [padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]
  have e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  have e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]

theorem prod_neg' {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib, h]

theorem exists_eB (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ}
    (w : LB.Gen (LB.LinComb D.P.L φV εV)) (hw : w.IsGen)
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k) :
    ∃ eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu))
        (fun i => (𝟙 D.P.A * cQ D D.P.A mu).left ≫ D.famφB α i)) (DegPre.deltaε k)), eB.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val eB ρ.left z J = cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹ * val w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  obtain ⟨e, he, ve⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB (α + k • mu))
      (fun i => (𝟙 D.P.A * m).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have S : ∀ {K K' : Type} {_ : Fintype K} {_ : Fintype K'} (f : K ⊕ K' → U),
          ∏ i, f i = (∏ i, f (.inl i)) * ∏ i, f (.inr i) := fun f => Fintype.prod_sum_type f
      rw [S, S]
      erw [S]
      simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε]
      erw [prod_neg' _ _ p₁]
      rw [p₂, p₃, prod_neg' _ _ p₄]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift (𝟙 D.P.A) m)).left)))
      (LB.pullGen D.P.L _ _ w D.P.A.hom))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hw _))
  refine ⟨e, he, fun T ρ z J hJ => ?_⟩
  have E := (ve _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))) (val_pull hJ _ _ _)))
  refine E.trans ?_
  rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]

end Cube

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThickKer
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] {X : Scheme.{0}}

def strMap (p : X ⟶ Sp V) (U : X.Opens) : V →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom

theorem constFn_eq_strMap (p : X ⟶ Sp V) (U : X.Opens) (a : V) : constFn p U a = strMap p U a := rfl

theorem fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem appLE_top_eq {Y W : Scheme.{0}} (f : Y ⟶ W) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

theorem mem_map_of_app_fst_eq_zero (p : X ⟶ Sp V) (J : Ideal V) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (ha : ((pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom a = 0) :
    a ∈ J.map (strMap p U) := by
  let I₀ : Ideal Γ(X, U) := J.map (strMap p U)
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I₀ := Ideal.Quotient.mk I₀
  let ψ : V ⧸ J →+* Γ(X, U) ⧸ I₀ := Ideal.quotientMap I₀ (strMap p U) Ideal.le_comap_map
  let z : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  have hz : ⊤ ≤ z ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : z.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : z.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp, fromSpec_appLE_top]
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (z.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  have m1 : (z ≫ p).appTop = p.appLE ⊤ U le_top ≫ z.appLE U ⊤ hz :=
    ((Scheme.Hom.appLE_comp_appLE z p ⊤ U ⊤ le_top hz).trans (appLE_top_eq _ _)).symm
  have m5 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))).symm
  have m6 : (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)).symm
  have e5 : ∀ c : V, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J c) :=
    fun c => congrArg (fun φ => φ.hom c) m5
  have e6 : ∀ c : V ⧸ J, (Spec.map (CommRingCat.ofHom ψ)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (ψ c) :=
    fun c => congrArg (fun φ => φ.hom c) m6
  have hsq : z ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1
    ext b
    show (z ≫ p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b) =
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    rw [m1, Scheme.Hom.comp_appTop]
    show (z.appLE U ⊤ hz).hom ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b))
    rw [k1, e5, e6, Ideal.quotientMap_mk]
    rfl
  let l := pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) hsq
  have hl : l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = z := pullback.lift_fst _ _ _
  have tr : ∀ (w : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X) (hw : w = z) (e : ⊤ ≤ w ⁻¹ᵁ U),
      (w.appLE U ⊤ e).hom a = (z.appLE U ⊤ hz).hom a := by
    intro w hw e
    subst hw
    rfl
  have k2 : ((l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appLE U ⊤
      (hl ▸ hz)).hom a = 0 := by
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  rw [tr _ hl, k1] at k2
  have h1 : q a = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).hom.hom k2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem loc_div {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, hU, g, rfl⟩ := P.presheaf.exists_germ_eq t
  have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
  have e : gs (𝟙 P) x (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) x (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := by
    rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_constFn p' _ _ x hm, Category.id_comp, ht,
      gs_eq _ x U hU]
    rfl
  rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
  obtain ⟨U', hU', i₁, i₂, e'⟩ := P.presheaf.germ_eq x hm hm _ _ e
  have le : U' ≤ W ⊓ U := i₁.le
  refine ⟨U', le.trans inf_le_left, hU', (P.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom g, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 P) y U') e'
  have k := (gs_res (𝟙 P) y le hy _).symm.trans (e''.trans (gs_res (𝟙 P) y le hy _))
  have hy' : (𝟙 P : P ⟶ P) y ∈ W ⊓ U := le hy
  have k' : gs (𝟙 P) y (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) y (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := k
  rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_constFn p' _ _ y hy', Category.id_comp] at k'
  rw [k', gs_res _ y _ hy]

theorem dvd_germ_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r ∣
      gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a := by
  let P := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  let f : P ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of V) J
  have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have h' : cst (f ≫ p) x' r ∣ gs (𝟙 P) x' (f ⁻¹ᵁ W) ((f.app W).hom a) := by
    rw [gs_pull (𝟙 P) f x' W hx, Category.id_comp]; exact h
  obtain ⟨U', hU'W, hxU', t', ht'⟩ := loc_div (f ≫ p) (f ⁻¹ᵁ W) ((f.app W).hom a) r x' hx h'
  obtain ⟨O, hO, hOeq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.1 U'.isOpen
  have hxO : f x' ∈ O := by
    have : x' ∈ f.base ⁻¹' O := by rw [hOeq]; exact hxU'
    exact this
  obtain ⟨U, hU, hxU, hUsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
    (show f x' ∈ (⟨O, hO⟩ ⊓ W : X.Opens) from ⟨hxO, hx⟩)
  have hUW : U ≤ W := hUsub.trans inf_le_right
  have hfU : f ⁻¹ᵁ U ≤ U' := fun y hy => by
    have hyO : f y ∈ O := (hUsub hy).1
    have : y ∈ f.base ⁻¹' O := hyO
    rw [hOeq] at this
    exact this
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective f U hU ((P.presheaf.map (homOfLE hfU).op).hom t')
  have hd : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a) = (f.app U).hom (constFn p U r * b) := by
    apply fn_ext
    intro y hy
    have hyW : f y ∈ W := hUW hy
    have L1 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy ((X.presheaf.map (homOfLE hUW).op).hom a)
      rw [Category.id_comp, gs_res f y hUW hy] at e1
      have e2 := gs_pull (𝟙 P) f y W hyW a
      rw [Category.id_comp] at e2
      rw [e1, ← e2]
      exact ht' y (hfU hy)
    have L2 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom (constFn p U r * b)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy (constFn p U r * b)
      rw [Category.id_comp, gs_mul f y U hy, gs_constFn p U f y hy] at e1
      have e3 := gs_pull (𝟙 P) f y U hy b
      rw [Category.id_comp, hb, gs_res (𝟙 P) y hfU hy] at e3
      rw [e1, e3]
    exact L1.trans L2.symm
  have hd0 : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hmem := mem_map_of_app_fst_eq_zero p J hU _ hd0
  have hle : J.map (strMap p U) ≤ Ideal.span {strMap p U r} := by
    refine (Ideal.map_mono hJ).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hle hmem)
  have ha : (X.presheaf.map (homOfLE hUW).op).hom a = constFn p U r * (b + c) := by
    rw [mul_add, ← constFn_eq_strMap] at *
    linear_combination -hc
  refine ⟨gs (𝟙 X) (f x') U (b + c), ?_⟩
  rw [← gs_res (𝟙 X) (f x') hUW hxU, ha, gs_mul (𝟙 X) (f x') U hxU, gs_constFn p U (𝟙 X) (f x') hxU, Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem appTop_specMap {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop.hom r = (Scheme.ΓSpecIso S).inv.hom (g.hom ((Scheme.ΓSpecIso R).hom.hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

abbrev TO : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (fO v hϖ hv)))

abbrev ιS : TF (R := V) F ⟶ TO hϖ hv :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ Spec.map (CommRingCat.ofHom (fO v hϖ hv)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jO : DegPre.BF D.toPre F ⟶ TO hϖ hv ⊗ D.toPre.P.A := ιS hϖ hv ▷ D.toPre.P.A

theorem jO_snd : (jO hϖ hv (D := D)).left ≫ (snd (TO hϖ hv) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jO_fst : (jO hϖ hv (D := D)).left ≫ (fst (TO hϖ hv) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιS hϖ hv).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : F :=
  algebraMap (Ov v) F ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom r)

theorem v_ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : (0 : WithTop ℚ) ≤ v (ιr (v := v) r) := v_nonneg v _

theorem gs_jO {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) := by
  have e1 : gs (ρ ≫ (jO hϖ hv (D := D)).left) z ⊤ ((fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jO hϖ hv (D := D)).left) ≫ (fst (TO hϖ hv) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jO_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιS hϖ hv).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιS hϖ hv).left.appTop.hom r) := (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιr (v := v) r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιr (v := v) r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιS hϖ hv).left = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) from rfl, appTop_specMap]
  rfl

theorem vge_moveO (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {H : (TO hϖ hv ⊗ D.toPre.P.A).left ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left}
    (hh : h ≫ (jO hϖ hv (D := D)).left = (jO hϖ hv).left ≫ H)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → ((TO hϖ hv ⊗ D.toPre.P.A).left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eO : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heO : eO.IsGen)
    (hform : FormEq (Sum.elim (fun i => (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫ D.toPre.famφB α i) ψ)
      (Sum.elim (DegPre.famε k) δ) (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ i) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eO (jO hϖ hv).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L
      (fun j => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ j) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ i) (ρ ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) z J * (val eO ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) eO heO)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heO ρ z hJ)⟩
  choose S hS using e1
  have e2 := fun i => hTW V D.toPre k hk χ (Ov v) (fO v hϖ hv) inferInstance (S i)
  choose m rr σ' hsp using e2
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e3 : ∀ (i : Fin n) (l : Fin (m i)), ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i l) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i l => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i l) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e3
  let eqv := (finSigmaFinEquiv (n := m)).symm
  let co : Fin (∑ i, m i) → F := fun t => c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2)
  have hprB : h ≫ (DegPre.prB D.toPre F).left = (jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left := by
    rw [← jO_snd hϖ hv, ← Category.assoc, hh, Category.assoc]

  have CORE : ∀ (y : (DegPre.BF D.toPre F).left) (I), Good D.toPre.P.L y I →
      sval s' (𝟙 _) y I = ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
    intro y I hIy
    have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
    have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
    rw [H1, H2, hc y I hIy, Finset.sum_mul]
    rw [← (Equiv.sum_comp eqv.symm _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
      rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
    have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I := by
      rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hprB, Category.id_comp]
    have A3 := hS i _ (jO hϖ hv).left y I hIy
    have A4 := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr i l))
      (fun l => pullSec D.toPre.P.L _ _ (σ' i l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hsp i j)
      (jO hϖ hv).left y hIy
    rw [A1, A2]
    have A5 : sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
        (val eO (jO hϖ hv).left y I).val = ∑ l, gs (𝟙 _) y ⊤ (gF D.toPre F (ιr (v := v) (rr i l))) *
          sval (σ'F i l) (𝟙 _) y I := by
      rw [← A3, A4]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [sval_pullSec _ _ _ _ _ y hIy, jO_snd, hσ'F i l _ (𝟙 _) y I hIy, Category.id_comp]
      congr 1
      have := gs_jO hϖ hv (D := D) (𝟙 _) y (rr i l)
      rwa [Category.id_comp] at this
    calc _ = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) * gs (𝟙 _) y ⊤ (gF D.toPre F c) *
          (sval (σ i) ((jO hϖ hv).left ≫ H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) y I *
            (val eO (jO hϖ hv).left y I).val) := by ring
      _ = _ := by
        rw [A5, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [co, eqv, Equiv.symm_symm, map_mul]
        rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, l⟩ : (i : Fin n) × Fin (m i))) = ⟨i, l⟩ from
          Equiv.symm_apply_apply _ _, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
        ring
  refine ⟨∑ i, m i, co, fun t => σ' (eqv t).1 (eqv t).2, fun t => σ'F (eqv t).1 (eqv t).2, fun t => ?_, fun t => ?_,
    fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F _ _ _ (𝟙 _) y J hJ).symm
  · show ((r + q : ℚ) : WithTop ℚ) ≤ v (c * a (eqv t).1 * ιr (v := v) (rr (eqv t).1 (eqv t).2))
    rw [AddValuation.map_mul, AddValuation.map_mul, WithTop.coe_add]
    calc ((r : ℚ) : WithTop ℚ) + (q : WithTop ℚ) = (q : WithTop ℚ) + (r : WithTop ℚ) + 0 := by
          rw [add_zero, add_comm]
      _ ≤ _ := add_le_add (add_le_add hq (hva _)) (v_ιr _)
  · show s'.f j = ∑ t, resTop _ (gF D.toPre F (co t)) * (σ'F (eqv t).1 (eqv t).2).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have mm := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' mm
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ t, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from
            (σ'F (eqv t).1 (eqv t).2).f j)) =
        τ * ∑ t, gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) * sval (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (co t))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (co t)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F (eqv t).1 (eqv t).2) (𝟙 _) y hy' mm, hτ]
      exact mul_left_comm _ _ _
    exact T0.trans ((congrArg (fun x => τ * x) (CORE y I hIy)).trans RHS.symm)

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end
