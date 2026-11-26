module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.EndRosati

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem mφ_comp {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂)
    {T : Over S} (x y : T ⟶ H₁) (k : MK) :
    (lift x y).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr)
        (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₁ ![x, y] I.down).left ≫ coprod.inl) k := by
  rcases k with I | I
  · have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) ≫ psum H₂ (x2 H₂) I.down =
        psum H₂ ![x ≫ a, y ≫ b] I.down := by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr =
      (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr
    rw [← e]
    simp only [Over.comp_left, Category.assoc]
  · have e : lift x y ≫ psum H₁ (x2 H₁) I.down = psum H₁ ![x, y] I.down := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl = (psum H₁ ![x, y] I.down).left ≫ coprod.inl
    rw [← e]
    simp only [Over.comp_left, Category.assoc]

theorem mφ_push {S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} [GrpObj E₁] [IsCommMonObj E₁] [GrpObj E₂]
    [IsCommMonObj E₂] {A₁ A₂ : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂)
    (hm₁ : ∀ {T : Over S'} (x y : T ⟶ E₁), push p₁ (x * y) = push p₁ x * push p₁ y)
    (hm₂ : ∀ {T : Over S'} (x y : T ⟶ E₂), push p₂ (x * y) = push p₂ x * push p₂ y)
    {a' b' : E₁ ⟶ E₂} {a b : A₁ ⟶ A₂} (ha : push p₂ a' = p₁ ≫ a) (hb : push p₂ b' = p₁ ≫ b)
    {T : Over S'} (x y : T ⟶ E₁) (k : MK) :
    (lift (push p₁ x) (push p₁ y)).left ≫ mφ A₁ A₂ a b k =
      (lift x y).left ≫ mφ E₁ E₂ a' b' k ≫ coprod.map p₁.left p₂.left := by
  let ρ₁ : (T ⟶ E₁) →* ((Over.map j).obj T ⟶ A₁) :=
    MonoidHom.mk' (push p₁) fun x y => hm₁ x y
  let ρ₂ : (T ⟶ E₂) →* ((Over.map j).obj T ⟶ A₂) :=
    MonoidHom.mk' (push p₂) fun x y => hm₂ x y
  have pa : ∀ (z : T ⟶ E₁) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}, push p₂ c' = p₁ ≫ c → push p₂ (z ≫ c') = push p₁ z ≫ c :=
    fun z c' c h => by
      simp only [push, Functor.map_comp, Category.assoc] at h ⊢
      rw [h]
  rw [← Category.assoc, mφ_comp, mφ_comp]
  rcases k with I | I
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₂ ![x ≫ a', y ≫ b'] I.down
    have e' : (fun i => ρ₂ ((![x ≫ a', y ≫ b'] : Fin 2 → (T ⟶ E₂)) i)) = ![push p₁ x ≫ a, push p₁ y ≫ b] := by
      funext i
      fin_cases i
      · exact pa x ha
      · exact pa y hb
    rw [e'] at e
    show (psum A₂ ![push p₁ x ≫ a, push p₁ y ≫ b] I.down).left ≫ coprod.inr =
      ((psum E₂ ![x ≫ a', y ≫ b'] I.down).left ≫ coprod.inr) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inr_map, ← Category.assoc]
    rfl
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₁ ![x, y] I.down
    have e' : (fun i => ρ₁ ((![x, y] : Fin 2 → (T ⟶ E₁)) i)) = ![push p₁ x, push p₁ y] := by
      funext i
      fin_cases i <;> rfl
    rw [e'] at e
    show (psum A₁ ![push p₁ x, push p₁ y] I.down).left ≫ coprod.inl =
      ((psum E₁ ![x, y] I.down).left ≫ coprod.inl) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inl_map, ← Category.assoc]
    rfl

end GlobalTheory.HomMum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTorusInvariantOfMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTorusInvariantOfMultiplicative
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati

theorem prod_psum_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A)
    (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  rcases hxy with rfl | rfl
  · rw [_root_.one_mul y, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]
  · rw [_root_.mul_one x, mul_left_comm (h x.left)⁻¹, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]

theorem prod_mφ_eq_one {S : Scheme.{0}} {H₁ H₂ T : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (x y : T ⟶ H₁) (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k = 1 := by
  simp only [mφ_comp]
  rw [Fintype.prod_sum_type]
  have e₁ := prod_psum_eq_one (x ≫ a) (y ≫ b)
    (hxy.imp (fun e => by rw [e, MonObj.one_comp]) (fun e => by rw [e, MonObj.one_comp]))
    (fun q => h (q ≫ coprod.inr))
  have e₂ := prod_psum_eq_one x y hxy (fun q => h (q ≫ coprod.inl))
  simp only [Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
  rw [e₁, e₂, inv_one, _root_.mul_one]

theorem push_pG_two {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) :
    push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ a := by
  rw [push, GtCoord.pG, GtCoord.pG, ← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (push_fstG e a)


set_option maxHeartbeats 1600000 in
theorem gen_invariant_of_mul : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ v hv hm
  have := (U₁.gt e).q_hom
  have := (U₁.gt e).i_hom
  have hM := jn_isLB D₁.toPre D₂.toPre
  have ti : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (t : Z ⟶ splitTorus _ D₁.toPre.X),
      push (U₁.gt e).pG (t ≫ (U₁.gt e).i) = 1 := fun t =>
    (TorusCoord.im_congr (U₁.gt e) (x' := 1) (by
      rw [Category.assoc, (U₁.gt e).isKernel.w, MonObj.one_comp, comp_toUnit_assoc, Hom.one_def])).trans
      (TorusCoord.im_one (U₁.gt e))
  have unit : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G₁),
      push (U₁.gt e).pG x = 1 ∨ push (U₁.gt e).pG y = 1 → ∃ ρ : Γ(T.left, ⊤)ˣ,
        ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (r : Z ⟶ T) (z : Z.left) (J),
          Good (JN D₁.toPre D₂.toPre) z J →
          gm r.left z ⊤ ρ = val v (lift (r ≫ x) (r ≫ y)).left z J := fun x y hxy => by
    obtain ⟨ρ, hρ⟩ := exists_unit_of_formal hM (fun V _ h =>
      (Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (mφ_push (U₁.gt e).pG (U₂.gt e).pG
        (TorusCoord.im_mul (U₁.gt e)) (TorusCoord.im_mul (U₂.gt e)) (push_pG_two U₁ U₂ e hf)
        (push_pG_two U₁ U₂ e hg) x y k).symm).trans
        (prod_mφ_eq_one fB gB (push (U₁.gt e).pG x) (push (U₁.gt e).pG y) hxy h))
      (LB.pullGen (JN D₁.toPre D₂.toPre) _ _ v (lift x y).left) (DVR.pullGen_isGen _ _ _ _ hv _)
    refine ⟨ρ, fun Z r z J hJ => (hρ _ r.left z J hJ).symm.trans ((val_pull hJ _ _ _).trans ?_)⟩
    rw [← Over.comp_left, comp_lift]
  have one : ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J),
      Good (JN D₁.toPre D₂.toPre) z J →
      ∀ y : T ⟶ thickObj R I e G₁, val v (lift 1 y).left z J = 1 ∧ val v (lift y 1).left z J = 1 :=
    fun T z J hJ y => by
      have := hm T z J hJ 1 1 y (TorusCoord.im_one (U₁.gt e))
      rw [_root_.mul_one] at this
      exact ⟨left_eq_mul.1 this.1, left_eq_mul.1 this.2⟩
  have gd : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good (JN D₁.toPre D₂.toPre) z J := fun {Z} z => by
    choose J hJ using fun χ : Z ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left => Geo.Tor.exists_chart hM (χ z)
    exact ⟨J, hJ⟩
  obtain ⟨ρ₁, h₁⟩ := unit (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (snd _ _) (Or.inl (ti _))
  obtain ⟨ρ₂, h₂⟩ := unit (snd _ _) (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (Or.inr (ti _))
  have e₁ := fun Z t y z J hJ => h₁ Z (lift t y) z J hJ
  have e₂ := fun Z t y z J hJ => h₂ Z (lift t y) z J hJ
  simp only [lift_fst_assoc, lift_snd] at e₁ e₂
  have k₁ := fun Z t y z => unit_eq_one ρ₁ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).1) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₁ Z t 1 z J hJ).trans (one Z z J hJ _).2) (Z := Z) t y z
  have k₂ := fun Z t y z => unit_eq_one ρ₂ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).2) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₂ Z t 1 z J hJ).trans (one Z z J hJ _).1) (Z := Z) t y z
  intro T z J hJ x x' y y' hx hy
  obtain ⟨t, rfl⟩ := TorusCoord.exists_torus (U₁.gt e) x x' hx
  obtain ⟨t', rfl⟩ := TorusCoord.exists_torus (U₁.gt e) y y' hy
  rw [(hm T z J hJ _ x' _ (ti t)).1, (hm T z J hJ _ y' x' (ti t')).2, ← e₁ T t _ z J hJ, ← e₂ T t' _ z J hJ, k₁, k₂,
    _root_.one_mul, _root_.one_mul]

end GlobalTheory.HomMum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTorusInvariantOfMultiplicativeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_torus_invariant_of_multiplicative : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  first | exact @GlobalTheory.HomMum.gen_invariant_of_mul | exact GlobalTheory.HomMum.gen_invariant_of_mul | (intros; apply GlobalTheory.HomMum.gen_invariant_of_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedGeneratorThickenedAbelianPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedGeneratorThickenedAbelianPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section
namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati


set_option maxHeartbeats 800000 in
theorem exists_gen_thick_two : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg v hv hi
  have hM := jn_isLB D₁.toPre D₂.toPre
  have := (U₁.gt e).q_affine
  have pp : ∀ {c : G₁ ⟶ G₂} {cB : D₁.toPre.P.A ⟶ D₂.toPre.P.A},
      (Over.pullback (thick R I e)).map c ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map cB →
      push (U₂.gt e).pG ((Over.pullback (thick R I e)).map c) = (U₁.gt e).pG ≫ cB := fun {c cB} h => by
    rw [push, GtCoord.pG, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc, Category.assoc]
    exact congrArg _ (GlobalTheory.EndRosati.push_fstG e cB)
  let m := (U₁.gt e).q ⊗ₘ (U₁.gt e).q
  have : Flat m.left := MorphismProperty.pullbackMap (P := @Flat) (U₁.gt e).q_flat (U₁.gt e).q_flat
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have : Surjective m.left :=
    have : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ => inferInstance⟩
    MorphismProperty.pullbackMap (P := @Surjective) (U₁.gt e).q_surj (U₁.gt e).q_surj
      (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have qc : QuasiCompact (U₁.gt e).q.left := inferInstance
  have : QuasiCompact m.left := MorphismProperty.pullbackMap (P := @QuasiCompact) qc qc
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  let Be := thickObj R I e D₁.toPre.P.A
  let π := lift (push (fstG I e D₁.toPre.P.A) (fst Be Be)) (push (fstG I e D₁.toPre.P.A) (snd Be Be))
  have hπ : m.left ≫ π.left = (lift (push (U₁.gt e).pG (fst _ _)) (push (U₁.gt e).pG (snd _ _))).left := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) (fst _ _ ≫ (U₁.gt e).q) (snd _ _ ≫ (U₁.gt e).q)).trans ?_
    simp only [push, Functor.map_comp, Category.assoc]
    rfl
  have hφ : ∀ k, mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f)
      ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left =
      m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k := fun k => by
    rw [← Category.assoc, hπ, mφ_push (U₁.gt e).pG (U₂.gt e).pG (TorusCoord.im_mul (U₁.gt e))
      (TorusCoord.im_mul (U₂.gt e)) (pp hf) (pp hg) (fst _ _) (snd _ _) k, lift_fst_snd]
    exact (Category.id_comp _).symm
  obtain ⟨v', hv', vv⟩ := exists_gen hM (φ' := fun k => m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k)
    (ε' := mε) (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (hφ k)) v hv
  obtain ⟨t, ht, -⟩ := CoordCompare.exists_gen_of_val_eq hM _ _ m.left v' hv' fun Z r r' z J hJ h => by
    have hw : r ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom := by
      rw [← Over.w m, reassoc_of% h]
    let T := Over.mk (r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom)
    let s : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r hw
    let s' : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r' rfl
    have hs : s ≫ m = s' ≫ m := Over.OverMorphism.ext h
    have := hi T z J hJ (s ≫ fst _ _) (s' ≫ fst _ _) (s ≫ snd _ _) (s' ≫ snd _ _)
      (by simpa [m] using congrArg (· ≫ fst _ _) hs) (by simpa [m] using congrArg (· ≫ snd _ _) hs)
    rw [lift_comp_fst_snd, lift_comp_fst_snd] at this
    exact (vv _ r z J hJ).trans (this.trans (vv _ r' z J hJ).symm)
  have hn : (lift ((Over.pullback (thick R I e)).map (fst D₁.toPre.P.A D₁.toPre.P.A))
      ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left ≫ π.left =
      pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) _ _).trans ?_
    rw [GlobalTheory.EndRosati.push_fstG, GlobalTheory.EndRosati.push_fstG, lift_comp_fst_snd]
    rfl
  have := (GlobalTheory.EndRosati.gen_iff_sum hM _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht (lift ((Over.pullback (thick R I e)).map
    (fst D₁.toPre.P.A D₁.toPre.P.A)) ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left⟩
  refine (GlobalTheory.EndRosati.gen_iff_sum hM _ _).2 (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) this)
  rw [← hn, Category.assoc]

end GlobalTheory.HomMum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedGeneratorThickenedAbelianPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_generator_thickened_abelian_part : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  first | exact @GlobalTheory.HomMum.exists_gen_thick_two | exact GlobalTheory.HomMum.exists_gen_thick_two | (intros; apply GlobalTheory.HomMum.exists_gen_thick_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedUniformisationIsoOneLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedUniformisationIsoOneLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.Mum.Two.GlueLevel

section General

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}

theorem map_inl_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁) :
    (coprod.map f₁ f₂) ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x) = (coprod.inl : B₁ ⟶ B₁ ⨿ B₂) (f₁ x) := by
  change ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inl_map]; rfl

theorem map_inr_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂) :
    (coprod.map f₁ f₂) ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x) = (coprod.inr : B₂ ⟶ B₁ ⨿ B₂) (f₂ x) := by
  change ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inr_map]; rfl

theorem mem_pull_inl (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₁.pull f₁).U (fun _ => (J PUnit.unit).1) := by
  rw [mem_pull, mem_pull, map_inl_apply]
  exact (isPart_inl M₁ M₂).mem _ _

theorem mem_pull_inr (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₂.pull f₂).U (fun _ => (J PUnit.unit).2) := by
  rw [mem_pull, mem_pull, map_inr_apply]
  exact (isPart_inr M₁ M₂).mem _ _

end General

section Glue

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}
  {p₁ : X₁ ⟶ B₁} {p₂ : X₂ ⟶ B₂} {f₁ : X₁ ⟶ H₁} {f₂ : X₂ ⟶ H₂}

theorem gm_div_inl (x : X₁) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inl x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₁) x _ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).g
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inl_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inl M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inl M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inl L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inl L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inl x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₁) (F := p₁) (L' := L₁.pull f₁) (𝟙 X₁) x (I₁ PUnit.unit).1 (I₂ PUnit.unit).1
    (fun _ => (K₁ PUnit.unit).1) (fun _ => (K₂ PUnit.unit).1) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inl x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₁ f₁ (𝟙 X₁) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inl_map, coprod.inl_map,
    (isPart_inl M₁ M₂).g _ p₁ x _ _ a₁' a₂', (isPart_inl L₁ L₂).g _ f₁ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem gm_div_inr (x : X₂) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inr x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₂) x _ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).g
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inr_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inr M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inr M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inr L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inr L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inr x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₂) (F := p₂) (L' := L₂.pull f₂) (𝟙 X₂) x (I₁ PUnit.unit).2 (I₂ PUnit.unit).2
    (fun _ => (K₁ PUnit.unit).2) (fun _ => (K₂ PUnit.unit).2) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inr x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₂ f₂ (𝟙 X₂) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inr_map, coprod.inr_map,
    (isPart_inr M₁ M₂).g _ p₂ x _ _ a₁' a₂', (isPart_inr L₁ L₂).g _ f₂ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem exists_iso_glue (w₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (w₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂))
    (hw₁ : w₁.IsGen) (hw₂ : w₂.IsGen) :
    ∃ W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)), W.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₁ (r z) ∈ M₁.U j.1 →
        f₁ (r z) ∈ L₁.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw w₁ r z j.1 (fun _ => k.1)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₂) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₂ (r z) ∈ M₂.U j.2 →
        f₂ (r z) ∈ L₂.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw w₂ r z j.2 (fun _ => k.2) := by
  have key : ∀ p : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι),
      ∃ a : Γ(X₁ ⨿ X₂,
        (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inl) z _ a =
          gm ψ z _ (w₁.s (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inr) z _ a =
          gm ψ z _ (w₂.s (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2)) := fun p =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)
      ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))
      ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2))
      (fun x hx => ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2⟩)
      (fun x hx => ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2⟩) _ _
  choose s hs₁ hs₂ using key
  let W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)) := ⟨s⟩
  refine ⟨W, fun i j => unit_ext_coprod (fun x hx => ?_) (fun x hx => ?_), fun Z r z j k hj hk => ?_,
    fun Z r z j k hj hk => ?_⟩
  · have e₁ := hs₁ i X₁ (𝟙 _) x hx.1
    have e₂ := hs₁ j X₁ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₁) x _) (hw₁ (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
      (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1))
    have m : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) ⊓
        (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inl x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · have e₁ := hs₂ i X₂ (𝟙 _) x hx.1
    have e₂ := hs₂ j X₂ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₂) x _) (hw₂ (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
      (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2))
    have m : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) ⊓
        (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inr x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · exact hs₁ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inl L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩
  · exact hs₂ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inr L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩

end Glue

theorem exists_iso_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ), ∃ W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left)), W.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e
  exact exists_iso_glue (U₁.w e) (U₂.w e) (U₁.w_gen e) (U₂.w_gen e)

end GlobalTheory.Mum.Two.GlueLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedUniformisationIsoOneLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_uniformisation_iso_one_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ), ∃ W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left)), W.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) := by
  first | exact @GlobalTheory.Mum.Two.GlueLevel.exists_iso_level | exact GlobalTheory.Mum.Two.GlueLevel.exists_iso_level | (intros; apply GlobalTheory.Mum.Two.GlueLevel.exists_iso_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMultiplicativeOnQuotientKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMultiplicativeOnQuotientKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

theorem prod_psum_two {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A) {V : Type}
    [CommGroup V] (h : (T.left ⟶ A.left) → V) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ A).left := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_mφ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {V : Type} [CommGroup V] (h : (T.left ⟶ H₁.left ⨿ H₂.left) → V) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ((Finset.prod_congr rfl fun I _ => ?_).trans
    (prod_psum_two (x ≫ a) (y ≫ b) (fun q => h (q ≫ coprod.inr))))
    ((Finset.prod_congr rfl fun I _ => ?_).trans ((Finset.prod_inv_distrib _).trans
      (congrArg (·⁻¹) (prod_psum_two x y (fun q => h (q ≫ coprod.inl))))))
  · rw [mφ_comp]; rfl
  · rw [mφ_comp]; exact zpow_neg _ _

theorem push_comp_two {S S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} {A₁ A₂ : Over S}
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}
    (h : GlobalTheory.EndRosati.push p₂ c' = p₁ ≫ c) {T : Over S'} (x : T ⟶ E₁) :
    GlobalTheory.EndRosati.push p₂ (x ≫ c') = GlobalTheory.EndRosati.push p₁ x ≫ c := by
  simp only [GlobalTheory.EndRosati.push, Functor.map_comp, Category.assoc] at h ⊢
  rw [h]

theorem push_pG_pair {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {fB : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB) :
    GlobalTheory.EndRosati.push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ fB := by
  rw [GlobalTheory.EndRosati.push]
  simp only [GtCoord.pG]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (GlobalTheory.EndRosati.push_fstG e fB)

theorem add_left_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a a' b : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ (x * y))⁻¹ * (W₁ (x' * y))⁻¹ * W₁ x * W₁ x' * W₁ y *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ (a * b))⁻¹ * (W₂ (a' * b))⁻¹ * W₂ a * W₂ a' * W₂ b *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ *
        v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * y) * (W₁ x)⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a' * b) * (W₂ a')⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x' * y) * (W₁ x')⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₂) := by
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

theorem add_right_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a b b' : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (y * x * x') * (W₁ (y * x))⁻¹ * (W₁ (y * x'))⁻¹ * (W₁ (x * x'))⁻¹ * W₁ y * W₁ x * W₁ x' *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * b * b') * (W₂ (a * b))⁻¹ * (W₂ (a * b'))⁻¹ * (W₂ (b * b'))⁻¹ * W₂ a * W₂ b * W₂ b' *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * (b * b')) * (W₂ a)⁻¹ * (W₂ (b * b'))⁻¹ * W₂ 1) *
        (W₁ (y * (x * x')) * (W₁ y)⁻¹ * (W₁ (x * x'))⁻¹ * W₁ 1)⁻¹ * v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (y * x) * (W₁ y)⁻¹ * (W₁ x)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a * b') * (W₂ a)⁻¹ * (W₂ b')⁻¹ * W₂ 1) * (W₁ (y * x') * (W₁ y)⁻¹ * (W₁ x')⁻¹ * W₁ 1)⁻¹ * v₂) := by
  rw [← _root_.mul_assoc a b b', ← _root_.mul_assoc y x x']
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

end GlobalTheory.HomMum

end

namespace GlobalTheory.HomMum


set_option maxHeartbeats 1600000 in
theorem exists_gen_mul_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))), W.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) → ∀ (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), u.IsGen → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε), v.IsGen ∧ (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg W hW hW₁ hW₂ u hu hadd
  let f' := (Over.pullback (thick R I e)).map f
  let g' := (Over.pullback (thick R I e)).map g
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have hL : (join U₁.LG.L U₂.LG.L).IsLB := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u', hu', vu⟩ := exists_gen hL
    (φ' := fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k ≫
      coprod.map (fstG I e G₁).left (fstG I e G₂).left) (ε' := mε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (by
      rw [mφ_push (fstG I e G₁) (fstG I e G₂) (GlobalTheory.EndRosati.fstG_mul e) (GlobalTheory.EndRosati.fstG_mul e)
        (GlobalTheory.EndRosati.push_fstG e f) (GlobalTheory.EndRosati.push_fstG e g) (fst _ _) (snd _ _) k, lift_fst_snd,
        Over.id_left, Category.id_comp]))
    (LB.pullGen (join U₁.LG.L U₂.LG.L) _ _ u
      (lift (GlobalTheory.EndRosati.push (fstG I e G₁) (fst (thickObj R I e G₁) (thickObj R I e G₁)))
        (GlobalTheory.EndRosati.push (fstG I e G₁) (snd (thickObj R I e G₁) (thickObj R I e G₁)))).left)
    (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨v, hv, vv⟩ := GlobalTheory.EndRosati.exists_gen_through hL (jn_isLB D₁.toPre D₂.toPre) W hW
    (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k) mε u' hu'
  refine ⟨v, hv, fun T z J hJ x x' y hx => ?_⟩
  choose N hN using fun χ : T.left ⟶ G₁.left ⨿ G₂.left => exists_chart hL (χ z)
  have hN' : Good (join U₁.LG.L U₂.LG.L) z N := hN
  have gJ₁ : Good D₁.toPre.P.L z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inl _ _).good hJ
  have gJ₂ : Good D₂.toPre.P.L z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inr _ _).good hJ
  have gN₁ : Good U₁.LG.L z (rl N) := (isPart_inl _ _).good hN'
  have gN₂ : Good U₂.LG.L z (rr N) := (isPart_inr _ _).good hN'
  let W₁ : (T ⟶ thickObj R I e G₁) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N) q.left
  let W₂ : (T ⟶ thickObj R I e G₂) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N) q.left
  have hinl : ∀ q : T ⟶ thickObj R I e G₁, gw W (q.left ≫ coprod.inl) z
      (J ((q.left ≫ coprod.inl) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inl) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₁ q := fun q => by
    have := hW₁ T.left q.left z (J ((q.left ≫ (U₁.gt e).pG.left) ≫ coprod.inl))
      (N ((q.left ≫ (fstG I e G₁).left) ≫ coprod.inl)) (gJ₁ _) (gN₁ _)
    simp only [Category.assoc, coprod.inl_map] at this ⊢
    exact this
  have hinr : ∀ q : T ⟶ thickObj R I e G₂, gw W (q.left ≫ coprod.inr) z
      (J ((q.left ≫ coprod.inr) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inr) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₂ q := fun q => by
    have := hW₂ T.left q.left z (J ((q.left ≫ (U₂.gt e).pG.left) ≫ coprod.inr))
      (N ((q.left ≫ (fstG I e G₂).left) ≫ coprod.inr)) (gJ₂ _) (gN₂ _)
    simp only [Category.assoc, coprod.inr_map] at this ⊢
    exact this
  let p₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ G₁) := GlobalTheory.EndRosati.push (fstG I e G₁)
  let p₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ G₂) := GlobalTheory.EndRosati.push (fstG I e G₂)
  let q₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ D₁.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₁.gt e).pG
  let q₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ D₂.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₂.gt e).pG
  have hV : ∀ a b : T ⟶ thickObj R I e G₁, val v (lift a b).left z J =
      (W₂ ((a ≫ f') * (b ≫ g')) * (W₂ (a ≫ f'))⁻¹ * (W₂ (b ≫ g'))⁻¹ * W₂ 1) *
        (W₁ (a * b) * (W₁ a)⁻¹ * (W₁ b)⁻¹ * W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (val u (lift (p₁ a) (p₁ b)).left z N) :=
    fun a b => by
      refine (vv _ _ z J N hJ hN').trans (congrArg₂ (· * ·) ?_
        ((vu _ _ z N hN').trans ((val_pull hN' _ _ _).trans (congrArg (val u · z N) (GlobalTheory.EndRosati.lift_push _ a b)))))
      refine (prod_mφ f' g' a b (fun ψ => gw W ψ z (J (ψ ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
        (fun _ => N (ψ ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)))).trans ?_
      beta_reduce
      erw [hinr ((a ≫ f') * (b ≫ g')), hinr (a ≫ f'), hinr (b ≫ g'), hinr 1, hinl (a * b), hinl a, hinl b, hinl 1]
  have hc₁ : ∀ a b c : T ⟶ thickObj R I e G₁,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) (q₁ b) (q₁ c)) =
      W₁ (a * b * c) * (W₁ (a * b))⁻¹ * (W₁ (a * c))⁻¹ * (W₁ (b * c))⁻¹ * W₁ a * W₁ b * W₁ c * (W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₁.cubG (T := (Over.map (thick R I e)).obj T) z (rl N) (p₁ a) (p₁ b) (p₁ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₁ ![a, b, c] gJ₁ gN₁).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N))))
  have hc₂ : ∀ a b c : T ⟶ thickObj R I e G₂,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) (q₂ b) (q₂ c)) =
      W₂ (a * b * c) * (W₂ (a * b))⁻¹ * (W₂ (a * c))⁻¹ * (W₂ (b * c))⁻¹ * W₂ a * W₂ b * W₂ c * (W₂ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₂.cubG (T := (Over.map (thick R I e)).obj T) z (rr N) (p₂ a) (p₂ b) (p₂ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₂ ![a, b, c] gJ₂ gN₂).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N))))
  have C₁ := isCub_cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₁
  have C₂ := isCub_cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₂
  have c₁ : ∀ a b c, q₁ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₁ b) (q₁ c)) h).trans (C₁.face _ _)).symm.trans (hc₁ a b c)
  have c₂ : ∀ a b c, q₁ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) · (q₁ c)) h).trans (C₁.face₂ _ _)).symm.trans (hc₁ a b c)
  have d₁ : ∀ a b c, q₂ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₂ b) (q₂ c)) h).trans (C₂.face _ _)).symm.trans (hc₂ a b c)
  have d₂ : ∀ a b c, q₂ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) · (q₂ c)) h).trans (C₂.face₂ _ _)).symm.trans (hc₂ a b c)
  have hx' : q₁ x = 1 := hx
  have xf : q₂ (x ≫ f') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hf) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have xg : q₂ (x ≫ g') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hg) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have pf : ∀ a, p₁ a ≫ f = p₂ (a ≫ f') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e f) a).symm
  have pg : ∀ a, p₁ a ≫ g = p₂ (a ≫ g') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e g) a).symm
  have pm : p₁ x * p₁ x' = p₁ (x * x') := (GlobalTheory.EndRosati.fstG_mul e x x').symm
  obtain ⟨r₁, r₂⟩ := hadd ((Over.map (thick R I e)).obj T) z N hN' (p₁ x) (p₁ x') (p₁ y)
  rw [pm, pf, pf, pg] at r₁
  rw [pm, pf, pg, pg] at r₂
  rw [hV, hV, hV, hV, hV, hV, MonObj.mul_comp x x' f', MonObj.mul_comp x x' g']
  exact ⟨add_left_two W₁ W₂ (c₁ _ _ _ hx') (d₁ _ _ _ xf) r₁, add_right_two W₁ W₂ (c₂ _ _ _ hx') (d₂ _ _ _ xg) r₂⟩

end GlobalTheory.HomMum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMultiplicativeOnQuotientKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_multiplicative_on_quotient_kernel : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))), W.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) → ∀ (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), u.IsGen → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε), v.IsGen ∧ (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) := by
  first | exact @GlobalTheory.HomMum.exists_gen_mul_level | exact GlobalTheory.HomMum.exists_gen_mul_level | (intros; apply GlobalTheory.HomMum.exists_gen_mul_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

theorem GlobalTheory.HomMum.exists_gen_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), IsNrm u → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ u hu hadd
  obtain ⟨W, hW, h₁, h₂⟩ := GlobalTheory.T.exists_glued_uniformisation_iso_one_level U₁ U₂ e
  obtain ⟨v, hv, hm⟩ := GlobalTheory.T.exists_generator_multiplicative_on_quotient_kernel U₁ U₂ e hf hg W hW h₁ h₂ u hu.1 hadd
  exact GlobalTheory.T.exists_descended_generator_thickened_abelian_part U₁ U₂ e hf hg v hv (GlobalTheory.T.generator_torus_invariant_of_multiplicative U₁ U₂ e hf hg v hv hm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordGenerator_abelianPart_at_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), IsNrm u → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  first | exact @GlobalTheory.HomMum.exists_gen_level | exact GlobalTheory.HomMum.exists_gen_level | (intros; apply GlobalTheory.HomMum.exists_gen_level <;> assumption)
end
