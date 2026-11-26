module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
set_option linter.dupNamespace false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

structure Host (E : Type) [Field E] [NumberField E] [IsCMField E] where
  d : ℕ
  d_mod : d % 16 = 7
  d_prime : d.Prime
  rt : 𝓞 E
  rt_sq : rt ^ 2 = -(d : 𝓞 E)
  w0 : 𝓞 E
  two_weight_eq_one_add_root : 2 * w0 = 1 + rt
  bar : 𝓞 E ≃+* 𝓞 E
  bar_eq : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)
  unram : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)
  rt0 : ℂ
  sqrt_neg_disc_sq : rt0 ^ 2 = -(d : ℂ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Datum (H : Host E) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 E) La]
  fin : Module.Finite (𝓞 E) La
  proj : Module.Projective (𝓞 E) La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)
  p : ℕ
  q : ℕ
  rank : Module.finrank (𝓞 E) La = p + q
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) (t : ℂ), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im

attribute [instance] Datum.acg Datum.mod

structure Level (H : Host E) where
  M : ℕ
  three_le : 3 ≤ M
  odd : Odd M
  Mb : Ideal (𝓞 E)
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {H.w0}}
  prod : Mb * Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)}
  coprime : Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤
  A : ℕ
  A_pos : 0 < A

def Level.M' {H : Host E} (l : Level H) : ℕ := Nat.lcm l.M l.A

def Level.Dvd {H : Host E} (l l₂ : Level H) : Prop := l.M ∣ l₂.M ∧ l₂.Mb ≤ l.Mb ∧ l.A ∣ l₂.A

def Level.GoodAt {H : Host E} (l : Level H) (p : ℕ) : Prop := 3 ≤ l.M / p ^ l.M.factorization p

variable {S : Scheme.{0}}

structure SAB (H : Host E) (S : Scheme.{0}) where
  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G
  act : OAct (𝓞 E) G
  PP : RigLB G
  cub : CubicalStr G PP
  sym : PP.IsSymmetric
  adj : ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L)
  prim : LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L)

attribute [instance] SAB.grp SAB.comm

structure SABMap {H : Host E} {S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) where
  cm : CubeMap t'.G t.G
  cart : IsGrpPullback t'.G t.G f cm.F
  base : cm.e = f
  act : ∀ a, (t'.act.act a).left ≫ cm.F = cm.F ≫ (t.act.act a).left
  lin : cm.IsPullCubical t'.cub t.cub

abbrev SABMap.φ {H : Host E} {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    t'.G.left ⟶ t.G.left := m.cm.F

def unitOn {R : Type} [CommRing R] (u : Rˣ) : (Γ(Sp R, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u

section Lie

variable {k : Type} [Field k]

abbrev epsPt (t : Sp k ⟶ S) : Over S := Over.mk (spMap (algebraMap k (DualNumber k)) ≫ t)

def epsScale (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom

def IsLieEigen {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k)
    (v : epsPt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScale (τ a)) ≫ v.left

def LieMult {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k)
    (n : ℕ) : Prop :=
  ∃ v : Fin n → (epsPt t ⟶ G), (∀ i, IsLieEigen act t τ (v i)) ∧ ∀ w, IsLieEigen act t τ w →
    ∃! c : Fin n → k, ∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def DetCond {H : Host E} (D : Datum H) {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) (t : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act t τ D.p) ∧ (τ H.rt ≠ ρ → LieMult act t τ D.q)

end Lie

structure Base {H : Host E} (l : Level H) (B : Type) [CommRing B] where
  unit : ∀ n : ℕ, 0 < n → IsUnit (n : B)
  ρ : B
  ρ_sq : ρ ^ 2 = -(H.d : B)
  ζ : B
  ζ_prim : IsPrimitiveRoot ζ l.A

structure TateIso {H : Host E} (D : Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n a b, ev n (a + b) = ev n a * ev n b
  lin : ∀ n (c : 𝓞 E) a, ev n (c • a) = act c (ev n a)
  ker : ∀ n, 0 < n → ∀ a, ev n a = 1 ↔ ∃ b, a = n • b
  onto : ∀ n, 0 < n → ∀ x, x ^ n = 1 ↔ ∃ a, ev n a = x
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, ev (n * m) a ^ m = ev n a
  isom : ∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) (ζ n ^ D.EF a b)

structure Obj {H : Host E} (D : Datum H) (l : Level H) {B : Type} [CommRing B] (b : Base l B) (s : S ⟶ Sp B) where
  t : SAB H S
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  eta : D.La → (𝟙_ (Over S) ⟶ t.G)
  eta_add : ∀ a c, eta (a + c) = eta a * eta c
  eta_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), eta a = 1
  etaA : D.La → (𝟙_ (Over S) ⟶ t.G)
  etaA_add : ∀ a c, etaA (a + c) = etaA a * etaA c
  etaA_ker : ∀ a, etaA (l.A • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β b.ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ l.A : k) = β b.ζ ∧ (∀ a, toUnit _ ≫ etaA a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ eta a = I.ev l.M a

structure ObjMap {H : Host E} {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (o' : Obj D l b' s') (o : Obj D l b s)
    (f : S' ⟶ S) extends SABMap o'.t o.t f where
  eta : ∀ a, (o'.eta a).left ≫ cm.F = f ≫ (o.eta a).left
  etaA : ∀ a, (o'.etaA a).left ≫ cm.F = f ≫ (o.etaA a).left

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (f : G ⟶ G) [IsMonHom f] : IsTan (w ≫ f) := by
  unfold IsTan at hw ⊢
  rw [← Category.assoc, hw]
  first
  | simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
  | simp [Hom.one_def]

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def tvec (c : Fin n → R) : sp (R₀ := R) (DualNumber R) ⟶ G := spMap (dualLift c) ≫ x 1

include hx in
theorem isTan_tvec (c : Fin n → R) : IsTan (tvec (x := x) c) := isTan_dualLift hx c

private lemma sp_tangent_ext {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (hw' : IsTan w')
    (h : tcoord hx w hw = tcoord hx w' hw') : w = w' := by
  calc w = spMap (dualLift (tcoord hx w hw)) ≫ x 1 := tcoord_spec hx w hw
    _ = spMap (dualLift (tcoord hx w' hw')) ≫ x 1 := by rw [h]
    _ = w' := (tcoord_spec hx w' hw').symm

theorem tcoord_tvec (c : Fin n → R) : tcoord hx (tvec (x := x) c) (isTan_tvec hx c) = c :=
  (exists_coord hx (tvec (x := x) c) (isTan_tvec hx c)).unique (tcoord_spec hx _ _) rfl

include hx in
theorem tvec_add (c c' : Fin n → R) : tvec (x := x) (c + c') = tvec (x := x) c * tvec (x := x) c' := by
  refine sp_tangent_ext hx (isTan_tvec hx (c + c')) (isTan_mul (isTan_tvec hx c) (isTan_tvec hx c')) ?_
  rw [tcoord_mul hx (isTan_tvec hx c) (isTan_tvec hx c'), tcoord_tvec, tcoord_tvec, tcoord_tvec]

include hx in
theorem tvec_smul (a : R) (c : Fin n → R) : tvec (x := x) (a • c) = spMap (scaleD a) ≫ tvec (x := x) c := by
  refine sp_tangent_ext hx (isTan_tvec hx (a • c)) (isTan_scale a (isTan_tvec hx c)) ?_
  rw [tcoord_scale hx a (isTan_tvec hx c), tcoord_tvec, tcoord_tvec]

theorem tcoord_congr {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (h : w = w') (hw : IsTan w) (hw' : IsTan w') :
    tcoord hx w hw = tcoord hx w' hw' := by
  subst h
  rfl

def tmap (f : G ⟶ G) [IsMonHom f] : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun c := tcoord hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)
  map_add' c c' := by
    have e : tvec (x := x) (c + c') ≫ f = (tvec (x := x) c ≫ f) * (tvec (x := x) c' ≫ f) := by
      rw [tvec_add hx, Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
    show tcoord hx _ _ = tcoord hx _ _ + tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_mul (isTan_comp (isTan_tvec hx c) f) (isTan_comp (isTan_tvec hx c') f)),
      tcoord_mul hx]
  map_smul' a c := by
    have e : tvec (x := x) (a • c) ≫ f = spMap (scaleD a) ≫ (tvec (x := x) c ≫ f) := by
      rw [tvec_smul hx, Category.assoc]
    show tcoord hx _ _ = a • tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_scale a (isTan_comp (isTan_tvec hx c) f)), tcoord_scale hx]

theorem tvec_tmap (f : G ⟶ G) [IsMonHom f] (c : Fin n → R) : tvec (x := x) (tmap hx f c) = tvec (x := x) c ≫ f :=
  (tcoord_spec hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)).symm

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsTor
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusPts

open TorusInj

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  rw [charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 2
  first
  | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])
  | (simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])
  | (ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])

theorem ringHom_ext_ZU {A : Type} [CommRing A] {f g : AddMonoidAlgebra ZU.{0} X →+* A}
    (h : ∀ χ, f (AddMonoidAlgebra.single χ 1) = g (AddMonoidAlgebra.single χ 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  have e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X) := by
    rw [AddMonoidAlgebra.intCast_def]
    congr 1
  rw [e, map_intCast, map_intCast]

theorem torusPt_ext {Z : Over S} {τ₁ τ₂ : Z ⟶ splitTorus S X}
    (h : ∀ χ, τ₁.left.appTop.hom (charUnit S X χ).val = τ₂.left.appTop.hom (charUnit S X χ).val) :
    τ₁ = τ₂ := by
  have key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X),
      (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop →
        f = g := by
    intro f g hfg
    have hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop =
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop := by
      intro f'
      have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop
      have hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))
          ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op :=
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm
      conv_lhs => rw [hf]
      exact h0
    have hψ := (hh f).symm.trans (hfg.trans (hh g))
    exact (ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective
      (congrArg Quiver.Hom.op hψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply key
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro χ
    have e1 := charUnit_appTop τ₁.left χ
    have e2 := charUnit_appTop τ₂.left χ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← e1, ← e2]
    exact h χ
  · exact (Over.w τ₁).trans (Over.w τ₂).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
end
end
