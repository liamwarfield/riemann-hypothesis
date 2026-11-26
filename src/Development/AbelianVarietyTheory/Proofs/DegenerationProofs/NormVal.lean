module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FrAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsComb {k : ℕ} {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) : Prop :=
  ∀ j, σ.f j = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b l)) * (t l).f j
end
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

structure ThetaSys.Real.UTest.Geom (u : ρ.UTest p y₀) where
  pt : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
  pt_over : ∀ a, (pt a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃! a, pt a = z
  weil : ∀ a b (c : (PadicAlgCl p)ˣ),
    (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) →
    WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (u.A.L.pull (eSec u.A.A))
  rig_gen : rig.IsGen
  fr : ∀ a, FrAt (pt a)
  fr_tors : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (pt a) (fr a)
  th : SecA u.A (PadicAlgCl p) 1
  th_val : ∀ a, ValAt th (pt a) (fr a) (y₀ ⟨S.th a, S.th_mem a⟩)
  s : S.J → SecA u.A (PadicAlgCl p) S.N
  ev_val : ∀ a i, ValAt (s i) (pt a) (fr a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)
  α : LB.Gen (LB.LinComb u.A.L (K := Fin 2) ![(snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A).left,
    (snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -((1 : ℕ) : ℤ)])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr u.A.L _ _ _ _ (LB.pullGen u.A.L _ _ α (ptSecT u.A.A 1).left)
    (rigT u.A.A u.A.L rig (TFK (R := u.V) (PadicAlgCl p)) ((S.N : ℤ) - 1))
  s_zero : IsTwistPull u.A.A u.A.L (mulT u.A.A _ (ρ.n ^ ρ.k)) (snd _ u.A.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _)
    (S.N : ℤ) ((1 : ℕ) : ℤ) α th (s ρ.i₀)
  U : S.Gam → ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  U_sym : ∀ a, SymLift u.A.A u.A.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf u.A.A u.A.L S.N (U a) (s i) σ ↔ IsComb s (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) σ

def NormVal {p : ℕ} [Fact p.Prime] (π : PadicAlgCl p) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ (x : PadicAlgCl p) (q : ℚ), v x = (q : WithTop ℚ) ↔ ‖x‖ = ‖π‖ ^ (q : ℝ)
end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem labelled_torsion_pull {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over B') {E : Over B}
    (U : Over.mk (T.hom ≫ f) ⟶ E) {Γ : Type} [Add Γ] (pt : Γ → (E ⟶ G)) (m : ℕ)
    (hadd : ∀ a b, pt (a + b) = pt a * pt b) (htors : ∀ a, pt a ^ m = 1)
    (hbij : ∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ m = 1 → ∃! a, U ≫ pt a = z) :
    ∃ x : Γ → (T ⟶ G'), (∀ a, (x a).left ≫ φ = U.left ≫ (pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧
      Function.Injective x ∧ ∀ z : T ⟶ G', z ^ m = 1 → ∃ a, z = x a := by
  have hinj : Function.Injective (pushHom h T) := fun x y e => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) e
    · rw [Over.w, Over.w]
  have hsurj : Function.Surjective (pushHom h T) := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  choose x hx using fun a => hsurj (U ≫ pt a)
  refine ⟨x, fun a => congrArg (fun z => z.left) (hx a), fun a b => hinj ?_, fun a b e => ?_, fun z hz => ?_⟩
  · rw [map_mul, hx, hx, hx, hadd, MonObj.comp_mul]
  · have ht : (U ≫ pt a) ^ m = 1 := by
      have := map_pow (preHom U) (pt a) m
      rw [htors, map_one] at this
      exact this.symm
    exact (hbij _ ht).unique rfl (by rw [← hx, ← hx, e])
  · obtain ⟨a, ha, -⟩ := hbij (pushHom h T z) (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj (by rw [hx, ha])⟩

theorem utest_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  intro o Ω _ _ _ S ρ p _ y₀ u
  have e : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull u.cart (TFK (R := u.V) (PadicAlgCl p))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK :) (by simp)) ρ.pt (S.r * S.N) ρ.pt_add
    (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (PadicAlgCl p) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_model_labelled_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  first | exact @GlobalTheory.ZH.utest_torsion_points | exact GlobalTheory.ZH.utest_torsion_points | (intros; apply GlobalTheory.ZH.utest_torsion_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftGlobal

open CommPairing GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem exists_symLift_pull_val (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) :
    ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q


omit [GrpObj A] in
theorem exists_lift_res {T : Over S} (V : T.left.Opens) {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left)
    (hρ : ∀ z, (fst T A).left (ρ z) ∈ V) :
    ∃ n : Z ⟶ (overRes V ⊗ A).left, n ≫ (overResι V ▷ A).left = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left :=
    ⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hρ y), IsOpenImmersion.lift_fac _ _ _⟩
  let ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A := Over.homMk ρ rfl
  let v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V := Over.homMk v (by
    show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom
    rw [← Category.assoc, hv, Category.assoc, Over.w (fst T A)])
  have e : v' ≫ overResι V = ρ' ≫ fst T A := Over.OverMorphism.ext hv
  have e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, e]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
  exact ⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩

omit [GrpObj A] in
theorem mono_res {T : Over S} (V : T.left.Opens) : Mono (overResι V ▷ A).left := by
  have : Mono (overResι V).left := inferInstanceAs (Mono V.ι)
  have : Mono (overResι V) := Over.mono_of_mono_left _
  have : Mono (overResι V ▷ A) := ⟨fun a b e => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e,
        Category.assoc]
    · rw [← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩
  infer_instance

theorem tval_agree (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {T : Over S}
    {x : T ⟶ A} {V V' : T.left.Opens} {θ : ThetaGrp A L k (overRes V)} {θ' : ThetaGrp A L k (overRes V')}
    (H : SymLift A L k n (overResι V ≫ x) θ) (H' : SymLift A L k n (overResι V' ≫ x) θ')
    {Z : Scheme.{0}} (r : Z ⟶ (overRes V ⊗ A).left) (r' : Z ⟶ (overRes V' ⊗ A).left)
    (hr : r ≫ (overResι V ▷ A).left = r' ≫ (overResι V' ▷ A).left) (z : Z) (J) (hJ : Good L z J) :
    tval θ r z J = tval θ' r' z J := by
  have mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z),
      (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W := fun W s y => by
    have e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι := by
      rw [← Over.comp_left, whiskerRight_fst]; rfl
    exact (congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2
  obtain ⟨m, hm⟩ := exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left)
    (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)
  have inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W,
      i ≫ overResι W = overResι (V ⊓ V') := fun W hW =>
    ⟨Over.homMk (T.left.homOfLE hW) (by
      show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩
  obtain ⟨i, hi⟩ := inc V inf_le_left
  obtain ⟨i', hi'⟩ := inc V' inf_le_right
  obtain ⟨ξ, Hξ, vξ⟩ := exists_symLift_pull_val hL i H
  obtain ⟨ξ', Hξ', vξ'⟩ := exists_symLift_pull_val hL i' H'
  rw [← Category.assoc, hi] at Hξ
  rw [← Category.assoc, hi'] at Hξ'
  have := mono_res (A := A) V
  have := mono_res (A := A) V'
  have e : m ≫ (i ▷ A).left = r := by
    rw [← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]
  have e' : m ≫ (i' ▷ A).left = r' := by
    rw [← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]
  rw [← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]
  exact val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m

theorem exists_lift_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {T : Over S} {x : T ⟶ A}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L k (overRes V), SymLift A L k n (overResι V ≫ x) θ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  choose V hV θ hθ using h
  choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)
  have loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J →
        val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by
    have e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]
    obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2)
      (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ k) e₀
        · exact congrArg (fun q => f q ^ (-k)) e₁)
      (LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))
      (DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
  choose t ht hv using loc
  obtain ⟨u, hu, -⟩ := glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht
    (fun p q Z r r' z J hJ e => by
      rw [hv p Z r z J hJ, hv q Z r' z J hJ]
      exact tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)
  exact ⟨⟨x, u, hu⟩, rfl⟩

end GlobalTheory.SymLiftGlobal

namespace GlobalTheory

theorem exists_symLift_global : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k →
    IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  intro hLaw S _ P k hk hu T x hx
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk
    (hLaw.symLift S P k hk hu T x hx).1
  obtain ⟨nu, hnu⟩ := exists_gen_negLB hLaw.globalFns S P k T
  exact SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobalStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symLift_of_pow_eq_one : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k → IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  first | exact @GlobalTheory.exists_symLift_global | exact GlobalTheory.exists_symLift_global | (intros; apply GlobalTheory.exists_symLift_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def HasWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gs ((τ ≫ i) * g).left z U f = (gm τ.left z ⊤ (charUnit S X α)).val * gs g.left z U f

def GenWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J : (Z.left ⟶ Y) → L.ι), Good L z J →
    val t ((τ ≫ i) * g).left z J = gm τ.left z ⊤ (charUnit S X α) * val t g.left z J

def Red {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) {K K' : Type} [Fintype K] [Fintype K'] {ψ : K → (Φ.E.B.left ⟶ Y)} {ε : K → ℤ}
    {φt : K' → (Φ.G.left ⟶ Y)} {εt : K' → ℤ} (t : LB.Gen (LB.LinComb L φt εt)) (b : LB.Sec (LB.LinComb L ψ ε))
    (φ : (Φ.H 1).Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
    r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
    gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval b (r ≫ Φ.D.q.left) z J * (val t r z J).val

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnivBasisMove

open GlobalTheory.ThetaReal GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ}

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (s : SecM A L₁ a T) (s₀ : SecM G L₀ a T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    ThetaAct.sv s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * ThetaAct.sv s r z J'

theorem exists_rel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s₀ : SecM G L₀ a T₀) :
    ∃ s, Rel hp τ hτ w s s₀ := by
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ (SecM.toSec G s₀)
  exact ⟨SecM.ofSec A s, hs⟩

theorem exists_rel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s : SecM A L₁ a T) :
    ∃ s₀, Rel hp τ hτ w s s₀ := by
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ (SecM.toSec A s)
  exact ⟨SecM.ofSec G s₀, hs⟩

variable {hp τ hτ}

theorem Rel.unique_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s s' : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s' s₀) : s = s' :=
  ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    exact (Units.mul_right_inj _).1 ((h _ _ _ _ _ hJ hJ').symm.trans (h' _ _ _ _ _ hJ hJ'))

theorem Rel.unique_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s : SecM A L₁ a T} {s₀ s₀' : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s s₀') : s₀ = s₀' :=
  ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    have q := (h _ χ y _ _ hJ hJ').trans (h' _ χ y _ _ hJ hJ').symm
    rwa [h₂'] at q

theorem Rel.add {s t : SecM A L₁ a T} {s₀ t₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w t t₀) : Rel hp τ hτ w (s + t) (s₀ + t₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', h' _ _ _ _ _ hJ hJ', mul_add]

theorem Rel.smul {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (c : Γ(T₀.left, ⊤))
    (h : Rel hp τ hτ w s s₀) : Rel hp τ hτ w (τ.appTop.hom c • s) (c • s₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', mul_left_comm,
      Category.assoc, psi_fst', ← Category.assoc]
    exact congrArg (fun x => _ * (x * _)) (gs_pull _ τ z ⊤ trivial c).symm

theorem Rel.pull {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (h : Rel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (σ : T'.left ⟶ T₀'.left) (hσ : σ ≫ T₀'.hom = T'.hom ≫ f)
    (u : T' ⟶ T) (u₀ : T₀' ⟶ T₀) (hu : σ ≫ u₀.left = u.left ≫ τ) :
    Rel hp σ hσ w (VVRank.pullM A L₁ a u s) (VVRank.pullM G L₀ a u₀ s₀) :=
  fun Z r z J J' hJ hJ' => by
    have e : psi hp σ hσ ≫ (u₀ ▷ G).left = (u ▷ A).left ≫ psi hp τ hτ := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
          Category.assoc, Category.assoc, psi_fst', hu, ← Category.assoc (u ▷ A).left, ← Over.comp_left,
          whiskerRight_fst, Over.comp_left, Category.assoc]
      · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
          VVRank.whisker_snd_left]
    have q := h _ (r ≫ (u ▷ A).left) z _ _ hJ hJ'
    rw [Category.assoc, Category.assoc, ← e, VVRank.whisker_snd_left, ← Category.assoc] at q
    exact (VVRank.sv_pullS G a u₀ (SecM.toSec G s₀) _ z hJ).trans
      (q.trans (congrArg _ (VVRank.sv_pullS A a u (SecM.toSec A s) _ z hJ').symm))

theorem exists_linearEquiv (hp : IsGrpPullback A G f φ) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (a : ℤ) (T : Over S') :
    ∃ E : SecM G L₀ a (Over.mk (T.hom ≫ f)) ≃ₗ[Γ(T.left, ⊤)] SecM A L₁ a T,
      ∀ x, Rel hp (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) w (E x) x := by
  have : IsIso (C := Scheme.{0}) (X := T.left) (Y := (Over.mk (T.hom ≫ f)).left) (𝟙 T.left) := IsIso.id _
  choose D hD using exists_rel hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) (a := a)
    hw hL₀ hL₁
  let l : SecM G L₀ a (Over.mk (T.hom ≫ f)) →ₗ[Γ(T.left, ⊤)] SecM A L₁ a T :=
    { toFun := D
      map_add' := fun x y => (hD _).unique_down hL₀ hL₁ ((hD x).add (hD y))
      map_smul' := fun c x => (hD _).unique_down hL₀ hL₁ (Rel.smul (T₀ := Over.mk (T.hom ≫ f)) (τ := 𝟙 T.left) c (hD x)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun x y e => ?_, fun s => ?_⟩, hD⟩
  · have e' : D x = D y := e
    exact (hD x).unique_up hL₀ hL₁ (e' ▸ hD y)
  · obtain ⟨s₀, hs⟩ := exists_rel_up hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _)
      hw hL₀ hL₁ s
    exact ⟨s₀, (hD s₀).unique_down hL₀ hL₁ hs⟩

theorem univBasis_move : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  intro S S' f P P' φ hp hw n κ _ T₀ τ hτ b₀ hb₀
  obtain ⟨w, hw⟩ := hw
  have hτ' : τ ≫ T₀.hom = (baseOver S').hom ≫ f := hτ.trans (Category.id_comp _).symm
  choose b hb using fun i => exists_rel hp (T := baseOver S') τ hτ' hw P.isLB P'.isLB (b₀ i)
  refine ⟨b, fun T hT h => ?_⟩
  have hh : h.left = T.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk (T.hom ≫ τ) (by
    change (T.hom ≫ τ) ≫ T₀.hom = T.hom ≫ f
    rw [Category.assoc, hτ])
  have : IsAffine (Over.mk (T.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T
  refine ⟨Module.Basis.map (R := Γ(T.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ ((Category.id_comp _).trans (congrArg (· ≫ τ) hh.symm))

end GlobalTheory.UnivBasisMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalBasis_move_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  first | exact @GlobalTheory.UnivBasisMove.univBasis_move | exact GlobalTheory.UnivBasisMove.univBasis_move | (intros; apply GlobalTheory.UnivBasisMove.univBasis_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
noncomputable section
namespace GlobalTheory.TorsFrame

open CommPairing GlobalLift ThetaCoord

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_pow_two (hL : L.IsLB) {Y : Scheme.{0}} {f g : Y ⟶ A.left} {k : ℤ} (m : ℕ)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![k, -k])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![m * k, -(m * k)]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u' r z J = val u r z J ^ m := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![f, g]) (ε' := ![m * k, -(m * k)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg])
    (GeneratorPullback.powGen L _ _ u m) (DVR.powGen_isGen _ _ _ _ hu _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_powGen _ _ _ _ _)⟩

theorem exists_symLift_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k q x θ) (m : ℕ) :
    ∃ θ' : ThetaGrp A L (m * k) T, SymLift A L (m * k) q x θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ' r z J = tval θ r z J ^ m := by
  obtain ⟨ν, hν, -⟩ := H.sym
  obtain ⟨u, hu, vu⟩ := exists_pow_two hL m (u := θ.φ) θ.isGen
  obtain ⟨ν', hν', vν⟩ := exists_pow_two hL m (u := ν) hν
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨θ.pt, u, hu⟩ : ThetaGrp A L (m * k) T) r z J = tval θ r z J ^ m := vu
  have vν' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      nval (k := m * k) ν' r z J = nval ν r z J ^ m := vν
  refine ⟨⟨θ.pt, u, hu⟩, symLift_of_tval hL H.pt_eq (ν := ν') hν' (fun T' π z J hJ p => ?_)
    (fun T' π z J hJ p => ?_), vu'⟩
  · rw [Finset.prod_congr rfl fun j _ => vu' _ _ z J hJ, Finset.prod_pow, prod_tval H π hJ p, one_pow]
  · rw [vu' _ _ z J hJ, vu' _ _ z J hJ, vν' _ _ z J hJ, vν' _ _ z J hJ, ← inv_pow, ← mul_pow, ← mul_pow, ← mul_pow,
      sym_tval hG hA hL H hν π hJ p, one_pow]

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [eSec, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, e, one_pow]

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem exists_norm (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) {n : ℕ}
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good L z J → val α (r ≫ eSec A) z J =
        val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J ^ (n ^ 2) *
          (val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J)⁻¹ := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig (n ^ 2))
        (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig))
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (eSec A)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hr _) (DVR.invGen_isGen _ _ _ _ hr))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))) _))
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have e : (r ≫ eSec A) ≫ A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
  rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
    mul_comm, inv_mul_cancel_right]

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J := by
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A)
    (fun _ => J (r ≫ T.hom ≫ eSec A)) from Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

theorem tval_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {ν : LB.Gen (negLB A L 1 T)}
    (hν : ν.IsGen) {n : ℕ} (hn : Odd n)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (hα : α.IsGen)
    {y : T ⟶ A} (hy : y ^ (n ^ 2) = 1) {θ : ThetaGrp A L (n ^ 2 : ℕ) T} (H : SymLift A L (n ^ 2 : ℕ) (n ^ 2) y θ)
    {z : T.left} {J} (hJ : Good L z J) :
    tval θ (lift (𝟙 T) (1 : T ⟶ A)).left z J ^ (n ^ 2) =
      val α (1 : T ⟶ A).left z J ^ (n ^ 2) * val α (1 : T ⟶ A).left z J *
        (val α y.left z J ^ (n ^ 2) * val α (y ^ n).left z J)⁻¹ := by
  have e₁ : ∀ p : T ⊗ A ⟶ A, p.left ≫ (mulA A n).left = (p ^ n).left := fun p => by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) * (n ^ 2 : ℕ), -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L _ _ (LB.pullGen L _ _ α (snd T A).left) (n ^ 2))
      (LB.pullGen L _ _ α (snd T A ^ n).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) _)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have vβ' : ∀ p : T ⟶ A, bval (b := 1) β (lift (𝟙 T) p).left z J =
      val α p.left z J ^ (n ^ 2) * val α (p ^ n).left z J := fun p => by
    refine (vβ _ _ z J hJ).trans ?_
    rw [val_mul hJ, val_powGen, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, lift_snd]
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν 1
  obtain ⟨θ₁, H₁, v₁⟩ := exists_symLift_mulPull hA hL (one_dvd (n ^ 2)) (b := 1) hβ hy (hy.symm ▸ ho)
  obtain ⟨θ₂, H₂, v₂⟩ := exists_symLift_pow hG hA hL H (n ^ 2)
  have e : tval θ₂ (lift (𝟙 T) (1 : T ⟶ A)).left z J = tval θ₁ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn.pow θ₂ θ₁ H₂ H₁) _
  rw [v₂ _ _ z J hJ, v₁ _ _ z J hJ, vo _ _ z J hJ, vβ', vβ', one_pow, _root_.mul_one, _root_.mul_one,
    Category.id_comp] at e
  exact e

end GlobalTheory.TorsFrame

namespace GlobalTheory


open TorsFrame CommPairing in
theorem exists_isTorsFrame_of_symLift : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  intro hLaw S _ P rig hr n hn T y x hy hx θ H
  subst hx
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A n).left = (y ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, H.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ n).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (n ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  refine ⟨τ, by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ n) τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (n ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hn hα hy H hJ
    have c : val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
        (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    rw [one_left, vα _ _ z J hJ] at b
    rw [a, vτ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_mul hJ, c, val_powGen, val_pull hJ, val_pull hJ,
      val_pull hJ, val_rigT rig _ z hJ, Category.id_comp, Category.id_comp, Category.id_comp, mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLiftStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTorsFrame_of_symLift' : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  first | exact @GlobalTheory.exists_isTorsFrame_of_symLift | exact GlobalTheory.exists_isTorsFrame_of_symLift | (intros; apply GlobalTheory.exists_isTorsFrame_of_symLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.ThetaReal.NormMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  have v : ∀ (y : T.left) (i : Fin 1 → L.ι), y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k :=
    fun y i hi => (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res (𝟙 T.left) y (rigT_le A L i) hi _).trans
      (gm_pull (𝟙 T.left) T.hom y _ (rigT_le A L i hi) (ρ.s fun _ => i 0))))
  refine SymLiftOdd.isGen_of_gm fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hi) (rigT_le A L (T := T) j hj)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  rw [v y i hi, v y j hj, trF, Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd]; rfl

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left)
        (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b)) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + -b + (a + b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left))
      (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b))) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigT_isGen hρ a) (rigT_isGen hρ b))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end GlobalTheory.ThetaReal.NormMul

namespace GlobalTheory.ThetaReal

theorem exists_normalised_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  intro hLaw S _ P rig hrig m N hN T
  subst hN
  have H := hLaw.mulPull _ P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α₁, hα₁, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left]) α₀ hα₀ (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  exact NormMul.exists_normalised P.isLB hrig m _ _ α₁ hα₁

end GlobalTheory.ThetaReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOriginStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_mulPull_iso_origin : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  first | exact @GlobalTheory.ThetaReal.exists_normalised_mulPull | exact GlobalTheory.ThetaReal.exists_normalised_mulPull | (intros; apply GlobalTheory.ThetaReal.exists_normalised_mulPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : n ≠ 0) (hJ : 2 ≤ J)
    (t : ZMod (n ^ J)) (ht : n • t = 0) : ∃ s : ZMod (n ^ J), t = n • s := by
  have : NeZero (n ^ J) := ⟨pow_ne_zero _ hn⟩
  have hv : n ^ J ∣ n * t.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact ht
  obtain ⟨k, hk⟩ := hv
  have h1 : t.val = n * (n ^ (J - 2) * k) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    rw [hk, show n ^ J = n * (n * n ^ (J - 2)) by
      rw [← pow_succ', ← pow_succ']; congr 1; omega]
    ring
  refine ⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]

theorem closure_eq_ker_of_meets_torsion_cosets :
    ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  intro I X _ _ n J M hn hJ hM yy hyy Z hZ hcov
  subst hM
  have key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b := by
    intro b hb hbk
    have hc : ∀ i, ∃ s, b i = n • s := fun i =>
      zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by
        simpa using congrFun hb i)
    choose c hc using hc
    have hbc : b = n • c := funext fun i => by simpa using hc i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (yy c)
    have hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]
      exact hbk
    obtain ⟨x', hx'⟩ := hnx
    have hx'' : (n ^ J) • x' = n • x := hx'
    have hxx : x = n ^ (J - 1) • x' := by
      have h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x') := by
        rw [natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]
        exact hx''.symm
      exact smul_right_injective X (by exact_mod_cast hn) h2
    obtain ⟨c', hc'⟩ := hyy (QuotientAddGroup.mk x')
    refine ⟨c - n ^ (J - 1) • c', ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx,
        sub_self]
    · have h0 : (n ^ J) • c' = 0 := funext fun i => by
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).2 hZ
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    have hbk : b ∈ yy.ker := by
      have h3 : yy (a + b) = 0 := hZ hab
      rw [AddMonoidHom.mem_ker] at ha ⊢
      rwa [map_add, ha, zero_add] at h3
    obtain ⟨k, hk, hkb⟩ := key b hb hbk
    obtain ⟨b', hb', hkb'⟩ := hcov k hk
    have h4 : a = (a + b) - n • (k + b') := by
      rw [smul_add, hb', add_zero, hkb, add_sub_cancel_right]
    rw [h4]
    exact sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosetsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.closure_eq_ker_of_meets_torsion_cosets' : ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  first | exact @GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | exact GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | (intros; apply GlobalTheory.closure_eq_ker_of_meets_torsion_cosets <;> assumption)
end
end
