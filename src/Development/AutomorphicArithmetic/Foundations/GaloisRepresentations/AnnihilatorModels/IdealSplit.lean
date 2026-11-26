module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w 𝔞 : Ideal (𝓞 D.F)} {j c ρ : ℕ}

structure TjE (E : EtModel b N 𝔞 ρ) {π : E.X ⟶ M.X} (mπ : ObjMap E.univ M.univ π) (T : TjD M r w j c) : Type 1 where
  Z : Scheme.{0}
  s : Z ⟶ E.X
  t : Z ⟶ E.X
  g : Z ⟶ T.Y
  pb : IsPullback s g π T.s
  tπ : t ≫ π = g ≫ T.t
  o : Obj b N (s ≫ E.s)
  o' : Obj b N (s ≫ E.s)
  ms : ObjMap o E.univ s
  mt : ObjMap o' E.univ t
  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ
  m₀ : ObjMap o T.o g
  m' : ObjMap o' T.o' g
  sq : m₀.φ ≫ T.ψ.left = ψ.left ≫ m'.φ
  tri : m₀.φ ≫ T.ms.φ = ms.φ ≫ mπ.φ
  tri' : m'.φ ≫ T.mt.φ = mt.φ ≫ mπ.φ
  lev : ∀ (y : D.La) (l : 𝟙_ (Over Z) ⟶ o.A), l.left ≫ ms.φ = s ≫ (E.lv y).left → (l ≫ ψ).left ≫ mt.φ = t ≫ (E.lv y).left

variable {E : EtModel b N 𝔞 ρ} {π : E.X ⟶ M.X} {mπ : ObjMap E.univ M.univ π} {T : TjD M r w j c}

def TjE.ksP (L : TjE E mπ T) (k : ℕ) : (GlobalTheory.KS.pow L.o.A k).left ⟶ (GlobalTheory.KS.pow E.univ.A k).left := GlobalTheory.KS.powMap L.s L.ms.φ L.ms.cart.1.w k

def TjE.ksR (L : TjE E mπ T) (k : ℕ) : (GlobalTheory.KS.pow L.o.A k).left ⟶ (GlobalTheory.KS.pow E.univ.A k).left :=
  (Limits.Pi.map fun _ : Fin k => L.ψ).left ≫ GlobalTheory.KS.powMap L.t L.mt.φ L.mt.cart.1.w k

structure KSOKE (L : TjE E mπ T) (k d : ℕ) : Prop where
  fin : IsFinite (L.ksP k)
  et : Etale (L.ksP k ∣_ (GlobalTheory.KS.pow E.univ.A k).left.basicOpen ((p : ℕ) : Γ((GlobalTheory.KS.pow E.univ.A k).left, ⊤)))
  deg : ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow E.univ.A k).left,
    Nat.card {z : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow L.o.A k).left // z ≫ L.ksP k = y} = d

def KSOKE.corr {L : TjE E mπ T} {k d : ℕ} (h : KSOKE L k d) : Corr p (GlobalTheory.KS.pow E.univ.A k).left :=
  ⟨(GlobalTheory.KS.pow L.o.A k).left, L.ksP k, L.ksR k, d, h.fin, h.et, h.deg⟩

end

def TjExF : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∃ T : TjD M r w j (p ^ (f * j)), Flat (T.s ≫ M.s)

def TjEEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c), Flat (T.s ≫ M.s) → ∀ (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ →
    (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) → ∀ (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → ∀ mπ : ObjMap E.univ M.univ π,
    Nonempty (TjE E mπ T)

def OrdKSE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j)))
    (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Flat π →
    ∀ (mπ : ObjMap E.univ M.univ π) (L : ∀ j, TjE E mπ (T j)) (k : ℕ),
    ∃ (d : Fin (D.n + 1) → ℕ) (h : ∀ j, KSOKE (L j) k (d j)),
      (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (h j).corr.p ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ∧
      OrdPt p (p ^ f) D.n (fn ((GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ϖ) fun j => (h j).corr

def OrdEmb : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j)))
    (Y : Scheme.{0}) (h : Y ⟶ M.X), Flat h → ∀ (I : Type) (a : I → (Y ⟶ M.univ.A.left)), (∀ i, a i ≫ M.univ.A.hom = h) →
    (∀ (X : Scheme.{0}) (u v : X ⟶ Y), u ≫ h = v ≫ h → (∀ i, u ≫ a i = v ≫ a i) → u = v) →
    ∀ (C : Fin (D.n + 1) → Corr p Y) (g : ∀ j, (C j).Z ⟶ (T j).Y), (∀ j, IsPullback (C j).p (g j) h (T j).s) →
    (∀ j, (C j).r ≫ h = g j ≫ (T j).t) → (∀ j i e, (C j).r ≫ a i = (T j).img (g j) ((C j).p ≫ a i) e) →
    OrdPt p (p ^ f) D.n (fn (h ≫ M.s) ϖ) C

def CorrBC : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (Y Z : Scheme.{0}) (h : Y ⟶ M.X) (s : Z ⟶ Y)
    (g : Z ⟶ T.Y), IsPullback s g h T.s → IsFinite s ∧ Etale (s ∣_ Y.basicOpen ((p : ℕ) : Γ(Y, ⊤))) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ Y,
        Nat.card {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ s = y} = Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) j)

def UKerW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c), Flat (T.s ≫ M.s) →
    ∀ (X : Over T.Y) (g : X ⟶ T.o.A), UKer r T.o T.ψ X g → KilledBy T.o w g

def IdealSplit : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (𝔞 : Ideal A) (x : A), x ≠ 0 → ∀ ρ : ℕ,
    ∃ (m : ℕ) (α : A), α - 1 ∈ 𝔞 ^ ρ ∧ ∀ a ∈ 𝔞 ^ m, a * α ∈ Ideal.span {x}

def LevPull : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s) (o₁ : Obj b N s')
    (m : ObjMap o₁ o f) (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (lv : D.La → (𝟙_ (Over S) ⟶ o.A)), IsEtLev o 𝔞 ρ lv →
    ∃ l : D.La → (𝟙_ (Over S') ⟶ o₁.A), IsEtLev o₁ 𝔞 ρ l ∧ ∀ y, (l y).left ≫ m.φ = f ≫ (lv y).left

def LevPush : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w 𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ → (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) →
    ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ →
    (∀ (X : Over S) (g : X ⟶ o.A), UKer r o ψ X g → KilledBy o w g) →
    ∀ lv : D.La → (𝟙_ (Over S) ⟶ o.A), IsEtLev o 𝔞 ρ lv → IsEtLev o' 𝔞 ρ fun y => lv y ≫ ψ

def EtInj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X),
    π ≫ M.s = E.s → ∀ (mπ : ObjMap E.univ M.univ π) (X : Scheme.{0}) (u v : X ⟶ E.X), u ≫ π = v ≫ π →
    (∀ y, u ≫ (E.lv y).left ≫ mπ.φ = v ≫ (E.lv y).left ≫ mπ.φ) → u = v

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledRead
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledRead_of :
    PullKer → PulledRead := by
  intro hKer p _ D R _ b N M r w j c T S x σ o₁ m₁ y hy P a
  have hw : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = y := by
    have h1 := P.m₀.cart.1.w
    have h2 : a.left ≫ o₁.A.hom = 𝟙 S := Over.w a
    rw [Category.assoc, h1, ← Category.assoc, h2]
    exact Category.id_comp y
  have htri : (a.left ≫ P.m₀.φ) ≫ T.ms.φ = a.left ≫ m₁.φ := by
    rw [Category.assoc, P.tri]
  let a₀ : Over.mk y ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw
  have ha₀ : a₀.left = a.left ≫ P.m₀.φ := rfl
  have hk := ((hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
    (𝟙_ (Over S)) (Over.mk y) rfl a a₀ (by simp [ha₀])).1
  refine ⟨⟨fun h a' ha' => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hEq : a' = a₀ := by
      apply Over.OverMorphism.ext
      apply T.ms.cart.1.hom_ext
      · rw [ha', ha₀, htri]
      · have h3 : a'.left ≫ T.o.A.hom = y := Over.w a'
        rw [h3, ha₀, hw]
    rw [hEq]
    exact hk.1 h
  · exact hk.2 (h a₀ (by rw [ha₀, htri]))
  · have hl : T.ms.cart.1.lift (a.left ≫ m₁.φ) y h = a.left ≫ P.m₀.φ := by
      apply T.ms.cart.1.hom_ext
      · rw [T.ms.cart.1.lift_fst, htri]
      · rw [T.ms.cart.1.lift_snd, hw]
    unfold TjD.img
    rw [hl, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% P.sq]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecCard
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secCard_of :
    SecCard := by
  intro p _ D R _ b N M r w j c T hm K _ _ hp x y hxy
  subst hxy
  let β : R →+* K := (Spec.preimage (y ≫ T.s ≫ M.s)).hom
  haveI : CharZero K := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · exfalso
      have hcast : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      by_cases hqp : ringChar K = p
      · rw [hqp] at hcast
        exact hp hcast
      · have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hq (Fact.out)).mpr hqp
        have hu := (b.unit _ hcop).map β
        rw [map_natCast, hcast] at hu
        exact not_isUnit_zero hu
    · haveI : CharP K 0 := ringChar.of_eq hq
      exact CharP.charP_to_charZero K
  obtain ⟨-, hcard⟩ := T.tj K y
  rw [hm, Nat.one_mul] at hcard
  rw [← hcard]
  symm
  have hK : ∀ a : Over.mk y ⟶ T.o.A,
      KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a) := by
    intro a
    unfold KilledBy
    refine forall₂_congr (fun c _ => ?_)
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]
  have hker : ∀ a : Over.mk y ⟶ T.o.A,
      KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1 := by
    intro a
    rw [ObjMap.ptEquiv_left]
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have ha : a' = a := by
        apply (T.ms.ptEquiv (Over.mk y)).injective
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']
      rw [ha]
      exact h
  refine Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))
  exact ⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPairCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw in
theorem UpperTheory.Gal.crystallineComparison.Mod.pairCalc_of :
    PairCalc := by
  intro p _ D R _ b N S s o
  have hcls : ∀ {X Y : Scheme} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X),
      cls (L.pull f) (pull_isLB hL f) = pull f (cls L hL) := by
    intro X Y L hL f
    rw [cls_linComb hL]
    simp
  have move : ∀ {T : Over S} (u : T ⟶ G2 o.A) (F₁ F₂ : G2 o.A ⟶ G2 o.A),
      LBIso (o.P.pull F₁.left) (o.P.pull F₂.left) →
        pull (u ≫ F₁).left (cls o.P o.isLB) = pull (u ≫ F₂).left (cls o.P o.isLB) := by
    intro T u F₁ F₂ h
    rw [Over.comp_left, Over.comp_left, pull_comp, pull_comp, ← hcls o.isLB F₁.left,
      ← hcls o.isLB F₂.left,
      (cls_eq_iff _ _).2 h]
  obtain ⟨e, he, k⟩ := o.kerP
  obtain ⟨t₁, h₁⟩ := o.rig₁
  obtain ⟨t₂, h₂⟩ := o.rig₂
  have hadd := additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
  refine ⟨hadd.1, hadd.2, ?_, ⟨e, he, fun T x hx => k T x ((triv_ev_iff o.isLB _ _).2 hx)⟩, ?_⟩
  · intro T x y a
    have h := move (lift x y) _ _ (o.rosati ((algebraMap (𝓞 D.F) D.O) a))
    rw [D.star_F, MulOpposite.unop_op] at h
    unfold evc
    convert h using 3 <;> simp
  · intro o' ψ c
    have hc : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = c • cls o.P o.isLB := by
      unfold Hecke.lbPow
      rw [cls_linComb o.isLB]
      simp [pull_id]
    have hcomp : ∀ {T : Over S} (x y : T ⟶ o.A),
        (lift x y).left ≫ sq2 ψ = (lift (x ≫ ψ) (y ≫ ψ)).left := by
      intro T x y
      unfold sq2
      rw [← Over.comp_left]
      simp
    constructor
    · rintro ⟨h⟩ T x y
      have h' : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
          cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ)) :=
        (cls_eq_iff _ _).2 h
      rw [hc, hcls o'.isLB] at h'
      unfold evc
      rw [← hcomp, pull_comp, ← h', map_nsmul]
    · intro h
      refine ⟨(cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB o'.isLB (sq2 ψ))).1 ?_⟩
      have h' := h (G2 o.A) (fst o.A o.A) (snd o.A o.A)
      unfold evc at h'
      rw [← hcomp, pull_comp] at h'
      simp only [lift_fst_snd, Over.id_left, pull_id] at h'
      show cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) =
        cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB (sq2 ψ))
      rw [hc, hcls o'.isLB, h']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPowExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def powSuccIso {S : Scheme.{0}} (A : Over S) (k : ℕ) :
    GlobalTheory.KS.pow A (k + 1) ≅ A ⨯ GlobalTheory.KS.pow A k :=
  let f : GlobalTheory.KS.pow A (k + 1) ⟶ A := Pi.π _ 0
  let g : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
    Pi.lift fun i : Fin k => Pi.π (fun _ : Fin (k + 1) => A) i.succ
  have hf : Limits.prod.lift f g ≫ Limits.prod.fst = f := Limits.prod.lift_fst f g
  have hg : Limits.prod.lift f g ≫ Limits.prod.snd = g := Limits.prod.lift_snd f g
  have hgi (i : Fin k) : g ≫ Pi.π (fun _ : Fin k => A) i = Pi.π (fun _ : Fin (k + 1) => A) i.succ :=
    Pi.lift_comp_π _ _
  let b : A ⨯ GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A (k + 1) :=
    Pi.lift (Fin.cases Limits.prod.fst (fun i => Limits.prod.snd ≫ Pi.π _ i))
  have hb0 : b ≫ Pi.π (fun _ : Fin (k + 1) => A) 0 = Limits.prod.fst := Pi.lift_comp_π _ _
  have hbs (i : Fin k) : b ≫ Pi.π (fun _ : Fin (k + 1) => A) i.succ =
      Limits.prod.snd ≫ Pi.π (fun _ : Fin k => A) i := Pi.lift_comp_π _ _
  { hom := Limits.prod.lift f g
    inv := b
    hom_inv_id := by
      apply Pi.hom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Category.assoc, hb0, hf, Category.id_comp]
      · rw [Category.assoc, hbs, ← Category.assoc, hg, hgi, Category.id_comp]
    inv_hom_id := by
      apply Limits.prod.hom_ext
      · rw [Category.assoc, hf, Category.id_comp]
        exact hb0
      · rw [Category.assoc, hg, Category.id_comp]
        apply Pi.hom_ext
        intro i
        rw [Category.assoc, hgi, hbs] }

private theorem flat_pow {S : Scheme.{0}} (A : Over S) (h : Flat A.hom) :
    ∀ k, Flat (GlobalTheory.KS.pow A k).hom
  | 0 => by
    have t : IsTerminal (GlobalTheory.KS.pow A 0) :=
      IsTerminal.ofUniqueHom (fun Y => Pi.lift (fun i => i.elim0))
        (fun Y m => Pi.hom_ext _ _ (fun i => i.elim0))
    let e := t.uniqueUpToIso Over.mkIdTerminal
    have h1 : (GlobalTheory.KS.pow A 0).hom = e.hom.left := by simpa using (Over.w e.hom).symm
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance
  | k + 1 => by
    haveI := flat_pow A h k
    let e := powSuccIso A k
    have h1 : (GlobalTheory.KS.pow A (k + 1)).hom = e.hom.left ≫ (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom ≫
        pullback.fst A.hom (GlobalTheory.KS.pow A k).hom ≫ A.hom := by
      rw [← Category.assoc (Over.prodLeftIsoPullback A (GlobalTheory.KS.pow A k)).hom, Over.prodLeftIsoPullback_hom_fst]
      simp
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    rw [h1]
    infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.powExt_of :
    PowExt := by
  intro S A k
  refine ⟨fun h => flat_pow A inferInstance k, ?_⟩
  intro X u v h1 h2
  exact GlobalTheory.KS.PowPB.pow_left_hom_ext u v h1 h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullIsog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.CechPic GlobalTheory.UPel.HT.ES.PIsogExt

theorem UpperTheory.Gal.crystallineComparison.Mod.pullIsog_of :
    PullIsog := by
  intro p _ D R _ b N S S' s s' f hs c o o' ψ hψ o₁ m
  subst hs
  have hcpos : 0 < c := hψ.pos
  obtain ⟨hk, hmon, hact, heta, ⟨hiso⟩, ψ', hmon', h₁, h₂⟩ := hψ
  haveI := hmon
  haveI := hmon'
  obtain ⟨o₁', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o'
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, Over.w ψ, m.cart.1.w])) (m'.cart.1.lift_snd _ _ _)
  let ψ₁' : o₁'.A ⟶ o₁.A := Over.homMk (m.cart.1.lift (m'.φ ≫ ψ'.left) o₁'.A.hom
    (by rw [Category.assoc, Over.w ψ', m'.cart.1.w])) (m.cart.1.lift_snd _ _ _)
  have e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := (m'.cart.1.lift_fst _ _ _).symm
  have e' : m'.φ ≫ ψ'.left = ψ₁'.left ≫ m.φ := (m.cart.1.lift_fst _ _ _).symm
  have pt : ∀ (T : Over S') (x : T ⟶ o₁.A), m'.ptEquiv T (x ≫ ψ₁) = m.ptEquiv T x ≫ ψ := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e])
  have pt' : ∀ (T : Over S') (x : T ⟶ o₁'.A), m.ptEquiv T (x ≫ ψ₁') = m'.ptEquiv T x ≫ ψ' := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e'])
  have mh : IsMonHom ψ₁ := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁ fun T x y => (m'.ptEquiv T).injective (by
    rw [map_mul, pt, pt, pt, map_mul, MonObj.mul_comp])
  have mh' : IsMonHom ψ₁' := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁' fun T x y => (m.ptEquiv T).injective (by
    rw [map_mul, pt', pt', pt', map_mul, MonObj.mul_comp])
  have hsq := isSquare_square_compatible_homs m.sq m'.sq e
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
  have hM₁ : (o₁'.P.pull (sq2 ψ₁)).IsLB := pull_isLB o₁'.isLB _
  have e1 := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
  have e2 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
  have hL₀ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have e3 : cls _ hL₀ = cls _ (pull_isLB o'.isLB (sq2 ψ)) := (cls_eq_iff hL₀ (pull_isLB o'.isLB (sq2 ψ))).2 hiso
  have ext₁ : ∀ {T : Over S'} (g h : T ⟶ o₁.A), g.left ≫ m.φ = h.left ≫ m.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m.cart.1.hom_ext H (by simp))
  have ext₂ : ∀ {T : Over S'} (g h : T ⟶ o₁'.A), g.left ≫ m'.φ = h.left ≫ m'.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext H (by simp))
  have hcls : cls _ hL₁ = cls _ hM₁ := by
    calc cls _ hL₁ = c • cls o₁.P o₁.isLB := hcL _ _ _
      _ = c • pull m.φ₂ (cls o.P o.isLB) := by rw [e2, cls_pull o.isLB]
      _ = pull m.φ₂ (c • cls o.P o.isLB) := (map_nsmul _ _ _).symm
      _ = pull m.φ₂ (cls _ (pull_isLB o'.isLB (sq2 ψ))) := by
        rw [← hcL o.P o.isLB hL₀, e3]
      _ = pull (m.φ₂ ≫ sq2 ψ) (cls o'.P o'.isLB) := by rw [cls_pull o'.isLB, pull_comp]
      _ = pull (sq2 ψ₁) (pull m'.φ₂ (cls o'.P o'.isLB)) := by rw [hsq, pull_comp]
      _ = pull (sq2 ψ₁) (cls o₁'.P o₁'.isLB) := by rw [e1, cls_pull o'.isLB]
      _ = cls _ hM₁ := (cls_pull o₁'.isLB _ _).symm
  refine ⟨o₁', m', ψ₁, ⟨hk, mh, fun c' => ?_, fun x => ?_, ⟨(cls_eq_iff hL₁ hM₁).1 hcls⟩, ψ₁', mh', ?_, ?_⟩, e⟩
  · refine ext₂ _ _ ?_
    have h := congrArg (fun q => m.φ ≫ q.left) (hact c')
    simp only [Over.comp_left] at h ⊢
    rw [Category.assoc, ← e, ← Category.assoc, m.act c', Category.assoc, h, Category.assoc, m'.act c',
      ← Category.assoc (Over.Hom.left ψ₁), ← e, Category.assoc]
  · refine ext₂ _ _ ?_
    rw [m'.eta x, heta x, Over.comp_left, Over.comp_left, Category.assoc, ← e,
      ← Category.assoc (Over.Hom.left (o₁.eta x)), m.eta x, Category.assoc]
  · refine ext₁ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e', ← Category.assoc, ← e, Category.assoc, ← Over.comp_left, h₁,
      pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine ext₂ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e, ← Category.assoc, ← e', Category.assoc, ← Over.comp_left, h₂,
      pow_comp_of_isGrpPullback m'.cart c hcpos]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ResSurj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable abbrev resU {V : Type} [CommRing V] [IsDomain V] {S : Scheme.{0}} (z : Sp V ⟶ S) :
    Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
  Over.homMk (spMap (algebraMap V (FractionRing V))) rfl

private theorem res_inj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S) {g g' : Over.mk z ⟶ A}
    (e : resU z ≫ g = resU z ≫ g') : g = g' := by
  apply Over.OverMorphism.ext
  have e' := congrArg CommaMorphism.left e
  simp only [Over.comp_left, Over.homMk_left] at e'
  exact (hV S A.left A.hom hA V z).1 g.left g'.left (by simpa using Over.w g)
    (by simpa using Over.w g') e'

private theorem res_surj (hV : ValPtsX) {S : Scheme.{0}} {A : Over S} (hA : IsProper A.hom)
    {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] (z : Sp V ⟶ S)
    (g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A) :
    ∃ g' : Over.mk z ⟶ A, resU z ≫ g' = g := by
  obtain ⟨l, h₁, h₂⟩ := (hV S A.left A.hom hA V z).2 g.left (by simpa using Over.w g)
  exact ⟨Over.homMk l h₁, Over.OverMorphism.ext h₂⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.wVal_of :
    ValPtsX → WVal := by
  intro hV p _ D R _ b N M w V _ _ _ x
  have hU : IsProper M.univ.A.hom := @IsAbelianScheme.proper _ M.univ.A M.univ.grp M.univ.ab
  let φ : (Over.mk x ⟶ M.univ.A) →* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A) :=
    { toFun := fun g => resU x ≫ g
      map_one' := comp_one _
      map_mul' := fun g h => comp_mul _ g h }
  let ρ := MulEquiv.ofBijective φ
    ⟨fun g g' e => res_inj hV hU x e, fun g => res_surj hV hU x g⟩
  have hρ : ∀ g, ρ g = resU x ≫ g := fun _ => rfl
  refine ⟨ρ, ?_⟩
  simp only [hρ]
  refine ⟨fun g => by simp, fun g a => (Category.assoc _ _ _).symm, fun g => ?_, ?_⟩
  · constructor
    · intro hg a ha
      rw [Category.assoc, hg a ha, comp_one]
    · intro hg a ha
      apply res_inj hV hU x
      rw [comp_one, ← Category.assoc]
      exact hg a ha
  · intro r j c T z hz g
    have hO : IsProper T.o.A.hom := @IsAbelianScheme.proper _ T.o.A T.o.grp T.o.ab
    have hO' : IsProper T.o'.A.hom := @IsAbelianScheme.proper _ T.o'.A T.o'.grp T.o'.ab
    constructor
    · intro hk b' hb'
      obtain ⟨a', ha'⟩ := res_surj hV hO z b'
      have ha2 := congrArg CommaMorphism.left ha'
      simp only [Over.comp_left, Over.homMk_left] at ha2
      have hb2 : b'.left ≫ T.ms.φ = spMap (algebraMap V (FractionRing V)) ≫ g.left := by
        simpa using hb'
      have hw : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
        rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
        exact hz
      have key : (Over.homMk (a'.left ≫ T.ms.φ) hw : Over.mk x ⟶ M.univ.A) = g := by
        apply res_inj hV hU x
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        rw [← Category.assoc, ha2, hb2]
      have hg : a'.left ≫ T.ms.φ = g.left := by
        rw [← key]
        simp
      rw [← ha', Category.assoc, hk a' hg, comp_one]
    · intro hk a' ha'
      apply res_inj hV hO' z
      rw [comp_one, ← Category.assoc]
      apply hk
      simp [ha']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.EwOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.ew_of :
    WModEx → RankN → LineC → SecEquiv → KerRead → RedPts → CountIn → PulledEx → CaseE → CaseW → EW := by
  intro hW hRank hLine hSec hKR hRed hCI hPull hE hCW
  intro p _ D O _ _ _ _ f b N r w _ hS M T V _ _ _ _ _ hp x hcl hord φ hφ
  obtain ⟨W⟩ := hW p D O b N M.X M.s M.univ w (Over.mk x)
  obtain ⟨hfin, hrank⟩ := hRank p D O f b N r w hS M V hp x W
  obtain ⟨C, hC1, hC⟩ := hLine p D O f b N r w hS M V hp x hord W
  have hsec := fun j : Fin (D.n + 1) =>
    hSec p D O f b N r w hS M j (Nat.lt_succ_iff.mp j.2) (T j) V hp x W
  choose e he using hsec
  haveI : CharP (IsLocalRing.ResidueField V) p := hord.1
  obtain ⟨β, hβ⟩ : ∃ β : O →+* IsLocalRing.ResidueField V, (resPt V ≫ x) ≫ M.s = spMap β :=
    ⟨(Spec.preimage ((resPt V ≫ x) ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, β a = 0 := by
    intro a ha
    have h1 : (spMap β) (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint O := by
      rw [← hβ]
      have : (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V :=
        IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
      change M.s (x ((resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = _
      rw [this, hcl]
    have h2 : a ∈ ((spMap β) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))).asIdeal := by
      rw [h1]; exact ha
    have h3 : β a ∈ IsLocalRing.maximalIdeal (IsLocalRing.ResidueField V) := h2
    simpa [IsLocalRing.maximalIdeal_eq_bot] using h3
  obtain ⟨o₁, ⟨m₁⟩⟩ : ∃ o₁ : Obj b N (spMap β), Nonempty (ObjMap o₁ M.univ (resPt V ≫ x)) := by
    rw [← hβ]
    exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N M.X (Sp (IsLocalRing.ResidueField V)) M.s (resPt V ≫ x) M.univ
  have hinj : ∀ a a' : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A,
      a.left ≫ m₁.φ = a'.left ≫ m₁.φ → a = a' := by
    intro a a' h
    apply Over.OverMorphism.ext
    apply m₁.cart.1.hom_ext h
    rw [Over.w a, Over.w a']
  have hlift : ∀ q : Sp (IsLocalRing.ResidueField V) ⟶ M.univ.A.left, q ≫ M.univ.A.hom = resPt V ≫ x →
      ∃ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A, a.left ≫ m₁.φ = q := by
    intro q hq
    refine ⟨Over.homMk (m₁.cart.1.lift q (𝟙 _) (by simpa using hq)) ?_, ?_⟩
    · simp
    · simp
  let ρ : W.H → (Sp (IsLocalRing.ResidueField V) ⟶ M.univ.A.left) := fun h => resPt V ≫ (W.pt h).left
  have hρ : ∀ a a', ρ a = ρ a' ↔ a - a' ∈ C := hC
  have key : ∀ (j : ℕ) (Tj : TjD M r w j (p ^ (f * j))) (z : Sp V ⟶ Tj.Y) (_ : z ≫ Tj.s = x)
      (Dd : Submodule (𝓞 D.F ⧸ w) W.H) (_ : ∀ h, h ∈ Dd ↔ KerAt Tj z (W.pt h).left)
      (P : Pulled Tj m₁ (resPt V ≫ z)), RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j) ∧
        ∀ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A,
          UKer r o₁ P.ψ _ a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H) := by
    intro j Tj z hz Dd hD P
    obtain ⟨h1, h2⟩ := hKR p D O f b N r w hS M j Tj V hp x z hz (spMap β) o₁ m₁ P
    refine ⟨h1, fun a => (h2 a).trans ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, hk, ha⟩
      obtain ⟨h, rfl⟩ := (W.range g).2 hg
      exact ⟨h, (hD h).2 hk, ha.symm⟩
    · rintro ⟨h, hh, ha⟩
      exact ⟨W.pt h, (W.range _).1 ⟨h, rfl⟩, (hD h).1 hh, ha.symm⟩
  have hcard : ∀ (Dd : Submodule (𝓞 D.F ⧸ w) W.H)
      (U : (𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A) → Prop),
      (∀ a, U a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H)) →
      Nat.card {a // U a} = Nat.card (ρ '' (Dd : Set W.H)) := by
    intro Dd U hU
    refine Nat.card_eq_of_bijective
      (fun a : {a // U a} => (⟨a.1.left ≫ m₁.φ, (hU _).1 a.2⟩ : ρ '' (Dd : Set W.H))) ⟨?_, ?_⟩
    · intro a a' h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨q, h, hh, rfl⟩
      obtain ⟨a, ha⟩ := hlift (ρ h) (by
        have := Over.w (W.pt h)
        simp only [ρ, Category.assoc]
        rw [this]
        rfl)
      exact ⟨⟨a, (hU a).2 (ha ▸ ⟨h, hh, rfl⟩)⟩, Subtype.ext ha⟩
  have hk : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← hS.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) :=
    Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hcnt : ∀ (j : ℕ) (Dd : Submodule (𝓞 D.F ⧸ w) W.H), Module.finrank (𝓞 D.F ⧸ w) Dd = j → ¬ C ≤ Dd →
      Nat.card (ρ '' (Dd : Set W.H)) = (p ^ f) ^ j := by
    intro j Dd hj hn
    rw [(hRed _ _ _ C ρ hρ Dd).1, hk, ← (hCI _ _ C hC1).2.2 Dd hn, hj]
  have hiff : ∀ (Dd Dd' : Submodule (𝓞 D.F ⧸ w) W.H)
      (U U' : (𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A) → Prop),
      (∀ a, U a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H)) →
      (∀ a, U' a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd' : Set W.H)) → Dd.map C.mkQ = Dd'.map C.mkQ →
      ∀ a, U a ↔ U' a := by
    intro Dd Dd' U U' hU hU' hm a
    rw [hU, hU', (hRed _ _ _ C ρ hρ Dd).2 Dd' hm]
  have hy : ∀ (j : Fin (D.n + 1)) (z : {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = x}),
      (resPt V ≫ z.1) ≫ (T j).s = resPt V ≫ x := by
    intro j z
    rw [Category.assoc, z.2]
  have hP : ∀ (j : Fin (D.n + 1)) (z : {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = x}),
      Nonempty (Pulled (T j) m₁ (resPt V ≫ z.1)) := fun j z =>
    hPull p D O b N hS.three hS.cop M r w j _ (T j) _ (resPt V ≫ x) (spMap β) hβ o₁ m₁ _ (hy j z)
  refine ⟨W.H, inferInstance, inferInstance, hfin, C, e, hrank, hC1, ?_, ?_⟩
  · intro j z z' hn hn' hm
    obtain ⟨P⟩ := hP j z
    obtain ⟨P'⟩ := hP j z'
    obtain ⟨hr, hi⟩ := key j (T j) z.1 z.2 (e j z).1 (he j z) P
    obtain ⟨hr', hi'⟩ := key j (T j) z'.1 z'.2 (e j z').1 (he j z') P'
    have := hE p D O f b N r w hS M j _ (T j) _ (resPt V ≫ x) (spMap β) hβ o₁ m₁ _ _ (hy j z) (hy j z')
      P P' _ hr hr' ((hcard _ _ hi).trans (hcnt j _ (e j z).2 hn)) (hiff _ _ _ _ hi hi' hm)
    exact ⟨by simpa only [Category.assoc] using this.1, this.2⟩
  · intro j j' z z' hjj hin hn' hm
    obtain ⟨P⟩ := hP j z
    obtain ⟨P'⟩ := hP j' z'
    obtain ⟨hr, hi⟩ := key j (T j) z.1 z.2 (e j z).1 (he j z) P
    obtain ⟨hr', hi'⟩ := key j' (T j') z'.1 z'.2 (e j' z').1 (he j' z') P'
    have := hCW p D O f b N r w hS M j' j hjj (T j) (T j') _ φ hφ (resPt V ≫ x) β hβ hker o₁ m₁ _ _
      (hy j z) (hy j' z') P P' hr hr' ((hcard _ _ hi').trans (hcnt j' _ (e j' z').2 hn'))
      (hiff _ _ _ _ hi hi' hm)
    exact ⟨by simpa only [Category.assoc] using this.1, this.2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerRead
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.kerRead_of :
    KerU → FFRead → LiftFF → PullKer → WVal → KerRead := by
  intro hKU hFF hLF hPK hWV p _ D O _ _ _ _ f b N r w _ hS M j T V _ _ _ _ hp x z hz σ o₁ m₁ P
  haveI := M.smooth
  haveI := T.fin
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : LocallyOfFiniteType M.s := inferInstance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.s
  have hcz : CharZero (FractionRing V) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ M.s)
    have key : ∀ n : ℕ, n ≠ 0 → (n : V) ≠ 0 := by
      intro n hn
      obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
      have hmu : IsUnit (m : O) :=
        b.unit m ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hm).symm
      have hmV : IsUnit (m : V) := by simpa using hmu.map φ.hom
      push_cast
      exact mul_ne_zero (pow_ne_zero _ hp) hmV.ne_zero
    refine charZero_of_inj_zero fun n hn => by_contra fun h => key n h ?_
    rw [← map_natCast (algebraMap V (FractionRing V))] at hn
    exact IsFractionRing.injective V (FractionRing V) (by simpa using hn)
  obtain ⟨-, hmon, hact, -, -, ψ', hmon', h1, h2⟩ := T.isog
  obtain ⟨hRep, -, hKill⟩ := hKU p D O b N r w (Ideal.IsMaximal.ne_top ‹_›) hS.ule T.Y (T.s ≫ M.s)
    T.o T.o' T.ψ ψ' (f * j) hmon hmon' hact h1 h2
  have ukerComp : ∀ {T1 T2 : Over T.Y} (u : T1 ⟶ T2) (g : T2 ⟶ T.o.A),
      UKer r T.o T.ψ T2 g → UKer r T.o T.ψ T1 (u ≫ g) := by
    intro T1 T2 u g hg
    obtain ⟨hg1, e, hg2⟩ := hg
    exact ⟨by rw [Category.assoc, hg1, comp_one], e, fun c hc => by rw [Category.assoc, hg2 c hc, comp_one]⟩
  have compat : ∀ (T' : Over (Sp (IsLocalRing.ResidueField V))) (g : T' ⟶ o₁.A)
      (g₀ : Over.mk (T'.hom ≫ resPt V ≫ z) ⟶ T.o.A), g₀.left = g.left ≫ P.m₀.φ →
      (UKer r o₁ P.ψ T' g ↔ UKer r T.o T.ψ (Over.mk (T'.hom ≫ resPt V ≫ z)) g₀) := by
    intro T' g g₀ hg
    obtain ⟨hA, -, hC⟩ := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.m₀ P.m' T.ψ P.ψ P.sq).1 T'
      (Over.mk (T'.hom ≫ resPt V ≫ z)) rfl g g₀ (by simpa using hg)
    simp only [UKer, hA, hC]
  have HT := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.ms T.ms (𝟙 M.univ.A) (𝟙 T.o.A) (by simp)).1
  have hwu : ∀ (T' : Over T.Y) (g : T' ⟶ T.o.A), KilledBy T.o w g →
      (UKer r T.o T.ψ T' g ↔ g ≫ T.ψ = 1) := by
    intro T' g hg
    exact ⟨fun h => h.1, fun h => ⟨h, 1, fun c hc => hg c (hS.ule (by simpa using hc))⟩⟩
  have hcard : Nat.card {g // UKer r T.o T.ψ
      (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g} = (p ^ f) ^ j := by
    have htj := T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)
    have he : ∀ g, UKer r T.o T.ψ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g ↔
        (g ≫ T.ψ = 1 ∧ KilledBy T.o w g) := by
      intro g
      constructor
      · intro hg
        exact ⟨hg.1, htj.1 g hg.1 hg.2⟩
      · intro hg
        exact (hwu _ g hg.2).mpr hg.1
    rw [Nat.card_congr (Equiv.subtypeEquivRight he), htj.2, hS.norm, hS.m1, _root_.one_mul]
  refine ⟨?_, fun a => ?_⟩
  · have hc : ((p ^ (f * j) : ℕ) : V) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hp
    have hR := hFF T.Y T.o.A T.o.ab (UKer r T.o T.ψ) hRep (p ^ (f * j)) hKill V hc z o₁.A P.m₀.φ
      P.m₀.cart.1 (UKer r o₁ P.ψ) compat
    rwa [hcard] at hR
  have hw0 : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = (Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z)).hom := by
    rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, Over.w a]
    rfl
  let a₀ : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw0
  have hiff : UKer r o₁ P.ψ _ a ↔ UKer r T.o T.ψ _ a₀ := compat _ a a₀ rfl
  rw [hiff]
  constructor
  · intro ha₀
    obtain ⟨K, i, -, hfin, hflat, hK⟩ := hRep
    obtain ⟨y0, hy0⟩ := (hK _ a₀).mpr ha₀
    obtain ⟨g', hg'1, hg'2⟩ := hLF T.Y K.left K.hom hfin hflat V z y0.left
      ((Over.w y0).trans (Category.id_comp _))
    have hw1 : (g' ≫ i.left) ≫ T.o.A.hom = (Over.mk z).hom := by
      rw [Category.assoc, Over.w i, hg'1]
      rfl
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (g' ≫ i.left) hw1
    have ha' : UKer r T.o T.ψ _ a' := (hK _ a').mp ⟨Over.homMk g' hg'1, by
      apply Over.OverMorphism.ext
      simp [a']⟩
    have hUi : resPt V ≫ a'.left = a.left ≫ P.m₀.φ := by
      have e1 := congrArg CommaMorphism.left hy0
      simp only [Over.comp_left, Over.homMk_left, a₀] at e1
      simp only [a', Over.homMk_left]
      rw [← Category.assoc, hg'2, e1]
    have hw2 : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
      rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
      exact hz
    let g : Over.mk x ⟶ M.univ.A := Over.homMk (a'.left ≫ T.ms.φ) hw2
    refine ⟨g, ?_, ?_, ?_⟩
    · obtain ⟨ρ, hρl, -, hρk, -⟩ := hWV p D O b N M w V x
      rw [hρk]
      let rz : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      have hag := ukerComp rz a' ha'
      have hkill := (T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)).1
        (rz ≫ a') hag.1 hag.2
      refine ((HT (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z))
        (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x)) rfl (rz ≫ a') (ρ g) ?_).2.2 w).mp hkill
      rw [hρl]
      simp [rz, g]
    · intro a'' ha''
      have e : a'' = a' := by
        apply Over.OverMorphism.ext
        exact T.ms.cart.1.hom_ext (by simpa [g] using ha'') ((Over.w a'').trans (Over.w a').symm)
      rw [e]
      exact ha'.1
    · simp only [g, Over.homMk_left]
      rw [← P.tri, ← Category.assoc, ← hUi, Category.assoc]
  · rintro ⟨g, hgk, hgker, hgeq⟩
    have hw3 : g.left ≫ M.univ.A.hom = z ≫ T.s := (Over.w g).trans hz.symm
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (T.ms.cart.1.lift g.left z hw3) (T.ms.cart.1.lift_snd _ _ _)
    have ha'l : a'.left ≫ T.ms.φ = g.left := T.ms.cart.1.lift_fst _ _ _
    have hk' : KilledBy T.o w a' :=
      ((HT (Over.mk z) (Over.mk x) rfl a' g (by simp [ha'l])).2.2 w).mpr hgk
    have ha' : UKer r T.o T.ψ _ a' := (hwu _ a' hk').mpr (hgker a' ha'l)
    let rp : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ Over.mk z :=
      Over.homMk (resPt V) (Category.id_comp _).symm
    have e : a₀ = rp ≫ a' := by
      apply Over.OverMorphism.ext
      simp only [a₀, rp, Over.homMk_left, Over.comp_left]
      apply T.ms.cart.1.hom_ext
      · rw [Category.assoc, P.tri, Category.assoc, ha'l, hgeq]
      · rw [hw0, Category.assoc, Over.w a']
        exact Category.id_comp _
    rw [e]
    exact ukerComp rp a' ha'
end
