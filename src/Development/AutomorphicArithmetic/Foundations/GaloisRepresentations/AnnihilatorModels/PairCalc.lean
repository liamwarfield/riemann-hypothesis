module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def WModEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S), Nonempty (WMod o w T)

def ObjTri : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R)
    (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃),
    (∀ m m' : ObjMap o₁ o₂ f, m.φ = m'.φ) ∧
    ∀ (fg : S₁ ⟶ S₃), f ≫ g = fg → ∀ (m₁₃ : ObjMap o₁ o₃ fg) (m₂₃ : ObjMap o₂ o₃ g), ∃ m₁₂ : ObjMap o₁ o₂ f, m₁₂.φ ≫ m₂₃.φ = m₁₃.φ

def PullIsog : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' →
    ∀ (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∀ (o₁ : Obj b N s') (m : ObjMap o₁ o f),
    ∃ (o₁' : Obj b N s') (m' : ObjMap o₁' o' f) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ

def PullKer : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s')
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A), m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ →
    (∀ (T : Over S') (T₀ : Over S) (h : T₀.left = T.left) (g : T ⟶ o₁.A) (g₀ : T₀ ⟶ o.A), g₀.left = eqToHom h ≫ g.left ≫ m.φ →
      (g ≫ ψ₁ = 1 ↔ g₀ ≫ ψ = 1) ∧ (g = 1 ↔ g₀ = 1) ∧ ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I g₀) ∧
    ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsTj r w j o o' ψ → IsTj r w j o₁ o₁' ψ₁

def PulledEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c)
    (S : Scheme.{0}) (x : S ⟶ M.X) (σ : S ⟶ Sp R), x ≫ M.s = σ → ∀ (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y : S ⟶ T.Y),
    y ≫ T.s = x → Nonempty (Pulled T m₁ y)

def KerU : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S]
    (s : S ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A) (e : ℕ), IsMonHom ψ → IsMonHom ψ' →
    (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) → ψ ≫ ψ' = (𝟙 o.A) ^ p ^ e → ψ' ≫ ψ = (𝟙 o'.A) ^ p ^ e →
    RepFF o.A (UKer r o ψ) ∧ IsSub o.A (UKer r o ψ) ∧ ∀ T g, UKer r o ψ T g → g ^ p ^ e = 1

def UElt : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ e : ℕ,
    ∃ α : 𝓞 D.F, (∀ a ∈ uIdeal D r ^ e, a * α ∈ Ideal.span {(p : 𝓞 D.F) ^ e}) ∧ α + D.bar α - 1 ∈ Ideal.span {(p : 𝓞 D.F) ^ e} ∧
      D.bar α ∈ uIdeal D r ^ e

def TanOne : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), D.m = 1 → D.a = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)), uIdeal D r ≤ w →
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (β : R →+* κ), (∀ i, ∀ x ∈ w, β (b.t i x) = 0) →
    ∀ (o : Obj b N (spMap β)) (e : ℕ), TanLe o.A (UKer r o ((𝟙 o.A) ^ p ^ (e + 1)))

def Adjoint : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A),
    IsPIsog c o o' ψ → IsMonHom ψ' → ψ' ≫ ψ = (𝟙 o'.A) ^ c → ∀ (T : Over (Sp k)) (x : T ⟶ o.A) (y : T ⟶ o'.A),
    evc o'.isLB (x ≫ ψ) y = evc o.isLB x (y ≫ ψ') ∧ evc o'.isLB y (x ≫ ψ) = evc o.isLB (y ≫ ψ') x

def PairCalc : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s),
    IsAdditive (A := o.A) (T := o.A) o.P ∧ IsAdditive (swap (A := o.A) (B := o.A) o.P) ∧
    (∀ (T : Over S) (x y : T ⟶ o.A) (a : 𝓞 D.F), evc o.isLB (x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) y =
      evc o.isLB x (y ≫ o.act.act (algebraMap (𝓞 D.F) D.O (D.bar a)))) ∧
    (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), evc o.isLB (snd o.A T ≫ x) (fst o.A T) = 0 → x ^ e = 1) ∧
    ∀ (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (c : ℕ), Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ↔
      ∀ (T : Over S) (x y : T ⟶ o.A), evc o'.isLB (x ≫ ψ) (y ≫ ψ) = c • evc o.isLB x y

def KerFromU : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ)
    (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ →
    (∀ T g, UKer r o ψ₁ T g ↔ UKer r o ψ₂ T g) → ∀ (T : Over (Sp k)) (g : T ⟶ o.A), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1

def IsoOfKer : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ)
    (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ →
    (∀ (T : Over (Sp k)) (g : T ⟶ o.A), g ≫ ψ₁ = 1 ↔ g ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.φ = ψ₂.left

def IsogComp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (c c' : ℕ) (o o₁ o₂ : Obj b N s) (ψ : o.A ⟶ o₁.A) (χ : o₁.A ⟶ o₂.A),
    IsPIsog c o o₁ ψ → IsPIsog c' o₁ o₂ χ → IsPIsog (c * c') o o₂ (ψ ≫ χ)

def QuasiInv : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (c : ℕ), 0 < c →
    ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ → IsFinite ψ.left → Surjective ψ.left →
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp κ) (g : Over.mk z ⟶ o.A), g ≫ ψ = 1 → g = 1) →
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

def FrobIsog : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (φ : κ →+* κ),
    (∀ a, φ a = a ^ p ^ f) → spMap φ ≫ s = s → ∀ o : Obj b N s, ∃ (o' : Obj b N s) (m : ObjMap o' o (spMap φ)) (F : o.A ⟶ o'.A),
      IsPIsog (p ^ f) o o' F ∧ (∀ a : 𝟙_ (Over (Sp κ)) ⟶ o.A, (a ≫ F).left ≫ m.φ = spMap φ ≫ a.left) ∧
      ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), g ≫ F = 1 ↔ FrobKill p f Fact.out g

def SameE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (κ : Type) [Field κ] [IsAlgClosed κ] (s : Sp κ ⟶ Sp R) (o o₁ o₂ : Obj b N s)
    (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsMonHom ψ₂ → IsSub o.A (UKer r o ψ₁) → ∀ d : ℕ, RepAlg o.A (UKer r o ψ₁) d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₁ _ g} = d → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o.A, UKer r o ψ₁ _ g → g ≫ ψ₂ = 1) →
    ∀ T g, UKer r o ψ₁ T g → UKer r o ψ₂ T g

def FrobPass : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (o o' : Obj b N s)
    (ψ : o.A ⟶ o'.A), IsMonHom ψ → ∀ d : ℕ, RepAlg o.A (UKer r o ψ) d → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d →
    (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o'.A, FrobKill p f Fact.out g → g = 1) ∧
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) (g : algPt κ Λ ⟶ o.A),
      (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → Inf ε g → (FrobKill p f Fact.out (g ≫ ψ) ↔ FrobKill p f Fact.out g)

def SameW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), D.m = 1 → D.a = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w →
    ∀ (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (β : R →+* κ), (∀ i, ∀ x ∈ w, β (b.t i x) = 0) →
    ∀ (o o₁ o₂ o₃ : Obj b N (spMap β)) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A) (F : o₂.A ⟶ o₃.A) (e : ℕ),
    IsPIsog (p ^ (e + 1)) o o₁ ψ₁ → IsMonHom ψ₂ → IsPIsog (p ^ (e + 1)) o o₃ (ψ₂ ≫ F) →
    (∀ (T : Over (Sp κ)) (g : T ⟶ o₂.A), g ≫ F = 1 ↔ FrobKill p f Fact.out g) → ∀ d : ℕ, 0 < d →
    RepAlg o.A (UKer r o ψ₁) (p ^ f * d) → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₁ _ g} = d →
    RepAlg o.A (UKer r o ψ₂) d → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₂ _ g} = d →
    (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o.A, UKer r o ψ₁ _ g ↔ UKer r o ψ₂ _ g) → ∀ T g, UKer r o ψ₁ T g ↔ UKer r o (ψ₂ ≫ F) T g

def OMod : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → ∀ x : D.O, ∃ (c : 𝓞 D.F) (y : D.O),
    x = algebraMap (𝓞 D.F) D.O c + algebraMap (𝓞 D.F) D.O (p : 𝓞 D.F) * y

def ImgEq : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (S : Scheme.{0}) (s : S ⟶ Sp R) (o₁ o₂ : Obj b N s)
    (t₁ t₂ : S ⟶ M.X), t₁ ≫ M.s = s → t₂ ≫ M.s = s → ∀ (n₁ : ObjMap o₁ M.univ t₁) (n₂ : ObjMap o₂ M.univ t₂) (m : ObjMap o₁ o₂ (𝟙 S)),
    t₁ = t₂ ∧ m.φ ≫ n₂.φ = n₁.φ

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MValPtsX
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MResClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAlgOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.algOf_of :
    AlgOf := by
  intro S K h hfin hflat V _ _ z
  let h' : pullback h z ⟶ Sp V := pullback.snd h z
  haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin
  haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat
  haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'
  let φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤) := (Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop
  letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra
  have hfinite : φ.hom.Finite := by
    have h1 : h'.appTop.hom.Finite := Scheme.Hom.finite_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hflat' : φ.hom.Flat := by
    have h1 : h'.appTop.hom.Flat := Scheme.Hom.flat_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)
    exact RingHom.Flat.comp h2 h1
  haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite
  haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'
  refine ⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf,
    Module.free_of_flat_of_isLocalRing, ?_⟩
  have key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩
  have := sq.paste_horiz (IsPullback.of_hasPullback h z)
  rwa [Category.id_comp] at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRedPts
namespace UpperTheory.Gal.crystallineComparison.Mod

theorem redPts_of : RedPts := by
  intro k H X _ _ _ _ _ C ρ h D
  obtain ⟨s, hs⟩ : ∃ s : H ⧸ C → H, Function.RightInverse s C.mkQ :=
    ⟨Function.surjInv (Submodule.mkQ_surjective C), Function.rightInverse_surjInv _⟩
  let g : H ⧸ C → X := fun q => ρ (s q)
  have hg : ∀ a, ρ a = g (C.mkQ a) := by
    intro a
    refine (h _ _).2 ?_
    have h1 : C.mkQ (s (C.mkQ a)) = C.mkQ a := hs _
    have h2 := (Submodule.Quotient.eq C).1 h1
    have h3 : a - s (C.mkQ a) = -(s (C.mkQ a) - a) := by abel
    rw [h3]
    exact C.neg_mem h2
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    have hm := (h _ _).1 hq
    have e := (Submodule.Quotient.eq C).2 hm
    simpa [Submodule.mkQ_apply, hs q1, hs q2] using
      (show C.mkQ (s q1) = C.mkQ (s q2) from e)
  have himg : ∀ E : Submodule k H, ρ '' (E : Set H) = g '' ((Submodule.map C.mkQ E : Submodule k (H ⧸ C)) : Set (H ⧸ C)) := by
    intro E
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun a _ => hg a)
  have hcard : ∀ V : Submodule k (H ⧸ C), Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V
    have : Finite (H ⧸ C) := Module.finite_of_finite k
    letI := Fintype.ofFinite k
    letI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  refine ⟨?_, ?_⟩
  · rw [himg D, Nat.card_image_of_injective hinj]
    exact hcard _
  · intro D' hD
    rw [himg D, himg D', hD]

end UpperTheory.Gal.crystallineComparison.Mod
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPicFrob
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem gm_absFrob (p f : ℕ) (hp : p.Prime) (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (y : X)
    (U : X.Opens) (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    gm (GlobalTheory.SS.FrobField.absFrob X p f hp h) y U a = gm (𝟙 X) y U a ^ p ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, gm_val _ _ _ hy, gm_val _ _ _ hy, ← map_pow]
  rfl

theorem picFrob_of : PicFrob := by
  unfold PicFrob
  intro p f hp X h c
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  set F := GlobalTheory.SS.FrobField.absFrob X p f hp h
  have hB : (lbPow L (p ^ f)).IsLB := by
    rw [lbPow]
    exact LB.isLB_linComb hL _ _
  have hmem : ∀ (J : PUnit.{1} → L.ι) (x : X), x ∈ L.U (J PUnit.unit) →
      x ∈ L.wchart (fun _ => 𝟙 X) J := by
    intro J x hx
    show x ∈ ⋂ k, (𝟙 X : X ⟶ X) ⁻¹' (L.U (J k) : Set X)
    rw [Set.mem_iInter]
    intro k
    exact hx
  rw [← GlobalTheory.CechPic.cls_pull hL F (pull_isLB hL F), ← GlobalTheory.CechPic.cls_lbPow hL (p ^ f) hB,
    GlobalTheory.CechPic.cls_eq_iff]
  refine GlobalTheory.CechPic.iso_of_chart hB ⟨fun J => J, ?_, ?_⟩
  · intro J x hx
    exact hmem J x (mem_pull.1 hx)
  · intro y i j hi hj
    have hi' : y ∈ L.U (i PUnit.unit) := mem_pull.1 hi
    have hj' : y ∈ L.U (j PUnit.unit) := mem_pull.1 hj
    rw [gm_pull_g L F (𝟙 X) y i j hi hj]
    erw [gm_linComb L (fun _ => 𝟙 X) (fun _ => ((p ^ f : ℕ) : ℤ)) (𝟙 X) y i j (hmem i y hi')
      (hmem j y hj')]
    rw [Category.id_comp, Category.comp_id, Fintype.prod_unique, zpow_natCast]
    exact gm_absFrob p f hp X h y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ⟨hi', hj'⟩ _

end UpperTheory.Gal.crystallineComparison.Mod
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobHom_of :
    FrobHom := by
  intro p f hp κ _ _ φ hφ A A' _ _ ψ hpull h
  obtain ⟨hpb, hmul⟩ := hpull
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := by
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (CharP.cast_eq_zero κ p)
    rw [map_natCast, map_zero] at e
    exact e
  have hfrκ : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hsq : GlobalTheory.SS.FrobField.absFrob A.left p f hp h ≫ A.hom = A.hom ≫ spMap φ := by
    rw [GlobalTheory.SS.FrobField.absFrob_nat A.hom p f hp h hκ, hfrκ]
  let F : A ⟶ A' := Over.homMk (hpb.lift (GlobalTheory.SS.FrobField.absFrob A.left p f hp h) A.hom hsq)
    (hpb.lift_snd _ _ _)
  have hFψ : F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h := hpb.lift_fst _ _ _
  have hTz : ∀ T : Over (Sp κ), ((p : ℕ) : Γ(T.left, ⊤)) = 0 := fun T =>
    GlobalTheory.SS.FrobField.cast_zero_of_hom T.hom hκ
  have key : ∀ (T : Over (Sp κ)) (x : T ⟶ A),
      (x ≫ F).left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ x.left := by
    intro T x
    rw [Over.comp_left, Category.assoc, hFψ]
    exact (GlobalTheory.SS.FrobField.absFrob_nat x.left p f hp (hTz T) h).symm
  let Fr : ∀ T : Over (Sp κ), Over.mk (T.hom ≫ spMap φ) ⟶ T := fun T =>
    Over.homMk (GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T)) (by
      simp only [Over.mk_hom]
      rw [GlobalTheory.SS.FrobField.absFrob_nat T.hom p f hp (hTz T) hκ, hfrκ])
  haveI hF : IsMonHom F := by
    apply isMonHom_of_mul F
    intro T x y
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [← hmul T (x ≫ F) (y ≫ F) (Fr T ≫ x) (Fr T ≫ y) (by rw [key]; rfl) (by rw [key]; rfl),
        ← MonObj.comp_mul, key, Over.comp_left]
      rfl
    · rw [Over.w, Over.w]
  refine ⟨F, hF, hFψ, fun T g => ?_⟩
  have hone : (1 : T ⟶ A').left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ (1 : T ⟶ A).left := by
    rw [← MonObj.one_comp (X := T) F, key]
  constructor
  · intro hg h'
    have e := congrArg (fun k => k.left ≫ ψ) hg
    rw [key, hone] at e
    exact e
  · intro hk
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [key, hone]
      exact hk (hTz T)
    · rw [Over.w, Over.w]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MConstSub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory GlobalTheory.PointQuot

private theorem constObj_hom_ext {S : Scheme} {I : Type} {Z : Over S} (f₁ f₂ : constObj S I ⟶ Z)
    (h : ∀ c, PointQuot.constPt S c ≫ f₁ = PointQuot.constPt S c ≫ f₂) : f₁ = f₂ := by
  ext : 1
  apply Sigma.hom_ext
  intro c
  have := congrArg Over.Hom.left (h c)
  exact this

theorem UpperTheory.Gal.crystallineComparison.Mod.constSub_of : ConstSub := by
  intro K _ A _ hsep Γ hfin
  have hinj : Function.Injective (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) := Subtype.val_injective
  haveI hmono : Mono (constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A))) := mono_constDesc _ hinj
  obtain ⟨hG, hmon⟩ := exists_grpObj_constObj (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) Γ
    Subtype.range_coe
  have hsplit : FinEt.IsSplitOfRank (constObj (Sp K) Γ).hom (Nat.card Γ) := by
    rw [FinEt.isSplitOfRank_iff_exists_iso]
    refine ⟨Sigma.reindex (Finite.equivFin Γ).symm (fun _ => Sp K), ?_⟩
    apply Sigma.hom_ext
    intro j
    have h := Sigma.ι_reindex_hom (Finite.equivFin Γ).symm (fun _ : Γ => Sp K) j
    simp only [constObj, Over.mk_hom]
    rw [← Category.assoc]
    erw [h]
    simp
  haveI := hsplit.isFinite
  haveI := hsplit.etale
  refine ⟨constObj (Sp K) Γ, hG, constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)), hmon, hmono,
    hsplit.isFinite, hsplit.etale, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsplit.isFinite, (inferInstance : Flat (constObj (Sp K) Γ).hom), ?_, hsplit.finrank_eq⟩
    let c0 : Γ := ⟨1, Γ.one_mem⟩
    have hw : (PointQuot.constPt (Sp K) c0).left ≫ (toUnit (constObj (Sp K) Γ)).left = 𝟙 _ := by
      rw [← Over.comp_left]
      simp
    refine ⟨fun y => ⟨(PointQuot.constPt (Sp K) c0).left y, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hw]
    rfl
  · intro g
    constructor
    · rintro ⟨y, hy⟩
      let z : (𝟙_ (Over (Sp K))).left := (⊥ : PrimeSpectrum K)
      obtain ⟨V, hzV, c, hc⟩ := locally_const_desc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) y z
      haveI : Nonempty (openObj (𝟙_ (Over (Sp K))) V).left := ⟨⟨z, hzV⟩⟩
      haveI := epi_toUnit (openObj (𝟙_ (Over (Sp K))) V)
      have e : openι (𝟙_ (Over (Sp K))) V = toUnit _ := toUnit_unique _ _
      rw [hy, e] at hc
      have := (cancel_epi _).1 hc
      rw [this]
      exact c.2
    · intro hg
      exact ⟨PointQuot.constPt (Sp K) (⟨g, hg⟩ : Γ), constPt_desc _ _⟩
  · intro α hα
    apply constObj_hom_ext
    intro c
    rw [← Category.assoc, constPt_desc]
    exact (hα _ c.2).trans (comp_one _).symm
  · intro α hα
    refine ⟨constDesc (fun c : Γ => PointQuot.constPt (Sp K) (⟨c.1 ≫ α, hα _ c.2⟩ : Γ)), ?_⟩
    apply constObj_hom_ext
    intro c
    simp only [← Category.assoc, constPt_desc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exA (hIn : CountIn) (hOut : CountOut) {n : ℕ} {P : Type} {I : Fin (n + 1) → Type}
    (v : ∀ j, I j → P) {k H : Type} [Field k] [Finite k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (e : ∀ j, I j ≃ Gr k H j)
    (hn : Module.finrank k H = n) (hC : Module.finrank k C = 1) :
    ∃ (A : Submodule k (H ⧸ C) → P) (D : Submodule k (H ⧸ C) → Submodule k H),
      (∀ E, ¬ C ≤ D E) ∧ (∀ E, (D E).map C.mkQ = E) ∧
      (∀ E, Module.finrank k (D E) = Module.finrank k E) ∧
      (∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1) ∧
      ∀ E (j' : Fin (n + 1)) (hj' : Module.finrank k (D E) = j'),
        A E = v j' ((e j').symm ⟨D E, hj'⟩) := by
  classical
  have hex : ∀ E : Submodule k (H ⧸ C), ∃ D : Submodule k H, ¬ C ≤ D ∧ D.map C.mkQ = E := by
    intro E
    have hcard := hOut k H C hC E
    have hpos : 0 < Nat.card {D : Submodule k H // ¬ C ≤ D ∧ D.map C.mkQ = E} := by
      rw [hcard]
      exact pow_pos Nat.card_pos _
    obtain ⟨⟨D, hD⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨D, hD⟩
  choose D hDC hDE using hex
  have hrk : ∀ E, Module.finrank k (D E) = Module.finrank k E := by
    intro E
    rw [(hIn k H C hC).2.2 (D E) (hDC E), hDE E]
  have hlt : ∀ E : Submodule k (H ⧸ C), Module.finrank k E < n + 1 := by
    intro E
    have h1 : Module.finrank k E ≤ Module.finrank k (H ⧸ C) := Submodule.finrank_le E
    have h2 : Module.finrank k (H ⧸ C) ≤ Module.finrank k H := Submodule.finrank_quotient_le C
    omega
  refine ⟨fun E => v ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩
      ((e _).symm ⟨D E, rfl⟩), D, hDC, hDE, hrk, hlt, ?_⟩
  intro E j' hj'
  obtain rfl : j' = ⟨Module.finrank k (D E), by rw [hrk]; exact hlt E⟩ := Fin.ext hj'.symm
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.ordReadOf_of :
    CountIn → CountOut → OrdReadOf := by
  intro hIn hOut q n P F I v k H _ _ _ _ _ C e hq hn hC h1 h2
  obtain ⟨A, D, hDC, hDE, hrk, hlt, hA⟩ := exA hIn hOut v C e hn hC
  refine ⟨k, H, _, inferInstance, _, _, inferInstance, C, A, e, hq, hn, hC, fun j i => ⟨fun hle => ?_, fun hnle => ?_⟩⟩
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : (j : ℕ) = Module.finrank k E + 1 := by
      rw [← (e j i).2, (hIn k H C hC).2.1 _ hle]
    let j' : Fin (n + 1) := ⟨Module.finrank k E, hlt E⟩
    have hj' : Module.finrank k (D E) = j' := hrk E
    have hs : ((e j') ((e j').symm ⟨D E, hj'⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j') ⟨D E, hj'⟩)
    rw [hA E j' hj']
    apply h2 j j' i
    · exact hj
    · exact hle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
  · set E := ((e j i).1).map C.mkQ with hEdef
    have hj : Module.finrank k (D E) = j := by
      rw [hrk E, ← (e j i).2, (hIn k H C hC).2.2 _ hnle]
    have hs : ((e j) ((e j).symm ⟨D E, hj⟩)).1 = D E :=
      congrArg Subtype.val (Equiv.apply_symm_apply (e j) ⟨D E, hj⟩)
    rw [hA E j hj]
    apply h1 j i
    · exact hnle
    · rw [hs]; exact hDC E
    · rw [hs, hDE E]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSplitAlg
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.splitAlg_of :
    SplitAlg := by
  classical
  intro κ B Λ _ _ _ _ _ _ _ hcard ε g
  have hli := linearIndependent_toLinearMap κ B κ
  haveI : Finite (B →ₐ[κ] κ) := hli.finite
  letI := Fintype.ofFinite (B →ₐ[κ] κ)
  have hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Subspace.dual_finrank_eq).symm
  have h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0 := by
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff κ x]
    intro f
    have hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, rfl⟩ := hy
      exact hx φ
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  have hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y := by
    intro y hy
    by_contra h
    have hym : y ∈ IsLocalRing.maximalIdeal Λ := h
    have hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom := by
      rw [RingHom.mem_ker]
      simp
    have hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ := by
      have := Ideal.sub_mem _ hym (hk hd)
      simpa using this
    exact hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))
  ext b
  simp only [AlgHom.comp_apply, Algebra.ofId_apply]
  set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS
  set c := ε (g b) with hc
  have hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    apply h0
    intro φ
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := φ b) (by simp [hS])
    simp
  have hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hqb, map_zero]
  have hcS : c ∈ S := by
    have h1 := congrArg ε hq
    rw [← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨s, hs, hs0⟩ := h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0
    rw [hc, hs0]
    exact hs
  rw [← Finset.mul_prod_erase S _ hcS, map_mul] at hq
  have hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s))) := by
    apply hunit
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod,
      Finset.prod_ne_zero_iff]
    intro s hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have h2 := hr.mul_left_eq_zero.mp hq
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  exact sub_eq_zero.mp h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobFin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIntegral_of_pow {R : Type} [CommRing R] (φ : R →+* R) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ y, φ y = y ^ n) : φ.IsIntegral := by
  intro y
  refine ⟨Polynomial.X ^ n - Polynomial.C y, Polynomial.monic_X_pow_sub_C y hn.ne', ?_⟩
  simp [hφ]

private theorem isIntegralHom_absFrob_affine (p f : ℕ) (hp : Nat.Prime p) (Y : Scheme) [IsAffine Y] (h : ((p : ℕ) : Γ(Y, ⊤)) = 0) :
    IsIntegralHom (GlobalTheory.SS.FrobField.absFrob Y p f hp h) := by
  have hk : ((p : ℕ) : Γ(Sp Γ(Y, ⊤), ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Γ(Y, ⊤) h
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk =
      spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h) :=
    GlobalTheory.SS.FrobField.absFrob_spec Γ(Y, ⊤) p f hp hk _ (fun _ => rfl)
  have hnat := GlobalTheory.SS.FrobField.absFrob_nat Y.isoSpec.hom p f hp h hk
  have he : GlobalTheory.SS.FrobField.absFrob Y p f hp h =
      Y.isoSpec.hom ≫ GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk ≫ Y.isoSpec.inv := by
    rw [← Category.comp_id (GlobalTheory.SS.FrobField.absFrob Y p f hp h), ← Y.isoSpec.hom_inv_id,
      ← Category.assoc, hnat, Category.assoc]
    rfl
  rw [he, hsp]
  have hi : IsIntegralHom (spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h)) :=
    (IsIntegralHom.SpecMap_iff).mpr (isIntegral_of_pow _ (pow_pos hp.pos f) (fun _ => rfl))
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.frobFin_of :
    FrobFin := by
  intro p f hp κ _ _ _ X s hs h
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : ((p : ℕ) : κ) = 0 := CharP.cast_eq_zero κ p
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp κ hk0
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ _ (fun _ => rfl)
  have hb : Function.Bijective (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
    constructor
    · intro x y hxy
      change x ^ p ^ f = y ^ p ^ f at hxy
      have hz : (x - y) ^ p ^ f = 0 := by rw [sub_pow_char_pow, hxy, sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos hp.pos f).ne' |>.mp hz)
    · intro y
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hp.pos f)
      exact ⟨x, hx⟩
  let e : κ ≃+* κ := RingEquiv.ofBijective _ hb
  haveI : IsIso (spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0)) := by
    change IsIso (Spec.map (RingEquiv.toCommRingCatIso e).hom)
    infer_instance
  refine ⟨?_, ⟨fun x => ⟨x, rfl⟩⟩⟩
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  constructor
  · rw [@HasAffineProperty.eq_targetAffineLocally @IsIntegralHom _ IsIntegralHom.hasAffineProperty]
    intro U
    haveI : IsAffine U.1.toScheme := U.2
    apply (@HasAffineProperty.iff_of_isAffine @IsIntegralHom _ IsIntegralHom.hasAffineProperty _ _ _ _).mp
    have hU : ((p : ℕ) : Γ(U.1.toScheme, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_of_hom U.1.ι h
    have heq : GlobalTheory.SS.FrobField.absFrob X p f hp h ⁻¹ᵁ U.1 = U.1 := rfl
    have hres : GlobalTheory.SS.FrobField.absFrob X p f hp h ∣_ U.1 =
        (X.isoOfEq heq).hom ≫ GlobalTheory.SS.FrobField.absFrob U.1.toScheme p f hp hU := by
      rw [← cancel_mono U.1.ι, morphismRestrict_ι, Category.assoc,
        GlobalTheory.SS.FrobField.absFrob_nat U.1.ι p f hp hU h, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    rw [hres]
    haveI := isIntegralHom_absFrob_affine p f hp U.1.toScheme hU
    infer_instance
  · have hc : GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s = s ≫ spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
      rw [GlobalTheory.SS.FrobField.absFrob_nat s p f hp h hκ, hsp]
    haveI : LocallyOfFiniteType (GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ s
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftPt_of :
    LiftPt := by
  intro V _ _ _ _ B _ _ _ _ χ hχ
  classical
  let m : Ideal B := RingHom.ker χ
  haveI : m.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨q, hqmin, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : q.IsPrime := hqmin.1.1
  have hnzd : ∀ v : V, v ≠ 0 → algebraMap V B v ∈ nonZeroDivisors B := by
    intro v hv
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
    · rw [← Algebra.commutes, ← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
  have hinj : Function.Injective (algebraMap V (B ⧸ q)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hqmin) hv (hnzd v hv0)
  have hK : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V (FractionRing V)
  haveI : Module.IsTorsionFree V (B ⧸ q) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hinj (by rw [h, map_zero])
  haveI : Module.IsTorsionFree V (FractionRing V) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hK (by rw [h, map_zero])
  haveI : Algebra.IsIntegral V (B ⧸ q) := inferInstance
  haveI : Algebra.IsAlgebraic V (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φ : (B ⧸ q) →ₐ[V] FractionRing V := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := V)
    ext v
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, RingHom.coe_coe, AlgHom.commutes]
    exact map_eq_zero_iff _ hK
  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) := hx
    rwa [hker] at this
  let ψ : B →ₐ[V] FractionRing V := φ.comp (Ideal.Quotient.mkₐ V q)
  have hψ : ∀ b, ψ b ∈ (⊥ : Subalgebra V (FractionRing V)) := by
    intro b
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral (R := V) (Ideal.Quotient.mkₐ V q b)).map φ)
    exact ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective hK
  let z : B →ₐ[V] V := e.toAlgHom.comp (ψ.codRestrict ⊥ hψ)
  have hz : ∀ b, algebraMap V (FractionRing V) (z b) = ψ b := by
    intro b
    have h1 := e.symm_apply_apply (ψ.codRestrict ⊥ hψ b)
    have h2 := e.symm.commutes (z b)
    have h3 : (algebraMap V V) (z b) = e (ψ.codRestrict ⊥ hψ b) := rfl
    rw [h3, h1] at h2
    have h4 := congrArg (fun s : (⊥ : Subalgebra V (FractionRing V)) => (s : FractionRing V)) h2
    simpa using h4.symm
  refine ⟨z, ?_⟩
  ext b
  have hc : b - algebraMap V B (z b) ∈ q := by
    have h0 : z (b - algebraMap V B (z b)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h1 : ψ (b - algebraMap V B (z b)) = 0 := by
      rw [← hz, h0, map_zero]
    have h2 : Ideal.Quotient.mkₐ V q (b - algebraMap V B (z b)) = 0 :=
      hφinj (by rw [map_zero]; exact h1)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  have hm : χ (b - algebraMap V B (z b)) = 0 := hqm hc
  rw [map_sub, sub_eq_zero] at hm
  rw [hm, ← RingHom.comp_apply, hχ]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ExistsAlg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma exists_alg {κ B Λ : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing Λ] [Algebra κ Λ]
    (u : Sp Λ ⟶ Sp B) (h : u ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ)) :
    ∃ ν : B →ₐ[κ] Λ, u = spMap ν.toRingHom := by
  obtain ⟨φ, rfl⟩ : ∃ φ, u = Spec.map φ := ⟨Spec.preimage u, (Spec.map_preimage u).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ Λ := by
    have h' : Spec.map (CommRingCat.ofHom (algebraMap κ B) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Λ)) := by
      rw [Spec.map_comp]
      exact h
    have h'' := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom h''
  refine ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, ?_⟩
  rfl

theorem UpperTheory.Gal.crystallineComparison.Mod.infE_of :
    SplitAlg → InfE := by
  intro hS κ _ A _ P d hRep hcard Λ _ _ _ ε g hP hInf
  obtain ⟨B, _, _, hfin, hfree, hrank, i, hmono, hiff⟩ := hRep
  haveI : Mono i := hmono
  have key : ∀ (Λ' : Type) [CommRing Λ'] [Algebra κ Λ'] (ν : B →ₐ[κ] Λ'),
      spMap ν.toRingHom ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ') := by
    intro Λ' _ _ ν
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  have hid : spMap (algebraMap κ κ) = 𝟙 (Sp κ) := by simp [spMap]
  let F : (B →ₐ[κ] κ) → { g // P (𝟙_ (Over (Sp κ))) g } := fun ν =>
    ⟨Over.homMk (U := 𝟙_ (Over (Sp κ))) (V := algPt κ B) (spMap ν.toRingHom)
        (by
          show spMap ν.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
          rw [key κ ν, hid]) ≫ i,
      (hiff _ _).1 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro ν₁ ν₂ h
      have h1 := congrArg Subtype.val h
      have h2 := (cancel_mono i).1 h1
      have h3 := congrArg CommaMorphism.left h2
      have h4 : CommRingCat.ofHom ν₁.toRingHom = CommRingCat.ofHom ν₂.toRingHom :=
        Spec.map_injective h3
      ext x
      exact congrArg (fun φ => φ.hom x) h4
    · rintro ⟨g₀, hg₀⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg₀
      obtain ⟨ν, hν⟩ := exists_alg (Λ := κ) y.left (by
        rw [hid]
        exact Over.w y)
      refine ⟨ν, Subtype.ext ?_⟩
      show _ ≫ i = g₀
      rw [← hy]
      congr 1
      apply Over.OverMorphism.ext
      simp [hν]
  have hpts : Nat.card (B →ₐ[κ] κ) = Module.finrank κ B := by
    rw [hrank, ← hcard]
    exact Nat.card_congr (Equiv.ofBijective F hF)
  obtain ⟨y, hy⟩ := (hiff _ _).2 hP
  obtain ⟨ν, hν⟩ := exists_alg y.left (Over.w y)
  have hsplit := hS κ B Λ hpts ε ν
  have e1 : spMap ν.toRingHom = spMap (algebraMap κ Λ) ≫ spMap (ε.comp ν).toRingHom := by
    conv_lhs => rw [hsplit]
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e2 : spMap ε.toRingHom ≫ spMap (algebraMap κ Λ) = 𝟙 (Sp κ) := by
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show ε.toRingHom.comp (algebraMap κ Λ) = RingHom.id κ from by ext r; simp]
    simp
  have gl : g.left = y.left ≫ i.left := by
    rw [← hy]
    rfl
  have one_l : ∀ T : Over (Sp κ), (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
    intro T
    show (toUnit T ≫ η[A]).left = _
    rw [Over.comp_left]
    congr 1
  have hI : spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left := hInf
  rw [one_l, gl, hν, e1] at hI
  simp only [← Category.assoc, e2, Category.id_comp] at hI
  apply Over.OverMorphism.ext
  rw [one_l, gl, hν, e1, Category.assoc, hI]
  rfl
end
