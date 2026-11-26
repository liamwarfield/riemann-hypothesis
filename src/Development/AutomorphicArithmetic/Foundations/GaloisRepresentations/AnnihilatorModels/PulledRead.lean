module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def KerAt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left) : Prop :=
  ∀ a' : Over.mk z ⟶ T.o.A, a'.left ≫ T.ms.φ = a → a' ≫ T.ψ = 1

def PulledRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c)
    (S : Scheme.{0}) (x : S ⟶ M.X) (σ : S ⟶ Sp R) (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y : S ⟶ T.Y), y ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (a : 𝟙_ (Over S) ⟶ o₁.A), (a ≫ P.ψ = 1 ↔ KerAt T y (a.left ≫ m₁.φ)) ∧
      ∀ h, T.img y (a.left ≫ m₁.φ) h = (a ≫ P.ψ).left ≫ P.m'.φ ≫ T.mt.φ

def SecCard : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c), D.m = 1 →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ (x : Sp K ⟶ M.X) (y : Sp K ⟶ T.Y), y ≫ T.s = x →
    Nat.card {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g ∧ KerAt T y g.left} = Ideal.absNorm w ^ j

def SecInj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def SecSurj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (G : Subgroup (Over.mk x ⟶ M.univ.A)), (∀ g ∈ G, KilledBy M.univ w g) →
    (∀ g ∈ G, ∀ a : 𝓞 D.F, g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O a) ∈ G) → Nat.card G = Ideal.absNorm w ^ j →
    ∃ y : Sp K ⟶ T.Y, y ≫ T.s = x ∧ ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ g ∈ G)

def WVal : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (w : Ideal (𝓞 D.F)) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : Sp V ⟶ M.X),
    ∃ ρ : (Over.mk x ⟶ M.univ.A) ≃* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A),
      (∀ g, (ρ g).left = spMap (algebraMap V (FractionRing V)) ≫ g.left) ∧ (∀ g (a : M.univ.A ⟶ M.univ.A), ρ (g ≫ a) = ρ g ≫ a) ∧
      (∀ g, KilledBy M.univ w g ↔ KilledBy M.univ w (ρ g)) ∧
      ∀ (r : ℤ) (j c : ℕ) (T : TjD M r w j c) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ g,
        KerAt T z g.left ↔ KerAt T (spMap (algebraMap V (FractionRing V)) ≫ z) (ρ g).left

def RankN : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)),
    Module.Finite (𝓞 D.F ⧸ w) W.H ∧ Module.finrank (𝓞 D.F ⧸ w) W.H = D.n

def LineC : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [IsAlgClosed (IsLocalRing.ResidueField V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X), IsWOrd M.univ w (resPt V ≫ x) →
    ∀ W : WMod M.univ w (Over.mk x), ∃ C : Submodule (𝓞 D.F ⧸ w) W.H, Module.finrank (𝓞 D.F ⧸ w) C = 1 ∧
      ∀ a a', resPt V ≫ (W.pt a).left = resPt V ≫ (W.pt a').left ↔ a - a' ∈ C

def SecEquiv : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)), ∃ e : {z : Sp V ⟶ T.Y // z ≫ T.s = x} ≃ Gr (𝓞 D.F ⧸ w) W.H j,
      ∀ z h, h ∈ (e z).1 ↔ KerAt T z.1 (W.pt h).left

def KerRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ (σ : Sp (IsLocalRing.ResidueField V) ⟶ Sp O) (o₁ : Obj b N σ)
      (m₁ : ObjMap o₁ M.univ (resPt V ≫ x)) (P : Pulled T m₁ (resPt V ≫ z)), RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j) ∧
      ∀ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A, UKer r o₁ P.ψ _ a ↔
        ∃ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g ∧ KerAt T z g.left ∧ a.left ≫ m₁.φ = resPt V ≫ g.left

def CaseE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ M.X) (σ : Sp κ ⟶ Sp O),
    x ≫ M.s = σ → ∀ (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y y' : Sp κ ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (P' : Pulled T m₁ y') (d : ℕ), RepAlg o₁.A (UKer r o₁ P.ψ) d → RepAlg o₁.A (UKer r o₁ P'.ψ) d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P.ψ _ g} = d → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = y' ≫ T.t ∧ ∀ a h h', T.img y a h = T.img y' a h'

def CaseW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (j₁ : ℕ), j₁ = j + 1 → ∀ (T : TjD M r w j₁ (p ^ (f * j₁))) (T' : TjD M r w j (p ^ (f * j)))
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (φ : κ →+* κ), (∀ a, φ a = a ^ p ^ f) → ∀ (x : Sp κ ⟶ M.X) (β : O →+* κ),
    x ≫ M.s = spMap β → (∀ a ∈ IsLocalRing.maximalIdeal O, β a = 0) → ∀ (o₁ : Obj b N (spMap β)) (m₁ : ObjMap o₁ M.univ x)
      (y : Sp κ ⟶ T.Y) (y' : Sp κ ⟶ T'.Y), y ≫ T.s = x → y' ≫ T'.s = x → ∀ (P : Pulled T m₁ y) (P' : Pulled T' m₁ y'),
    RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j₁) → RepAlg o₁.A (UKer r o₁ P'.ψ) ((p ^ f) ^ j) →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P'.ψ _ g} = (p ^ f) ^ j → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = spMap φ ≫ y' ≫ T'.t ∧ ∀ a h h', T.img y a h = spMap φ ≫ T'.img y' a h'

def PowExt : Prop := ∀ (S : Scheme.{0}) (A : Over S) (k : ℕ), (Smooth A.hom → Flat (GlobalTheory.KS.pow A k).hom) ∧
    ∀ (X : Scheme.{0}) (u v : X ⟶ (GlobalTheory.KS.pow A k).left), u ≫ (GlobalTheory.KS.pow A k).hom = v ≫ (GlobalTheory.KS.pow A k).hom →
      (∀ i, u ≫ (GlobalTheory.KS.pr A i).left = v ≫ (GlobalTheory.KS.pr A i).left) → u = v

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.sameE_of :
    KillLocal → InfE → SameE := by
  intro hK hI p _ D R _ b N r κ _ _ s o o₁ o₂ ψ₁ ψ₂ hψ₂ hsub d hrep hcard hkill T g hg
  refine ⟨hK κ o.A o₂.A ψ₂ hψ₂ (UKer r o ψ₁) d hrep hsub hkill ?_ T g hg, hg.2⟩
  intro Λ _ _ _ ε g' hP hinf
  rw [hI κ o.A (UKer r o ψ₁) d hrep hcard Λ ε g' hP hinf]
  exact MonObj.one_comp _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsogComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem comp_pow' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : f ≫ (g ^ n) = (f ≫ g) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem pow_comp' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom g] (n : ℕ) : (f ^ n) ≫ g = (f ≫ g) ^ n := by
  exact map_pow (IsMonHom.monoidHom g X) f n

theorem UpperTheory.Gal.crystallineComparison.Mod.isogComp_of :
    PairCalc → IsogComp := by
  intro hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2
  obtain ⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩ := h1
  obtain ⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩ := h2
  haveI := hψ
  haveI := hχ
  haveI := hψ'
  haveI := hχ'
  refine ⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩
  · intro a
    rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro x
    rw [he', he, Category.assoc]
  · rw [(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]
    intro T x y
    have e1 := ((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL
    have e2 := ((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'
    rw [← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]
  · rw [Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1,
      ← pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2,
      ← pow_mul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MWModEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private def killedSub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) :
    letI := ptModuleWvs o T
    Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) :=
  letI := ptModuleWvs o T
  { carrier := {g | KilledBy o w g.toMul}
    zero_mem' := KilledBy.one o w T
    add_mem' := fun {g h} hg hh a ha => by
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg a ha, hh a ha, _root_.mul_one]
    smul_mem' := fun c g hg a ha => by
      show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg a ha,
        one_comp] }

theorem UpperTheory.Gal.crystallineComparison.Mod.wModEx_of :
    WModEx := by
  intro p _ D R _ b N S s o w T
  letI := ptModuleWvs o T
  have htor : Module.IsTorsionBySet (𝓞 D.F) (killedSub o w T) (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show (a : 𝓞 D.F) • (x : Additive (T ⟶ o.A)) = Additive.ofMul 1
    exact x.2 a a.2
  letI : Module (𝓞 D.F ⧸ w) (killedSub o w T) := htor.module
  refine ⟨⟨killedSub o w T, fun x => Additive.toMul (x : Additive (T ⟶ o.A)), ?_, ?_, ?_, ?_⟩⟩
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective h)
  · intro g
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hg
      exact ⟨⟨Additive.ofMul g, hg⟩, rfl⟩
  · intro x y
    rfl
  · intro a x
    rw [Module.IsTorsionBySet.mk_smul]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem pt_core {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s} {o₁ o₁' : Obj b N s'}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A)
    (hsq : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (T : Over S') (g : T ⟶ o₁.A) :
    (g ≫ ψ₁ = 1 ↔ m.ptEquiv T g ≫ ψ = 1) ∧ (g = 1 ↔ m.ptEquiv T g = 1) ∧
      ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I (m.ptEquiv T g) := by
  have key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ := by
    apply Over.OverMorphism.ext
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq,
      Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key, MulEquiv.map_eq_one_iff]
  · rw [MulEquiv.map_eq_one_iff]
  · intro I
    unfold KilledBy
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]

theorem UpperTheory.Gal.crystallineComparison.Mod.pullKer_of :
    PullKer := by
  intro p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq
  refine ⟨?_, ?_⟩
  · intro T T₀ h g g₀ hg₀
    have hw : T₀.hom = eqToHom h ≫ T.hom ≫ f := by
      have e1 := Over.w g₀
      have e2 := Over.w (m.ptEquiv T g)
      rw [ObjMap.ptEquiv_left] at e2
      simp only [Category.assoc] at e2
      rw [← e1, hg₀]
      simp only [Category.assoc]
      rw [e2]
      rfl
    obtain ⟨L, ⟨⟨⟩⟩, hom⟩ := T₀
    change L = T.left at h
    subst h
    simp only [eqToHom_refl, Category.id_comp] at hw hg₀
    subst hw
    have hg : g₀ = m.ptEquiv T g := by
      apply Over.OverMorphism.ext
      rw [ObjMap.ptEquiv_left, hg₀]
    subst hg
    exact pt_core m m' ψ ψ₁ hsq T g
  · intro r w j htj k _ _ _ x
    obtain ⟨h1, h2⟩ := htj k (x ≫ f)
    have c := fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g
    refine ⟨fun g hg he => ?_, ?_⟩
    · rw [(c g).2.2 w]
      obtain ⟨n, hn⟩ := he
      exact h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩
    · rw [← h2]
      exact Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by
        rw [(c g).1, (c g).2.2 w]
        rfl)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.adjoint_of :
    PairCalc → TorsFree → Adjoint := by
  intro hPC hTF p _ D R _ b N k _ s c o o' ψ ψ' hψ hψ' hc T x y
  have hpos : 0 < c := hψ.pos
  obtain ⟨a₁, a₂, -, -, hsim⟩ := hPC p D R b N _ s o
  obtain ⟨a₁', a₂', -, -, -⟩ := hPC p D R b N _ s o'
  obtain ⟨-, hmon, -, -, hiso, -⟩ := hψ
  have hsim' := (hsim o' ψ c).1 hiso
  haveI := hmon
  haveI := hψ'

  have hsym : ∀ (q : Obj b N s) {Y : Over (Sp k)} (u v : Y ⟶ q.A),
      evc q.isLB u v = evc q.isLB v u := by
    intro q Y u v
    have h1 := (GlobalTheory.CechPic.cls_eq_iff q.isLB (pull_isLB q.isLB _)).2 q.symm
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift u v).left) h1
    rw [GlobalTheory.AbDual.cls_ev q.isLB, GlobalTheory.AbDual.pull_evc, lift_snd, lift_fst] at h2
    exact h2

  have hL1 := pull_isLB o'.isLB (lift (fst o.A o'.A ≫ ψ) (snd o.A o'.A)).left
  have hL2 := pull_isLB o.isLB (lift (fst o.A o'.A) (snd o.A o'.A ≫ ψ')).left
  have hL := LB.isLB_div hL1 hL2
  have cL := GlobalTheory.CechPic.cls_div hL1 hL2 hL
  have hev : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc hL u v = evc o'.isLB (u ≫ ψ) v - evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [GlobalTheory.AbDual.evc, cL, map_sub, GlobalTheory.AbDual.cls_ev o'.isLB, GlobalTheory.AbDual.cls_ev o.isLB,
      GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]
  have add₁ := (GlobalTheory.AbDual.isAdditive_iff o.isLB).1 a₁
  have add₁' := (GlobalTheory.AbDual.isAdditive_iff o'.isLB).1 a₁'
  have add₂ := (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 a₂
  have add₂' := (GlobalTheory.BirigidLift.isAdditive_swap_iff o'.isLB).1 a₂'
  have bL₁ : IsAdditive (A := o.A) (T := o'.A) _ := (GlobalTheory.AbDual.isAdditive_iff hL).2 fun Y u u' v ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₁', add₁]
    abel
  have bL₂ : IsAdditive (swap _) := (GlobalTheory.BirigidLift.isAdditive_swap_iff hL).2 fun Y u v v' ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₂', add₂]
    abel

  have hpow : ∀ {Y : Over (Sp k)} (u : Y ⟶ o'.A) (v : Y ⟶ o'.A) (n : ℕ),
      evc o'.isLB u (v ^ n) = n • evc o'.isLB u v := by
    intro Y u v n
    induction n with
    | zero =>
      have e := add₂' Y u 1 1
      rw [_root_.mul_one] at e
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 e
    | succ n ih => rw [pow_succ, add₂', ih, succ_nsmul]
  have hcm : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      c • evc o'.isLB (u ≫ ψ) v = c • evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← hsim' Y u (v ≫ ψ'), ← hpow, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
  have hcls : GlobalTheory.CechPic.cls _ hL = evc hL (fst o.A o'.A) (snd o.A o'.A) := by
    rw [GlobalTheory.AbDual.evc, lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have hz : GlobalTheory.CechPic.cls _ hL = 0 := hTF k o.A o'.A o.ab o'.ab _ hL bL₁ bL₂ c hpos (by
    rw [hcls, hev, smul_sub, hcm, sub_self])
  have hmain : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc o'.isLB (u ≫ ψ) v = evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← sub_eq_zero, ← hev, GlobalTheory.AbDual.evc, hz, map_zero]
  exact ⟨hmain x y, by rw [hsym o', hmain, hsym o]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

private theorem pow_hom_comm {S : Scheme.{0}} {A : Over S} [GrpObj A] (h : A ⟶ A) [IsMonHom h] (n : ℕ) :
    h ≫ ((𝟙 A) ^ n) = ((𝟙 A) ^ n) ≫ h := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih =>
    simp only [pow_succ, Hom.mul_def, comp_lift_assoc, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, Category.comp_id, Category.id_comp, ih]

theorem UpperTheory.Gal.crystallineComparison.Mod.sameW_of :
    KillLocal → InfW → FrobPass → KerU → RepOfFF → TanOne → SameW := by
  intro hKL hInf hFP hKU hRep hTan
  intro p _ D R _ b N hm ha r w hw hu f κ _ _ _ β hβ o o₁ o₂ o₃ ψ₁ ψ₂ F e h1 hψ₂ h3 hF d hd hR1 hc1 hR2 hc2 hcl T g
  have hp : Nat.Prime p := Fact.out
  obtain ⟨-, hm1, hact1, -, -, ψ₁', hψ₁', h11, h12⟩ := h1
  obtain ⟨-, hm3, hact3, -, -, χ', hχ', h31, h32⟩ := h3
  haveI := hm1
  haveI := hm3
  haveI := hψ₁'
  haveI := hχ'
  haveI := hψ₂
  haveI hpow : IsMonHom ((𝟙 o.A) ^ p ^ (e + 1)) := isMonHom_pow o.A _
  have hactP : ∀ a : D.O, o.act.act a ≫ ((𝟙 o.A) ^ p ^ (e + 1)) = ((𝟙 o.A) ^ p ^ (e + 1)) ≫ o.act.act a := by
    intro a
    haveI := o.act.hom a
    exact pow_hom_comm (o.act.act a) _
  have kP := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o ((𝟙 o.A) ^ p ^ (e + 1)) (𝟙 o.A) (e + 1)
    hpow inferInstance hactP (by simp) (by simp)
  obtain ⟨d', hRP⟩ := hRep κ o.A _ kP.1
  have k1 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₁ ψ₁ ψ₁' (e + 1) hm1 hψ₁' hact1 h11 h12
  have k3 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₃ (ψ₂ ≫ F) χ' (e + 1) hm3 hχ' hact3 h31 h32
  obtain ⟨d₃, hR3⟩ := hRep κ o.A _ k3.1
  have sub1 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o ψ₁ T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h11, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have sub3 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o (ψ₂ ≫ F) T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h31, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have hI := hInf p f hp κ o.A (UKer r o ψ₁) (UKer r o ((𝟙 o.A) ^ p ^ (e + 1))) d d' hR1 k1.2.1 hc1 hd hRP sub1
    (hTan p D R b N hm ha r w hu κ β hβ o e)
  have fp := hFP p D R b N r f κ (spMap β) o o₂ ψ₂ hψ₂ d hR2 hc2
  have hF1 : (1 : 𝟙_ (Over (Sp κ)) ⟶ o₂.A) ≫ F = 1 := (hF _ 1).2 (fun _ => rfl)
  constructor
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₃.A (ψ₂ ≫ F) hm3 (UKer r o ψ₁) (p ^ f * d) hR1 k1.2.1 ?_ ?_ T g hg
    · intro g' hg'
      rw [← Category.assoc, ((hcl g').1 hg').1, hF1]
    · intro Λ _ _ _ ε g' hg' hi
      rw [← Category.assoc]
      exact (hF _ _).2 ((fp.2 Λ ε g' hg'.2 hi).2 ((hI Λ ε g' (sub1 _ _ hg') hi).1 hg'))
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₁.A ψ₁ hm1 (UKer r o (ψ₂ ≫ F)) d₃ hR3 k3.2.1 ?_ ?_ T g hg
    · intro g' hg'
      have h2 : g' ≫ ψ₂ = 1 := fp.1 (g' ≫ ψ₂) ((hF _ _).1 (by rw [Category.assoc]; exact hg'.1))
      exact ((hcl g').2 ⟨h2, hg'.2⟩).1
    · intro Λ _ _ _ ε g' hg' hi
      have hk : FrobKill p f hp (g' ≫ ψ₂) := (hF _ _).1 (by rw [Category.assoc]; exact hg'.1)
      exact ((hI Λ ε g' (sub3 _ _ hg') hi).2 ((fp.2 Λ ε g' hg'.2 hi).1 hk)).1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.TensorDecomp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open scoped TensorProduct

private lemma UpperTheory.Gal.crystallineComparison.Mod.tensor_decomp (p : ℕ) [Fact p.Prime] (B : Type) [AddCommGroup B]
    (a : B ⊗[ℤ] ℤ_[p]) :
    ∃ (c : B) (a' : B ⊗[ℤ] ℤ_[p]), a = c ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • a' := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c z =>
    obtain ⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by
      have h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]
        exact PadicInt.sub_zmodRepr_mem z
      obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp h
      refine ⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩
      have : z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p := by rw [hz']; ring
      simp only [zsmul_eq_mul, mul_one]
      push_cast
      rw [mul_comm (p : ℤ_[p])]
      first | (rw [mul_one]; exact this) | simpa using this
    refine ⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩
    rw [hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨c, a', rfl⟩ := ha
    obtain ⟨d, b', rfl⟩ := hb
    exact ⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.oMod_of :
    OMod := by
  intro p _ D hm x
  obtain ⟨e⟩ := D.splitP
  have hsub : Subsingleton (Fin D.m) := by rw [hm]; infer_instance
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  obtain ⟨c, a', ha⟩ := tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)
  let M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Matrix.of fun _ _ => a'
  have hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M' := by
    ext i j
    obtain rfl := Subsingleton.elim i i0
    obtain rfl := Subsingleton.elim j i0
    rw [ha]
    simp [M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]
  have hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) =
      (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M' := by
    have := congrArg e.symm hM
    rw [e.symm_apply_apply, map_add (f := _), map_zsmul, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply] at this
    exact this
  let P : Submodule ℤ D.O := LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))
  have hP : ∀ q : D.O ⧸ P, p • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P := TensorProduct.lift <|
    LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P))
      (fun y y' z => by simp [smul_add])
      (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _)
      (fun y z z' => by simp [add_smul])
      (fun n y z => by rw [map_zsmul, smul_assoc])
  have h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y := by
    intro y
    change PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _
    rw [map_one, one_smul]
  have h2 := congrArg Φ hx
  rw [map_add (f := _), map_zsmul, h1, h1] at h2
  have h3 : (p : ℤ) • Φ (e.symm M') = 0 := by
    rw [natCast_zsmul]; exact hP _
  rw [h3, add_zero, Submodule.Quotient.eq] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨c, y, ?_⟩
  have hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c := hy
  rw [map_natCast, ← sub_eq_iff_eq_add', ← hy']
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.UEltOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uElt_of :
    UElt := by
  intro p _ D r w hw huw e
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hbb : ∀ x : 𝓞 D.F, D.bar (D.bar x) = x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    rw [D.bar_eq, D.bar_eq]
    exact IsCMField.complexConj_apply_apply _ _
  have hp : (p : 𝓞 D.F) ∈ uIdeal D r := p_mem_uIdeal D r
  have hs : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r := sub_mem_uIdeal D r
  set ub : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.bar D.ω - (r : 𝓞 D.F)} with hub
  have hmap : Ideal.map D.bar (uIdeal D r) = ub := by
    simp [uIdeal, Ideal.map_span, Set.image_pair, hub]
  have hc : (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - r) = (r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + D.nm := by
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    apply hw
    rw [Ideal.eq_top_iff_one]
    apply huw
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - r) * (D.bar D.ω - r)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * hc
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hs))
  have hprod : uIdeal D r * ub ≤ Ideal.span {(p : 𝓞 D.F)} := by
    obtain ⟨k, hk⟩ := hdvd
    show Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)} * ub ≤ _
    rw [hub, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [SetLike.mem_coe, hc, Ideal.mem_span_singleton]
      exact ⟨(k : 𝓞 D.F), by exact_mod_cast hk⟩
  have hsup : uIdeal D r ⊔ ub = ⊤ := by
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 D.disc_p
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    rw [Ideal.eq_top_iff_one]
    have hdiff : D.ω - D.bar D.ω ∈ uIdeal D r ⊔ ub := by
      have : D.ω - D.bar D.ω = (D.ω - r) - (D.bar D.ω - r) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hs) (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    have hpm : (p : 𝓞 D.F) ∈ uIdeal D r ⊔ ub := Ideal.mem_sup_left hp
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - D.bar D.ω) * (D.ω - D.bar D.ω)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * (D.ω + D.bar D.ω + D.tr) * D.tr_eq + 4 * (b : 𝓞 D.F) * D.nm_eq
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hdiff))
  have hcopE : uIdeal D r ^ e ⊔ ub ^ e = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hsup).pow)
  have hle : uIdeal D r ^ e * ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← mul_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hprod e
  have hinf : uIdeal D r ^ e ⊓ ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← Ideal.mul_eq_inf_of_coprime hcopE]
    exact hle
  have h1 : (1 : 𝓞 D.F) ∈ uIdeal D r ^ e ⊔ ub ^ e := by
    rw [hcopE]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  have hbz : D.bar z ∈ uIdeal D r ^ e := by
    rw [← hmap, ← Ideal.map_pow] at hz
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv D.bar z).mp hz
    rwa [hbb]
  have hup : ∀ x ∈ uIdeal D r ^ e, D.bar x ∈ ub ^ e := by
    intro x hx
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have hx0u : z + D.bar z - 1 ∈ uIdeal D r ^ e := by
    have : z + D.bar z - 1 = D.bar z - y := by
      rw [← hyz]
      ring
    rw [this]
    exact Ideal.sub_mem _ hbz hy
  have hx0b : z + D.bar z - 1 ∈ ub ^ e := by
    have h := hup _ hx0u
    have : D.bar (z + D.bar z - 1) = z + D.bar z - 1 := by
      rw [map_sub, map_add (f := _), map_one, hbb]
      ring
    rwa [this] at h
  exact ⟨z, fun a ha => hle (Ideal.mul_mem_mul ha hz), hinf (Ideal.mem_inf.mpr ⟨hx0u, hx0b⟩), hbz⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobPass
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable def frPt {κ Λ Λ' : Type} [Field κ] [CommRing Λ] [CommRing Λ'] [Algebra κ Λ] [Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ') : algPt κ Λ' ⟶ algPt κ Λ :=
  Over.homMk (spMap σ) (by
    change spMap σ ≫ spMap (algebraMap κ Λ) = spMap (algebraMap κ Λ')
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ])

private theorem frob_mid (hI : InfE) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {r : ℤ} {κ : Type} [Field κ] {s : Sp κ ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} {d : ℕ}
    (hrep : RepAlg o.A (UKer r o ψ) d)
    (hcard : Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsLocalRing Λ'] [Algebra κ Λ] [algΛ' : Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ')
    (ε : Λ →ₐ[κ] κ) (ε' : Λ' →+* κ) (h1 : ∀ c, ε' (algebraMap κ Λ' c) = c)
    (h2 : ε'.comp σ = ε.toRingHom) (g : algPt κ Λ ⟶ o.A)
    (hK : ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) (hinf : Inf ε g)
    (hker : spMap σ ≫ (g ≫ ψ).left = spMap σ ≫ (1 : algPt κ Λ ⟶ o'.A).left) :
    spMap σ ≫ g.left = spMap σ ≫ (1 : algPt κ Λ ⟶ o.A).left := by
  let ε'' : Λ' →ₐ[κ] κ := { ε' with commutes' := h1 }
  have hfl : (frPt σ hσ).left = spMap σ := rfl
  have hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1 := by
    intro X Y A _ f
    simp [Hom.one_def]
  have hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]
  have hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1 := by
    rw [← hone (frPt σ hσ)]
    ext1
    simp only [Over.comp_left] at hker ⊢
    rw [hfl, Category.assoc]
    exact hker
  obtain ⟨e, he⟩ := hK
  have hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g) := by
    refine ⟨hgψ, e, ?_⟩
    intro a ha
    rw [Category.assoc, he a ha, hone]
  have hinf' : Inf ε'' (frPt σ hσ ≫ g) := by
    unfold Inf at hinf ⊢
    rw [Over.comp_left, hfl, ← Category.assoc, hcomp]
    exact hinf
  have h0 := hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'
  have h0' := congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)
  simp only [Over.comp_left] at h0'
  exact h0'

theorem UpperTheory.Gal.crystallineComparison.Mod.frobPass_of :
    InfE → FrobPass := by
  intro hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard
  haveI := hψ
  have hp : Nat.Prime p := Fact.out
  have hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1 := by
    intro X A B _ _ h _
    simp [Hom.one_def]
  let φ : κ ≃+* κ := iterateFrobeniusEquiv κ p f
  have hφ : ∀ c : κ, φ c = c ^ p ^ f := fun c => rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    have h0 := GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)
    have e := GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ
    have hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
      rw [← e]
      exact hg h0
    have hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _ := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      simp
    ext1
    calc g.left = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ g.left := by rw [hinv, Category.id_comp]
      _ = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
        rw [Category.assoc, hk, ← Category.assoc]
      _ = _ := by rw [hinv, Category.id_comp]
  · intro Λ _ _ _ ε g hK hinf
    have hΛ : (p : Λ) = 0 := by
      rw [← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]
    let τ := GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ
    have hτ : ∀ c : Λ, τ c = c ^ p ^ f := fun c => rfl
    let ε' : Λ →+* κ := φ.symm.toRingHom.comp ε.toRingHom
    have h2 : ε'.comp τ = ε.toRingHom := by
      ext x
      show φ.symm (ε (x ^ p ^ f)) = ε x
      rw [map_pow, ← hφ, RingEquiv.symm_apply_apply]
    constructor
    · intro hk h
      have e := GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ
      have hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left := by
        rw [← e]
        exact hk h
      have h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c := by
        intro c
        show (ε'.comp τ) (algebraMap κ Λ c) = c
        rw [h2]
        exact ε.commutes c
      have := frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g
        ⟨hK.choose, hK.choose_spec⟩ hinf hker
      rw [← e] at this
      exact this
    · intro hk h
      have h' := hk h
      rw [Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']
end
