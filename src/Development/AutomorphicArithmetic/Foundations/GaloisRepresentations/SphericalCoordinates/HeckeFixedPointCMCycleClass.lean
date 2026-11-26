module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.TotW
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ}

abbrev TIs {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  GTateIso D.toG k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def IsTr (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s) (ψ : o'.A ⟶ o''.A) : Prop :=
  IsMonHom ψ ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∃ (ψ' : o''.A ⟶ o'.A) (d : ℕ), IsMonHom ψ' ∧ (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
      ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ d.Coprime p) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : ℂ →+* k), t ≫ s = spMap β →
      ∃ (I' : TIs o' t) (I'' : TIs o'' t), (∀ y, toUnit _ ≫ o'.eta y = I'.ev N' y) ∧ (∀ y, toUnit _ ≫ o''.eta y = I''.ev N y) ∧
        ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
          I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

structure Leg (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) where
  q : X'.X ⟶ X.X
  o : GObj gb N X'.s
  ψ : X'.univ.A ⟶ o.A
  φ : GObjMap o X.univ q
  ov : q ≫ X.s = X'.s
  tr : IsTr L h X'.univ o ψ

variable {L} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'} {X : GenModel gb N}

def Leg.tot (c : Leg L h X' X) : X'.univ.A.left ⟶ X.univ.A.left := c.ψ.left ≫ c.φ.φ

theorem Leg.tot_w (c : Leg L h X' X) : c.tot ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q := by
  change (c.ψ.left ≫ c.φ.φ) ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q
  rw [Category.assoc, c.φ.cart.1.w, ← Category.assoc, Over.w]

def Leg.pw (c : Leg L h X' X) (k : ℕ) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  GlobalTheory.KS.powMap c.q c.tot c.tot_w k

def Leg.tw (c : Leg L h X' X) {k : ℕ} (α : Fin k → 𝓞 D.F) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  c.pw k ≫ (GlobalTheory.KS.matEnd X.univ.act (Matrix.diagonal fun s => algebraMap (𝓞 D.F) D.O (α s))).left

abbrev sZ {N : ℕ} (X : GenModel gb N) (k : ℕ) : (GlobalTheory.KS.pow X.univ.A k).left ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def gfamD {N : ℕ} (X : GenModel gb N) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom)
    (hL : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB) : Fam ℂ D.O D.La D.g := gfam X.univ hX hL

def LevOk (L : Link D G) (N N' : ℕ) (h : G.GAf) : Prop :=
  3 ≤ N ∧ N.Coprime p ∧ 3 ≤ N' ∧ N'.Coprime p ∧ N ∣ N' ∧ ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N

end UpperTheory.Gal.W2
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def TateWit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp ℂ) (o : GObj gb N s)
    (hX : SmoothOfRelativeDimension D.g o.A.hom) (hL) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ S) e, 0 < N → N.Coprime p →
    UnifAt (gfam o hX hL) (RingHom.id ℂ) ρ N D' t P x e → ∀ I : TIs o x, (∀ y, toUnit _ ≫ o.eta y = I.ev N y) →
    ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ), IsWit D' f nu ∧ (∀ a, ∃ u, f N a = t a + N • u) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a))

def IsogAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La) (d : ℕ),
      D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ d.Coprime p ∧ (∀ u'', ∃ u, inc u = d • u'') ∧
      ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ) (f'' : ℕ → D.La →+ D''.La) (nu'' : ℕ → ℤ), IsWit D' f nu ∧ IsWit D'' f'' nu'' ∧ (∀ a, ∃ u, f N' a = t a + N' • u) ∧
        (∀ a, ∃ u, f'' N a = t'' a + N • u) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
          (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w

def HeckeCoord : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ (B : GlobalTheory.LKCx.Form G) (j : D'.La →+ VQ D) (h₁ : G.GAf) (M : AddSubgroup (VQ D)), IsPlace L B.β D' j → IsCoordA L (trivX B) N' D' t j h₁ →
    IsLocP D' j M → ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La)
      (j'' : D''.La →+ VQ D), D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ (∀ u'', ∃ (d : ℕ) (u : D'.La), d ≠ 0 ∧ inc u = d • u'') ∧ (∀ u, j'' (inc u) = j u) ∧
      IsPlace L B.β D'' j'' ∧ IsCoordA L (trivX B) N D'' t'' j'' (h₁ * h⁻¹) ∧ IsLocP D'' j'' M

def OneAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t → ∀ (j : D'.La →+ VQ D) (a : G.GAf × Gr G 1), IsPlace L B.β D' j →
    IsCoordA L (trivX B) N' D' t j a.1 → IsLocP D' j (PD.lat a.2) → ∀ P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ e₁, UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D' t P (x ≫ c₁.q) e₁ ∧ ∀ z, (e₁ z).left = (e z).left ≫ c₁.tot

def FixFwd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e → x ≫ c₁.q = x ≫ c₂.q → ∃ y, Sees B {g | h * g ∈ L.KN N} a y

def FixGa : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∃ (ga : D'.La →ₗ[D.O] D'.La) (H : Matrix (Fin D.g) (Fin D.g) ℂ), (∀ u, j (ga u) = actY L y⁻¹ (j u)) ∧ FixesPer D' P ga H ∧
      ∀ w, ∀ Q : VQ D →+ (Fin D.g → ℂ), (∀ u, Q (j u) = P u) → ∀ hQ : IsPerQ L B.β ρ Q, Q (actY L y⁻¹ w) = H *ᵥ Q w

def FixEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ u, j (ga u) = actY L y⁻¹ (j u)) →
    ∀ P₁ P₂ (x₁ x₂ : Sp ℂ ⟶ X'.X) e₁ e₂, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₁ x₁ e₁ → UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₂ x₂ e₂ → (∀ u, P₂ (ga u) = P₁ u) →
      x₁ ≫ c₂.q = x₂ ≫ c₁.q ∧ ∀ z, (e₁ z).left ≫ c₂.tot = (e₂ z).left ≫ c₁.tot

def PwOver : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (k : ℕ),
    c.pw k ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧
    (∀ i, c.pw k ≫ (GlobalTheory.KS.pr X.univ.A i).left = (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot) ∧
    (∀ b : D.O, (X'.univ.act.act b).left ≫ c.tot = c.tot ≫ (X.univ.act.act b).left) ∧
    ∀ α : Fin k → 𝓞 D.F, c.tw α ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧ ∀ i, c.tw α ≫ (GlobalTheory.KS.pr X.univ.A i).left =
      (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot ≫ (X.univ.act.act (algebraMap (𝓞 D.F) D.O (α i))).left

def PowCorr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (S : Sheet X'.s X'.univ.A D' ρ),
    (∀ P, IsPeriod D' ρ P → ∀ (b : D.O) z, (S.ex P (ρ b *ᵥ z)).left = (S.ex P z).left ≫ (X'.univ.act.act b).left) →
    ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ P₁ P₂, IsPeriod D' ρ P₁ → IsPeriod D' ρ P₂ → (∀ u, P₂ (ga u) = P₁ u) →
      S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧ ∀ z, (S.ex P₁ z).left ≫ c₂.tot = (S.ex P₂ z).left ≫ c₁.tot) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), CorrEq S (c₁.pw k) (c₂.tw α) ga (diagAct (algebraMap (𝓞 D.F) D.O) ρ α) ∧
      ∀ P, IsPeriod D' ρ P → (∀ z z', (S.ex P z).left ≫ c₁.tot = (S.ex P z').left ≫ c₁.tot → z - z' ∈ P.range) →
        ∀ z z', S.pt k P z ≫ c₁.pw k = S.pt k P z' ≫ c₁.pw k → S.pt k P z = S.pt k P z'

def FixLoc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) → IsSigD D ρ t₀ →
    SmoothOfRelativeDimension (D.n - 1) X'.s → (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (U : Unif (gfamD X' hX' hL') (RingHom.id ℂ) ρ N' (D.Cls N')) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀)
      (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ)) (j : (U.Di i).La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsPeriod (U.Di i) ρ P →
      IsCoord L B PD RD N' (U.Di i) (U.t i) P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y →
      ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
      ∃ Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ)), (∀ x, x ∈ Fx ↔ x.1 ≫ (GlobalTheory.KS.pow X'.univ.A k).hom = U.u i P ∧
          x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ Fx.Nonempty ∧
        ∀ At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ, (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x)) → (∀ x ∈ Fx, (1 - At x).det ≠ 0) ∧ ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
            wtFix L v t₀ α t (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v _ y a.2.1)

def PowSm : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d g : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → IsSeparated s →
    ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ k : ℕ,
    SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ QuasiCompact ((GlobalTheory.KS.pow A k).hom ≫ s) ∧
      IsSeparated ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ LocallyOfFiniteType ((GlobalTheory.KS.pow A k).hom ≫ s)

def HeckeFixedPointCMCycleClass : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      {x : GlobalTheory.LKCx.AllPts G v (L.KN N') (KHT p G.m G.n 1 G.Fw) | ∃ y, Sees (Quot.out x.1) {g | h * g ∈ L.KN N} (Quot.out x.2) y}.Finite ∧
      (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (L.KN N : Set G.GAf) a y → y = 1) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N') ({g | h * g ∈ L.KN N}.indicator 1) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

def FixZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t = ((L.KN N').relIndex (GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N) (Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ArchFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

def sgnV (v : InfinitePlace G.F) : ℂ := if v.embedding (L.e (D.ω : D.F)) = D.ρc then 1 else -1

abbrev Arch (G : HTGroup p) : Type := InfinitePlace G.F → Fin G.n → ℂ

def hv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ := star y ⬝ᵥ (M *ᵥ x)

structure ArchFrame where
  th : VQ D →+ Arch G
  r : InfinitePlace G.F → ℝ
  r_pos : ∀ v, 0 < r v
  act : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v
  form : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, r v * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
  span : Submodule.span ℝ (Set.range th) = ⊤
  dim : Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D)
  dimg : Module.finrank ℝ (Arch G) = 2 * D.g

def IsFMat (kp : VQ D ≃+ (Fin G.n → G.F)) (σ : G.C ≃ₐ[G.F] Matrix (Fin G.n) (Fin G.n) G.F) : Prop :=
  ∀ c w, kp (L.rep c w) = σ c *ᵥ kp w

def IsPosJ {n : ℕ} (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : Prop :=
  J * J = -1 ∧ Jᴴ * M * J = M ∧ ∀ x, x ≠ 0 → 0 < (-s * Complex.I * hv M (J *ᵥ x) x).re

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigSame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.SameEigenvalues

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ}

private theorem toV_mul (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem toV_inv_cancel (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec]

private theorem same_symm {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) : GlobalTheory.LKCx.Same G v β x t hx Kf K' b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, inv_mem hk1, inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · rw [h1, map_inv, map_inv, ← Prod.inv_mk]
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b d : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) (h' : GlobalTheory.LKCx.Same G v β x t hx Kf K' b d) :
    GlobalTheory.LKCx.Same G v β x t hx Kf K' a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, mul_mem hk1 hk1', mul_mem hk2 hk2', mul_ne_zero hc' hc, ?_, ?_⟩
  · rw [h1', h1, map_mul, map_mul]
    simp only [← Prod.mk_mul_mk, _root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, toV_mul, smul_smul]

private theorem minpoly_conj {F C : Type} [Field F] [Ring C] [Algebra F C] (u : Cˣ) (x : C) :
    minpoly F ((u : C) * x * ((u⁻¹ : Cˣ) : C)) = minpoly F x := by
  let e : C ≃ₐ[F] C :=
    { toFun := fun w => (u : C) * w * ((u⁻¹ : Cˣ) : C)
      invFun := fun w => ((u⁻¹ : Cˣ) : C) * w * (u : C)
      left_inv := fun w => by simp [_root_.mul_assoc]
      right_inv := fun w => by simp [_root_.mul_assoc]
      map_mul' := fun w w' => by simp [_root_.mul_assoc]
      map_add' := fun w w' => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : C) * algebraMap F C r * ((u⁻¹ : Cˣ) : C) = algebraMap F C r
        rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] }
  exact minpoly.algEquiv_eq e x

private theorem posV_ne (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

private theorem eigL_eq {y : GlobalTheory.LKCx.grp G β} {z : Fin G.n → ℂ} {e : ℂ} (hz : z ≠ 0)
    (h : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z) :
    GlobalTheory.RootSumWeights.eigL G v β y z = e := by
  have hf : GlobalTheory.LKCx.FixL G v β y z := ⟨e, h⟩
  unfold GlobalTheory.RootSumWeights.eigL
  rw [dite_eq_left hf]
  have hs := hf.choose_spec
  exact smul_left_injective ℂ hz (hs.symm.trans h)

private theorem conj_eig (y₀ y : GlobalTheory.LKCx.grp G β) (c e : ℂ) (hc : c ≠ 0) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β (y₀ * y * y₀⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
                 (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) =
      e • (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ↔
    (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z := by
  rw [Matrix.mulVec_smul, toV_mul, toV_mul, toV_inv_cancel, smul_comm e c,
    ← Matrix.mulVec_smul _ e z]
  constructor
  · intro h
    have h' := smul_right_injective (Fin G.n → ℂ) hc h
    have h'' := congrArg (fun w => (GlobalTheory.LKCx.toV G v β y₀⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h'
    simpa only [toV_inv_cancel] using h''
  · intro h
    rw [h]

end UpperTheory.Gal.W2.SameEigenvalues

open UpperTheory.Gal.W2.SameEigenvalues in
theorem UpperTheory.Gal.W2.eigSame_of :
    UpperTheory.Gal.W2.EigSame := by
  intro p _ G v c B K S hS a a' hq
  have hE := Quot.eqvGen_exact hq
  have hsame := (Equivalence.eqvGen_iff ⟨fun _ => GlobalTheory.LKCx.same_refl _ _ _ _ _ _ _ _ _,
    fun h => same_symm h, fun h h' => same_trans h h'⟩).mp hE
  obtain ⟨y₀, k, d, hk1, hk2, hd, h1, h2⟩ := hsame
  refine ⟨(MulAut.conj y₀).toEquiv, by simp, fun y => ?_⟩
  have hA : a'.1.1 = B.toAf y₀ * a.1.1 * k.1 := congrArg Prod.fst h1
  have hP : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2 := congrArg Prod.snd h1
  have hV : a'.2.1 =
      d • ((GlobalTheory.LKCx.toV G v B.β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := h2
  have hFix : GlobalTheory.LKCx.FixL G v B.β (y₀ * y * y₀⁻¹) a'.2.1 ↔ GlobalTheory.LKCx.FixL G v B.β y a.2.1 := by
    unfold GlobalTheory.LKCx.FixL
    rw [hV]
    exact exists_congr fun e => conj_eig y₀ y d e hd a.2.1
  have hAf : a'.1.1⁻¹ * B.toAf (y₀ * y * y₀⁻¹) * a'.1.1 ∈ S ↔ a.1.1⁻¹ * B.toAf y * a.1.1 ∈ S := by
    rw [hA, map_mul, map_mul, map_inv]
    have : (B.toAf y₀ * a.1.1 * k.1)⁻¹ * (B.toAf y₀ * B.toAf y * (B.toAf y₀)⁻¹) *
        (B.toAf y₀ * a.1.1 * k.1) = k.1⁻¹ * (a.1.1⁻¹ * B.toAf y * a.1.1) * k.1 := by group
    rw [this]
    exact hS k.1 hk1 _
  have hP1 : a'.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β (y₀ * y * y₀⁻¹) * a'.1.2 ∈ KHT p G.m G.n 1 G.Fw ↔
      a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
    rw [hP, map_mul, map_mul, map_inv]
    have : (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2)⁻¹ *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * GlobalTheory.LKCx.toP1 G B.β y * (GlobalTheory.LKCx.toP1 G B.β y₀)⁻¹) *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2) =
        k.2⁻¹ * (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2) * k.2 := by group
    rw [this]
    constructor
    · intro hm
      have h3 := mul_mem (mul_mem hk2 hm) (inv_mem hk2)
      simpa [_root_.mul_assoc] using h3
    · intro hm
      exact mul_mem (mul_mem (inv_mem hk2) hm) hk2
  have hSees : Sees B S a' (y₀ * y * y₀⁻¹) ↔ Sees B S a y := and_congr hFix (and_congr hAf hP1)
  refine ⟨hSees.symm, fun hs => ⟨?_, ?_⟩⟩
  · show minpoly G.F (((y₀ * y * y₀⁻¹ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ).1 : G.C) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul]
    exact minpoly_conj _ _
  · obtain ⟨e, he⟩ := hs.1
    rw [eigL_eq (posV_ne a.2) he]
    apply eigL_eq (posV_ne a'.2)
    rw [hV]
    exact (conj_eig y₀ y d e hd a.2.1).mpr he
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRegSep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.regSep_of :
    UpperTheory.Gal.W2.RegSep := by
  intro p _ D G L v hv B a y hfix hreg
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv B.β B.sym B.trivR _ _
    B.trivAf.choose_spec.choose_spec y a.1.1 a.2 hfix hreg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordOcc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordOcc_of :
    UpperTheory.Gal.W2.WitOfAd → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordOcc := by
  intro hW hP p _ D G L _ _ v _ t₀ _ ρ _ PD RD N hN hNp B a
  obtain ⟨D', t, j, hcls, hpl, hco, hloc⟩ :=
    hW p D G L B N hN hNp a.1.1 ((PD B).lat a.1.2) ((PD B).isLat _) ((PD B).perf _)
  obtain ⟨Q, hQ, hrel⟩ := (RD B).per a.2
  have hev : Even (Module.finrank ℚ D.F) := by
    rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
    simp [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  have hg : 2 * D.g = Module.finrank ℤ D.La := by
    obtain ⟨k, hk⟩ := hev
    rw [D.rankLa, Datum.g, hk, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact ⟨D', t, Q.comp j, j, hcls, (hP p D G L B.β ρ D' j hpl).2 Q hQ hg, hpl, hco, hloc, Q, hQ,
    fun u => rfl, hrel⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordEx_of :
    UpperTheory.Gal.W2.PlaceEx → UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.PlaceLoc → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordEx := by
  intro hEx hAd hLoc hPer p _ D G L ha hm v hv t₀ ht₀ ρ hρ PD RD N hN hNp D' t P hC hP
  obtain ⟨q, j, hj⟩ := hEx p D G L ha hm v hv t₀ ht₀ ρ hρ N D' t hC ⟨P, hP⟩
  obtain ⟨⟨f, nu, rfl, h1, h2⟩, hH⟩ := hC
  have hW : IsWit D' f nu := by
    refine ⟨h1, fun n hn hnp => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := h2 n hn hnp
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have e : D.plat.EF a a' = 2 * D.EF a a' := by
      show ((2 : ℤ) • D.EF) a a' = _
      simp [LinearMap.smul_apply]
    have := a5 a a'
    rw [e] at this
    exact this
  obtain ⟨h₁, hR⟩ := hAd p D G L (Quot.out q) D' j hj f nu hW
  obtain ⟨M, hM, hs, hML⟩ := hLoc p D G L _ D' j hj hH
  obtain ⟨hp, rfl⟩ := (PD (Quot.out q)).onto M hM hs
  obtain ⟨Q, hQ, hQP⟩ := (hPer p D G L _ ρ D' j hj).1 P hP
  obtain ⟨z, hz⟩ := (RD (Quot.out q)).line Q hQ
  exact ⟨q, ((h₁, hp), z), j, hj, hR N hN hNp, hML, Q, hQ, hQP, hz⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdAct
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIntMult
namespace UpperTheory.Gal.W2

theorem intMult_of : IntMult := by
  unfold IntMult
  intro O _ bar D' ga r hr h
  let Iv : Ideal ℤ := Ideal.span {x | ∃ u u', D'.EF u u' = x}
  have hval : ∀ u u', D'.EF u u' ∈ Iv := fun u u' => Ideal.subset_span ⟨u, u', rfl⟩
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal Iv).principal
  have hc' : Iv = Ideal.span {c} := hc
  have key : ∀ x ∈ Iv, ∃ y ∈ Iv, (y : ℚ) = r * x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, u', rfl⟩ := hx
      exact ⟨_, hval (ga u) (ga u'), h u u'⟩
    | zero => exact ⟨0, Iv.zero_mem, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨y, hy, e⟩ := iha
      obtain ⟨z, hz, e'⟩ := ihb
      exact ⟨y + z, Iv.add_mem hy hz, by push_cast; rw [e, e']; ring⟩
    | smul a x _ ih =>
      obtain ⟨y, hy, e⟩ := ih
      exact ⟨a * y, Iv.mul_mem_left a hy, by simp only [smul_eq_mul]; push_cast; rw [e]; ring⟩
  by_cases hc0 : c = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have hz : ∀ u u', D'.EF u u' = 0 := fun u u' => by
      have := hval u u'
      rw [hc', hc0, Ideal.mem_span_singleton] at this
      simpa using this
    rw [hz, hz, mul_zero]
  · have hcI : c ∈ Iv := by rw [hc']; exact Ideal.mem_span_singleton_self c
    obtain ⟨y, hy, e⟩ := key c hcI
    rw [hc', Ideal.mem_span_singleton] at hy
    obtain ⟨m, rfl⟩ := hy
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hm : (m : ℚ) = r := by
      push_cast at e
      have : (c : ℚ) * m = c * r := by rw [e]; ring
      exact mul_left_cancel₀ hcq this
    refine ⟨m, ?_, fun u u' => ?_⟩
    · have : (0 : ℚ) < m := hm ▸ hr
      exact_mod_cast this
    · have := h u u'
      rw [← hm] at this
      exact_mod_cast this

end UpperTheory.Gal.W2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRigid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rigid_of :
    UpperTheory.Gal.W2.Rigid := by
  intro O _ bar g ρ Λ N D' t P w h hN hfull hper ⟨hiso, hmark⟩ hPw
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hper
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add (f := _), map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  intro u
  rw [← hσ, key]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMinBridge
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.minBridge_of :
    UpperTheory.Gal.W2.MinBridge := by
  intro p _ D G L β D' j hP ga c hga
  obtain ⟨hinj, hsmul, hspan, -⟩ := hP
  set f : 𝓞 D.F →+* G.F := (L.e : D.F →+* G.F).comp (algebraMap (𝓞 D.F) D.F) with hf
  have hpow : ∀ (n : ℕ) (u : D'.La), j ((ga ^ n) u) = (L.rep c ^ n) (j u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, hga, pow_succ, Module.End.mul_apply]
  have key : ∀ (q : (𝓞 D.F)[X]) (u : D'.La),
      j (q.sum fun i b => algebraMap (𝓞 D.F) D.O b • (ga ^ i) u) =
        L.rep (aeval c (q.map f)) (j u) := by
    intro q u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Polynomial.sum_def, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hpow, map_mul, map_pow, Module.End.mul_apply, ← L.rep_F]
    rfl
  have hK : ∀ q : (𝓞 D.F)[X], Kills (algebraMap (𝓞 D.F) D.O) ga q ↔ aeval c (q.map f) = 0 := by
    intro q
    constructor
    · intro h
      apply L.rep_inj
      rw [map_zero]
      refine LinearMap.ext fun w => ?_
      obtain ⟨m, u, hm, hmu⟩ := hspan w
      have h1 : L.rep (aeval c (q.map f)) (j u) = 0 := by rw [← key, h u, map_zero]
      have h2 : m • L.rep (aeval c (q.map f)) w = 0 := by
        rw [← LinearMap.map_smul_of_tower, hmu, h1]
      rw [← Nat.cast_smul_eq_nsmul ℚ] at h2
      rw [LinearMap.zero_apply]
      exact (smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm)
    · intro h x
      apply hinj
      rw [key, h, map_zero, LinearMap.zero_apply, map_zero]
  refine ⟨(minpoly.monic (Algebra.IsIntegral.isIntegral c)).map _, fun q => ?_⟩
  have hcomp : (L.e.symm : G.F →+* D.F).comp f = algebraMap (𝓞 D.F) D.F := by
    ext b
    simp [hf]
  rw [hK, ← minpoly.dvd_iff, ← map_dvd_iff (Polynomial.mapEquiv L.e.symm),
    Polynomial.mapEquiv_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, hcomp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdOfWit
private theorem UpperTheory.Gal.W2.mul_inv_star_of_triv {S A : Type*} [Ring S] [CommRing A] [Algebra A S]
    (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ) (t t' : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x * x'⁻¹ : Sˣ) : S) * (σ ((x * x'⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t * t'⁻¹ : Aˣ) : A) := by
  have key : ∀ u : Sˣ, (σ (u : S)).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    intro u
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = ((x'⁻¹ : Sˣ) : S) * (algebraMap A S t' * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
    rw [← hx']
    calc b = (((x'⁻¹ : Sˣ) : S) * x') * b * ((σ (x' : S)).unop * (σ ((x'⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, key, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hb] at hx
  simp only [mul_assoc, Algebra.left_comm] at hx
  simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  calc _ = algebraMap A S ((t'⁻¹ * t' : Aˣ) : A) * ((x : S) * (((x'⁻¹ : Sˣ) : S) *
        ((σ ((x'⁻¹ : Sˣ) : S)).unop * (σ (x : S)).unop))) := by simp
    _ = algebraMap A S ((t'⁻¹ : Aˣ) : A) * algebraMap A S t := by
        rw [Units.val_mul, map_mul, mul_assoc, hx]
    _ = _ := Algebra.commutes _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.adOfWit_of :
    UpperTheory.Gal.W2.AdCore → UpperTheory.Gal.W2.AdOfWit := by
  intro hcore
  unfold AdCore at hcore
  unfold AdOfWit
  intro p _ D G L B D' j hpl f nu hw
  obtain ⟨x, c, hxc, hread⟩ := hcore p D G L B.β D' j hpl f nu hw
  obtain ⟨t0, ht0⟩ := B.trivAf.choose_spec
  have hmem : ((trivX B * x⁻¹, t0 * c⁻¹) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) ∈ UPts G.star (AfP p) := by
    rw [UPts, mem_uGroup]
    exact mul_inv_star_of_triv _ _ _ _ _ _ ht0 hxc
  let h : G.GAf := ⟨(trivX B * x⁻¹, t0 * c⁻¹), hmem⟩
  refine ⟨h, ?_⟩
  have hrd : ∀ w, rd L (trivX B) h w = rd L x 1 w := by
    intro w
    have hy : (((trivX B * x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C) = x := by
      rw [← Units.val_mul]
      congr 1
      group
    simp only [rd, inv_one, map_one, one_apply_eq_self]
    rw [← hy, map_mul, mul_apply_eq_comp]
    rfl
  intro n hn hcop
  obtain ⟨h1, h2⟩ := hread n hn hcop
  exact ⟨fun w => by rw [hrd]; exact h1 w, fun a => by rw [hrd]; exact h2 a⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PGFine
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem diag_comp' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · have h1 := hs.1
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (fst A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := hs.2
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (snd A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

private theorem diag_lbIso' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂)
    {P' : LB (G2 A').left} {P : LB (G2 A).left} (hP' : P'.IsLB) (hP : P.IsLB) (hpol : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  have h₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp hpol _ (diag_comp' hs).symm
  have h₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP _)) φ rfl
  exact LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) h₁ h₂.symm

theorem gFine_of : GFine := by
  intro p _ D b gb N M X ρ h hL f hf hG hpts hfine
  obtain ⟨φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ := hG
  have hX : SmoothOfRelativeDimension D.g X.univ.A.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} D.g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.g) hcart.1 h
  have hL' : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB := pull_isLB X.univ.isLB _
  have hB := diag_lbIso' hsq X.univ.isLB M.univ.isLB hpol
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap, Sp]
  have key := fun (D' : PLat D.O D.inv) (t : D.La → D'.La) P (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ)) =>
    GlobalTheory.T.uniformisationAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La (M.univ.fam h hL) (gfam X.univ hX hL') N f φA
      hcart hact hB heta D' t P y hy (by
        show (y ≫ f) ≫ M.s = _
        rw [Category.assoc, hf, hy])
  refine ⟨hX, hL', ?_, ?_, ?_⟩
  · intro (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ))
    have hy' : (y ≫ f) ≫ M.s = spMap (RingHom.id ℂ) := by rw [Category.assoc, hf, hy]
    obtain ⟨D', t, P, e, hC, hU⟩ := hfine.pts (y ≫ f) hy'
    obtain ⟨e', he', -⟩ := (key D' t P y hy).2 e hU
    exact ⟨D', t, P, e', hC, he'⟩
  · intro D' t P hC hP
    obtain ⟨y', e, hU⟩ := hfine.occ D' t P hC hP
    obtain ⟨y, ⟨hy, rfl⟩, -⟩ := hpts y' (hU.1)
    obtain ⟨e', he', -⟩ := (key D' t P y (hy.trans hid.symm)).2 e hU
    exact ⟨y, e', he'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w u hw hQ
    obtain ⟨e₁, he₁, -⟩ := (key D' t P y hU.1).1 e hU
    obtain ⟨e₂, he₂, -⟩ := (key D'' t' P' y' hU'.1).1 e' hU'
    have hyy := hfine.sep D' D'' t t' P P' (y ≫ f) (y' ≫ f) e₁ e₂ he₁ he₂ w u hw hQ
    obtain ⟨z, -, huniq⟩ := hpts (y ≫ f) he₁.1
    have a₁ : y = z := huniq y ⟨hU.1.trans hid, rfl⟩
    have a₂ : y' = z := huniq y' ⟨hU'.1.trans hid, hyy.symm⟩
    rw [a₁, a₂]

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseC
noncomputable section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped Classical

namespace UpperTheory.Gal.W2

private theorem rho_ne_conj {p : ℕ} [Fact p.Prime] (D : Datum p) :
    (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h0 := D.ρc_root
  rw [hr] at h0
  have h1 : (r : ℝ) ^ 2 - D.tr * r + D.nm = 0 := by exact_mod_cast h0
  have h2 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * r - D.tr)]

private theorem type_sum {p : ℕ} [Fact p.Prime] (D : Datum p) (t₀ : D.F →+* ℂ) (h₀ : t₀ (D.ω : D.F) = D.ρc)
    (hn : 1 ≤ D.n) (c : 𝓞 D.F) :
    ∑ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      t₀ (c : D.F) + ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (t₀ (c : D.F)) := by
  have hne : ComplexEmbedding.conjugate t₀ ≠ t₀ := by
    intro h
    apply rho_ne_conj D
    have := congrArg (fun τ : D.F →+* ℂ => τ (D.ω : D.F)) h
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using this
  have hc : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using rho_ne_conj D
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      (if τ = t₀ then τ (c : D.F) else 0) + (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) -
        (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0) := by
    intro τ
    unfold typeMult epsD
    by_cases h1 : τ = t₀
    · subst h1
      simp [hne.symm, h₀]
    · by_cases h2 : τ = ComplexEmbedding.conjugate t₀
      · subst h2
        have hc' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
          simpa [ComplexEmbedding.conjugate_coe_eq] using hc
        simp [h1, hc', Nat.cast_sub hn]
        ring
      · by_cases h3 : τ (D.ω : D.F) = D.ρc <;> simp [h1, h2, h3]
  rw [Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_filter]
  simp [ComplexEmbedding.conjugate_coe_eq]

theorem baseC_of : BaseC := by
  intro p _ D ha hm t₀ ht ρ hs gb hst
  have hsub : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
  let i₀ : Fin D.a := ⟨0, by omega⟩
  let b : Base D ℂ :=
    { unit := fun k hk => by
        refine isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 fun h => ?_)
        subst h
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
      ρ := gb.ρ
      ρ_root := gb.ρ_root
      t := gb.t
      t_ω := gb.t_ω
      comax := fun i j hij => absurd (hsub.elim i j) hij
      apart := fun i j hij => absurd (hsub.elim i j) hij }
  refine ⟨b, rfl, fun i => (RingHom.id_comp _).symm, ?_⟩
  intro c
  have hti : b.t i₀ c = t₀ (c : D.F) := by
    have := hst.2 i₀ c
    rw [ht i₀] at this
    exact this
  have hb : b.ρ = D.ρc := hst.1
  have h₀ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  rw [hs.tr c, type_sum D t₀ h₀ hs.pos c, hm, Fintype.sum_subsingleton _ i₀, Fintype.sum_subsingleton _ i₀]
  simp [hti, hb]

end UpperTheory.Gal.W2
end
end
