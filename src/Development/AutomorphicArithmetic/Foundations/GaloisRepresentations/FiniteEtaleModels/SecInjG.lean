module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

structure BPt (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
    {f : X₁.Y.X ⟶ X₂.M.X} (mf : ObjMap X₁.Y.univ X₂.M.univ f) {c : ℕ} (Tj : TjD X₂.M r 𝔴' i c) : Type where
  y : (T.M M₁).X ⟶ Tj.Y
  ys : y ≫ Tj.s = C₁.j ≫ f
  yt : y ≫ Tj.t = W.π ≫ C₂.j ≫ X₂.π
  fa : (T.M M₁).univ.A.left ⟶ Tj.o.A.left
  fb : W.o.A.left ⟶ Tj.o'.A.left
  ca : IsGrpPullback (T.M M₁).univ.A Tj.o.A y fa
  cb : IsGrpPullback W.o.A Tj.o'.A y fb
  sq : fa ≫ Tj.ψ.left = W.ψ.left ≫ fb
  ms : fa ≫ Tj.ms.φ = C₁.m.φ ≫ mf.φ
  mt : fb ≫ Tj.mt.φ = W.φ.φ ≫ C₂.m.φ ≫ X₂.mπ.φ

end

def IsogG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R' : Type) [CommRing R'] [Algebra ℚ R'] (gb : GBase D.toG R')
    (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴₀ 𝔴 : Ideal (𝓞 D.F)) (atq : AtPrime D q r 𝔴₀)
    (sp : Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))), D.m = 1 → 𝔴.IsMaximal → uId D q r ≤ 𝔴 →
    ∀ (R : Type) [CommRing R] (b : Base (datAt atq sp) R) (N₀ : ℕ), N₀.Coprime q → ∀ (i e : ℕ), Ideal.absNorm 𝔴 ^ i = q ^ e →
    ∀ (h u : G.GAf), IsTjElt L q r 𝔴 i h → Integ L h → u ∈ L.KN N₀ → ∀ (N' N : Lv p) (c' c : ℕ), N'.1 = N₀ * c' → N.1 = N₀ * c →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L (h * u) o' o ψ →
    ∀ (s₀ : X ⟶ Sp R) (o₁ o₂ : Obj b N₀ s₀) (n₁ : QMap (D := datAt atq sp) (gb := gb) o' o₁ (𝟙 _) c')
      (n₂ : QMap (D := datAt atq sp) (gb := gb) o o₂ (𝟙 _) c),
    ∃ ψ₀ : o₁.A ⟶ o₂.A, n₁.φ ≫ ψ₀.left = ψ.left ≫ n₂.φ ∧ ES.IsPIsog (q ^ e) o₁ o₂ ψ₀ ∧ ES.IsTj (D := datAt atq sp) r 𝔴 i o₁ o₂ ψ₀

def TjExG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal →
    ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) → ∀ M : Model b N, Nonempty (TjD M r w j (p ^ e))

def SecInjG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
    ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal → ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) →
    ∀ (M : Model b N) (T : TjD M r w j (p ^ e)) (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
      (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, ES.KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def DescExt : Prop :=
  ∀ (O E : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E]
    (V X Y B : Scheme.{0}) (s : X ⟶ Sp O) (σ : V ⟶ Sp E) (j : V ⟶ X) (ov : j ≫ s = σ ≫ spMap (algebraMap O E)), Smooth s →
    IsFinite (pullback.lift j σ ov) → Etale (pullback.lift j σ ov) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (τ : Sp Ω ⟶ Sp E), x ≫ s = τ ≫ spMap (algebraMap O E) → ∃ v, v ≫ j = x ∧ v ≫ σ = τ) →
    ∀ (f : X ⟶ B) (g : Y ⟶ B) (y : V ⟶ Y), IsFinite g → y ≫ g = j ≫ f →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ V), x ≫ j = x' ≫ j → x ≫ y = x' ≫ y) → ∃ y' : X ⟶ Y, j ≫ y' = y ∧ y' ≫ g = f

def LatB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (q : ℕ) (r : ℤ) (𝔴 𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (i : ℕ) (h : G.GAf),
    AtPrime D q r 𝔴 → IsTjElt L q r 𝔴 i h → Integ L h → 𝔟₁ ≤ 𝔟₂ * 𝔴 → (∃ e : ℕ, uId D q r ^ e ≤ 𝔟₁) →
    ∀ (M₁ M₂ : Lv p) (a₁ a₂ : 𝓞 D.F), IsGen a₁ M₁.1 𝔟₁ → IsGen a₂ M₂.1 𝔟₂ → ∀ y : D.La, ∃ x : D.La, ∃ v ∈ LaHat D,
      L.actG h (inAf D (M₂.1 • algebraMap (𝓞 D.F) D.O a₁ • x)) = inAf D (M₁.1 • algebraMap (𝓞 D.F) D.O a₂ • y) + (M₁.1 * M₂.1) • v

def EtaPtB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X) (x y : D.La),
    (∃ v ∈ LaHat D, L.actG h (inAf D (N.1 • x)) = inAf D (N'.1 • y) + (N'.1 * N.1) • v) →
    toUnit (Over.mk z) ≫ o'.eta x ≫ ψ = toUnit (Over.mk z) ≫ o.eta y

def BRead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    Nonempty (BPt C₁ C₂ W mf Tj)

def BKer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y

def BLev : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y →
      x ≫ W.π ≫ C₂.j = x' ≫ W.π ≫ C₂.j

end UpperTheory.Gal.FiniteEtaleModels
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

def Cg {M : Type} [AddCommGroup M] (n : ℕ) (x y : M) : Prop := ∃ z, x = y + n • z

def MOne : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 →
  Function.Bijective (algebraMap (𝓞 D.F) D.O) ∧ Module.Projective D.O D.La ∧ Module.Finite D.O D.La

def Idem : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∃ ε : ℕ → 𝓞 D.F, ∀ e : ℕ,
  1 - ε e ∈ ES.uIdeal D r ^ e ∧ D.bar (ε e) ∈ ES.uIdeal D r ^ e ∧ (∀ x ∈ ES.uIdeal D r ^ e, (q : 𝓞 D.F) ^ e ∣ ε e * x) ∧
  (q : 𝓞 D.F) ^ e ∣ ε e + D.bar (ε e) - 1 ∧ (q : 𝓞 D.F) ^ e ∣ ε (e + 1) - ε e ∧
  ∀ (𝔞 : Ideal (𝓞 D.F)), (∃ f : ℕ, ES.uIdeal D r ^ f ≤ 𝔞) → (q : 𝓞 D.F) ^ e ∈ 𝔞 → ES.uIdeal D r ^ e ≤ 𝔞

def LiftUnit : Prop := ∀ (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  (u 𝔞 : Ideal A), u ≠ ⊥ → (∃ f : ℕ, u ^ f ≤ 𝔞) → ∀ g₀ : (M ⧸ (𝔞 • ⊤ : Submodule A M)) ≃ₗ[A] (M ⧸ (𝔞 • ⊤ : Submodule A M)),
  ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, (𝔞 • ⊤ : Submodule A M).mkQ (g x) = g₀ ((𝔞 • ⊤ : Submodule A M).mkQ x)) ∧
    ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M)

def Adj : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (e : ℕ), (∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0) ∧
  (∀ h : D.La →ₗ[D.O] D.La, ∃ k : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (h x) y - D.EF x (k y)) ∧
    ∀ (c : D.O) y, Cg (q ^ e) (k (c • y)) (c • k y)) ∧
  ∀ g : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g x) (g y) - D.EF x y) →
    (∀ x, Cg (q ^ e) (g x) 0 → Cg (q ^ e) x 0) ∧ ∀ x, ∃ y, Cg (q ^ e) (g y) x

def QSys : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)),
  (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La, ∀ e : ℕ,
    (∀ (c : D.O) x, Cg (q ^ e) (g e (c • x)) (c • g e x)) ∧ (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g e x) (g e y) - D.EF x y) ∧
    (∀ x, Cg (q ^ e) (g (e + 1) x) (g e x)) ∧ ((q : 𝓞 D.F) ^ e ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g e x) = g₀ ((wSub D 𝔞 1).mkQ x))

structure IsSys {G : GDatum} (g : ℕ → G.La →+ G.La) : Prop where
  lin : ∀ n, 0 < n → ∀ (c : G.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  onto : ∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v
  iso : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ G.EF (g n x) (g n y) - G.EF x y
  tow : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z

def TResim : Prop := ∀ (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop)
  (I : GTateIso G k Q act e) (g : ℕ → G.La →+ G.La), IsSys g → ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g n x)

def OResim : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (N N₀ c : ℕ), N = N₀ * c → 0 < N → ∀ (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R) (o : GObj gb N s)
  (u : Obj b N₀ s₁) (f : X ⟶ X₁) (n : QMap o u f c) (g : ℕ → D.La →+ D.La), IsSys (G := D.toG) g → (∀ x, ∃ z, g N₀ x = x + N₀ • z) →
  ∃ (o' : GObj gb N s) (n' : QMap o' u f c), ∀ y : D.La, (o'.eta y).left ≫ n'.φ = (o.eta (g N y)).left ≫ n.φ

def TExt : Prop := ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G R) (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (σ : Sp Ω ⟶ Sp R) (o : GObj gb N σ)
  (I : GTateIso G Ω (Over.mk (𝟙 (Sp Ω)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
  (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp Ω),
  ∃ I' : GTateIso G k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ n, 0 < n → ∀ y, (I'.ev n y).left = x ≫ (I.ev n y).left

def Raise : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ), N = N₀ * c → 0 < N → N₀.Coprime q →
  ∀ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp R) (u : Obj b N₀ s₁) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ X₁) (σ : Sp Ω ⟶ Sp R'),
  y ≫ s₁ = σ ≫ spMap β → ∃ o : GObj gb N σ, Nonempty (QMap o u y c)

def ClsAt : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm →
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β →
  ∀ (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), N = N₀ * c → 0 < N → N₀.Coprime q → IsGen a N 𝔞 → (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) →
  ∀ (Y : EtModel b N₀ 𝔞 1) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Y.X) (σ : Sp Ω ⟶ Sp R'), y ≫ Y.s = σ ≫ spMap β →
  ∃ (o : GObj gb N σ) (C : Cls Y β o c a), C.j = y

def EpsEx : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔟₁ 𝔟₂ : Ideal A) (a₁ a₂ : A) (M₁ M₂ t : ℕ), 0 < M₁ →
  M₁ = M₂ * t → 𝔟₁ ≤ 𝔟₂ → IsGen a₁ M₁ 𝔟₁ → IsGen a₂ M₂ 𝔟₂ → ∃ ε : A, (M₁ : A) ∣ ε * a₁ - t * a₂ ∧ (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁

def LevDown : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R)
  (o : Obj b N s) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (ε : 𝓞 D.F), 𝔟₁ ≠ ⊥ → (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ → ∀ l : D.La → (𝟙_ (Over S) ⟶ o.A),
  IsEtLev o 𝔟₁ 1 l → IsEtLev o 𝔟₂ 1 fun y => l (algebraMap (𝓞 D.F) D.O ε • y)

def DownEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → D.a = 1 → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
  (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
  (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (ε : 𝓞 D.F), (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ →
  ∃ (t : X₁.Y.X ⟶ X₂.Y.X) (m : ObjMap (X₁.Y.univ.forget N₀ (Dvd.intro _ rfl) X₁.lev.2.1) X₂.Y.univ t), t ≫ X₂.Y.s = X₁.Y.s ∧ IsFinite t ∧ Etale t ∧
    ∀ y : D.La, (X₁.Y.lv (algebraMap (𝓞 D.F) D.O ε • y)).left ≫ m.φ = t ≫ (X₂.Y.lv y).left

end UpperTheory.Gal.FiniteEtaleModels.O
end
end
