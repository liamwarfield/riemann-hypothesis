module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def N1ab : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H),
    1 ≤ D.p + D.q → Nonempty (Moduli D l)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def Datum.ModN (D : Datum H) (n : ℕ) (x : D.La) : Prop := ∃ b, x = n • b

structure Sim (D : Datum H) where
  f : ℕ → D.La →ₗ[𝓞 E] D.La
  ν : ℕ → ℤ
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, D.ModN n (f (n * m) a - f n a)
  inv : ∀ n, 0 < n → ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f n a) - a) ∧ D.ModN n (f n (g a) - a)
  mult : ∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ D.EF (f n a) (f n b) - ν n * D.EF a b

def Sim.InGam (g : Sim D) (l l₂ : Level H) : Prop :=
  (l₂.A : ℤ) ∣ g.ν l₂.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
    ∀ a, D.ModN l.A (g.f l.A a - a)

def Sim.TrivAt (g : Sim D) (l₂ : Level H) : Prop :=
  (∀ a, g.f l₂.M a - a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ ∀ a, D.ModN l₂.A (g.f l₂.A a - a)

def Moduli.LevAut {l : Level H} (Xo : Moduli D l) (g : Sim D) (ρ : Xo.X ≅ Xo.X) : Prop :=
  ρ.hom ≫ Xo.s = Xo.s ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t ρ.hom,
    (∀ a, (Xo.univ.eta (g.f l.M a)).left ≫ ν.φ = ρ.hom ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l.A a)).left ≫ ν.φ = ρ.hom ≫ (Xo.univ.etaA a).left

def ToroidalLevelCompatibility : Prop :=
  ∀ (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), l.Dvd l₂ →
    ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r),
      (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧
      (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
      (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) ∧
      (∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) ∧
      ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F), ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
        rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
        rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧
        IsFinite rF ∧ Etale rF ∧ Surjective rF ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF →
          (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧
            y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧
          ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ →
            y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂

variable {S : Scheme.{0}}

def SAB.tors (t : SAB H S) (T : Over S) (I : Ideal (𝓞 E)) : Set (T ⟶ t.G) :=
  {x | ∀ a ∈ I, x ≫ t.act.act a = 1}

def SAB.HeckeKer (t : SAB H S) (T : Over S) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (C : Subgroup (T ⟶ t.G)) :
    Prop :=
  (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) ∧
  (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → t.tors T J ⊆ C) ∧
  (C : Set (T ⟶ t.G)) ⊆ t.tors T (Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E)) ∧
  (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1) ∧
  Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ∧
  Nat.card (t.tors T (Ideal.span {(p : 𝓞 E)})) =
    Nat.card ((C : Set (T ⟶ t.G)) ∩ t.tors T (Ideal.span {(p : 𝓞 E)}) : Set (T ⟶ t.G)) * Ideal.absNorm 𝔓 ^ i

def fibPt {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} (x : Over.mk y ⟶ G) :
    Sp k ⟶ pullback G.hom y :=
  pullback.lift x.left (𝟙 _) (by simp [Over.w x])

def ToroidalHeckeCompatibility : Prop :=
  ∀ (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 𝔓.IsMaximal →
    𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → ¬ p ∣ l.M' →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)),
      Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C →
      ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧
        ∃ (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
          (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)),
          ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
          (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
          Function.Surjective ψp ∧ ψp.ker = C ∧
          (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (c : kˣ), n.Coprime p →
            Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c) →
            Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
          ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
            ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
            ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a

def N1 : Prop :=
  N1ab ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

abbrev lbPow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

def hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

namespace HolUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def IsFnPow (n : ℕ) (s : (lbPow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n

def IsThetaFn (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : u.Λ) z, θ (z + l) =
    (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ n * θ z

end HolUnif

def ThetaUnifAV : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧
      (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
      (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
        Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

section Siegel

variable {S : Scheme.{0}}

def omegaStd {h : ℕ} (a b : Fin h ⊕ Fin h → ℤ) : ℤ := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))

structure SiegPre (h M₁ : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)
  lev_add : ∀ a b, lev (a + b) = lev a * lev b
  lev_tors : ∀ a, lev a ^ M₁ = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ s = spMap β → (z : k) = β ζ →
    (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M₁ • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M₁ = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M₁ (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

attribute [instance] SiegPre.grp SiegPre.comm

variable {h M₁ : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {s : S ⟶ Sp B}

def SiegPre.diag (o : SiegPre h M₁ ζ s) : LB o.A.left := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left

def SiegPre.Principal (o : SiegPre h M₁ ζ s) : Prop :=
  Out.RelAmple o.A o.diag ∧
    ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x = 1

def IsSquare {S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left)
    (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left) : Prop :=
  φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ ∧ φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ

def SiegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} (o' : SiegPre h M₁ ζ' s') (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) : Prop :=
  ∃ (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φ ∧ IsSquare φ φ₂ ∧ LBIso o'.P (o.P.pull φ₂) ∧
      ∀ a, (o'.lev a).left ≫ φ = f ≫ (o.lev a).left

def ZP (p M : ℕ) : Subring ℂ := Subring.closure ({zeta M} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})

def zetaZP (p M : ℕ) : ZP p M := ⟨zeta M, Subring.subset_closure (Or.inl rfl)⟩

def IsUnitBall (O C : Type) [CommRing O] [NormedField C] [Algebra O C] : Prop :=
  Function.Injective (algebraMap O C) ∧ ∀ x : C, x ∈ Set.range (algebraMap O C) ↔ ‖x‖ ≤ 1

structure SiegelFamily (h p M₁ : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (ZP p M₁)
  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s
  qc : QuasiCompact s
  univ : SiegPre h M₁ (zetaZP p M₁) s
  princ : univ.Principal

  points : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ‖(p : C)‖ < 1 →
    ∀ (β : ZP p M₁ →+* O) (o : SiegPre h M₁ (zetaZP p M₁) (spMap β)),
      (∃ o' : SiegPre h M₁ (zetaZP p M₁) (spMap (algebraMap O C) ≫ spMap β),
        SiegPB o' o (spMap (algebraMap O C)) ∧ o'.Principal) →
      Out.RelAmple (Over.mk (pullback.snd o.A.hom (spMap (IsLocalRing.residue O))))
        (o.diag.pull (pullback.fst o.A.hom (spMap (IsLocalRing.residue O)))) →
      ∃ x : Sp O ⟶ X, x ≫ s = spMap β ∧ SiegPB o univ x

  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : SiegPre h M₁ (zetaZP p M₁) (x ≫ s)),
    SiegPB o univ x → SiegPB o univ (constPt x) → x = constPt x

def N0 : Prop :=
  ∀ h p n : ℕ, 1 ≤ h → p.Prime → n.Prime → Odd n → n ≠ p →
    ∃ j : ℕ, 3 ≤ n ^ j ∧ Nonempty (SiegelFamily h p (n ^ j))

end Siegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

structure Idx (H : Host E) (p : ℕ) where
  l : Level H
  c : Coeff l
  good : l.GoodAt p

abbrev Coeff.V {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) : ValuationSubring c.F :=
  W.comap c.F.val.toRingHom

abbrev LocalSystem (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) :=
  ∀ i : Idx H p, Model (Xo i.l) i.c (i.c.V W).subtype

section Local

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Model.GoodRedExt (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (b : O →+* V) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j ≫ Y.s = spMap (algebraMap V K) ≫ spMap b →
    (∃ (𝒜 : Over (Sp V)) (_ : GrpObj 𝒜) (𝓛 : LB 𝒜.left) (A : Over (Sp K)) (_ : GrpObj A)
      (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ Y.oF.t.G.left),
      IsAbelianScheme 𝒜 ∧ 𝓛.IsLB ∧ Out.RelAmple 𝒜 𝓛 ∧ IsGrpPullback A 𝒜 (spMap (algebraMap V K)) φ₁ ∧
      IsGrpPullback A Y.oF.t.G y φ₂ ∧ LBIso (𝓛.pull φ₁) (Y.oF.t.PP.L.pull φ₂)) →
    ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y ≫ Y.j ∧
      Set.range y' ⊆ abLocus Y.t.G

def Model.LevelStructureConditions (Y : Model Xo c β) (p : ℕ) : Prop :=
  Y.LevelActs ∧ (l.A = 1 → Y.Descends) ∧ PushInvertible Y.t.G Y.t.PP.L ∧
  (∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (a : D.La) (n : ℕ), n.Coprime p →
    (Y.oF.eta a ^ n = 1 → Y.Extends U (Y.oF.eta a)) ∧ (Y.oF.etaA a ^ n = 1 → Y.Extends U (Y.oF.etaA a))) ∧
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K) ∧
  ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 → Y.GoodRedExt V C

def SiegelCompare {l₁ : Level H} {Xo₁ : Moduli D l₁} {c₁ : Coeff l₁} {O₁ : Type} [CommRing O₁] {β₁ : O₁ →+* c₁.F}
    (Y : Model Xo c β) (Y₁ : Model Xo₁ c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) {g p M₁ : ℕ}
    (Ag : SiegelFamily g p M₁) (z : ZP p M₁ →+* O₁) : Prop :=
  ∀ (U : Y.X.Opens) (U₁ : Y₁.X.Opens), (U : Set Y.X) = abLocus Y.t.G → (U₁ : Set Y₁.X) = abLocus Y₁.t.G →
    (∃ e : U₁.toScheme ⟶ pullback (U.ι ≫ Y.s) (spMap b),
      e ≫ pullback.fst _ _ ≫ U.ι = U₁.ι ≫ π ∧ e ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧
      IsFinite e ∧ Etale e ∧ Surjective e) ∧
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : U₁.toScheme ⟶ pullback Ag.s (spMap z))
      (o : SiegPre g M₁ (zetaZP p M₁) (U₁.ι ≫ Y₁.s ≫ spMap z)) (φ : o.A.left ⟶ Y₁.t.G.left)
      (φ₂ : (G2 o.A).left ⟶ (G2 Y₁.t.G).left),
      (∀ u v, D.EF (bas u) (bas v) = omegaStd u v) ∧
      IsGrpPullback o.A Y₁.t.G U₁.ι φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ Y₁.t.G Y₁.t.PP.L).pull φ₂) ∧
      (∀ u (j' : Xo₁.XF c₁ ⟶ U₁.toScheme), j' ≫ U₁.ι = Y₁.j →
        j' ≫ (o.lev u).left ≫ φ = (Y₁.oF.etaA (bas u) ^ (l₁.A / M₁)).left ≫ Y₁.m.φ) ∧
      cl ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧ IsFinite cl ∧
      (¬ p ∣ l.M' →
        ∃ (XX : Scheme.{0}) (u : U₁.toScheme ⟶ XX) (w : XX ⟶ pullback Ag.s (spMap z)) (W : XX.Opens)
          (t : SAB H XX) (t₁ : SAB H U₁.toScheme) (m₁ : SABMap t₁ Y₁.t U₁.ι) (m₂ : SABMap t₁ t u)
          (η' ηA' : D.La → (𝟙_ (Over XX) ⟶ t.G)),
          u ≫ w = cl ∧ IsFinite u ∧ Surjective u ∧ Dense (W : Set XX) ∧ IsIso (u ∣_ W) ∧
          Dense ((u ⁻¹ᵁ W : U₁.toScheme.Opens) : Set U₁.toScheme) ∧
          IsAbelianScheme t.G ∧ IsReduced XX ∧ Flat (w ≫ pullback.snd _ _) ∧ IsFinite w ∧ FormallyUnramified w ∧
          ∀ (a : D.La) (j' : Xo₁.XF c₁ ⟶ U₁.toScheme) (g₁ : Xo₁.XF c₁ ⟶ t₁.G.left), j' ≫ U₁.ι = Y₁.j →
            (g₁ ≫ m₁.φ = (Y₁.oF.eta a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (η' a).left) ∧
            (g₁ ≫ m₁.φ = (Y₁.oF.etaA a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (ηA' a).left))

end Local

def IsIncl {l l₂ : Level H} {c : Coeff l} {c₂ : Coeff l₂} {W : ValuationSubring ℂ} (b : c.V W →+* c₂.V W) : Prop :=
  ∀ x : c.V W, (((b x : c₂.V W) : c₂.F) : ℂ) = ((x : c.F) : ℂ)

def N2 {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) : Prop :=
  (∀ i, (Y i).LevelStructureConditions p) ∧
  ∃ π : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F → ((Y i₂).X ⟶ (Y i).X),
    (∀ i i₂ hl hc (b : i.c.V W →+* i₂.c.V W), IsIncl b → IsTransition (Y i) (Y i₂) b (π i i₂ hl hc)) ∧
    ∃ (n j : ℕ) (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p (n ^ j)),
      n.Prime ∧ Odd n ∧ n ≠ p ∧ 3 ≤ n ^ j ∧ (∀ l : Level H, n.Coprime l.M) ∧
      ∀ i i₁ hl hc (b : i.c.V W →+* i₁.c.V W) (z : ZP p (n ^ j) →+* i₁.c.V W), IsIncl b →
        (∀ x, (((z x : i₁.c.V W) : i₁.c.F) : ℂ) = (x : ℂ)) →
        i₁.l.M = i.l.M → i₁.l.Mb = i.l.Mb → i₁.l.A = Nat.lcm i.l.A (n ^ j) →
        i₁.c.F = i.c.F ⊔ IntermediateField.adjoin ℚ {zeta (n ^ j)} →
        SiegelCompare (Y i) (Y i₁) b (π i i₁ hl hc) Ag z

def N6 {Xo : ∀ l : Level H, Moduli D l}
    (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W) : Prop :=
  ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p), l.A = 1 →
    ∃ Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), Ygl.Descends ∧
      ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
        (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
set_option linter.dupNamespace false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField IsLocalRing MvPolynomial
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Tan

variable {V : Type} [CommRing V]

abbrev ptOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap (algebraMap V R))

abbrev epsOver (V R : Type) [CommRing V] [CommRing R] [Algebra V R] : Over (Sp V) :=
  Over.mk (spMap ((algebraMap R (DualNumber R)).comp (algebraMap V R)))

def epsMul {R : Type} [CommRing R] (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

variable {R : Type} [CommRing R] [Algebra V R] {G : Over (Sp V)} [GrpObj G]

def IsTan (v : epsOver V R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : ptOver V R ⟶ G).left

def IsComb {m : ℕ} (v : Fin m → (epsOver V R ⟶ G)) (c : Fin m → R) (w : epsOver V R ⟶ G) : Prop :=
  ∃ u : Fin m → (epsOver V R ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

end Tan

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure ValPt (Y : Model Xo c β) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  K' : Type
  [fld : Field K']
  [alg : Algebra V K']
  [frac : IsFractionRing V K']
  complete : IsAdicComplete (maximalIdeal V) V
  char0 : CharZero K'
  oV : O →+* V
  fK : c.F →+* K'
  compat : (algebraMap V K').comp oV = fK.comp β
  y : Sp K' ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = spMap fK
  yt : Sp V ⟶ Y.X
  yt_over : yt ≫ Y.s = spMap oV
  ext : spMap (algebraMap V K') ≫ yt = y ≫ Y.j
  G : SAB H (Sp V)
  pull : SABMap G Y.t yt

attribute [instance] ValPt.ring ValPt.dom ValPt.dvr ValPt.fld ValPt.alg ValPt.frac

variable {Y : Model Xo c β}

def ValPt.emb (P : ValPt Y) (τ : E →+* ℂ) (a : 𝓞 E) : P.K' := P.fK ⟨τ (a : E), c.conj τ a⟩

def ValPt.IsEig (P : ValPt Y) {R : Type} [CommRing R] [Algebra P.V R] (τ : E →+* ℂ)
    (v : epsOver P.V R ⟶ P.G.G) : Prop :=
  ∀ (a : 𝓞 E) (z : P.V), algebraMap P.V P.K' z = P.emb τ a →
    (v ≫ P.G.act.act a).left = spMap (epsMul (algebraMap P.V R z)) ≫ v.left

def Datum.mult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def conjEmb (τ : E →+* ℂ) : E →+* ℂ := (starRingEnd ℂ).comp τ

structure FlagBasis (P : ValPt Y) where
  u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (epsOver P.V P.V ⟶ P.G.G)
  tan : ∀ τ i, IsTan (u τ i)
  eig : ∀ τ i, P.IsEig τ (u τ i)
  basis : ∀ τ (w : epsOver P.V P.V ⟶ P.G.G), IsTan w → P.IsEig τ w → ∃! a : Fin (D.mult τ) → P.V, IsComb (u τ) a w

section Letters

variable (D) (n : ℕ)

def Letter : Type := {x : (E →+* ℂ) × ℕ × Fin n // x.2.1 < D.mult x.1}

variable {D n}

def Letter.row (x : Letter D n) : (E →+* ℂ) × ℕ := (x.1.1, x.1.2.1)

def letter (τ : E →+* ℂ) (i : ℕ) (b : Fin n) (h : i < D.mult τ) : Letter D n := ⟨(τ, i, b), h⟩

def harmOp (τ : E →+* ℂ) (i i' : ℕ) (hi : i < D.mult τ) (hi' : i' < D.mult (conjEmb τ)) :
    MvPolynomial (Letter D n) ℤ →ₗ[ℤ] MvPolynomial (Letter D n) ℤ :=
  ∑ b : Fin n, (pderiv (letter τ i b hi)).toLinearMap ∘ₗ (pderiv (letter (conjEmb τ) i' b hi')).toLinearMap

def rowWt (r : (E →+* ℂ) × ℕ) (x : Letter D n) : ℕ := if x.row = r then 1 else 0

def rowAdd (τ : E →+* ℂ) (j i : ℕ) (hji : j < i) (t : ℤ) :
    MvPolynomial (Letter D n) ℤ →ₐ[ℤ] MvPolynomial (Letter D n) ℤ :=
  bind₁ fun x => if h : x.1.1 = τ ∧ x.1.2.1 = i then
      X x + C t * X (letter τ j x.1.2.2 (by have h3 := x.2; rw [h.1, h.2] at h3; omega))
    else X x

def FF (a : (E →+* ℂ) × ℕ → ℕ) : Submodule ℤ (MvPolynomial (Letter D n) ℤ) :=
  (⨅ (τ : E →+* ℂ) (_ : τ (H.rt : E) = H.rt0) (i : ℕ) (i' : ℕ) (hi : i < D.mult τ) (hi' : i' < D.mult (conjEmb τ)),
      LinearMap.ker (harmOp τ i i' hi hi')) ⊓
    (⨅ r : (E →+* ℂ) × ℕ, weightedHomogeneousSubmodule ℤ (rowWt r) (a r)) ⊓
    ⨅ (τ : E →+* ℂ) (j : ℕ) (i : ℕ) (h : j < i) (t : ℤ),
      LinearMap.ker ((rowAdd τ j i h t).toLinearMap - LinearMap.id)

end Letters

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

abbrev JetR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)

abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R A))

def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (spMap (ψ : A →+* B)) (by
    dsimp
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

def jetTruncR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

def jetZeroR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

abbrev zR {R : Type} [CommRing R] {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨PUnit.unit, LinearMap.ext fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (map_zero f).symm⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => by simp, fun x hx => absurd (Subsingleton.elim x 0) hx,
    fun a A t _ ht => by
      have hA : A = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
      subst hA
      simp [ht]⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
end
end
