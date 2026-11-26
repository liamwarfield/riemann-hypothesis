module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT

structure TorsTower (p : ℕ) {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] where

  Γ : ∀ n, QFGroup O (LevGrp La p n)

  i : ∀ n, (Γ n).G.left ⟶ G.left
  tors : ∀ n, (Γ n).IsTorsionAlong G y (p ^ n) (i n)
  compat : ∀ n (a : La), ((Γ n).pt (lev p n a)).left ≫ i n = ((Γ (n + 1)).pt (lev p (n + 1) (p • a))).left ≫ i (n + 1)

namespace TorsTower

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)

def IsDer {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ)
    (f : LevGrp La p n → O) (w : Module.Dual O L) : Prop :=
  ∃ s : Γ((X.Γ n).G.left, ⊤), (X.Γ n).HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))) ⟶ (X.Γ n).G.left,
      v ≫ (X.Γ n).G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (O ⧸ Ideal.span {((p ^ n : ℕ) : O)})
        (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ X.i n = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)}) (w e))

def Induces (u : G ⟶ G) (φ : La →+ La) : Prop :=
  ∀ n (a : La), ((X.Γ n).pt (lev p n (φ a))).left ≫ X.i n = ((X.Γ n).pt (lev p n a)).left ≫ X.i n ≫ u.left

def PairingRegular (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s : Γ(((X.Γ n).G ⊗ (X.Γ n).G).left, ⊤), ∀ a b : La,
    valAt (lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))).left ⊤ le_top s =
      algebraMap O (FractionRing O) ((ζ n ^ B a b : Oˣ) : O)

end TorsTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

def IsPointOf {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {κ : O} {N : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    {L : Type} [AddCommGroup L] [Module O L] (p : ℕ)
    (der : ∀ n, (LevGrp La p n → O) → Module.Dual O L → Prop) (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ)
    (ρL : 𝓞 E →+* Module.End O L) (u : Fin N → La)
    (P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L)) : Prop :=
  (∀ i, P.t i = 1 ⊗ₜ u i) ∧ (∀ (a : 𝓞 E) (x : La), P.ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧
  (∀ x y : La, P.e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧
  P.om = LinearMap.range (TensorProduct.mk O C (Module.Dual O L) 1) ∧
  (∀ (a : 𝓞 E) (w : Module.Dual O L),
    P.ρΩ a (1 ⊗ₜ w) = 1 ⊗ₜ (w ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a))) ∧
  ∀ (n : ℕ) (x : La) (f : LevGrp La p n → O) (w : Module.Dual O L),
    (∀ b, f (lev p n b) = ((ζ n ^ EF x b : Oˣ) : O)) → der n f w →
      ∃ y ∈ P.om, P.ht (1 ⊗ₜ x) = 1 ⊗ₜ w + (p ^ n) • y

def IsHTConst {C O : Type} [Field C] [CommRing O] [Algebra O C] (v : Valuation C NNReal) (p : ℕ) (κ : O) : Prop :=
  algebraMap O C κ ≠ 0 ∧ v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)

structure IsPolLattice {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La) : Prop where
  free : Module.Free ℤ La
  finite : Module.Finite ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (RingOfIntegers.mapRingEquiv c a • y)
  rank : Module.finrank ℤ La = N * Module.finrank ℚ E
  span : ∀ x : La, ∃ (a : Fin N → 𝓞 E) (x' : La), x = ∑ i, a i • u i + p • x'

def PointHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O →
    ∀ (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
      (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u →
    ∀ (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L)
      (act : 𝓞 E → (G ⟶ G)) (ρL : 𝓞 E →+* Module.End O L), (∀ a, IsMonHom (act a)) → M.IsActOf act ρL →
      (∀ a : 𝓞 E, X.Induces (act a) (DistribSMul.toAddMonoidHom La a)) →
      2 * Module.finrank O L = Module.finrank ℤ La →
    ∀ ζ : ℕ → Oˣ, (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingRegular EF ζ →
    ∀ κ : O, IsHTConst v p κ →
      ∃ P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L), IsPointOf p (X.IsDer M) EF ζ ρL u P

namespace PointTest

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {v : Valuation C NNReal} {p : ℕ}

theorem val_sub_one_pow [hp : Fact p.Prime] {ζ : C} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : C) := by
  have h1 : v ζ ≤ 1 := by
    have := congrArg v hζ.pow_eq_one
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hp.out.ne_zero).1 this).le
  let z : v.integer := ⟨ζ, h1⟩
  have hz : IsPrimitiveRoot z p := IsPrimitiveRoot.of_map_of_injective (f := v.integer.subtype) hζ Subtype.val_injective
  have key : ∀ k ∈ Finset.range (p - 1), v (1 - ζ ^ (k + 1)) = v (ζ - 1) := by
    intro k hk
    have hk' : k + 1 < p := by have := Finset.mem_range.1 hk; omega
    have hc : (k + 1).Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt k.succ_pos hk')).symm
    have ha := hz.associated_sub_one_pow_sub_one_of_coprime hc
    rw [Valuation.map_sub_swap]
    exact le_antisymm ((Valuation.integer.integers v).le_of_dvd ha.dvd)
      ((Valuation.integer.integers v).le_of_dvd ha.symm.dvd)
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  rw [Nat.add_sub_cancel] at key
  have := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod, Finset.prod_congr rfl key, Finset.prod_const, Finset.card_range] at this
  simpa using this

theorem isHTConst_sub_one [hp : Fact p.Prime] {ζ : O} (hζ : IsPrimitiveRoot (algebraMap O C ζ) p) :
    IsHTConst v p (ζ - 1) := by
  refine ⟨?_, ?_⟩ <;> rw [map_sub, map_one]
  · exact hζ.sub_one_ne_zero hp.out.one_lt
  · exact (val_sub_one_pow hζ).le

end PointTest

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

def TwistAut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : HostAut H), Nonempty (TwIso D g) ∧ ∀ a : TwIso D g, ∃ (h : TwOK Xo.univ g a) (Φ : Xo.X ≅ Xo.X),
      Φ.hom ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ.hom)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

def PropFTop : Prop :=
  PtsIntegrableStatement → MetricLocalStatement → DegreeStatement →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
      (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (rd Lval : ℝ),
      IsIntersectionSystem II → T.Conv II → T.Proportional → T.Prop6 II frob → 1 ≤ rd → (∀ p ∈ T.bad, p.Prime) →
      (∀ c τ, ∃ R : RootFlat (T.M 2 c) τ, NearRecord N T.bad rd Lval R.ht) → T.PropF II 4 rd Lval

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
