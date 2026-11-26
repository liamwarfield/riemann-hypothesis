module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPar
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPol
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatTest
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenom

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FreeOfFg
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem free_of_fg {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (L : Submodule O Ω) (hL : L.FG) : Module.Free O L := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have hx0 : (a : O) • (x : Ω) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O) (x : Ω), smul_eq_zero] at hx0
    rcases hx0 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero a)
    · exact (Submodule.mem_bot O).mpr (Subtype.ext (by simpa using h))
  exact Module.free_of_flat_of_isLocalRing

end PositivityTheory.HtPt.Gd
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenomBis
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint.Par

def zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    rw [div_add_div _ _ hb0 hb0']
    push_cast
    ring
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩

theorem mem_range_zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zp Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_adjoin_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin o T) : w ∈ Algebra.adjoin o' T := by
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem mem_adjoin_of_int (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin ℤ T) : w ∈ Algebra.adjoin o T :=
  mem_adjoin_of_range_le (o := ℤ) (o' := o) (fun n => ⟨(n : o), by simp⟩) T hw

theorem isUnit_natCast {A O : Type} [CommRing A] [CommRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := _root_.PositivityTheory.Xgn.PackingFacts.isUnit_natCast (A := A) (O := O) m p hpm b hb

theorem exists_denom {o A O Ω : Type} [CommRing o] [CommRing A] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra A Ω]
    [Algebra A O] [Algebra O Ω] [IsScalarTower A O Ω] (M : Submonoid A) [IsLocalization M O] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) {w : Ω} (hw : w ∈ Algebra.adjoin O T) :
    ∃ s : M, w * algebraMap A Ω s ∈ Algebra.adjoin o T := _root_.PositivityTheory.Xgn.PackingFacts.exists_denom (o := o) (A := A) (O := O) (Ω := Ω) (w := w) M T hA hw

theorem isIntegrallyClosed_of_denom {o O Ω : Type} [CommRing o] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra O Ω]
    (B : Subalgebra o Ω) (B' : Subalgebra O Ω) [IsIntegrallyClosed B] (hle : ∀ w ∈ B, w ∈ B')
    (hden : ∀ w ∈ B', ∃ s ∈ B, (∃ t ∈ B', s * t = 1) ∧ w * s ∈ B) : IsIntegrallyClosed B' := _root_.PositivityTheory.Xgn.PackingFacts.isIntegrallyClosed_of_denom (o := o) (O := O) (Ω := Ω) B B' hle hden

theorem chart_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ c' hc'
  haveI hch : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, -, -, -, hchart⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (zp Ω p) (mem_range_zp Ω p)
  obtain ⟨-, hic, hfr, -⟩ := hchart c' hc'
  obtain ⟨-, -, -, hconst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  have eO := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := O) y c' hc'
  have eo := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := zp Ω p) y c' hc'
  have eZ := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := ℤ) y c' hc'
  have hr : ∀ a : zp Ω p, algebraMap (zp Ω p) Ω a ∈ (algebraMap O Ω).range := by
    intro a
    obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zp Ω p _).1 ⟨a, rfl⟩
    have hu := isUnit_natCast (O := O) m p hpm b hb
    refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
    rw [hab, map_mul, map_intCast, div_eq_mul_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
  have hle : ∀ w ∈ chartRing (zp Ω p) (mseg y) c', w ∈ CR O y c' := by
    intro w hw
    exact eO.ge (mem_adjoin_of_range_le hr _ (eo.le hw))
  have hA : ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin (zp Ω p) (Set.range fun j => mseg y j / mseg y c') := by
    intro a
    have h1 : algebraMap A Ω a ∈ chartRing ℤ (mseg y) c' := hconst c' hc' a
    rw [eZ] at h1
    exact mem_adjoin_of_int _ _ h1
  refine ⟨hch, ?_, ?_, ?_⟩
  · haveI : Algebra.FiniteType O (CR O y c') := by
      refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => mseg y j / mseg y c').toFinset, ?_⟩
      rw [Set.Finite.coe_toFinset]
      exact eO.symm
    exact Algebra.FiniteType.isNoetherianRing O _
  · refine isIntegrallyClosed_of_denom (chartRing (zp Ω p) (mseg y) c') (CR O y c') hle fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_denom m.primeCompl _ hA (eO.le hw)
    have hu := IsLocalization.map_units O s
    refine ⟨algebraMap A Ω s, eo.ge (hA _), ⟨algebraMap O Ω ↑hu.unit⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩, eo.ge hs⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu.mul_val_inv, map_one]
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, h, -, e⟩ := IsFractionRing.div_surjective (A := chartRing (zp Ω p) (mseg y) c') a
    exact ⟨⟨g, hle _ g.2⟩, ⟨h, hle _ h.2⟩, e.symm⟩

open GlobalTheory.CompanionTheory.Ar.HT

section Scale

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]

noncomputable def scalePt (P : HTPoint C O c κ N V Ω) (a : Oˣ) : HTPoint C O c κ N V Ω :=
  have ha : algebraMap O C (a : O) ≠ 0 := (a.isUnit.map (algebraMap O C)).ne_zero
  { P with
    e := algebraMap O C (a : O) • P.e
    alt := fun x => by simp [P.alt]
    nondeg := fun y hy => P.nondeg y fun x => by simpa [ha] using hy x
    perfect := by
      refine Eq.trans ?_ P.perfect
      ext y
      simp only [LatBasic.mem_dualLat, LinearMap.smul_apply, smul_eq_mul]
      refine forall₂_congr fun x _ => ⟨fun h => ?_, fun h => Subring.mul_mem _ ⟨_, rfl⟩ h⟩
      have := Subring.mul_mem _ (⟨((a⁻¹ : Oˣ) : O), rfl⟩ : _ ∈ (algebraMap O C).range) h
      rwa [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul] at this
    adj := fun b x y => by simp [P.adj]
    lagr := fun x => by
      rw [P.lagr]
      simp [ha] }

end Scale

theorem isUnit_of_coprime {C O : Type} [Field C] [CommRing O] [Algebra O C] {v : Valuation C NNReal}
    (hv : v.Integers O) {p a : ℕ} (hp : v (algebraMap O C (p : O)) < 1) (h : a.Coprime p) : IsUnit (a : O) := by
  rw [hv.isUnit_iff_valuation_eq_one]
  by_contra hne
  have h1 : v (algebraMap O C (a : O)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
  obtain ⟨r, s, hrs⟩ := Nat.Coprime.cast (R := O) h
  have h2 : v (algebraMap O C (r * a + s * p)) < 1 := by
    rw [map_add (f := _), map_mul, map_mul]
    refine Valuation.map_add_lt v ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le h1
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le hp
  rw [hrs, map_one, map_one] at h2
  exact lt_irrefl _ h2

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]

def withE (D : HTChart A K c p R N Ω) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R))
    (alt : ∀ x, e x x = 0)
    (adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y))
    (hs : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) (hi : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') :
    HTChart A K c p R N Ω :=
  { D with e := e, alt := alt, adj := adj, e_surj := hs, e_inj := hi }

end Chart

noncomputable def relabel {R : Type} [CommRing R] [IsDomain R] {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T)
    (b : T' ≃* T) : QFGroup R T' :=
  { Γ with
    pt := Γ.pt.comp b.toMonoidHom
    pt_inj := fun s t x y h => b.injective (Γ.pt_inj _ _ x y h)
    pt_onto := fun g hg => by
      obtain ⟨t, x, h⟩ := Γ.pt_onto g hg
      obtain ⟨s, rfl⟩ := b.surjective t
      exact ⟨s, x, h⟩ }

theorem exists_mulEquiv {A B C : Type} [Group A] [Group B] [Group C] (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (h : ∀ a, f a = 1 ↔ g a = 1) :
    ∃ b : B ≃* C, ∀ a, b (f a) = g a := by
  have hk : f.ker = g.ker := Subgroup.ext h
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun a => ?_⟩
  have : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) = (a : A ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  rw [MulEquiv.trans_apply, this]
  rfl

theorem pow_val_mul {G : Type} [Monoid G] (g : G) (n : ℕ) [NeZero n] (hg : g ^ n = 1) (a : ℕ) (e : ZMod n) :
    g ^ ((a : ZMod n) * e).val = (g ^ a) ^ e.val := by
  have h0 : ((a : ZMod n) * e).val = (a * e.val) % n := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h0, ← pow_mul, ← pow_eq_pow_mod _ hg]

theorem pow_val_intCast {G : Type} [Group G] (g : G) (N : ℕ) [NeZero N] (hg : g ^ N = 1) (j : ℤ) :
    g ^ (j : ZMod N).val = g ^ j := by
  have h : (((j : ZMod N).val : ℕ) : ℤ) = j % N := ZMod.val_intCast j
  rw [← zpow_natCast, h, ← zpow_eq_zpow_emod' j hg]

theorem cp_descend {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (p : ℕ) (κ : A) (h : IsCp p (algebraMap A Ω κ)) :
    if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1 := by
  unfold IsCp at h
  split_ifs at h ⊢
  · exact hinj (by rw [h, map_ofNat])
  · obtain ⟨ζ, h1, h2⟩ := h
    refine ⟨κ + 1, IsPrimitiveRoot.of_map_of_injective (f := algebraMap A Ω) ?_ hinj, by ring⟩
    rwa [map_add, map_one, h2, sub_add_cancel]

theorem qhom_surj {E : Type} [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := by
  intro t
  choose z hz using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  exact ⟨Multiplicative.ofAdd z, congrArg Multiplicative.ofAdd (funext hz)⟩

theorem qhom_eq_one {E : Type} [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have : qhom N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (y i) = 0 :=
    ⟨fun h i => congrFun (congrArg Multiplicative.toAdd h) i, fun h => congrArg Multiplicative.ofAdd (funext h)⟩
  rw [this]
  simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · intro h
    choose y' hy' using h
    exact ⟨y', funext fun i => by rw [hy' i]; simp⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp⟩


open PositivityTheory.HtPt.Htat in
theorem exists_coords {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {S : Scheme.{0}}
    (t : SAB H S) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ S) (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ (p ^ m) ev ζ₀)
    (pt : TorsT E (D.p + D.q) (p ^ m) →* (Over.mk ξ ⟶ t.G))
    (onto : ∀ g : Over.mk ξ ⟶ t.G, g ^ (p ^ m) = 1 ↔ ∃ s, pt s = g)
    (lin : ∀ (a : 𝓞 E) (x : Fin (D.p + D.q) → 𝓞 E), pt (qmk _ (a • x)) = pt (qmk _ x) ≫ t.act.act a) :
    ∃ u : Fin (D.p + D.q) → D.La, IsPolLattice (cmConj E) p D.EF u ∧
      ∀ z : Fin (D.p + D.q) → 𝓞 E, ev (∑ k, z k • u k) = pt (qmk _ z) := by
  classical
  have hu : ∀ k, ∃ a, ev a = pt (qmk _ (Pi.single k 1)) := fun k => (hev.onto _).1 ((onto _).2 ⟨_, rfl⟩)
  choose u hu using hu
  have ev0 : ev 0 = 1 := (hev.ker 0).2 ⟨0, by simp⟩
  have hadd : ∀ x y : Fin (D.p + D.q) → 𝓞 E, pt (qmk _ (x + y)) = pt (qmk _ x) * pt (qmk _ y) := fun x y =>
    (pt.comp (qhom _ _)).map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
  have hz : ∀ z : Fin (D.p + D.q) → 𝓞 E, ev (∑ k, z k • u k) = pt (qmk _ z) := by
    intro z
    have : ∀ s : Finset (Fin (D.p + D.q)),
        ev (∑ k ∈ s, z k • u k) = pt (qmk _ (∑ k ∈ s, z k • (Pi.single k 1 : Fin (D.p + D.q) → 𝓞 E))) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, ev0]
        exact (pt.comp (qhom _ _)).map_one.symm
      | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hev.add, hadd, ih, hev.lin, hu, lin]
    rw [this, ← pi_eq_sum_univ' z]
  obtain ⟨u', hu'⟩ := pol_lattice E H D p
  refine ⟨u, ⟨hu'.free, hu'.finite, hu'.alt, hu'.unimod, hu'.adj, hu'.rank, fun x => ?_⟩, hz⟩
  obtain ⟨s, hs⟩ := (onto (ev x)).1 ((hev.onto _).2 ⟨x, rfl⟩)
  obtain ⟨z, rfl⟩ := qhom_surj _ _ s
  have h1 : ev (∑ k, z.toAdd k • u k) = ev x := (hz _).trans hs
  have h2 : ev (x - ∑ k, z.toAdd k • u k) = 1 := by
    have := hev.add (x - ∑ k, z.toAdd k • u k) (∑ k, z.toAdd k • u k)
    rw [sub_add_cancel, h1] at this
    exact (mul_eq_right.1 this.symm)
  obtain ⟨b, hb⟩ := (hev.ker _).1 h2
  refine ⟨z.toAdd, p ^ (m - 1) • b, ?_⟩
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hm, ← hb, add_sub_cancel]

theorem spMap_cancel {F Ω k : Type} [Field F] [Field Ω] [Field k] (κ : F ≃+* Ω) (f : F →+* k) {Z : Scheme.{0}}
    (g : Sp F ⟶ Z) : spMap (f.comp κ.symm.toRingHom) ≫ spMap κ.toRingHom ≫ g = spMap f ≫ g := by
  rw [← Category.assoc, ← Tor.spMap_comp]
  congr 2
  ext a
  simp

end PositivityTheory.Xgn.TestGroupPoint.Par
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ChartMatrices
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

section Pt

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem pt_swap (P : HTPoint C O c κ N V Ω') (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

theorem pt_tate (P : HTPoint C O c κ N V Ω') (m : Ix E N) :
    P.tate (dl m) = P.ρ (RingOfIntegers.basis E m.2) (P.t m.1) :=
  PositivityTheory.HtPt.Gd.tate_single P m.1 _

theorem pt_matrices {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω') {g : ℕ}
    (bo : Basis (Fin g) O P.om) :
    ∃ (Hm : Matrix (Fin g) (Ix E N) O) (Eg : Matrix (Ix E N) (Ix E N) O),
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', algebraMap O C (Eg m m') = P.e (P.tate (dl m)) (P.tate (dl m'))) ∧
      ∀ m, ∃ h : P.ht (P.tate (dl m)) ∈ P.om, ∀ k, Hm k m = bo.repr ⟨_, h⟩ k := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gb.isFractionRing_of_integers hv
  haveI : P.om.IsFullLattice C := P.om_lat
  have hinj := hv.hom_inj
  have hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Ix E N =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
    rw [← Submodule.span_span_of_tower O C, ← P.free.2.2, P.free.2.1]
  let B : Basis (Ix E N) C V := Basis.mk P.free.1 hsp
  have hBt : ∀ m, P.tate (dl m) = B m := fun m => by rw [pt_tate, Basis.mk_apply]
  have hT : P.T = Submodule.span O (Set.range B) := by rw [Basis.coe_mk, ← P.free.2.2]
  have hB : ∀ q, B q ∈ P.T := fun q => by
    rw [hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  haveI : FiniteDimensional C V := Module.Finite.of_basis B
  have hnd : ∀ x, (∀ y, P.e x y = 0) → x = 0 := fun x hx =>
    P.nondeg x fun y => by rw [pt_swap, hx, neg_zero]
  have hei : Function.Injective (P.e : V →ₗ[C] Module.Dual C V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact hnd x fun y => by rw [hx]; rfl
  have hes := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hei
  have hE : ∀ m m', ∃ r : O, algebraMap O C r = P.e (B m) (B m') := fun m m' => by
    have := hB m'
    rw [← P.perfect] at this
    exact this _ (hB m)
  choose Eg hEg using hE
  choose w hw using fun m => hes (B.coord m)
  have hwT : ∀ m, w m ∈ P.T := fun m => by
    rw [← P.perfect]
    intro x hx
    rw [pt_swap, hw]
    refine neg_mem ?_
    rw [hT] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨a m, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul_of_tower, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
    simp [Algebra.smul_def]
  choose Ei hEi using fun m => (Submodule.mem_span_range_iff_exists_fun O).1 (hT ▸ hwT m)
  let bC := bo.extendOfIsFullLattice C
  have hbC_apply (j : Fin g) : bC j = (bo j : Ω') :=
    Basis.extendOfIsFullLattice_apply C bo j
  have hbC : ∀ (y : P.om) k, bC.repr (y : Ω') k = algebraMap O C (bo.repr y k) := fun y k => by
    have e : (y : Ω') = ∑ j, algebraMap O C (bo.repr y j) • bC j := by
      calc
        (y : Ω') = ((∑ j, bo.repr y j • bo j : P.om) : Ω') :=
          congrArg Subtype.val (bo.sum_repr y).symm
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul, hbC_apply]
    rw [e, bC.repr_sum_self]
  let Hm : Matrix (Fin g) (Ix E N) O := fun k m => bo.repr ⟨P.ht (B m), P.ht_mem _ (hB m)⟩ k
  have hHm : ∀ k m, algebraMap O C (Hm k m) = bC.repr (P.ht (B m)) k := fun k m =>
    (hbC ⟨_, P.ht_mem _ (hB m)⟩ k).symm
  refine ⟨Hm, Matrix.of Eg, ?_, ?_, ⟨Matrix.of Ei, ?_, ?_⟩, fun m m' => by rw [hBt, hBt]; exact hEg m m',
    fun m => ⟨by rw [hBt]; exact P.ht_mem _ (hB m), fun k => by simp only [Hm, hBt]⟩⟩
  · have hsurj : LinearMap.range P.ht = ⊤ := by
      rw [eq_top_iff, ← bC.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨x, -, hx⟩ := P.κ_mem _ (bo k).2
      refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
      rw [map_smul, hx, ← algebraMap_smul C κ, inv_smul_smul₀ P.κ_ne]
      exact (hbC_apply k).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker P.ht
    rw [hsurj, finrank_top, finrank_eq_card_basis bC, finrank_eq_card_basis B, Fintype.card_fin] at h1
    have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
      ext x
      rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, P.lagr]
      refine forall_congr' fun y => ?_
      rw [LinearMap.mem_ker]
      refine imp_congr_right fun _ => ?_
      change P.e y x = 0 ↔ _
      rw [pt_swap P y x, neg_eq_zero]
    have h2 := LinearMap.BilinForm.finrank_orthogonal (B := P.e) ⟨hnd, P.nondeg⟩ (LinearMap.ker P.ht)
    rw [horth, finrank_eq_card_basis B] at h2
    omega
  · ext m m'
    apply hinj
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply, map_neg, hEg]
    exact pt_swap P _ _
  · ext m m'
    apply hinj
    have h := congrArg (fun f : Module.Dual C V => f (B m')) (hw m)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hEi m, map_sum, LinearMap.sum_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, ← hEg] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul, ← Algebra.smul_def]
    rw [h, Matrix.one_apply, Finsupp.single_apply]
    by_cases hm : m = m'
    · simp [hm]
    · simp [hm, Ne.symm hm]
  · ext k k'
    apply hinj
    let x : V := ∑ m, algebraMap O C (Hm k m) • w m
    have hx : P.e x = (bC.coord k) ∘ₗ P.ht := by
      refine B.ext fun m => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_smul, hw, LinearMap.sum_apply, LinearMap.smul_apply, Basis.coord_apply,
        Basis.repr_self, LinearMap.comp_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [hHm]
    have h0 : P.ht x = 0 := (P.lagr x).2 fun y hy => by rw [hx, LinearMap.comp_apply, hy, map_zero]
    have h1 := congrArg (fun z => bC.repr z k') h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, ← hEi, map_sum, map_smul, LinearMap.map_smul_of_tower, Finsupp.coe_finsetSum, Finset.sum_apply,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Matrix.zero_apply, map_zero, ← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul,
        Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hHm k' m', ← algebraMap_smul C (Ei m m'), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Pt

theorem chart_matrices {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} (hR : 1 ≤ R)
    {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω)
    {C O : Type} [Field C] [CommRing O] [Algebra O C] [Algebra A O] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω')
    (ι₀ : D.om →ₛₗ[algebraMap A O] Ω') (hr : D.ReducesTo (algebraMap A O) P ι₀) :
    ∃ (g : ℕ) (io : D.om →ₛₗ[algebraMap A O] (Fin g → O)) (Hm : Matrix (Fin g) (Ix E N) O)
      (Eg : Matrix (Ix E N) (Ix E N) O),
      Submodule.span O (Set.range io) = ⊤ ∧
      (∀ f : D.om →ₛₗ[algebraMap A O] C, ∃ ev : (Fin g → C) →ₗ[C] C,
        ∀ u, ev (fun k => algebraMap O C (io u k)) = f u) ∧
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((D.e (dl m) (dl m')).val : O) ∈ Ideal.span {(p : O)}) ∧
      ∀ m k, Hm k m - io ⟨D.h (dl m), D.h_mem _⟩ k ∈ Ideal.span {(p : O)} := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gd.free_of_fg hv P.om P.om_lat.fg
  haveI : Module.Finite O P.om := Module.Finite.iff_fg.2 P.om_lat.fg
  let bo := Module.finBasis O P.om
  have hmem : ∀ u, ι₀ u ∈ P.om := fun u => by
    rw [← hr.span_eq]
    exact Submodule.subset_span ⟨u, rfl⟩
  let ι₁ : D.om →ₛₗ[algebraMap A O] P.om := ι₀.codRestrict P.om hmem
  let io : D.om →ₛₗ[algebraMap A O] (Fin _ → O) := bo.equivFun.toLinearMap.comp ι₁
  have hio : ∀ u k, io u k = bo.repr ⟨ι₀ u, hmem u⟩ k := fun _ _ => rfl
  obtain ⟨Hm, Eg, h1, h2, h3, h4, h5⟩ := pt_matrices hv P bo
  obtain ⟨j, hj, hjr, hjι⟩ := PositivityTheory.HtPt.Gb.bc_iso A K Ω D.om C v O hv Ω' P.om ι₀
    D.om_lat D.om_proj P.om_lat hr.span_eq hr.rank_eq
  have hpR : ∀ z : O, (p : O) ^ R * z ∈ Ideal.span {(p : O)} := fun z =>
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hR)
  refine ⟨_, io, Hm, Eg, ?_, fun f => ?_, h1, h2, h3, fun m m' => ?_, fun m k => ?_⟩
  · have h6 : Submodule.span O (Set.range ι₁) = ⊤ := by
      apply Submodule.map_injective_of_injective P.om.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hr.span_eq
    have : Set.range io = bo.equivFun.toLinearMap '' Set.range ι₁ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h6, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨jf, hjf, -⟩ := PositivityTheory.HtPt.Gb.exists_lift f
    let e : (O ⊗[A] D.om) ≃ₗ[O] P.om := (LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hjr)
    have he : ∀ u, e (1 ⊗ₜ u) = ⟨ι₀ u, hmem u⟩ := fun u => Subtype.ext (hjι u)
    refine ⟨Fintype.linearCombination C fun k => jf (e.symm (bo k)), fun u => ?_⟩
    rw [Fintype.linearCombination_apply, ← hjf, ← e.symm_apply_apply (1 ⊗ₜ u), he]
    conv_rhs => rw [← bo.sum_repr ⟨ι₀ u, hmem u⟩]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hio, algebraMap_smul]
  · obtain ⟨z, hz⟩ := hr.e_eq (dl m) (dl m')
    rw [hv.hom_inj ((h4 m m').trans hz), add_sub_cancel_left]
    exact hpR z
  · obtain ⟨h, hk⟩ := h5 m
    obtain ⟨y, hy, hz⟩ := hr.ht_eq (dl m)
    have : (⟨ι₀ ⟨D.h (dl m), D.h_mem _⟩, hmem _⟩ : P.om) = ⟨_, h⟩ + (p : O) ^ R • ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact hz
    rw [hk, hio, this, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel_left]
    exact neg_mem (hpR _)

end PositivityTheory.Xgn.TestGroupPoint
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open GlobalTheory.CompanionTheory.Ar.HT PositivityTheory.Xgn.TestGroupPoint.Par

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]

def ReducesAt (D : HTChart A K c p R N Ω) (κ : A) (C O : Type) [Field C] [CommRing O] [Algebra O C] [Algebra A O] :
    Prop :=
  ∃ (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
    (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
    (P : HTPoint C O c (algebraMap A O κ) N V Ω') (io : D.om →ₛₗ[algebraMap A O] Ω'),
    D.ReducesTo (algebraMap A O) P io

theorem reducesAt_of_withE [NeZero (p ^ R)] (D : HTChart A K c p R N Ω)
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (alt adj hs hi) (a : ℕ) (ha : a.Coprime p)
    (he : ∀ x y, D.e x y = (a : ZMod (p ^ R)) * e x y) (κ : A) {C O : Type} [Field C] [CommRing O] [Algebra O C]
    [Algebra A O] {v : Valuation C NNReal} (hv : v.Integers O) (hp : v (p : C) < 1)
    (h : ReducesAt (withE D e alt adj hs hi) κ C O) : ReducesAt D κ C O := by
  obtain ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, P, io, hr⟩ := h
  obtain ⟨b, hb⟩ := isUnit_of_coprime hv (by rwa [map_natCast]) ha
  refine ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, scalePt P b, io,
    ⟨hr.span_eq, hr.rank_eq, hr.lin, hr.ht_eq, fun x y => ?_⟩⟩
  obtain ⟨z, hz⟩ := hr.e_eq x y
  have h1 : ((D.e x y).val : O) + (p : O) ^ R * ((a * (e x y).val / p ^ R : ℕ) : O) = (a : O) * ((e x y).val : O) := by
    have h0 : (D.e x y).val = (a * (e x y).val) % p ^ R := by
      rw [he, ← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [h0]
    exact_mod_cast congrArg (Nat.cast : ℕ → O) (Nat.mod_add_div (a * (e x y).val) (p ^ R))
  refine ⟨((a * (e x y).val / p ^ R : ℕ) : O) + a * z, ?_⟩
  change algebraMap O C (b : O) • P.e (P.tate x) (P.tate y) = _
  rw [hz, smul_eq_mul, ← map_mul, hb]
  congr 1
  change (a : O) * (((e x y).val : O) + (p : O) ^ R * z) = _
  linear_combination -h1

end Chart

open TensorProduct in
theorem reducesAt_of : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → ∀ (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O] (v : Valuation C NNReal), v.Integers O → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : O)}) O → Function.Injective (algebraMap R O) → ReducesAt Dc κ C O := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ C O _ _ _ _ _ _ _ v hv hp hO hinj
  obtain ⟨-, -, hIC, -, hAC, -⟩ := PositivityTheory.HtPt.Twhopf.padic_alg p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp (algebraMap R O)) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := PositivityTheory.HtPt.Htat.TestPts.reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀
    i hi L M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hio⟩

set_option maxHeartbeats 3200000 in
open PositivityTheory.HtPt.Htat in
theorem reducesAt_pack (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c')
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (C O' : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O']
    [IsDomain O'] [Algebra O' C] [Algebra (CR O y c') O'] (v : Valuation C NNReal) (hv : v.Integers O')
    (hvp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O')}) O')
    (hφ : Function.Injective (algebraMap (CR O y c') O')) :
    ReducesAt P.Dh (algebraMap O (CR O y c') w) C O' := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ :=
    chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, hprop, hTa, hrk, -, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (zp Ω p) (mem_range_zp Ω p)
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ 𝔐.R p) := ⟨hn⟩
  have hR : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := IsFractionRing.injective _ _
  haveI : CharZero (CR O y c') := (algebraMap (CR O y c') Ω).charZero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ GlobalTheory.T.torsion_points_defined_generic (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hTa
  obtain ⟨u, hu, huz⟩ := exists_coords D 𝔐.t 𝔐.ξ p (𝔐.R p) hR hev G.t₂.pt G.t₂.onto G.t₂.lin
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (HT.cmConj E) p (𝔐.R p) D.EF u hu
  obtain ⟨b, hb⟩ := exists_mulEquiv π (qhom (D.p + D.q) (p ^ 𝔐.R p)) hsurj (qhom_surj _ _)
    (fun z => (hker z.toAdd).trans (qhom_eq_one _ _ z.toAdd).symm)
  have hζ₀ : IsPrimitiveRoot (ζ₀ : Ω) (p ^ 𝔐.R p) := IsPrimitiveRoot.coe_units_iff.2 hev.prim
  obtain ⟨a, -, hac, haζ⟩ := (G.ζ_prim.isPrimitiveRoot_iff).1 hζ₀
  have hap : a.Coprime p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hac
  have hee : ∀ x x', G.e x x' = (a : ZMod (p ^ 𝔐.R p)) * e x x' := by
    intro x x'
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω _
    let ψ := bcPt 𝔐.ξ i _ rfl
    let cc : (AlgebraicClosure Ω)ˣ :=
      Units.map i.toMonoidHom (ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k))
    have h1 := (hev.weil (∑ k, x k • u k) (∑ k, x' k • u k) _ i (ψ ≫ ev _) (ψ ≫ ev _) cc rfl rfl).2 rfl
    have h2 := (G.weil x x' _ i _ _ cc (by rw [← huz]; rfl) (by rw [← huz]; rfl)).1 h1
    have h3 : ((ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k) : Ωˣ) : Ω) = G.ζ ^ (G.e x x').val := i.injective h2
    rw [← pow_val_intCast ζ₀ _ hev.prim.pow_eq_one, ← he, Units.val_pow_eq_pow_val, ← haζ,
      ← pow_val_mul _ _ G.ζ_prim.pow_eq_one] at h3
    exact ZMod.val_injective _ (G.ζ_prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3.symm)
  refine reducesAt_of_withE P.Dh e halt hadj hes hei a hap (fun x x' => by rw [P.Dh_e, hee]) _ hv hvp ?_
  have hζ1 : P.ζ ^ (p ^ 𝔐.R p) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
    exact (congrArg (· ^ (p ^ 𝔐.R p)) P.ζ_eq).trans G.ζ_prim.pow_eq_one))
  have hζa : algebraMap (CR O y c') Ω ((P.ζ ^ a : (CR O y c')ˣ) : CR O y c') = ζ₀ := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← haζ]
    exact congrArg (· ^ a) P.ζ_eq
  let κ : FractionRing (CR O y c') ≃+* Ω := (FractionRing.algEquiv (CR O y c') Ω).toRingEquiv
  have hκ : ∀ r, κ (algebraMap (CR O y c') _ r) = algebraMap (CR O y c') Ω r :=
    (FractionRing.algEquiv (CR O y c') Ω).commutes
  have hκf : fracToField (CR O y c') = κ.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    ext r
    exact (IsFractionRing.lift_algebraMap (g := algebraMap (CR O y c') Ω) hinj r).trans (hκ r).symm
  have hq : spMap κ.symm.toRingHom ≫ 𝔐.ξ = (BT.genPt (CR O y c')).hom ≫ P.x := by
    rw [← P.x_gen, ← Category.assoc, ← HTTie.spec_comp]
    congr 3
    ext r
    exact (RingEquiv.symm_apply_eq κ).2 (hκ r).symm
  haveI := P.fin
  refine reducesAt_of (GlobalTheory.T.pointHT_of_fargues_hodge_tate hF) E H D p (CR O y c') Ω (𝔐.R p) _ (withE P.Dh e halt hadj hes hei) u hu 𝔐.X 𝔐.t P.x (relabel P.Γ₂ b) P.i₂
    ⟨P.tors₂.isOver, P.tors₂.mul, P.tors₂.inj, P.tors₂.kernel⟩ P.L P.M P.ρ P.act P.j P.j_bc π (P.ζ ^ a) (algebraMap O (CR O y c') w)
    ⟨P.isHT.1, P.isHT.2.1, fun z => ?_⟩ hπ he ?_ (isProper_of_iso _ 𝔐.ξ _ _ hq) (fun k _ _ f => ?_)
    (cp_descend hinj p (algebraMap O (CR O y c') w) hw) C O' v hv hvp hO hφ
  · obtain ⟨χ, w₀, hχ, hh, s, hs, hHT⟩ := P.isHT.2.2 z
    refine ⟨χ.comp b.toMonoidHom, w₀, fun z' => ?_, hh, s, fun t => hs (b t), hHT⟩
    change χ (b (π _)) = (P.ζ ^ a) ^ (e z z').val
    rw [hb, hχ, P.Dh_e, hee, pow_val_mul _ _ hζ1]
  · rw [← hrk, P.toLi_bc.finrank_eq]
  · have hk : spMap (f.comp κ.symm.toRingHom) ≫ 𝔐.ξ = spMap f ≫ (BT.genPt (CR O y c')).hom ≫ P.x := by
      rw [← hq, Tor.spMap_comp, Category.assoc]
    obtain ⟨I, hz, hI⟩ := hev.tate' D 𝔐.t 𝔐.ξ k _ _ hk
    refine ⟨I, ?_, fun x => ?_⟩
    · rw [hz, ← hζa, ← hκ]
      exact congrArg f (κ.symm_apply_apply _)
    · obtain ⟨z, r, rfl⟩ := hdec x
      have e1 : HT.lev p (𝔐.R p) (∑ k, z k • u k + (p ^ 𝔐.R p) • r) = π (Multiplicative.ofAdd z) := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨r, ?_⟩)
        exact (add_sub_cancel_left _ _).symm
      rw [hI, hev.add, (hev.ker _).2 ⟨r, rfl⟩, _root_.mul_one, huz, P.pts₂, e1, hκf]
      change _ = spMap f ≫ (P.Γ₂.pt (b (π _))).left ≫ P.i₂
      rw [hb]
      exact spMap_cancel κ f _

theorem point_data (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (hT : IsTestPt p (CR O y c') RC) :
    ∃ (g : ℕ) (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hT.2.2.2] (Fin g → RC))
      (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C)) (Hm : Matrix (Fin g) (Ix E (D.p + D.q)) RC)
      (Eg : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC),
      Submodule.span RC (Set.range io) = ⊤ ∧
      (∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v)) ∧
      Fintype.card (Ix E (D.p + D.q)) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((G.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)}) ∧
      ∀ m k, Hm k m - io ⟨P.Dh.h (dl m), P.Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)} := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ := chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  have hC := hT.1
  obtain ⟨v, hv, hvp⟩ := hT.2.1
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap Ω C).injective
  have hint : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  letI : Algebra (CR O y c') RC := (toRC (CR O y c') RC hT.2.2.2).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  obtain ⟨V, Ω', _, _, _, _, _, _, _, _, Pt, io₀, hr⟩ := reducesAt_pack hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS A m hpm O G c' hc' P w hw C RC v hint hvp hT.2.2.1 hφ
  obtain ⟨g, io, Hm, Eg, h1, h2, h3, h4, h5, h6, h7⟩ :=
    chart_matrices (le_trans (by norm_num) (𝔐.R_ge p hpS)) P.Dh hint Pt io₀ hr
  let f : 𝔐.Li → (P.Dh.om →ₛₗ[algebraMap (CR O y c') RC] C) := fun x =>
    { toFun := fun u => algebraMap Ω C (u.1 x)
      map_add' := fun a b => by rw [Submodule.coe_add, LinearMap.add_apply, map_add (f := _)]
      map_smul' := fun r a => by
        change algebraMap Ω C ((r : Ω) * a.1 x) = algebraMap Ω C (r : Ω) * algebraMap Ω C (a.1 x)
        rw [map_mul] }
  choose ev hev using fun x => h2 (f x)
  refine ⟨g, io, ev, Hm, Eg, h1, fun x u => hev x u, h3, h4, h5, fun m m' => ?_, h7⟩
  rw [← P.Dh_e]
  exact h6 m m'

end PositivityTheory.Xgn.TestGroupPoint
