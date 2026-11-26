module

public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.SatakeDualWeyl.StatementC

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.DataHost
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

namespace Formalism.BasicNotions

theorem hypOdd_of_hostHyp {q d : ℕ} (h : HostHyp q d) : HypOdd q d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := h
  refine ⟨hq, hd, ?_, ?_, ?_⟩ <;> rintro rfl <;> omega

noncomputable def iotaH (e : ℕ) (i : ZMod (2 ^ e)) : HGrp e := hcl e (u5 (e + 2)) ^ i.val

noncomputable def iotaHInv (e : ℕ) (h : HGrp e) : ZMod (2 ^ e) := Function.invFun (iotaH e) h

inductive PrimeClass
  |   splitK
  |   signal
  |   inertClass
  |   ram2
  |   ramQ
  |   ramD
  deriving DecidableEq

noncomputable def primeClass {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) : PrimeClass :=
  if p ∈ H.small then .ram2 else if p = H.q then .ramQ else if p = H.d then .ramD
  else if jacobiSym (-(H.d : ℤ)) p = 1 then .splitK
  else if H.psAt p = 1 then .signal
  else .inertClass

structure Host (R : Ranks) extends Formalism.HC.HostAx R.toFrame where

  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq

  QS_exact : toHostRaw.Exact

  QS_le : QS ≤ R.n ^ 2

  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e

  q_ne_three : q ≠ 3

  qd_big : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d

  splitBound : ℕ
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ splitBound → jacobiSym (-(d : ℤ)) p = 1

  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ splitBound

  φ₀ : E →+* ℂ
  φ₀_mem : φ₀ ∈ toHostRaw.cmType

  𝔟 : Ideal (𝓞 E)
  𝔟_spec : differentIdeal (𝓞 toHostRaw.K) (𝓞 E) = 𝔟 * (toHostRaw.conj • 𝔟) ∧ 𝔟 ⊔ toHostRaw.conj • 𝔟 = ⊤

  𝔟_stable : ∀ σ : E ≃ₐ[ℚ] E, gal σ ∈ R.Psi → σ • 𝔟 = 𝔟

  levelPrimes : Finset ℕ

  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes

  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes

  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i

  ccK : Ideal (𝓞 toHostRaw.K)
  ccK_ne_bot : ccK ≠ ⊥

  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 toHostRaw.K)}

  ccK_split : ∀ P : Ideal (𝓞 toHostRaw.K), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(d : ℤ)) (Ideal.absNorm P) = 1

  ccK_coprime : ∀ p ∈ insert 2 (insert 3 (insert 5 (insert q (insert d levelPrimes)))), Nat.Coprime (Ideal.absNorm ccK) p

  ccK_coprimeS : Nat.Coprime (Ideal.absNorm ccK) QS

  level_coprimeS : ∀ p ∈ levelPrimes, Nat.Coprime p QS

  TT : Finset R.A

  T2 : Finset ℕ
  u0 : R.A
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw

  CT2 : ℝ

namespace Host

variable {R : Ranks} (H : Host R)

theorem hypOdd : HypOdd H.q H.d := hypOdd_of_hostHyp H.hyp

@[instance_reducible] noncomputable def cmStar : StarRing H.E :=
  @NumberField.IsCMField.starRing H.E _ _ H.isCMField_hostE _

noncomputable def sigmaOf (g : R.GG) : H.E ≃ₐ[ℚ] H.E := H.gal.symm g

noncomputable def emb (g : R.GG) : H.E →+* ℂ := H.φ₀.comp (H.sigmaOf g : H.E →+* H.E)

def MuCond {ι : Type} [Fintype ι] (g : ι → R.GG) (e : ι → ℚ) : Prop :=
  ∀ ζ : H.E, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ∏ τ, H.emb (g τ) ζ ^ (e τ).num = 1


open Classical in
noncomputable def topPlaces : Finset R.GG := H.TT.image R.tau1


open Classical in
noncomputable def thickPlaces : Finset R.GG :=
  H.T2.image (fun s => R.tau2 (R.dig s + H.u0))

def IsThin (g : R.GG) : Prop := g ∈ R.Psi ∧ g ∉ H.topPlaces ∧ g ∉ H.thickPlaces

noncomputable def cls (p : ℕ) : PrimeClass := primeClass H.toHostRaw p

noncomputable def rdE : ℝ :=
  |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))

noncomputable def v : ℝ := H.rdE / 2

noncomputable def ka : ℝ := Real.pi / H.v

def sqrtMinusD : H.E := H.sqd

noncomputable def xi0 : H.E := -1 / ((Ideal.absNorm H.ccK : H.E) * H.sqrtMinusD)

noncomputable def ccE : Ideal (𝓞 H.E) := Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK

noncomputable def AA0 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹

noncomputable def AA : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  (H.ccE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) * H.AA0

noncomputable def AAbar : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.conj • H.ccE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) *
    ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹

noncomputable def ddE : Ideal (𝓞 H.E) := differentIdeal ℤ (𝓞 H.E)

def secondSet_card_lower_bound : Prop :=
  (R.n0 : ℝ) * Real.exp (-(H.CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log H.Lw))) / H.Lw ≤ H.T2.card

end Host

def FactIota : Prop := ∀ e : ℕ,
  Function.Bijective (iotaH e) ∧
  (∀ i j : ZMod (2 ^ e), iotaH e (i + j) = iotaH e i * iotaH e j) ∧
  iotaH e 1 = hcl e (u5 (e + 2))

def bridge_iota : Prop := ∀ e : ℕ, ∀ ι : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e,
  ι (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) →
  ∀ i : ZMod (2 ^ e), ι (Multiplicative.ofAdd i) = iotaH e i

def bridge_star : Prop := ∀ (R : Ranks) (H : Host R) (x : H.E),
  (@star H.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
    (@StarRing.toStarMul _ _ H.cmStar))) x) = H.conj x

def FactCardPsi : Prop := ∀ (R : Ranks) (H : Host R),
  Nat.card R.Psi = R.f ∧ H.cmType.ncard = R.f

def FactEmb : Prop := ∀ (R : Ranks) (H : Host R),
  Function.Bijective H.emb ∧ ∀ g : R.GG, H.emb g ∈ H.cmType ↔ g ∈ R.Psi

def FactPlaces : Prop := ∀ φ : Formalism.HC.Frame,
  (∀ g : φ.GG, g ∈ φ.Psi ↔ (∃ t, g = φ.tau1 t) ∨ (∃ t, g = φ.tau2 t)) ∧
  ∀ t t' : φ.A, φ.tau1 t ≠ φ.tau2 t'

def FactTopsThick : Prop := ∀ (R : Ranks) (H : Host R),
  (∀ g ∈ H.topPlaces, g ∈ R.Psi) ∧ (∀ g ∈ H.thickPlaces, g ∈ R.Psi) ∧
  Disjoint H.topPlaces H.thickPlaces ∧
  H.topPlaces.card = H.TT.card ∧ H.thickPlaces.card = H.T2.card

def HNeZero {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    IsArithFrobAt ℤ σ P → Even (orderOf (H.galE σ).2)

theorem HNeZero.ne_one {R : Ranks} {H : Host R} {p : ℕ} (h : HNeZero H p) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) : (H.galE σ).2 ≠ 1 := by
  intro h1
  have := h P σ hσ
  rw [h1, orderOf_one] at this
  exact Nat.not_even_one this

def FactRd : Prop := ∀ (R : Ranks) (H : Host R),
  (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) * Real.sqrt H.d ≤ H.rdE ∧
  H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ (2 * R.f : ℝ) ≤ H.rdE ^ 2

def FactPrincipalDatum : Prop := ∀ (R : Ranks) (H : Host R),
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 H.E)) H.xi0 * H.AA * H.AAbar *
    ((H.ddE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) = 1

def FactMMUnimodular : Prop := ∀ (R : Ranks) (H : Host R), ∀ x : H.E,
  x ∈ H.AA0 ↔ ∀ y ∈ H.AA0,
    Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range

def FactClassFrob : Prop := ∀ (R : Ranks) (H : Host R),
  ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
  ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
    (H.cls p = .splitK ↔ ((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1))) ∧
    (H.cls p = .signal ↔ (H.galE σ).1 = (1, -1)) ∧
    (H.cls p = .inertClass ↔ (H.galE σ).1 = c0)

def FactFrobGeom : Prop := ∀ (R : Ranks) (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E),
  H.galE σ⁻¹ = (H.galE σ)⁻¹ ∧
  R.iotaInv (H.galE σ⁻¹).2 = - R.iotaInv (H.galE σ).2

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.DataArith
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.BasicNotions

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L]

def vAdd (w : HeightOneSpectrum R) (x : L) : ℤ := - WithZero.log (w.valuation L x)

def idxW {n : Type} [Fintype n] [DecidableEq n] (w : HeightOneSpectrum R) (γ : Matrix n n L) : ℤ :=
  vAdd w γ.det

end Val

def bridge_ccb_unit : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum R) (x : L), x ≠ 0 → (w.valuation L x = 1 ↔ vAdd w x = 0)

def bridge_ccb_integral : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum R) (x : L), w.valuation L x ≤ 1 ↔ 0 ≤ vAdd w x

section Places

variable (K : Type) [Field K] [NumberField K]

def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)

def eWL (w : HeightOneSpectrum (𝓞 K)) : ℕ := w.asIdeal.ramificationIdx ℤ

def unitRule (w : HeightOneSpectrum (𝓞 K)) (y : ℝ) : ℝ := (eWL K w : ℝ) * y

def sizeOfVal (w : HeightOneSpectrum (𝓞 K)) (y : ℝ) : ℝ := 2 * lw K w * y

end Places

def bridge_unit_rule : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) (w : HeightOneSpectrum (𝓞 K)), l.Prime →
    ((l : 𝓞 K) ∈ w.asIdeal) → vAdd w ((l : ℕ) : K) = (eWL K w : ℤ)


open scoped Classical in
open Classical in
def FactUnitNormalisation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ), p.Prime →
    (∑ᶠ w : HeightOneSpectrum (𝓞 K),
        if ((p : 𝓞 K) ∈ w.asIdeal) then 2 * lw K w * (eWL K w : ℝ) else 0) = 2 * Real.log p

structure HLat (K : Type) [Field K] [NumberField K] [StarRing K] where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module K V]
  [modOV : Module (𝓞 K) V]
  [towV : IsScalarTower (𝓞 K) K V]
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  b : Basis ι K V
  X : InfinitePlace K → Matrix ι ι ℂ
  L : Submodule (𝓞 K) V

attribute [instance] HLat.addV HLat.modV HLat.modOV HLat.towV HLat.finι HLat.decι

namespace HLat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

def Good : Prop := (∀ v, IsUnit (A.X v).det) ∧ A.L.FG ∧ Submodule.span K (A.L : Set A.V) = ⊤

def rank : ℕ := Formalism.HN.rkK A.L

def mu : ℝ := Formalism.HN.muDef A.b A.X A.L

def muMax : ℝ := Formalism.HN.muMaxDef A.b A.X A.L

def muMin : ℝ := Formalism.HN.muMinDef A.b A.X A.L

def lcv : ℝ := (2 / (finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht A.b A.X A.L)

def dualL : Submodule (𝓞 K) (Module.Dual K A.V) := Formalism.HN.dualLat A.L

def dualB : Basis A.ι K (Module.Dual K A.V) := A.b.dualBasis

def dualX : InfinitePlace K → Matrix A.ι A.ι ℂ := Formalism.HN.dualFrame A.X

def muDual : ℝ := Formalism.HN.muDef A.dualB A.dualX A.dualL

def muMaxDual : ℝ := Formalism.HN.muMaxDef A.dualB A.dualX A.dualL

def muMinDual : ℝ := Formalism.HN.muMinDef A.dualB A.dualX A.dualL

end HLat

def bridge_hn_mu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (A : HLat K),
    A.Good → 0 < A.rank → A.mu = - A.lcv / (A.rank : ℝ)

def bridge_dual_mu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (A : HLat K),
    A.Good → 0 < A.rank → A.muMinDual = - A.muMax

def bridge_ccb_dual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V W : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (A : Submodule (𝓞 K) V) (N : Submodule (𝓞 K) W)
    (B : W →ₗ[K] Module.Dual K V),
    (∃ β : N →ₗ[𝓞 K] Module.Dual (𝓞 K) A,
        ∀ (φ : N) (F : A), algebraMap (𝓞 K) K (β φ F) = B (φ : W) (F : V)) ↔
      N.map (B.restrictScalars (𝓞 K)) ≤ Formalism.HN.dualLat A

section Frame

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Words : Type} [Fintype Words]

def dU (Nu : Words → HLat K) (u : Words) : ℕ := (Nu u).rank

def Rsum (Nu : Words → HLat K) : ℕ := ∑ u, dU Nu u

def sFrame (Nu : Words → HLat K) (h : Words → ℝ) : ℝ :=
  (∑ u, (dU Nu u : ℝ) * ((Nu u).mu - h u)) / (Rsum Nu : ℝ)

def uFrame [Nonempty Words] (Nu : Words → HLat K) (h : Words → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u => (Nu u).muMax - h u) - sFrame Nu h

end Frame

structure DivData (K : Type) [Field K] [NumberField K] [StarRing K] (Words : Type) [Fintype Words]
    where

  RR : HLat K

  Nu : Words → HLat K

  Bk : ∀ u, (Nu u).V →ₗ[K] Module.Dual K RR.V

  h : Words → ℝ

  HH : ℝ

  HH_ge : sFrame Nu h + RR.muMax ≤ HH

  etaF : ℝ

  Dall : ℕ

  delP : ℝ
  delP_le_one : delP ≤ 1

namespace DivData

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Words : Type} [Fintype Words]
  (D : DivData K Words)

def Drows : ℕ := D.RR.rank

def cc : Submodule (𝓞 K) (Module.Dual K D.RR.V) := D.RR.dualL

def d (u : Words) : ℕ := dU D.Nu u

def R : ℕ := Rsum D.Nu

def s : ℝ := sFrame D.Nu D.h

def AllGood : Prop := D.RR.Good ∧ ∀ u, (D.Nu u).Good

def OneMapIntoCC : Prop := ∀ u, (D.Nu u).L.map ((D.Bk u).restrictScalars (𝓞 K)) ≤ D.cc

end DivData

def RankBoundMonotoneInDimension : Prop :=
  ∀ (a q η : ℝ) (D Dall : ℕ), 0 < D → D ≤ Dall → 0 ≤ η →
    a ≤ (1 + η) * q ^ 2 / (Dall : ℝ) → a ≤ (1 + η) * q ^ 2 / (D : ℝ)

def FactHHcc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (Words : Type)
    [Fintype Words] (D : DivData K Words), D.RR.Good → 0 < D.RR.rank →
    D.s - D.RR.muMinDual ≤ D.HH

def bSize (x ε : ℝ) : ℝ := Real.exp (x ^ ε)

def sizeBudget (R : Ranks) (x ε : ℝ) : ℝ := (R.f : ℝ) * R.m * bSize x ε * x ^ ε

def rankBudget (R : Ranks) (x ε : ℝ) : ℝ := (R.n : ℝ) * x ^ (-ε)

def budgetNc (R : Ranks) (x ε : ℝ) (T2card : ℕ) : ℝ :=
  (T2card : ℝ) * R.k * bSize x ε * x ^ ε / ((R.n : ℝ) * rankBudget R x ε)

def FactNc : Prop :=
  ∀ (R : Ranks) (x ε : ℝ) (T2card : ℕ), 0 < x →
    budgetNc R x ε T2card = (T2card : ℝ) * R.k * bSize x ε * x ^ (2 * ε) / ((R.n : ℝ) ^ 2)

end Formalism.BasicNotions
end
end

section -- merged from Formalism.LocalRingCardinality.DataLevel
noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

@[reducible] def tensTopL (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Defs

def IsProGrp {G : Type} [Group G] [TopologicalSpace G] (g : ℕ) (Uw : Subgroup G) : Prop :=
  IsCompact (Uw : Set G) ∧ ∀ N : Subgroup Uw, IsOpen (N : Set Uw) → N.Normal → ∃ m : ℕ, N.index = g ^ m

section Iw

variable (F : Type) [Field F] [NumberField F] (k : ℕ)

def upperUni (A : Type) [CommRing A] : Set (GL (Fin k) A) :=
  {x | ∀ i j : Fin k, (j < i → (x : Matrix (Fin k) (Fin k) A) i j = 0) ∧
    (x : Matrix (Fin k) (Fin k) A) i i = 1}

def iwU (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin k) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Subgroup.closure (upperUni k _))

end Iw

namespace Spaces

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem rank0 : (sp.X 0).rank = R.k := by
  simpa [Ranks.N] using sp.X_rank 0 (Nat.zero_le _)

def gram0 : Matrix (Fin R.k) (Fin R.k) E :=
  (sp.X 0).gram.reindex (finCongr sp.rank0) (finCongr sp.rank0)

def crd0 : (sp.X 0).V ≃ₗ[E] (Fin R.k → E) :=
  (sp.X 0).frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr sp.rank0).symm)

def crdLat0 (L : Submodule (𝓞 E) (sp.X 0).V) : Submodule (𝓞 E) (Fin R.k → E) :=
  L.map ((sp.crd0 : (sp.X 0).V →ₗ[E] (Fin R.k → E)).restrictScalars (𝓞 E))

private theorem hT_eq_hform_gram_reindex_frame (S : HSpace E) {n : ℕ} (h : S.rank = n) (x y : S.V) :
    S.hT x y = hform (starRingEnd E) (S.gram.reindex (finCongr h) (finCongr h))
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) x)
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) y) := by
  subst h
  simp [hform, HSpace.gram]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermitianForm_base_coordinates (x y : (sp.X 0).V) :
    (sp.X 0).hT x y = hform (sp.cm.sig : E →+* E) sp.gram0 (sp.crd0 x) (sp.crd0 y) := by
  exact hT_eq_hform_gram_reindex_frame (sp.X 0) sp.rank0 x y

theorem baseGram_isHermitian : IsHerm (sp.cm.sig : E →+* E) sp.gram0 := by
  unfold IsHerm cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, gram0, Matrix.reindex_apply,
    Matrix.submatrix_apply, HSpace.gram]
  exact (sp.X 0).herm.eq _ _

end Spaces

abbrev intV {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

def dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) : Set (n → E) :=
  {y | ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range}

structure ColLevel (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E) (gp : Fin 2 → ℕ)
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (A : ColumnsAtT R C)
    (clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V) where

  Lb : Submodule (𝓞 E) (Fin R.k → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin R.k → E)) = ⊤

  Lb_int : ∀ x ∈ Lb, x ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb

  Lb_dual : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb, (A.T : E) • y ∈ Lb

  Lb_index : Lb.toAddSubgroup.relIndex
    (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)).toAddSubgroup = A.T ^ (2 * R.f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin R.k) (E ⊗[F] v.adicCompletion F))
  Uloc_le : ∀ v, Uloc v ≤ UPts sp.cm.sig sp.gram0 (v.adicCompletion F)

  Uloc_lev : ∀ v, Uloc v ≤ levelVL sp.cm.sig sp.gram0 v Lb

  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((A.T : 𝓞 F) ∉ v.asIdeal) →
    Uloc v = levelVL sp.cm.sig sp.gram0 v Lb

  splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  splitG_sig : ∀ i v h x, splitG i v h (sigR sp.cm.sig (v.adicCompletion F) x) =
    swapR _ (splitG i v h x)

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    GL (Fin R.k) (v.adicCompletion F)

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    x ∈ Uloc v ↔ (frG i v h)⁻¹ * bc ((RingHom.fst _ _).comp (splitG i v h).toRingHom) x * frG i v h ∈
      iwU F R.k v

  fM : ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → Type
  [fM_acg : ∀ v h, AddCommGroup (fM v h)]
  [fM_mod : ∀ v h, Module (intV E v) (fM v h)]
  fT : ∀ v h, latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)) →ₗ[intV E v] fM v h
  fT_ne : ∀ v h, fT v h ≠ 0
  fT_T : ∀ v h x, fT v h ((A.T : intV E v) • x) = 0

  fM_card : ∀ v h, Nat.card (fM v h) = A.T

  fT_L : ∀ v h x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → fT v h x = 0

  UlocAlt : ∀ v h, Uloc v = levelVL sp.cm.sig sp.gram0 v Lb ⊓ stabFun _ (fT v h)

  U : Subgroup (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
    ∀ v, bc (prV (E := E) v) x ∈ Uloc v

  U_compact : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (U : Set (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
  U_open : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}

  w1 : HeightOneSpectrum (𝓞 F)
  reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal

  y : C.cls 0 → UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : C.cls 0 =>
    (Quotient.mk'' (y c) : ClassSet
      ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))))

  y_lat : ∀ c (x : Fin R.k → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (sp.crdLat0 (clsLat 0 c)) ↔
    ((((y c : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb

  stabI : ∀ c : C.cls 0, C.stab 0 c →* UJ (sp.cm.sig : E →+* E) sp.gram0
  stabI_inj : ∀ c, Function.Injective (stabI c)

  stabI_range : ∀ c (γ : GL (Fin R.k) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) sp.gram0),
    (⟨γ, hγ⟩ : UJ (sp.cm.sig : E →+* E) sp.gram0) ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin R.k) _)).toMonoidHom

  stabI_lat : ∀ c (γ : C.stab 0 c) (x : Fin R.k → E),
    x ∈ sp.crdLat0 (clsLat 0 c) ↔
      (((stabI c γ : GL (Fin R.k) E) : Matrix (Fin R.k) (Fin R.k) E) *ᵥ x) ∈ sp.crdLat0 (clsLat 0 c)

attribute [instance] ColLevel.fM_acg ColLevel.fM_mod

namespace ColLevel

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def ProG (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp (gp i) (L.Uloc v)

end ColLevel

end Formalism.BasicNotions

end
end
