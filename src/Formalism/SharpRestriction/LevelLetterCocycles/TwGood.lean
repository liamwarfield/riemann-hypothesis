module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.TwGood
noncomputable section

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

variable {Y}

variable (Y)

variable {Y}

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions

def TwistedAt (D : D7) (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

theorem twistedAt_conj (D : D7) (w : D.what₂.places.Pl) : TwistedAt D (D.what₂.places.conj w) ↔ TwistedAt D w := by
  unfold TwistedAt
  rw [D.what₂.muAt_conj]

structure TwIn (D : D7) where
  E : IntegralHeckeForms.XD D
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)

def TwIn.Sg {D : D7} (I : TwIn D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Dat i j b) :=
  IntegralHeckeForms.SgJ D.nexp I.E i j b

def TwIn.Ok {D : D7} (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp I.E i j b (I.Sg i j b)) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (I.Sg i j b) (I.S i j b))

def twEps (D : D7) (i : D.ntw.Tw) : ℝ := ((D.ntw.l i : ℝ) ^ 2)⁻¹

theorem twEps_pos (D : D7) (i : D.ntw.Tw) : 0 < twEps D i := by
  unfold twEps
  have hl : (0 : ℝ) < (D.ntw.l i : ℝ) := by exact_mod_cast (D.ntw.lPrime i).out.pos
  positivity

def rPrAv (D : D7) : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0Av (D : D7) : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPrAv D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

def avPrimes (D : D7) : Finset ℕ :=
  letI := D.wordFin
  ((insert 3 (insert 5 (insert (D.host.g 0) (insert (D.host.g 1) (insert D.host.pde (insert D.host.pde'
    (insert (q0Av D) (Finset.univ.image fun u => (D.mem u).A.T)))))))) ∪
    (Ideal.absNorm D.host.ccK).primeFactors).filter (· ≠ 0)

def AvSet (D : D7) : Set (PlE D.host) := ⋃ p ∈ avPrimes D, placesOver D.host.E p

theorem placesOver_finite_av (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hI : (Ideal.span {((p : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem avSet_finite (D : D7) : (AvSet D).Finite := by
  unfold AvSet
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun p hp =>
    placesOver_finite_av _ p (Finset.mem_filter.mp hp).2

def AvRec (D : D7) : Finset (PlE D.host) := (avSet_finite D).toFinset

theorem mem_avRec {D : D7} (v : PlE D.host) : v ∈ AvRec D ↔ ∃ p ∈ avPrimes D, v ∈ placesOver D.host.E p := by
  simp only [AvRec, AvSet, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]


open Classical in
def TwGoodOne (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) (AvRec D) Q k' (BlochKatoReduction.Gen.psiAt b ψ)

def TwGoodAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    I.Ok (C.twI w) ∧ TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

abbrev TwPack (D : D7) : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def twPack (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : TwPack D :=
  ⟨i, Q, k', BlochKatoReduction.Gen.psiAt b ψ⟩

def NChoicePack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D :=
  twPack D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

def TwConjAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    NChoicePack C (D.what₂.places.conj w) = NChoicePack C w ∧
      (D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w)

def TwGoodE {eps : ℝ} (Fm : FamP eps) (E : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, IntegralHeckeForms.XD (Fm.D x i)) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨E x hx i, N0, S⟩

def twEOf {D : D7} (T : ThData D) : IntegralHeckeForms.XD D := ⟨T.xd0, T.thetaBase_invariant_action⟩

def twE {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : IntegralHeckeForms.XD (Fm.D x i) := twEOf (Fm.ex x hx i).xd

def TwGood {eps : ℝ} (Fm : FamP eps) : Prop := TwGoodE Fm (twE Fm)

theorem psiAt_psiAt {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) :
    BlochKatoReduction.Gen.psiAt b (BlochKatoReduction.Gen.psiAt b ψ) = ψ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]


end Formalism.MainNotions

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.LiftingTheory (qp pk Over CaseA JumpsLet)
open Formalism.MainNotions.WachCoordinates (FilLev)
open Formalism.MainNotions.DeltaInvariantLattices (ιDi)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (k - j)

def IsExp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : W.DD T)
    (d : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m : ℤ, ∀ k < m, d k = 0) ∧ ∃ (a : LetA O n) (ha : a • x ∈ W.N T), W.lev i ζ a ≠ 0 ∧
    ∀ k : ℤ, W.levN T i ζ ⟨a • x, ha⟩ k = conv (W.lev i ζ a) d k

def ExpRing (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∃ u : PowerSeries LL, IsUnit u ∧ W.lev i ζ (qp W) = u * PowerSeries.X) ∧
    PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) ∧ IsUnit (W.lev i ζ (pk W 1))

def ExpRules (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∀ (x : W.DD T) (a : LetA O n), a • x ∈ W.N T → W.lev i ζ a ≠ 0 → ∃! d, IsExp W T i ζ x d) ∧
    (∀ x d, DL W T i x → IsExp W T i ζ x d → ∀ k, d k ∈ ιDi W T i) ∧
    (∀ x y d e, IsExp W T i ζ x d → IsExp W T i ζ y e → IsExp W T i ζ (x + y) (d + e)) ∧
    (∀ (c : O) x d, IsExp W T i ζ x d → IsExp W T i ζ (c • x) (fun k => algebraMap O LL c • d k)) ∧
    (∀ (a : LetA O n) x d, IsExp W T i ζ x d → IsExp W T i ζ (a • x) (conv (W.lev i ζ a) d)) ∧
    (∀ x d, IsExp W T i ζ x d →
      IsExp W T i ζ (W.γ T x) (fun k => (algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k)) ∧
    ∀ (T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T'.ρ → ∀ x d, IsExp W T i ζ x d →
      IsExp W T' i ζ (W.map F x)
        (fun k => AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (d k))

def ExpCrit (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      ((∃ k : ℕ, qp W ^ k • x ∈ W.N T) → (x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k))) ∧
      ((∃ k : ℕ, qp W ^ k • x ∈ pullJ W T (i - 1) 1) → (x ∈ pullJ W T (i - 1) 1 ↔ ∀ k < 0, d k = 0))

def LemK (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      (∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T x - x) ∈ W.N T) →
      (∀ k, k ≠ 0 → d k ∈ FilLev W T i 0 (-k)) ∧
      ∀ y : ℕ, qp W ^ y • x ∈ W.N T →
        d 0 ∈ FilLev W T i 0 (-(y : ℤ)) ∧ (x ∈ W.N T ↔ d 0 ∈ FilLev W T i 0 0)

def FilDim (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i →
    finrank LL ↥(ιDi W T i) = finrank LL T.V ∧
    ∀ a b : ℤ, a ≤ b → (finrank LL ↥(FilLev W T i 0 a) : ℤ) - finrank LL ↥(FilLev W T i 0 b) =
      ∑ u ∈ Finset.Ico a b, multV PD T.ρ τ u

def at0 (W : LocWach PD LL O v n) (f : PowerSeries O) : LetA O n := fun _ => PowerSeries.subst W.π₀₁ f

def IsBas (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T) : Prop :=
  (∀ k, e k ∈ W.N T ∧ DL W T i (e k)) ∧
    ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k

def BasTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ i : ZMod n,
    (∃ e : Fin (finrank LL T.V) → W.DD T, IsBas W T i e) ∧
    ∀ (r : ℕ) (e : Fin r → W.DD T), IsBas W T i e → ∀ j : ℕ,
      (∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
        ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k)) ∧
      ∀ (x : W.DD T) (s : ℕ), ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i j → x ∈ pullJ W T i j

def DetTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T Mi hi →
    ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i → ∀ (r : ℕ) (e e' : Fin r → W.DD T),
      IsBas W T i e → IsBas W T (i - 1) e' → ∀ (M : ℕ) (P : Matrix (Fin r) (Fin r) (PowerSeries O)),
        (∀ k, qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m) →
        ∃ (u : PowerSeries O) (w : ℕ), IsUnit u ∧
          P.det = u * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ w ∧
          (w : ℤ) = (M : ℤ) * r + ∑ a ∈ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a

def ZTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → 11 ≤ PD.p → ∀ (j X σ : ℕ), TCase PD.p j 1 X σ →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (r : ℕ) (e : Fin r → W.DD T) (he : IsBas W T i e),
      ∃ Z Z' R : Matrix (Fin r) (Fin r) (PowerSeries O),
        (∀ m k, PowerSeries.constantCoeff (Z m k) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0) ∧
        Z * Z' = ((PD.p : ℕ) : PowerSeries O) ^ (2 * σ) • (1 : Matrix (Fin r) (Fin r) (PowerSeries O)) +
          (PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X) • R ∧
        ∀ k, (∃ p ∈ pullJ W T i j,
            W.γ T (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) - ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m) =
              fMX W 1 X • p) ∧
          ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ d,
            IsExp W T (i + (j : ZMod n)) ζ (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) d →
            ∀ s : ℤ, s < X → d s = if s = 0 then (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
              ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨e k, (he.1 k).1⟩)) else 0

def ExtData (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T.L)) (y z : FF →ₗ[O] W.DD T) (μ ν : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  (∀ f, ∃ (x : ↥(W.wachCocyclesDelta T)) (hκ : (g f : G → T.V) ∈ latticeCocycles T.L), (x : W.DD T × W.DD T) = (y f, z f) ∧
    W.clK T x = Submodule.Quotient.mk (⟨(g f : G → T.V), hκ⟩ : ↥(latticeCocycles T.L))) ∧
  ∀ (i : ZMod n) (f : FF), DL W T i (μ i f) ∧ DL W T i (ν i f) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f) + (W.γ T (μ i f) - μ i f)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i f - qp W ^ a • μ i f ∈ W.N T

def ExtTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
      ∃ (N : ℕ) (y z : FF →ₗ[O] W.DD T₂) (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
        ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DdRFull
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

def DdRFull (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) →
    ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V

def DiRank (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (_Cm : CmpOf D.loc D.locA HW _F) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    IsCrys ((D.loc l).PD K) T.ρ → ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)),
      finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = finrank ↥LL.1 T.V

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.AlignN
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def tameList {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Option (Fin m × Bool) → (ZMod g)ˣ
  | none => 1
  | some (j, true) => χ j
  | some (j, false) => (χ j)⁻¹

def TameDistinct (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Prop :=
  Function.Injective (tameList χ) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB r g →
    Function.Injective (fun o => Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((tameList χ o : (ZMod g)ˣ) : ZMod g)))) ∧
  ∀ j, IsSquare (χ j)

def TameDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2) (v : (Fm.D x i).nd.PlG k),
    haveI : Fact ((Fm.D x i).host.g k).Prime := ⟨(Fm.D x i).host.g_prime k⟩
    TameDistinct (Fm.D x i).R.r ((Fm.D x i).host.g k) ((Fm.D x i).nd.chiT k v)

end Formalism.MainNotions
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
noncomputable section

namespace Formalism.MainNotions.UnusedSlot35.DssRec

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem rec_exists {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    (F : ℕ → M → M) (y₀ : M) : ∃ s : ℕ → M, s 0 = y₀ ∧ ∀ k, p • s (k + 1) = F k (s k) := by
  obtain ⟨u, hu⟩ := hp
  let s : ℕ → M := fun k => Nat.rec y₀ (fun k sk => ((u⁻¹ : Eˣ) : E) • F k sk) k
  refine ⟨s, rfl, fun k => ?_⟩
  show p • (((u⁻¹ : Eˣ) : E) • F k (s k)) = F k (s k)
  rw [← algebraMap_smul E p, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem smul_inj {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    {a b : M} (h : p • a = p • b) : a = b := by
  obtain ⟨u, hu⟩ := hp
  have h' : (u : E) • a = (u : E) • b := by
    rw [hu, algebraMap_smul, algebraMap_smul]
    exact h
  have := congrArg (fun m => ((u⁻¹ : Eˣ) : E) • m) h'
  simpa [smul_smul] using this

theorem rec_unique {R E O M : Type} [CommRing R] [CommRing E] [CommRing O] [Algebra R E]
    [AddCommGroup M] [Module R M] [Module E M] [Module O M] [IsScalarTower R E M] (p : R)
    (hp : IsUnit (algebraMap R E p)) (c : ℕ → O) (Gm : M → M) (L : ℕ) (s s' : ℕ → M)
    (h0 : s 0 = s' 0)
    (hs : ∀ k, k < L → p • (s (k + 1) + c k • s k) = Gm (s k))
    (hs' : ∀ k, k < L → p • (s' (k + 1) + c k • s' k) = Gm (s' k)) :
    ∀ k, k ≤ L → s k = s' k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have ih' := ih (by omega)
    have h1 := hs k (by omega)
    have h2 := hs' k (by omega)
    rw [← ih'] at h2
    have := smul_inj (E := E) p hp (h1.trans h2.symm)
    exact add_right_cancel this

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem π₀_unit (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨w, hw⟩ := ((h9 T hT hA.2.1 hA.2.2).2.2 hK).1.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def DssMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (Y : ℕ) (y₀ : W.DD T), Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi)
            (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • seq k) = W.γD T W.gam (seq k) - seq k) →
        seq (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length ∈ W.N T

theorem coreDss_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.LiftingTheory.coreDss W ↔ DssMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ s hs0 hrec⟩

def DssLetMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (i : ZMod n) (y' Y : ℕ) (y₀ : W.DD T), y' ≤ Y → Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.Nl T i →
      (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) →
        Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length ∈ W.Nl T i

theorem dssLet_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.RamifiedCoefficientChains.DssLet W ↔ DssLetMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ s hs0 hrec⟩

end Core

end Formalism.MainNotions.UnusedSlot35.DssRec
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LiftFOf
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem lc_pow (I : BaseId W) (e : ℕ) :
    I.Bs.lc ^ e = PowerSeries.C (((PD.p : ℕ) : O) ^ e) := by
  unfold Formalism.ExponentWindows.E.Base.lc
  rw [I.ℓ_eq, map_pow]

theorem map_mem_Z1DΔ (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) ∈ W.wachCocyclesDelta T₂ := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  show (W.map F x, W.map F y) ∈ W.wachCocyclesDelta T₂
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Formalism.BasicNotions.herrCocycles, Submodule.mem_inf,
    LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, ← map_neg, ← map_add (f := _), h1, map_zero]
  · have h3 := h2 d hd
    rw [← W.map_γ, ← W.map_γ]
    simp only [Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at h3 ⊢
    exact ⟨by rw [h3.1], by rw [h3.2]⟩

end Formalism.MainNotions.WachCoordinates.Br
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.InvariantsIsoOfGenerators
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

section Gen

variable (S : Sit)

def oneT (T : LocLat S.G S.Qp S.LL S.O) : ↥T.L.T →ₗ[S.O] TW S.RW T :=
  TensorProduct.mk S.O S.RW ↥T.L.T 1

def OneInj : Prop := ∀ T : LocLat S.G S.Qp S.LL S.O, Function.Injective (oneT S T)

def GenFix : Prop :=
  ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T),
    (∀ g, S.W.resΓ g = S.W.gamK → T.actT g t = t) →
    (∀ g, S.W.resΓ g ∈ S.W.DelF → T.actT g t = t) →
    (∀ g, S.W.resΓ g = 1 → T.actT g t = t) → ∀ g, T.actT g t = t

variable {S}

theorem oneT_apply (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) : oneT S T t = (1 : S.RW) ⊗ₜ[S.O] t := rfl

theorem TWact_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (g : S.G) (t : ↥T.L.T) : TWact f T g ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] T.actT g t := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem TWmap_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (t : ↥T.L.T) : TWmap f T ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] t := by
  simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

theorem mem_H0Lat {T : LocLat S.G S.Qp S.LL S.O} (t : ↥T.L.T) : t ∈ invariantLattice T ↔ ∀ g, T.actT g t = t := by
  simp only [invariantLattice, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  first
  | rfl
  | exact Iff.rfl
  | (constructor <;> intro h g <;> exact h g)

theorem mem_fixDD {T : LocLat S.G S.Qp S.LL S.O} (x : S.W.DD T) : x ∈ fixDD S.W T ↔
    S.W.φD T x = x ∧ S.W.γD T S.W.gamK x = x ∧ ∀ δ ∈ S.W.DelF, S.W.γD T δ x = x := by
  simp only [fixDD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc]

private theorem nonempty_invariantLattice_equiv_fixDD (E : S.Comparison₂)
    (hin : ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T), (∀ g, T.actT g t = t) →
      (1 : S.RW) ⊗ₜ[S.O] t ∈ Set.range (E.jD T))
    (hfix : ∀ (T : LocLat S.G S.Qp S.LL S.O) (b : TW S.RW T), TWmap S.φR T b = b →
      ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t)
    (hi : OneInj S) (hg : GenFix S) (T : LocLat S.G S.Qp S.LL S.O) :
    Nonempty (↥(invariantLattice T) ≃ₗ[S.O] ↥(fixDD S.W T)) := by

  have key : (invariantLattice T).map (oneT S T) = (fixDD S.W T).map (E.jD T) := by
    ext b
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_H0Lat] at ht
      obtain ⟨d, hd⟩ := hin T t ht
      refine ⟨d, ?_, ?_⟩
      · rw [mem_fixDD]
        refine ⟨?_, ?_, ?_⟩
        · apply E.jD_inj T
          rw [E.jD_φ, hd, TWmap_one]
        · obtain ⟨g, hgg⟩ := S.W.resΓ_onto S.W.gamK
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
        · intro δ _
          obtain ⟨g, hgg⟩ := S.W.resΓ_onto δ
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
      · rw [oneT_apply, hd]
    · rintro ⟨d, hd, rfl⟩
      rw [mem_fixDD] at hd
      obtain ⟨hφ, hγ, hδ⟩ := hd
      obtain ⟨t, ht⟩ := hfix T (E.jD T d) (by rw [← E.jD_φ, hφ])
      have hact : ∀ g : S.G, S.W.γD T (S.W.resΓ g) d = d → T.actT g t = t := by
        intro g hgd
        apply hi T
        rw [oneT_apply, oneT_apply, ← TWact_one (S.gR g), ← ht, ← E.jD_act, hgd]
      refine ⟨t, ?_, ?_⟩
      · rw [mem_H0Lat]
        apply hg T t
        · intro g hgK
          exact hact g (by rw [hgK, hγ])
        · intro g hgD
          exact hact g (hδ _ hgD)
        · intro g h1
          exact hact g (by rw [h1, S.W.γD_one])
      · rw [oneT_apply, ht]
  exact ⟨(Submodule.equivMapOfInjective (oneT S T) (hi T) (invariantLattice T)).trans
    ((LinearEquiv.ofEq _ _ key).trans
      (Submodule.equivMapOfInjective (E.jD T) (E.jD_inj T) (fixDD S.W T)).symm)⟩

end Gen

theorem invariants_iso_of_generators (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hi : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      OneInj (sit D.loc HW l (D.locA l) K 1 LL hA.2.2))
    (hg : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GenFix (sit D.loc HW l (D.locA l) K 1 LL hA.2.2)) :
    H0InvariantsTheorem D HW F := by
  intro hF l hl K LL hA T
  obtain ⟨hW, hD⟩ := hF l K 1 LL hA.2.2
  refine nonempty_invariantLattice_equiv_fixDD (S := sit D.loc HW l (D.locA l) K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie
    (fun T t ht => ?_) (fun T b hb => (hW T).2.1 b hb) (hi l K LL hA) (hg l K LL hA) T

  refine Set.mem_range.mpr (LinearMap.mem_range.mp ((hD T).2 _ ?_ ?_))
  · intro g _
    rw [TWact_one, ht g]
  · rw [TWmap_one, sub_self]
    exact Submodule.zero_mem _

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGCut

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lemG_sig (l H : ℕ) : ℕ := ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∃ (x la : W.DD T₂) (hP : LemGPair W T₂ b S η i x la),
        W.cmp T₂ ⟨x, hP.1⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

def LemGB [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
        ∃ y ∈ W.N T₁, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i y ∧ W.map F y = ((PD.p : O) ^ E) • x

theorem lemG_ceil_eq (l H E h b : ℕ) :
    (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ)⌉ : ℤ) =
      (E : ℤ) + ((lemG_sig l H : ℤ) + (h : ℤ) - (b : ℤ)) := by
  have hs : Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H = ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2]
    push_cast
    ring
  have h0 : 0 ≤ ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc : ((lemG_sig l H : ℕ) : ℤ) = ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉ := by
    unfold lemG_sig
    exact Int.natCast_ceil_eq_ceil h0
  rw [show (E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ) =
      (((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1) + (((E : ℤ) + h - b : ℤ) : ℝ) by
        rw [hs]; push_cast; ring,
    Int.ceil_add_intCast, ← hc]
  ring

theorem lemmaGs_of_lemGAB [NeZero n] (W : LocWach PD LL O v n) (hA : LemGA W) (hB : LemGB W) :
    LemmaGs W := by
  intro d T₁ T₂ F b S η m hset i hi
  obtain ⟨E, hEb, hEx⟩ := hB d T₁ T₂ F b S η m hset i hi
  refine ⟨E, hEb, ?_⟩
  rintro _ ⟨_, ⟨y, hy, hyD, rfl⟩, rfl⟩ hfil
  obtain ⟨x, la, hP, hcmp⟩ := hA d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨y1, hy1N, hy1D, hmap⟩ := hEx x la hP
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hset.2.2.2.2.1
    haveI : NeZero PD.p := ⟨by have := hset.2.1; omega⟩
    exact hζ.neZero'.out
  have hnat : ((PD.p : ℕ) : O) ^ E • x = (PD.p ^ E : ℕ) • x := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hx' : W.map F y1 ∈ W.N T₂ := by
    rw [hmap, hnat]
    exact nsmul_mem hP.1 _
  refine ⟨y1, hy1N, hx', hy1D, ?_⟩
  rw [lemG_ceil_eq, zpow_add₀ hp0, mul_smul, ← hcmp]
  have hsub : (⟨W.map F y1, hx'⟩ : W.N T₂) = (PD.p ^ E : ℕ) • (⟨x, hP.1⟩ : W.N T₂) :=
    Subtype.ext (by show W.map F y1 = (PD.p ^ E : ℕ) • x; rw [hmap, hnat])
  rw [hsub, map_nsmul, zpow_natCast, ← Nat.cast_smul_eq_nsmul LL, Nat.cast_pow]

def LemGLa [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (y la : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (i - 2) 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η)) y la ∧
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i la ∧
    Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA_la [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ y : W.DD T₂, y ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∃ la : W.DD T₂, LemGLa W T₂ b S η i y la

def GammaActionLemma [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
        ∃ x : W.DD T₂, x ∈ W.N T₂ ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x ∧
          Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la

def LemGA_0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
      ∀ (x : W.DD T₂) (hx : x ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x →
        Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la →
        W.cmp T₂ ⟨x, hx⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

theorem lemGA_of_pieces [NeZero n] (W : LocWach PD LL O v n) (hla : LemGA_la W) (hx : GammaActionLemma W)
    (h0 : LemGA_0 W) : LemGA W := by
  intro d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨la, hla⟩ := hla d T₁ T₂ F b S η m hset i hi y hy hyD
  obtain ⟨x, hxN, hxD, hxeq⟩ := hx d T₁ T₂ F b S η m hset i hi y hy hyD hfil la hla
  exact ⟨x, la, ⟨hxN, hxD, hxeq, hla.2.2.2⟩,
    h0 d T₁ T₂ F b S η m hset i hi y hy hyD la hla x hxN hxD hxeq⟩

end LemGCut

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.KillerSecondTheoremHolds
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem killer_first_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) :
    KillerWithConstantTheorem D HW F C := by
  intro hA
  obtain ⟨hL, hP⟩ := hA
  exact Formalism.MainNotions.ArcLiftingSetup.pi_stability_content_clause D HW F hC hL (fun l _ K LL hG hc h5 =>
    hP l K LL hc h5 ((HW l).W K 1 LL hG).gam)

theorem killer_second_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : KillerWachCoordinatesTheorem D HW F := by
  intro hP
  exact Formalism.MainNotions.WachCoordinates.killer_conditions_of_stable D HW F hP

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CardBasisEq
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem finrank_lat [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    finrank O ↥T.L.T = finrank LL T.V := by
  have := T.L.free
  have hfg : Module.Finite O ↥T.L.T := ⟨(Submodule.fg_top _).mpr T.L.fg⟩
  let e := Module.Free.chooseBasis O ↥T.L.T
  let w : Module.Free.ChooseBasisIndex O ↥T.L.T → T.V := fun j => (e j : T.V)
  have hli : LinearIndependent O w := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli' : LinearIndependent LL w := (LinearIndependent.iff_fractionRing O LL).mp hli
  have hspO : Submodule.span O (Set.range w) = T.L.T := by
    have : Set.range w = T.L.T.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    rw [← T.L.span, Submodule.span_le]
    intro x hx
    rw [← hspO] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' hsp), Module.finrank_eq_card_chooseBasisIndex]

theorem card_basis_eq [Nontrivial O] [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) {r : ℕ} (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    r = finrank O ↥T.L.T := by
  classical
  let w : Fin r → ↥(W.N T) := fun j => ⟨b j, hb j⟩
  have hli : LinearIndependent (LetA O n) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : (0 : W.DD T) = ∑ j, g j • b j := by
      have := congrArg Subtype.val hg
      simpa [w, Submodule.coe_sum] using this.symm
    have h1 : (0 : W.DD T) = ∑ j, (0 : Fin r → LetA O n) j • b j := by simp
    obtain ⟨a, _, ha⟩ := huniq 0 (W.N T).zero_mem
    have e1 := ha g h0
    have e2 := ha 0 h1
    intro j
    rw [e1, ← e2]; rfl
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • w j := by
      apply Subtype.ext
      simp [w, Submodule.coe_sum, ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := (W.N_base T hT).basis bN
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  have h1 := Module.finrank_eq_card_basis bD
  rw [(W.DD_free T).2, Fintype.card_fin] at h1
  exact h1.symm

end

end Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN
end
end
