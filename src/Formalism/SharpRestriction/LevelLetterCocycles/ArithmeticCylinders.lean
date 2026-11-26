module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Filter Topology
open scoped ComplexOrder

variable (D : D7)

def PointsLemma : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ σ : D.what₂.FT, D.nd.goodRow σ →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v)) →
    D.ntypes.cuspidal σ ∧ ∀ w : D.what₂.places.Pl,
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) ⊤ ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) Hs) ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ≠ D.host.g k →
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ),
          u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹ →
          ¬ (Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) _)).IsRoot
            (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((u : ZMod (D.host.g k)))))))

def TheoremThreePrime : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, Formalism.MainNotions.N.HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    Formalism.MainNotions.N.goodSig D.nd D.naut Sig →
    Formalism.MainNotions.N.IsCuspIso D.nd D.naut Sig ∧
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) ⊤ ∧
      (∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) Hs) ∧
      (∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ w ∈ placesOver D.host.E (D.host.g k),
        Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ¬ (((Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ (D.nd.gam0 i w) :
              GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
          (D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (Formalism.MainNotions.N.chi1 D.nd i (D.nd.gam0 i w)))))

def atPlace (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    MonoidAlgebra ℂ (G0g D.nd) := by
  classical
  exact MonoidAlgebra.ofCoeff (Finsupp.mapDomain
    (fun h => Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      ⟨k, v⟩ h)
    a.coeff)

def labAct (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Classical.epsilon fun f' : (ZMod (D.host.g k))[X] => f'.Monic ∧
    Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (τ (D.ntypes.teichC k x)))

def IsLabel (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0

def dualLab (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  Polynomial.C (f.coeff 0)⁻¹ * f.reverse

abbrev Tup (k : Fin 2) : Type := D.nd.PlG k → (ZMod (D.host.g k))[X]

abbrev Tup2 : Type := ∀ k : Fin 2, D.nd.PlG k → (ZMod (D.host.g k))[X]

def cyl (k : Fin 2) (S : Set (Tup D k)) : Set (Tup2 D) := {t | t k ∈ S}

def wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X]) : ℝ :=
  ((a * D.ntypes.eSer k f).coeff 1).re / (a.coeff 1).re

structure AllRows (D : D7) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin D.what₂.Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin D.what₂.Drows → Fin D.what₂.Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D}

def AllRows.dimT (A : AllRows D) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def LabelCountGoodInjective (A : AllRows D) : Prop :=
  (∀ S : Set (Tup2 D), A.dimT S = Nat.card {τ : Fin D.what₂.Dall // (fun k => A.labAll k τ) ∈ S}) ∧
    Function.Injective A.inc ∧ (∀ k σ, A.labAll k (A.inc σ) = D.nd.lab k (D.what₂.ft σ)) ∧
    ∀ τ : Fin D.what₂.Dall, D.ntypes.goodTuple (fun k => A.labAll k τ) ↔ τ ∈ Set.range A.inc

variable (D)

def TieAdmG : Prop := ∀ k, D.ntypes.admissible (D.host.g k)

abbrev VecAt : Type :=
  ∀ k : Fin 2, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))

def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹

def eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N IsUniUp (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

def phiJ {g : ℕ} (kk s : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : ZMod g :=
  (∑ i ∈ Finset.range (s - 1), entN M i (i + 1)) +
    (if 1 ≤ s then entN M (s - 1) (s + kk) + entN M (s + kk) (s + kk + 1) else 0) +
    (∑ i ∈ Finset.range (s - 1), entN M (s + kk + 1 + i) (s + kk + 2 + i)) +
    ∑ a ∈ Finset.range (kk - 1), entN M (s + a) (s + a + 1)

def eJ (g N : ℕ) [NeZero g] (kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0) (phiJ kk s) ψ₀

def eUk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eU (D.host.g k) D.R.r ψ₀

def eJk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

def admLq : Prop :=
  ∀ (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ), ψ₀ ≠ 1 →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∀ f, 0 ≤ wtOf D k (eUk D k ψ₀) f ∧ 0 ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eUk D k ψ₀) f =
        1 / ((UniqueFactorizationMonoid.normalizedFactors f).map
          (fun P => (D.host.g k : ℝ) ^ P.natDegree - 1)).prod) ∧
    (∀ f, IsLabel D k f → (1 - 1 / (D.host.g k : ℝ)) * wtOf D k (eUk D k ψ₀) f ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eJk D k ψ₀) f ≤
        (1 + 1 / (D.host.g k : ℝ)) ^ D.R.r * wtOf D k (eUk D k ψ₀) f)

def goodAt (k : Fin 2) (t : Tup D k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (D.nd.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (fun v j => (D.nd.chiT k v j)⁻¹)

def locShare (eV : VecAt D) (k : Fin 2) (S : Finset (Tup D k)) : ℝ :=
  ∑ t ∈ S, ∏ v, wtOf D k (eV k v) (t v)

variable {D}

variable (D)

end Formalism.MainNotions.ArithmeticCylinders
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]


variable (D)

end Formalism.MainNotions.SphericalInertData

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
noncomputable section

namespace Formalism.MainNotions.N

def LocsCoverTw (D : Formalism.BasicNotions.D7) : Prop := ∀ j' w', 1 ≤ j' → j' ≤ D.R.m → D.what₂.muAt w' ≠ D.what₂.mu0 →
  ∑ i ∈ D.nd.locs j' w', Module.finrank (D.nd.O i) (D.nd.Mt i) =
    Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w') j')

end Formalism.MainNotions.N

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
noncomputable section

namespace Formalism.MainNotions.BlochKatoDuality

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

section Rep

variable {G : Type} [Group G] {LL : Type} [Field LL]

def IsSubSumOf {W A B : Type} [AddCommGroup W] [Module LL W] [AddCommGroup A] [Module LL A]
    [AddCommGroup B] [Module LL B] (ρW : Representation LL G W) (ρA : Representation LL G A)
    (ρB : Representation LL G B) : Prop :=
  ∃ (a b : ℕ) (p : Fin a → W →ₗ[LL] A) (q : Fin b → W →ₗ[LL] B),
    (∀ i g w, p i (ρW g w) = ρA g (p i w)) ∧ (∀ j g w, q j (ρW g w) = ρB g (q j w)) ∧
    ∀ w, (∀ i, p i w = 0) → (∀ j, q j w = 0) → w = 0

end Rep

section Push

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {X : Type} [AddCommGroup X] [Module LL X] [Module Qp X] [IsScalarTower Qp LL X]
    [Module O X] [IsScalarTower O LL X] {ρX : Representation LL G X}
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    [Module O U] [IsScalarTower O LL U] {ρU : Representation LL G U}
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul LL X]

def IsGMapD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T)) :
    Prop :=
  ∀ g y, φ (actT LY g y) = repD LT g (φ y)

def pushD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T))
    (y : ↥(latticeCocycles LY)) : G → U ⧸ LT.T :=
  fun g => φ (evT LY g y)

end Push

section Stmts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

def LiftAll (A Bt : GRep G Qp LL O) (e : ℕ) : Prop :=
  ∀ W₁ W₂ : GRep G Qp LL O, IsSubSumOf W₁.ρ A.ρ Bt.ρ → IsSubSumOf W₂.ρ A.ρ Bt.ρ →
    ∀ (L₁ : Lattice (O := O) W₁.ρ) (L₂ : Lattice (O := O) W₂.ρ) (F : LatHom L₁ L₂),
      F.Onto → F.LiftF PD e

def spanPush (X U : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) : Submodule O (G → U.V ⧸ LT.T) :=
  Submodule.span O {c | ∃ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (_ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)), (y : G → X.V) ∈ latticeFiniteCocycles PD LY ∧ c = pushD LY LT φ y}

def lenMod {M : Type} [AddCommGroup M] [Module O M] (S H : Submodule O M) : ℕ∞ :=
  Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype)

end Stmts

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

def Hyp {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL] (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ)
    (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL) (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ) (e : ℕ) : Prop :=
  IsTwistRep χ⁻¹ V.ρ X.ρ ∧ IsDR PD U.ρ ∧ IsDual1 PD X.ρ X'.ρ PX ∧
    IsDualLat1 PD LT LT' PU ∧ (LiftAll PD X U e ∨ (IsDR PD X.ρ ∧ LiftAll PD X' U' e))

def ArcTheoremGlobal : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∀ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)), IsGMapD LY LT φ →
  ∀ y : ↥(latticeCocycles LY), (y : G → X.V) ∈ latticeFiniteCocycles PD LY →
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT

def PushoutSpanLengthBound : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∃ m k : ℕ, lenMod (spanPush PD X U LT) (HfD PD LT) = m ∧ lenOl PD (O := O) = k ∧
    m ≤ e * (finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T) * k

end Main

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

end Bridge

section Packet

open Formalism.BasicNotions

def Conclusion1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), ArcTheoremGlobal ((D.loc l).PD K)

def Conclusion2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), PushoutSpanLengthBound ((D.loc l).PD K)

def adm1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkACore ((D.loc l).PD K)

def adm2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkBCore ((D.loc l).PD K)

def adm3 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), LocalTateTopDegree ((D.loc l).PD K)

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), cycIntCore ((D.loc l).PD K)

def adm5 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), TateFiniteness ((D.loc l).PD K)

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), drDualCore ((D.loc l).PD K)

end Packet

end Formalism.MainNotions.BlochKatoDuality
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

structure PtGeo (l : ℕ) [Fact l.Prime] (Λ : Type) [AddCommGroup Λ] (σ : Type) where

  BB : Type
  [acgBB : AddCommGroup BB]
  tor_fin : ∀ N : ℕ, N ≠ 0 → Finite {z : BB // N • z = 0}

  Sec : ℕ → Type
  [acgSec : ∀ k, AddCommGroup (Sec k)]
  [modSec : ∀ k, Module ℂ_[l] (Sec k)]
  s : Sec 1

  nrm : ∀ k, Sec k → BB → ℝ
  nrm_nonneg : ∀ k F x, 0 ≤ nrm k F x
  nrm_smul : ∀ k (c : ℂ_[l]) F x, nrm k (c • F) x = ‖c‖ * nrm k F x
  nrm_add : ∀ k F F' x, nrm k (F + F') x ≤ max (nrm k F x) (nrm k F' x)

  pull : ∀ N : ℕ, Sec 1 →ₗ[ℂ_[l]] Sec (N ^ 2)
  pull_isom : ∀ N : ℕ, N ≠ 0 → ∀ F x, nrm (N ^ 2) (pull N F) x = nrm 1 F (N • x)

  Up : ∀ N : ℕ, BB → (Sec (N ^ 2) ≃ₗ[ℂ_[l]] Sec (N ^ 2))
  Up_fin : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ m : ℕ, m ≠ 0 ∧ (Up N z) ^ m = 1

  Up_cube : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ ph : BB → ℝ,
    (∀ F x, nrm (N ^ 2) (Up N z F) x = Real.exp (ph x) * nrm (N ^ 2) F (x + z)) ∧
    (∃ C, ∀ x, |ph x| ≤ C) ∧
    ∃ c, ∀ x x' x'', ph (x + x' + x'') - ph (x + x') - ph (x + x'') - ph (x' + x'') + ph x + ph x' + ph x''
      - ph 0 = c

  Gt : Type
  [acgGt : AddCommGroup Gt]
  Y : Type
  [acgY : AddCommGroup Y]
  per : Y →+ Gt
  unif : Gt →+ BB

  YR : Type
  [acgYR : AddCommGroup YR]
  [modYR : Module ℝ YR]
  iY : Y →+ YR
  Bf : YR →ₗ[ℝ] YR →ₗ[ℝ] ℝ
  w0 : YR →ₗ[ℝ] YR
  w0b : YR →ₗ[ℝ] YR

  chr : Y → Gt → ℂ_[l]
  cst : Y → ℂ_[l]
  trop : Gt →+ YR

  SecM : Type
  [acgSecM : AddCommGroup SecM]
  [modSecM : Module ℂ_[l] SecM]
  nrmM : SecM → Gt → ℝ
  nrmM_smul : ∀ (c : ℂ_[l]) F g, nrmM (c • F) g = ‖c‖ * nrmM F g
  nrmM_add : ∀ F F' g, nrmM (F + F') g ≤ max (nrmM F g) (nrmM F' g)
  up : Sec 1 →ₗ[ℂ_[l]] SecM
  be : SecM
  trY : Y → SecM →ₗ[ℂ_[l]] SecM

  Co : Type
  [finCo : Fintype Co]
  ser : ∀ k, Sec k →ₗ[ℂ_[l]] MvPowerSeries Co ℂ_[l]

  H : Type
  [acgH : AddCommGroup H]
  [modH : Module ℂ_[l] H]
  HO : AddSubgroup H
  HO_smul : ∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∀ h ∈ HO, c • h ∈ HO
  Fil : Submodule ℂ_[l] H
  curv : H →ₗ[ℂ_[l]] H →ₗ[ℂ_[l]] ℂ_[l]

  Gm : ℕ → Type
  [acgGm : ∀ k, AddCommGroup (Gm k)]
  [modGm : ∀ k, Module ℂ_[l] (Gm k)]
  germ : ∀ k, Sec k →ₗ[ℂ_[l]] Gm k
  pullG : ∀ N : ℕ, Gm 1 →ₗ[ℂ_[l]] Gm (N ^ 2)
  pullG_germ : ∀ N F, pullG N (germ 1 F) = germ (N ^ 2) (pull N F)
  pullG_inj : ∀ N : ℕ, N ≠ 0 → Function.Injective (pullG N)
  ev0 : ∀ k, Gm k →ₗ[ℂ_[l]] ℂ_[l]
  ev_zero_pull_square : ∀ N G, ev0 (N ^ 2) (pullG N G) = ev0 1 G
  IntG : ∀ k, AddSubgroup (Gm k)
  IntG_smul : ∀ k (c : ℂ_[l]), ‖c‖ ≤ 1 → ∀ G ∈ IntG k, c • G ∈ IntG k
  integral_ev_zero_norm_le_one : ∀ k, ∀ G ∈ IntG k, ‖ev0 k G‖ ≤ 1
  IntG_iff : ∀ k F, germ k F ∈ IntG k ↔ ∀ m, ‖MvPowerSeries.coeff m (ser k F)‖ ≤ 1

  nab : ∀ k, H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm k)
  nabD : H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm 1)

  EL : Set (σ → H)
  lf : σ → H
  lf_mem : lf ∈ EL

  half : ℕ → BB → BB
  half_spec : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 → N • half N z = z
  Uz : ℕ → BB → Gm 1
  Uz_def : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 →
    pullG N (Uz N z) = germ (N ^ 2) (Up N (half N z) (pull N s))

  kr : ℕ → Λ → BB → ℂ_[l]
  kr_per : ∀ (N : ℕ) x w z, kr N (x + N • w) z = kr N x z
  kr_int : ∀ N x z, ‖kr N x z‖ ≤ 1

  key : ℂ_[l]
  key_ne : key ≠ 0

attribute [instance] PtGeo.acgBB PtGeo.acgSec PtGeo.modSec PtGeo.acgGt PtGeo.acgY PtGeo.acgYR PtGeo.modYR
  PtGeo.acgSecM PtGeo.modSecM PtGeo.finCo PtGeo.acgH PtGeo.modH PtGeo.acgGm PtGeo.modGm

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

def mon {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (m : σ →₀ ℕ) : Module.End ℂ_[l] (X.Gm k) :=
  (ord.map fun u => (Dl (L u)) ^ (m u)).prod

def PN {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (P : MvPolynomial σ ℂ_[l]) (g : X.Gm k) : ℂ_[l] :=
  ∑ m ∈ P.support, P.coeff m * X.ev0 k (X.mon ord Dl L m g)

def hat (N e : ℕ) (φ : Λ → ℂ_[l]) (z : X.BB) : ℂ_[l] :=
  ((N : ℂ_[l]) ^ e)⁻¹ * ∑ᶠ c : Λ ⧸ (nsmulAddMonoidHom (α := Λ) N).range,
    φ (Quotient.out c) * X.kr N (Quotient.out c) z

def fG (N e : ℕ) (φ : Λ → ℂ_[l]) : X.Gm 1 :=
  ∑ᶠ z : {z : X.BB // N • z = 0}, X.hat N e φ z.1 • X.Uz N z.1

end PtGeo

variable (D : Formalism.BasicNotions.D7)

def Per {L V : Type} [AddCommGroup L] (n : ℕ) (φ : L → V) : Prop :=
  ∀ x z : L, φ (x + (n : ℤ) • z) = φ x

def PerI {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]
    (I : Ideal (𝓞 E)) (φ : L → V) : Prop :=
  ∀ x : L, ∀ y ∈ I • (⊤ : Submodule (𝓞 E) L), φ (x + y) = φ x

def ConjPl (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) → (x ∈ P.asIdeal ↔ y ∈ P'.asIdeal)

def VacOff {L V : Type} [AddCommGroup L] [Module (𝓞 D.host.E) L] (φ : L → V) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), ¬ IsSplitPl D.host w →
    ∃ I : Ideal (𝓞 D.host.E), IsCoprime I w.asIdeal ∧ PerI I φ

def SplitLev (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    IsSplitPl D.host w


open scoped Classical in
def vdd (l : ℕ) : ℝ :=
  ⨆ v : placesOver D.host.E l,
    ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 D.host.E))).count
        (v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal : ℝ) /
      ((v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal.ramificationIdx ℤ : ℝ)

variable {D}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

def iO (i : D.ntw.Tw) : D.ntw.O i →+* ℂ_[D.ntw.l i] :=
  (D.nth.iC i).comp (algebraMap (D.ntw.O i) (KK i))

def GalF (i : D.ntw.Tw) (F : Subfield (KK i)) : Set (RingAut ℂ_[D.ntw.l i]) :=
  {s | (∀ x, ‖s x‖ = ‖x‖) ∧ ∀ x ∈ F, s (D.nth.iC i x) = D.nth.iC i x}


variable (D) in
structure Geo where

  pt : ∀ i j (_ : D.nth.Pt i j), PtGeo (D.ntw.l i) (D.nth.Lt i j) (D.nth.Let i j)

  ord : ∀ i j, List (D.nth.Let i j)
  ord_nodup : ∀ i j, (ord i j).Nodup
  ord_mem : ∀ i j u, u ∈ ord i j

  thV_def : ∀ i j (φ : D.nth.Lt i j → KK i) (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i))
    (y : D.nth.Pt i j) (n : ℕ), Odd n → Nat.Coprime n (D.ntw.l i) → SplitLev D n →
    Per (D.ntw.l i ^ D.nth.aL i * n) φ →
    D.nth.thV i j φ P y = (pt i j y).key * (pt i j y).PN (ord i j) (pt i j y).nabD (pt i j y).lf
      (P.map (iO i)) ((pt i j y).fG (D.ntw.l i ^ D.nth.aL i * n) (2 * D.R.f * D.R.r * D.R.nV)
        (fun x => D.nth.iC i (φ x)))

  det_actK : ∀ i j P P', ConjPl D P P' → ∀ (k : D.nth.Kq i j P) (y : D.nth.Pt i j) {A : Type} [CommGroup A]
    (χ : G D.host.E D.nd.Om →* A), IsOpen (χ.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc χ →
    (∀ v, v = P ∨ v = P' → ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B v →
      ∀ σ ∈ Ine (F := D.host.E) B, χ σ = 1) →
    χ (D.nth.recDet i j (D.nth.actK i j P k y)) = χ (D.nth.recDet i j y)

  Ks : ∀ i : D.ntw.Tw, Subfield (KK i)
  Ks_le : ∀ i, Ks i ≤ D.nth.MaximalUnramifiedExtension i
  Ks_E : ∀ i (τ : D.host.E →+* ℂ_[D.ntw.l i]) (x : D.host.E), ∃ z ∈ Ks i, D.nth.iC i z = τ x
  Ks_zeta : ∀ i k, D.ntw.l i = D.host.g k → ∃ z ∈ Ks i, IsPrimitiveRoot z (D.ntw.l i)

  actG : ∀ i j, RingAut ℂ_[D.ntw.l i] → D.nth.Pt i j → D.nth.Pt i j
  actG_one : ∀ i j y, actG i j 1 y = y
  actG_mul : ∀ i j, ∀ s ∈ GalF i (Ks i), ∀ t ∈ GalF i (Ks i), ∀ y,
    actG i j (s * t) y = actG i j s (actG i j t y)

  tB : ∀ i j s y, (pt i j y).BB →+ (pt i j (actG i j s y)).BB
  tB_bij : ∀ i j s y, Function.Bijective (tB i j s y)
  tH : ∀ i j s y, (pt i j y).H →+ (pt i j (actG i j s y)).H
  tH_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) h, tH i j s y (c • h) = s c • tH i j s y h
  tG : ∀ i j s y, (pt i j y).Gm 1 →+ (pt i j (actG i j s y)).Gm 1
  tG_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) g, tG i j s y (c • g) = s c • tG i j s y g

  FQ : ∀ i j, Bool → Finset (HeightOneSpectrum (𝓞 D.host.E)) → Submodule ℂ_[D.ntw.l i] (D.nth.Pt i j → ℂ_[D.ntw.l i])

  Fm_desc : ∀ i j b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) → ∀ F : D.nth.Pt i j → ℂ_[D.ntw.l i],
    (∃ f, D.nth.ev i j b f = F) ↔ F ∈ FQ i j b QP ∧ (∀ s ∈ GalF i ⊤, ∀ y, F (actG i j s y) = s (F y)) ∧
      ∀ P ∈ QP, ∀ (k : D.nth.Kq i j P) y, F (D.nth.actK i j P k y) = F y

  FmUr_def : ∀ i j b (f : D.nexp.Fm i j b), f ∈ D.nth.FmUr i j b ↔
    ∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, D.nth.ev i j b f (actG i j s y) = s (D.nth.ev i j b f y)





variable (X : Geo D)


end Formalism.MainNotions.ExistsIdealDenominator
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FontExAll
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FontExAll (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (hG : Good K s LL)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π →
    Function.Injective (((HW l).W K s LL hG).map ι) ∧ Function.Surjective (((HW l).W K s LL hG).map π) ∧
      ∀ x, ((HW l).W K s LL hG).map π x = 0 ↔ ∃ y, ((HW l).W K s LL hG).map ι y = x

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.N

def WildTriv : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → v ∉ placesOver E l →
    ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ g, ∃ n : ℕ, φ g ^ (l ^ n) = 1) →
    ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → φ σ = 1

theorem qpow_of_tw (hW : WildTriv) (D : D7) (i : D.nd.Loc) :
    ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n := by
  classical
  intro v hv g hg
  have hS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hgk : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    rw [D.nd.S_def i v]
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hpd : v ∉ D.ntw.pD (D.ntw.twOf i) := by
    intro hp
    have h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
    exact hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)
  have hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact hl
  have hchi : ∀ h ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 h = D.ntw.psiL i h := by
    intro h hh
    have h1 := D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hgk hpd (D.nd.plOm.1 v)
      (D.nd.plOm.2 v) h hh
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]
  rw [hchi g hg, hchi _ (D.nd.locNd_chebotarevPlace_mem i v)]
  obtain ⟨m, hm⟩ := D.ntw.psiL_ord i (D.nd.gam0 i v)
  have hL : 1 ≤ D.nd.l i ^ m := Nat.one_le_pow _ _ (Fact.out : (D.nd.l i).Prime).pos
  let H : Subgroup (G D.host.E D.nd.Om) :=
    { carrier := {x | ∃ n : ℕ, D.ntw.psiL i x = D.ntw.psiL i (D.nd.gam0 i v) ^ n}
      mul_mem' := by
        rintro a b ⟨n, hn⟩ ⟨k, hk⟩
        exact ⟨n + k, by rw [map_mul, hn, hk, pow_add]⟩
      one_mem' := ⟨0, by rw [map_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨n, hn⟩
        refine ⟨n * (D.nd.l i ^ m - 1), ?_⟩
        rw [map_inv, hn]
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, show n * (D.nd.l i ^ m - 1) + n = D.nd.l i ^ m * n by
          rw [mul_comm n, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hL], pow_mul, hm, one_pow] }
  have hker : (D.ntw.psiL i).ker ≤ H := fun x hx => ⟨0, by rw [pow_zero]; exact hx⟩
  have hopen : IsOpen (H : Set (G D.host.E D.nd.Om)) := Subgroup.isOpen_mono hker (D.ntw.psiL_open i)
  have hclosed : IsClosed (H : Set (G D.host.E D.nd.Om)) := H.isClosed_of_isOpen hopen
  have hgen : Subgroup.closure (insert (D.nd.gam0 i v) {σ : G D.host.E D.nd.Om | ∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 v).valuation (σ y / y - 1) < 1}) ≤ H := by
    rw [Subgroup.closure_le, Set.insert_subset_iff]
    refine ⟨⟨1, (pow_one _).symm⟩, fun σ hσ => ⟨0, ?_⟩⟩
    rw [pow_zero]
    exact hW D.host.E D.nd.Om (D.nd.l i) Fact.out v (D.nd.plOm.1 v) (D.nd.plOm.2 v) hl (D.nd.O i)ˣ
      (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) σ hσ
  have hT := (D.nd.restN_tameGenerator_generates i v (Or.inr hv)).2 hg
  exact closure_minimal hgen hclosed hT

end Formalism.MainNotions.N

end
end
