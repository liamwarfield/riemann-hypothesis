module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

def nlen (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  ((Module.length O M : ℕ∞) : ℝ≥0∞) / ((Module.length O (O ⧸ Ideal.span {(l : O)}) : ℕ∞) : ℝ≥0∞)

def vO (O : Type) [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ := nlen O l (O ⧸ Ideal.span {x})

section Exc

variable {D : D7} (L : SizeData₂ D)

def sgPlus : ℤ := ⌊2 * L.sc.b / LevelStarExponents.lStar L⌋

def baseSizes : Set ℝ :=
  {W | W = L.sc.b ∨ W = L.sc.w'' D.R.n ∨
    ∃ t : D.host.TT, W = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)}

def window (W : ℝ) : Set ℤ :=
  {n | W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)}

def Exc : Set ℕ :=
  {l | l.Prime ∧ LevelStarExponents.lStar L < (l : ℝ) ∧ ∃ W ∈ baseSizes L, ∃ n ∈ window L W, (l : ℤ) ∣ n}

end Exc

section HidaSetting

variable (D : D7) (i : D.nd.Loc)

def liftIx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def param (ρ : D.what₂.Tau) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (D.R.k - 1))).val.map (fun a => (D.hc ρ).v a) +
  (Finset.univ : Finset (Fin D.R.m)).val.map (fun a => -(D.hc ρ).b a) +
  (Finset.Icc 1 D.R.t).val.map
    (fun c : ℕ => -(D.hc ρ).e (liftIx D i) + ((D.R.t : ℚ) + 1) / 2 - (c : ℚ))

def embSide (ρ : D.what₂.Tau) (s : Bool) : D.host.E →+* ℂ :=
  if s then D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)
  else ComplexEmbedding.conjugate (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG))

def WeightTie : Prop :=
  ∃ s : Bool, ∀ ρ : D.what₂.Tau, ∃ c : ℚ,
    D.naut.infWt i (embSide D ρ s) = (param D i ρ).map (fun p => ((p + c : ℚ) : ℂ)) ∧
    D.naut.infWt i (embSide D ρ (!s)) = (param D i ρ).map (fun p => ((-(p + c) : ℚ) : ℂ))

def IsRankRPart (rπ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ (g : GE D.nd) (u : Fin D.R.nV → KK D.nd i),
      e ((((rπ g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
          (toK D.nd i)).mulVec u) =
        ((((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
            (toK D.nd i)).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def vCC (π : D.nd.X i) : ℝ≥0∞ :=
  ⨅ f ∈ D.nd.cc i, vO (D.nd.O i) (D.nd.l i) (((f : D.nd.T i) : D.nd.X i → D.nd.O i) π)

def sPi (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : ℝ≥0∞ :=
  nlen (D.nd.O i) (D.nd.l i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℝ≥0∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) : ℕ∞) : ℝ≥0∞)

def vClass : ℝ≥0∞ := (padicValNat (D.nd.l i) (NumberField.classNumber D.host.E) : ℝ≥0∞)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def epsQ : ℝ≥0∞ :=
  (D.R.t : ℝ≥0∞) * ∑ P ∈ D.nd.Q i, vO (D.nd.O i) (D.nd.l i) (zetaP D i P - 1)

end HidaSetting

def CongBound_at (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc,
    LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → D.nd.l i ∉ Exc L →
    WeightTie D i → HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), IsRankRPart D i (r π) ρ →
      vCC D i π ≤ sPi D i π ρ + shaSum D i + vClass D i + epsQ D i

theorem zetaP_eq (D : D7) (i : D.nd.Loc) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P ∈ D.nd.Q i) :
    zetaP D i P = D.nd.zeta i P := by
  have hl : P ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i P (Or.inr hP)
  have hS : P ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hP
  rw [D.nd.S_def] at hS
  have h1 : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) (D.nd.gam0 i P) = 1 := by
    refine D.ntw.twistCharacterFamily_unramified _ _ _ P ?_ ?_ ?_ (D.nd.plOm.1 P) (D.nd.plOm.2 P) _ (D.nd.locNd_chebotarevPlace_mem i P)
    · rw [D.ntw.twOf_l]; exact hl
    · intro k hk
      apply hS
      refine ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    · intro h
      apply hS
      have h' : P ∈ (D.ntw.pD (D.ntw.twOf i) : Set _) := h
      rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
      exact ⟨Or.inr (Or.inr h'), hl⟩
  unfold zetaP NData.zeta
  rw [D.ntw.chi_tw]
  simp [h1]

theorem lStar_pos {D : D7} (L : SizeData₂ D) : 0 < LevelStarExponents.lStar L := by
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
  have hn : (0 : ℝ) < D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    exact_mod_cast (by unfold Ranks.n; omega : 0 < D.R.n)
  have hx : 0 < L.sc.x := by have := L.sc.one_lt_alt; linarith
  have hL : 0 < L.sc.L := by unfold Scale.L; positivity
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hS := L.Sc_pos
  unfold LevelStarExponents.lStar
  positivity

theorem vO_l (D : D7) (i : D.nd.Loc) : vO (D.nd.O i) (D.nd.l i) (D.nd.l i : D.nd.O i) = 1 := by
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h0 : (D.nd.l i : D.nd.O i) ≠ 0 := by
    intro h
    have h1 : (D.nd.embK i) ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), h, map_zero]
    have h2 : ((D.nd.l i : ℕ) : D.what₂.LL) = 0 := (map_eq_zero _).1 h1
    exact hp.ne_zero (by exact_mod_cast h2)
  have hu : ¬ IsUnit (D.nd.l i : D.nd.O i) := by
    intro hu
    have hinj : Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro z hz
      by_contra hz0
      rw [PadicInt.unitCoeff_spec hz0, map_mul, map_pow, map_natCast] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact ((PadicInt.unitCoeff hz0).isUnit.map _).ne_zero h
      · exact h0 (pow_eq_zero_iff'.1 h).1
    haveI : FaithfulSMul ℤ_[D.nd.l i] (D.nd.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have : IsUnit ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) :=
      IsLocalHom.map_nonunit (f := algebraMap ℤ_[D.nd.l i] (D.nd.O i)) _ (by rw [map_natCast]; exact hu)
    exact PadicInt.irreducible_p.not_isUnit this
  unfold vO nlen
  apply ENNReal.div_self
  · haveI : Nontrivial (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
    simpa using (Module.length_pos (R := D.nd.O i)).ne'
  · have hf : IsFiniteLength (D.nd.O i) (D.nd.O i ⧸ Ideal.span {(D.nd.l i : D.nd.O i)}) :=
      isFiniteLength_quotient_span_singleton (D.nd.O i) (mem_nonZeroDivisors_of_ne_zero h0)
    simpa using Module.length_ne_top_iff.2 hf

end GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Polynomial

section Base

variable {Γ : Type} [Group Γ] {X : Type} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}

abbrev mat {B : Type} [CommRing B] {k : ℕ} (σ : Γ →* GL (Fin k) B) (g : Γ) : Matrix (Fin k) (Fin k) B :=
  ((σ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)

abbrev toFr (A : Type) [CommRing A] : A →+* FractionRing A := algebraMap A (FractionRing A)

def overK {k : ℕ} (σ : Γ →* GL (Fin k) A) : Representation (FractionRing A) Γ (Fin k → FractionRing A) :=
  matRep (mapM (toFr A) ((Units.coeHom _).comp σ))

def InRing (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (a : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (f : Fin m → X → A) (h : Fin m → Γ), (∀ k, f k ∈ T) ∧
    a = ∑ k, fun x => f k x • mat (rep x) (h k)

def InMatrixCongruenceModule (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (e s : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (j : Fin m → X → A) (a : Fin m → X → Matrix (Fin n) (Fin n) A),
    (∀ k, j k ∈ T ∧ j k π = 0 ∧ InRing T rep (a k)) ∧
    s = ∑ k, fun x => j k x • (e x * a k x * e x)

def CharPolyIn (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (h : Γ) (d : ℕ), (fun x => (mat (rep x) h).charpolyRev.coeff d) ∈ T

def ResidualSame (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (x y : X) (h : Γ), ((mat (rep x) h).map (IsLocalRing.residue A)).charpoly =
    ((mat (rep y) h).map (IsLocalRing.residue A)).charpoly

def IsDecomp (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))) :
    Prop :=
  ∀ g u, e (overK σ g u) =
    (overK ρ g (e u).1, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A) * (e u).2 c)

def HidaSetting (t : ℕ) (T : Subalgebra A (X → A)) (Z : Finset X) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) : Prop :=
  IsLocalRing T ∧ (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) ∧
  (∀ x, IsSS (overK (rep x))) ∧
  CharPolyIn T rep ∧
  (∀ x, AbsIrrDistinct (overK (rep x))) ∧ ResidualSame rep ∧
  (∀ x ∈ Z, ∃ e, IsDecomp (t := t) (rep x) (ρ x) χ e) ∧
  (∀ x ∈ Z, AbsIrrSub (mapRep (IsLocalRing.residue A) (ρ x)) ⊤)

def blockPol (e M : Matrix (Fin n) (Fin n) A) : A[X] :=
  Matrix.det ((Polynomial.X : A[X]) • e.map (C (R := A)) - M.map (C (R := A)) + 1 - e.map (C (R := A)))

def IsChoice (t : ℕ) (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) (π : X) (g0 : Γ) (L : ℕ)
    (eB e1 X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧
  (∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
    (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
    ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧
      ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0)) ∧
  (∃ (ϖ : A) (s : X → Matrix (Fin n) (Fin n) A), Irreducible ϖ ∧ InMatrixCongruenceModule T rep π eB s ∧
    X0 = fun x => eB x * mat (rep x) g0 * eB x + ϖ ^ L • s x) ∧
  ∀ x, (((blockPol (eB x) (X0 x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t

def RootsIn (t : ℕ) (B : Type) [CommRing B] [Algebra A B] (eB X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ x, ∃ α : Fin t → FractionRing B,
    (blockPol (eB x) (X0 x)).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - C (α c))

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def IsInertiaCyclotomicGeneratorElement (g0 : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def IsEnlargement (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [Algebra A (N.O i)] (TA : Subalgebra A (N.X i → A))
    (repA : N.X i → (GE N →* GL (Fin R.nV) A)) (ρA : N.X i → (GE N →* GL (Fin R.r) A))
    (χA : ℕ → (GE N →* Aˣ)) : Prop :=
  Function.Injective (algebraMap A (N.O i)) ∧
  Subalgebra.toSubmodule (N.T i) =
    Submodule.span (N.O i) ((fun f : N.X i → A => fun x => algebraMap A (N.O i) (f x)) '' (TA : Set _)) ∧
  (∀ x, rep x = mapRep (algebraMap A (N.O i)) (repA x)) ∧
  (∀ x ∈ N.Z i, ρ x = mapRep (algebraMap A (N.O i)) (ρA x)) ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g, ((N.chi i c g : (N.O i)ˣ) : N.O i) = algebraMap A (N.O i) ((χA c g : Aˣ) : A)

def RepCont (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x, Continuous fun g => mat (rep x) g

def ConsExist : Prop :=
  ∀ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℤ_[N.l i] A]
    [Module.Finite ℤ_[N.l i] A] [Algebra A (N.O i)] [IsScalarTower ℤ_[N.l i] A (N.O i)]
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    RepCont N i rep → IsEnlargement N i rep ρ A TA repA ρA χA → HidaSetting R.t TA (N.Z i) repA ρA χA →
    (∀ π ∈ N.Z i, ∀ g0, IsInertiaCyclotomicGeneratorElement N i g0 → ∀ L : ℕ,
      ∃ eB e1 X0, IsChoice R.t TA repA ρA χA π g0 L eB e1 X0) ∧
    (∀ (g0 : N.X i → GE N) (L : N.X i → ℕ)
        (eB e1 X0 : N.X i → N.X i → Matrix (Fin R.nV) (Fin R.nV) A),
      (∀ π ∈ N.Z i, IsInertiaCyclotomicGeneratorElement N i (g0 π) ∧ IsChoice R.t TA repA ρA χA π (g0 π) (L π) (eB π) (e1 π) (X0 π)) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B),
        Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧
        ∀ π ∈ N.Z i, RootsIn R.t B (eB π) (X0 π)) ∧
    (∀ π ∈ N.Z i, ∀ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 → IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 →
      RootsIn R.t (N.O i) eB X0 →
      ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧
        (∀ x, S.eB x = (eB x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.e1 x = (e1 x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.X0 x = (X0 x).map (algebraMap A (N.O i))) ∧
        GoodCongruenceObjects N rep ρ π S)

theorem isEnlargement_self (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) :
    IsEnlargement N i rep ρ (N.O i) (N.T i) rep ρ (N.chi i) := by
  refine ⟨fun _ _ h => h, ?_, fun x => ?_, fun x _ => ?_, fun _ _ _ _ => rfl⟩
  · have : ((fun f : N.X i → N.O i => fun x => algebraMap (N.O i) (N.O i) (f x)) '' (N.T i : Set _)) =
        (Subalgebra.toSubmodule (N.T i) : Set _) := by
      simp
    rw [this, Submodule.span_eq]
  · ext g a b
    rfl
  · ext g a b
    rfl

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockComplementLattice
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section General

variable {O Γ : Type} [CommRing O] [IsDomain O] [Group Γ]

def fracRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) :
    Representation (FractionRing O) Γ (Fin a → FractionRing O) :=
  glRep (mapRep (algebraMap O (FractionRing O)) ρ)

def charSum (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ (Fin t → FractionRing O) where
  toFun g := LinearMap.pi fun c : Fin t =>
    algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) • LinearMap.proj c
  map_one' := by
    ext v c
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext c
    simp [mul_assoc, Algebra.smul_def]

def blockRep {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) :
    Representation (FractionRing O) Γ ((Fin a → FractionRing O) × (Fin t → FractionRing O)) :=
  (fracRep ρ).prod (charSum χ t)

def IsoBlock {n a : ℕ} (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ))
    (t : ℕ) : Prop :=
  ∃ e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin a → FractionRing O) × (Fin t → FractionRing O)),
    ∀ g v, e (fracRep r g v) = blockRep ρ χ t g (e v)

def BlockSemisimple {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) : Prop :=
  (blockRep ρ χ t).IsSemisimpleRepresentation


omit [IsDomain O] in
def LatticeContinuous [TopologicalSpace Γ] [TopologicalSpace O] {a : ℕ}
    (ρ : Γ →* GL (Fin a) O) : Prop :=
  Continuous fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)

theorem blockRep_apply {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : (Fin a → FractionRing O) × (Fin t → FractionRing O)) :
    blockRep ρ χ t g v =
      ((((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map
          (algebraMap O (FractionRing O))).mulVec v.1,
        fun c : Fin t => algebraMap O (FractionRing O) ((χ (c.1 + 1) g : Oˣ) : O) * v.2 c) := by
  rfl

end General

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

structure IsComplement (r₀ : G H.E N.Om →* GL (Fin R.nV) (N.O i))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop where

  rho : IsoBlock r₀ ρ (N.chi i) R.t

  ss : BlockSemisimple ρ (N.chi i) R.t

  cont : LatticeContinuous ρ

end Record

def Complement_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i,
    ∀ r₀ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i), IsHeckeGalois D.nd i π r₀ →
      ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsComplement D.nd i r₀ ρ

end GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def IsJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, multV PD ρ τ a = (J.count a : ℤ)

end Local

def blockJumps (t : ℕ) : Multiset ℤ := (Multiset.range t).map (fun k : ℕ => (k : ℤ))

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsBlockSum (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ (g : GE N) (u : Fin R.nV → KK N i),
      e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)

end Glob

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < t then 1 else 0 := by
  have hn : (blockJumps t).Nodup := (Multiset.nodup_range t).map Nat.cast_injective
  have hm : a ∈ blockJumps t ↔ 0 ≤ a ∧ a < t := by
    simp only [blockJumps, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨a.toNat, by omega, by omega⟩
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem hn (hm.2 h)
  · exact Multiset.count_eq_zero.2 (fun h' => h (hm.1 h'))

end GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable (D : D7)

abbrev TwDatum : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ), (D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)

def Twisted (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def SameBelow (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔ 0 ≤ D.what₂.places.val w' (x : D.what₂.LL)

def SamePair (w w' : D.what₂.places.Pl) : Prop :=
  SameBelow D w w' ∨ SameBelow D (D.what₂.places.conj w) w'

def LiesUnder (i : D.ntw.Tw) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

def TwistedPlaceSettings (twI : D.what₂.places.Pl → D.ntw.Tw) : Prop :=
  (∀ w, Twisted D w → D.ntw.l (twI w) = D.what₂.places.resChar w ∧
    (LiesUnder D (twI w) w ∨ LiesUnder D (twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → twI w = twI w'

def namedPrimes : Set ℕ :=
  {2, 3, 5, D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'} ∪ Set.range fun u : D.what₂.Word => (D.mem u).A.T

variable {D}

def expDat (xd : ThData D) : IntegralHeckeForms.XD D := ⟨xd.xd0, xd.thetaBase_invariant_action⟩

def GoodDatum (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : Finset (PlE D.host)) (t : TwDatum D) : Prop :=
  (∀ P ∈ t.2.1, ∀ P', IsConjPl D.host P P' → P' ∈ t.2.1) ∧
  (∀ P ∈ t.2.1, ∀ p ∈ namedPrimes D, P ∉ placesOver D.host.E p) ∧
  (∀ lam : D.ntw.abelian₂ t.1, (∑ δ, D.ntw.th t.1 ∅ lam δ) ≠ 0) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    IntegralHeckeForms.FullRk D.nexp (expDat xd) t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b)) ∧
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat t.1 j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.BasisOf D.nexp t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b) (S j b)) ∧
    ∀ a : ℤ, IsCoprime a (D.ntw.l t.1 : ℤ) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 t.1 (((D.ntw.l t.1 : ℝ) ^ 2)⁻¹) S A t.2.1 t.2.2.1
        (t.2.2.2 ^ a)

def GoodSystem (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : D.ntw.Tw → Finset (PlE D.host))
    (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  TwistedPlaceSettings D (fun w => (t w).1) ∧
  (∀ w, Twisted D w → GoodDatum xd N0 (A (t w).1) (t w)) ∧
  (∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → t w = t w') ∧
  ∀ w w', Twisted D w → Twisted D w' → ¬ SamePair D w w' →
    ∀ P ∈ (t w).2.1, ∀ P' ∈ (t w').2.1, ∀ p : ℕ, p.Prime →
      ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

def recorded (c : NChoice D) (w : D.what₂.places.Pl) : TwDatum D :=
  ⟨c.twI w, c.Q w, c.k' w, BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)⟩

def TwGoodAt (c : NChoice D) (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  GoodSystem xd N0 (fun _ => ∅) (recorded c) ∧
  ∀ w, Twisted D w → D.what₂.places.conj w ≠ w → c.sd (D.what₂.places.conj w) = !c.sd w

def ExistsChoice (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  (∃ twI, TwistedPlaceSettings D twI) ∧
  ∀ twI, TwistedPlaceSettings D twI → ∀ A : D.ntw.Tw → Finset (PlE D.host),
    ∃ t : D.what₂.places.Pl → TwDatum D, (∀ w, (t w).1 = twI w) ∧ GoodSystem xd N0 A t

def WithToricIntegralityConstant (D : D7) (P : (D.ntw.Tw → ℕ) → Prop) : Prop :=
  (∃ N0, BlochKatoReduction.adm9 D N0) ∧ ∀ N0, BlochKatoReduction.adm9 D N0 → P N0

def FamTwGood {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => TwGoodAt (Fm.ex x hx i).nch (Fm.ex x hx i).xd N0

def TwGoodClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamTwGood Fm

variable (D : _root_.Formalism.BasicNotions.D7) in
variable {D} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj (w : D.what₂.places.Pl) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D (D.what₂.places.conj w) ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted
  rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]

end GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Rep

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

def IsSemisimplificationOf {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) : Prop :=
  IsSS s ∧ ∃ (m : ℕ) (Ws : Fin m → Submodule k W) (e : W ≃ₗ[k] V),
    (∀ j, Stable s (Ws j)) ∧ DirectSum.IsInternal Ws ∧
    ∀ j g, ∀ v ∈ Ws j, ρ g (e v) - e (s g v) ∈ (⨆ j' ∈ Set.Iio j, Ws j').map (e : W →ₗ[k] V)

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

end Loc

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

section At

variable (D : D7) (i : D.nd.Loc)

def chiRatio (c : ℕ) : GE D.nd →* (D.nd.O i)ˣ := chiU D.nd i c * (chiU D.nd i 1)⁻¹

def IsConstituent {n : ℕ} (χ : GE D.nd →* (D.nd.O i)ˣ)
    (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  ∃ v : Fin n → KK D.nd i, v ≠ 0 ∧
    ∀ g, (mapM (toK D.nd i) M g).mulVec v = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def CharCrysAt (χ : GE D.nd →* (D.nd.O i)ˣ) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw χ))

def MatCrysAt {n : ℕ} (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def ChiRatioCrysAt : Prop :=
  ∀ c : ℕ, 1 ≤ c → c ≤ D.R.t →
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) ∧ CharCrysAt D i w hw (chiRatio D i c)

end At

theorem chiRatio_eq (D : D7) (i : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) :
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) := by
  unfold chiRatio chiU
  rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
  rfl

theorem chiRatO_apply (D : D7) (i : D.nd.Loc) (c : ℕ) (g : GE D.nd) :
    chiRatO D.nd i c g 0 0 = ((chiRatio D i c g : (D.nd.O i)ˣ) : D.nd.O i) := by
  simp [chiRatO, twistM, chiRatio]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
end
