module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
noncomputable section

namespace GlobalTheory.KEdge

variable {Γ : Type*} [Group Γ] {N : ℕ}

def edge (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) : ZMod N :=
  η (σ * h * σ⁻¹) - η h - (x h).toAdd * (y σ).toAdd + (x σ).toAdd * (y h).toAdd

def CobOn (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) : Prop :=
  ∀ g ∈ Δ, ∀ h ∈ Δ, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g

end GlobalTheory.KEdge
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L := Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom


open Classical in
def finSingle (v : HeightOneSpectrum (𝓞 L)) : v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L := by
  classical
  exact {
    toFun x := ⟨Pi.mulSingle v x, by
      refine Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset ?_)
      intro w hw
      by_contra h
      apply hw
      have h' : w ≠ v := h
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
    map_one' := by
      apply Subtype.ext
      exact Pi.mulSingle_one v
    map_mul' x y := by
      apply Subtype.ext
      exact Pi.mulSingle_mul v x y }

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp (finSingle L v))


open Classical in
def infIdele (w : InfinitePlace L) : (w.Completion)ˣ →* Ideles L := by
  classical
  exact Units.map ((MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w))

theorem valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by
  show Valued.v ((algebraMap (𝓞 L) L x : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr hx

end GlobalTheory.Mem.Chr
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
noncomputable section

namespace GlobalTheory.SgAlg

variable {E : Type} [CommRing E]

def IsQA (σ : E →+* E) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ IsReduced E ∧ IsUnit (2 : E) ∧
    ∀ x, σ x = x → x ≠ 0 → IsUnit x

def cT (σ : E →+* E) {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map σ).transpose

def IsHermU (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := cT σ J = J ∧ IsUnit J.det

def form (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  dotProduct (fun i => σ (y i)) (J.mulVec x)

def pairM (σ : E →+* E) {n : ℕ} {a b : Type} (J : Matrix (Fin n) (Fin n) E)
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E) : Matrix a b E := cT σ P * J * P'

def IsUn (σ : E →+* E) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) : Prop := cT σ g * J * g = J

def Free {n : ℕ} {a : Type} [Fintype a] [DecidableEq a] (P : Matrix (Fin n) a E) : Prop :=
  ∃ L : Matrix a (Fin n) E, L * P = 1

def IsUp {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLo {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (i < j → u i j = 0) ∧ (i = j → u i j = 1)

def lead {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) (l : ℕ) (hl : l ≤ m) : E :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def TF (r : ℕ) (T : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.diagonal fun a => if a = Fin.last r then -T else 0

def Gq (σ : E →+* E) {r : ℕ} (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * σ Z.det - T * T' * (lead Z r (Nat.le_succ r) * σ (lead Z r (Nat.le_succ r)))

def IsFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop := Free P ∧ pairM σ J P P = TF r T

def eOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin r) E :=
  P.submatrix id Fin.castSucc

def IsDual (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Prop :=
  pairM σ J f P = (Matrix.of fun a b => if a = Fin.castSucc b then 1 else 0) ∧ pairM σ J f f = 0

def InS (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ ∃ ν, IsUp ν ∧ g * P = P * ν

def InN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ (∃ ν, IsUp ν ∧ g * eOf P = eOf P * ν) ∧
    ∀ v : Fin n → E, (cT σ (eOf P) * J).mulVec v = 0 → ∃ c, g.mulVec v - v = (eOf P).mulVec c

def XZ (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E) :=
  {p | IsFrame σ J T p.1 ∧ IsFrame σ J T' p.2 ∧ pairM σ J p.2 p.1 = Z}

def PosOnPerp {n : ℕ} {a : Type} [Fintype a] (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) a ℂ) : Prop :=
  ∀ w : Fin n → ℂ, (cT (starRingEnd ℂ) A * J).mulVec w = 0 → w ≠ 0 →
    0 < (form (starRingEnd ℂ) J w w).re

end GlobalTheory.SgAlg
end
end
