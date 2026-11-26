module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

structure Frames (L : LocE F E) (r k : ℕ) where
  ϖ : 𝒪[F]
  ϖ_irr : Irreducible ϖ
  Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E
  herm : IsHermND L Hm
  T : Fˣ
  T' : Fˣ
  f : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  f' : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  es : Fin r → Fin (k + 2 * r + 1) → E
  es' : Fin r → Fin (k + 2 * r + 1) → E
  gram : ∀ a b, hf L Hm (f a) (f b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0
  gram' : ∀ a b, hf L Hm (f' a) (f' b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T' else 0
  dual : ∀ a j, hf L Hm (f a) (es j) = if a = j.castSucc then 1 else 0
  dual' : ∀ a j, hf L Hm (f' a) (es' j) = if a = j.castSucc then 1 else 0
  iso : ∀ i j, hf L Hm (es i) (es j) = 0
  iso' : ∀ i j, hf L Hm (es' i) (es' j) = 0
  w : Pt E (r + 1)
  relevant : ∀ a b, hf L Hm (f' b) (f a) = w.mat a b * (-1) ^ (r - (b : ℕ))
  G_ne : lead (Matrix.of fun a b => hf L Hm (f' b) (f a)) (Fin.last (r + 1)) *
      L.cj (lead (Matrix.of fun a b => hf L Hm (f' b) (f a)) (Fin.last (r + 1))) -
    algebraMap F E ((T : F) * T') * (lead (Matrix.of fun a b => hf L Hm (f' b) (f a)) (Fin.last r).castSucc *
      L.cj (lead (Matrix.of fun a b => hf L Hm (f' b) (f a)) (Fin.last r).castSucc)) ≠ 0
  gg : Bool
  gg_ok : gg = true → ¬ IsField E ∧ (∃ u : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) = T) ∧ ∃ u : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) = T'

namespace Frames

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

abbrev V (_ : Frames L r k) : Type := Fin (k + 2 * r + 1) → E

abbrev GLV : Type := S.V ≃ₗ[E] S.V

def h (x y : S.V) : E := hf L S.Hm x y

def th : F := if S.gg then (S.ϖ : F) else 1

def q : ℕ := resQ S.ϖ

def Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun a b => S.h (S.f' b) (S.f a)

def D (l : Fin (r + 2)) : E := lead S.Zh l

def G : E := S.D (Fin.last (r + 1)) * L.cj (S.D (Fin.last (r + 1))) -
  algebraMap F E ((S.T : F) * S.T') * (S.D (Fin.last r).castSucc * L.cj (S.D (Fin.last r).castSucc))

def vth : ℤ := if S.gg then 1 else 0

def a : ℤ := vE L S.ϖ S.G - 2 * (r + 1) * S.vth

def vD : ℤ := ∑ l : Fin (r + 2), if l ≠ 0 ∧ S.D l ≠ 0 then vE L S.ϖ (S.D l * L.cj (S.D l)) else 0

def Hp : ℝ := (S.q : ℝ) ^ (S.vth + S.a + S.vD)

def spanTo (g : Fin (r + 1) → S.V) (j : ℕ) : Submodule E S.V := Submodule.span E (g '' {i | (i : ℕ) < j})

def Nof (g : Fin (r + 1) → S.V) : Subgroup S.GLV :=
  isomG L S.Hm ⊓ (⨅ j : Fin r, unipOn (S.spanTo g (j + 1)) (S.spanTo g j)) ⊓
    unipOn (perp L S.Hm (S.spanTo g r)) (S.spanTo g r)

def coef (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (n : S.GLV) (j : Fin r) : E := S.h (n (g j.succ)) (gs j)

def psiOf (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (n : S.GLV) : ℂ :=
  L.psi0 (algebraMap F E S.th⁻¹ * ∑ j, S.coef g gs n j)

def N : Subgroup S.GLV := S.Nof S.f

def N' : Subgroup S.GLV := S.Nof S.f'

def psi : S.GLV → ℂ := S.psiOf S.f S.es

def psi' : S.GLV → ℂ := S.psiOf S.f' S.es'

def St : Subgroup S.GLV := S.N ⊓ S.N'

def X : Submodule E S.V := S.spanTo S.f r

def X' : Submodule E S.V := S.spanTo S.f' r

def ME : Submodule E S.V := S.spanTo S.f (r + 1) ⊔ S.spanTo S.f' (r + 1)

def W0 : Submodule E S.V := perp L S.Hm S.ME

def H0 : Subgroup S.GLV := isomG L S.Hm ⊓ unipOn S.ME ⊥

def InTh (Λ : Submodule L.O S.V) (x : S.V) : Prop := ∃ y ∈ Λ, x = algebraMap F E S.th • y

def IsInner (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (A : Submodule L.O S.V) : Prop :=
  (∀ x ∈ S.spanTo g r, x ∈ A) ∧ (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) ∧
  (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O).FG ∧
  (∀ y ∈ perp L S.Hm (S.spanTo g r), (∀ x ∈ A, S.h x y ∈ L.O) ↔ y ∈ A) ∧
  g (Fin.last r) ∈ A ∧ ∃ y ∈ A, S.h (g (Fin.last r)) y = 1

def stdLat (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (A : Submodule L.O S.V) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) ⊔
    (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) ⊔
    Submodule.span L.O (Set.range gs)

abbrev Datum : Type := Submodule L.O S.V × Submodule L.O S.V × Set (S.V × S.V)

def graphOf (Λ : Submodule L.O S.V) : Set (S.V × S.V) :=
  {p | ∃ y' ∈ Λ, ∃ y ∈ Λ, y' ∈ perp L S.Hm S.X' ∧ y ∈ perp L S.Hm S.X ∧ y' - p.1 ∈ S.X' ∧ y - p.2 ∈ S.X ∧
    S.InTh Λ (y' - y)}

def IsTermW (d : S.Datum) (Λ : Submodule L.O S.V) (n n' : S.GLV) : Prop :=
  S.IsInner S.f S.es d.1 ∧ S.IsInner S.f' S.es' d.2.1 ∧ n ∈ S.N ∧ n' ∈ S.N' ∧
  Λ = n • S.stdLat S.f S.es d.1 ∧ Λ = n' • S.stdLat S.f' S.es' d.2.1 ∧
  (∀ b, S.InTh Λ (n' (S.f' b) - n (S.f b))) ∧ d.2.2 = S.graphOf Λ

def IsTerm (d : S.Datum) (Λ : Submodule L.O S.V) : Prop := ∃ p : S.GLV × S.GLV, S.IsTermW d Λ p.1 p.2

def wit (d : S.Datum) (Λ : Submodule L.O S.V) : S.GLV × S.GLV :=
  if H : S.IsTerm d Λ then H.choose else (1, 1)

def fr (d : S.Datum) (Λ : Submodule L.O S.V) (b : Fin (r + 1)) : S.V := (S.wit d Λ).1 (S.f b)

def fr' (d : S.Datum) (Λ : Submodule L.O S.V) (b : Fin (r + 1)) : S.V := (S.wit d Λ).2 (S.f' b)

def om (d : S.Datum) (Λ : Submodule L.O S.V) : ℂ := S.psi (S.wit d Λ).1 * (S.psi' (S.wit d Λ).2)⁻¹

def Mof (g g' : Fin (r + 1) → S.V) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range g ∪ Set.range fun b => algebraMap F E S.th⁻¹ • (g' b - g b))

def M (d : S.Datum) (Λ : Submodule L.O S.V) : Submodule L.O S.V := S.Mof (S.fr d Λ) (S.fr' d Λ)

def sat (Λ : Submodule L.O S.V) : Submodule L.O S.V := Λ ⊓ S.ME.restrictScalars L.O

def be (d : S.Datum) (Λ : Submodule L.O S.V) : ℕ := (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup

def BBzero (d : S.Datum) (Λ : Submodule L.O S.V) : Prop := S.M d Λ = S.sat Λ

def K0 : Subgroup S.GLV :=
  S.St ⊓ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range S.f)) ⊓
    MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range S.f'))

def mu (Λ : Submodule L.O S.V) : ℝ := invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV Λ)

def amp (d : S.Datum) (P : Submodule L.O S.V → Prop) : ℂ :=
  ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
    if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0

def mass (d : S.Datum) (P : Submodule L.O S.V → Prop) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
    if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0

def complementReferenceCompactSubgroup : Subgroup S.GLV :=
  S.H0 ⊓ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V)))

def nu (d : S.Datum) : ℝ := invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV d)

def sumData (φ : S.Datum → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out

def nn : ℝ≥0∞ := S.sumData fun d => S.mass d fun _ => True

def ampSq (P : S.Datum → Submodule L.O S.V → Prop) : ℝ≥0∞ :=
  S.sumData fun d => ENNReal.ofReal (‖S.amp d (P d)‖ ^ 2)

def RR (x y : E) : Prop := y ∈ L.O ∧ ∃ c ∈ L.O, x + y = algebraMap F E S.th * c

def lev (g g' : Fin (r + 1) → S.V) (b : S.V) : ℕ :=
  sInf {j | ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
    ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}

def levC (d : S.Datum) (Λ : Submodule L.O S.V) (y : S.V) : ℕ :=
  S.lev (S.fr d Λ) (S.fr' d Λ) (algebraMap F E S.th • y)

def TypeBe (d : S.Datum) (Λ : Submodule L.O S.V) : Prop :=
  ¬ S.BBzero d Λ ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y ≤ r) ∧
    ∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh Λ (x₁ + x₁') → S.InTh Λ (x₂ + x₂') →
      ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c

def nLev (d : S.Datum) (Λ : Submodule L.O S.V) (J : ℕ) : ℕ :=
  Set.ncard {C : Set S.V | ∃ y ∈ S.sat Λ, S.levC d Λ y = J ∧ C = {x | x - y ∈ S.M d Λ}}

def InFF (β J βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) : Prop :=
  S.TypeBe d Λ ∧ S.be d Λ = β ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) ∧ (∃ y ∈ S.sat Λ, S.levC d Λ y = J) ∧
    S.nLev d Λ J = βJ

def complementLatticeOfDatum (d : S.Datum) : Set S.V := {w | w ∈ S.W0 ∧ w ∈ d.1 ∧ w ∈ d.2.1 ∧ (w, w) ∈ d.2.2}

def TauRel (d : S.Datum) (Λ : Submodule L.O S.V) (w y : S.V) : Prop :=
  ∃ la ∈ S.X, ∃ la' ∈ S.X', w + la ∈ Λ ∧ w + la' ∈ Λ ∧ S.InTh Λ (la' - la) ∧
    y - algebraMap F E S.th⁻¹ • (la' - la) ∈ S.M d Λ

def Ihat (d : S.Datum) (Λ : Submodule L.O S.V) : Submodule L.O S.V :=
  S.M d Λ ⊔ Submodule.span L.O {y | ∃ w ∈ S.complementLatticeOfDatum d, S.TauRel d Λ w y}

def cardI (d : S.Datum) (Λ : Submodule L.O S.V) : ℕ :=
  (S.M d Λ).toAddSubgroup.relIndex (S.Ihat d Λ).toAddSubgroup

abbrev FrP : Type := (Fin (r + 1) → S.V) × (Fin (r + 1) → S.V)

def frameCls (g g' : Fin (r + 1) → S.V) : Set S.FrP :=
  {p | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsIntM L A ∧ IsIntM L A' ∧
    (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = algebraMap F E S.th * c) ∧
    (∀ j, p.1 j = ∑ i, A i j • g i) ∧ ∀ j, p.2 j = ∑ i, A' i j • g' i}

def IsCls (C : Set S.FrP) : Prop :=
  ∃ n ∈ S.N, ∃ n' ∈ S.N', C = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b))

def IsIntCls (C : Set S.FrP) : Prop := S.IsCls C ∧ ∀ p ∈ C, ∀ a b, S.h (p.2 b) (p.1 a) ∈ L.O

def Fr (d : S.Datum) (Λ : Submodule L.O S.V) : Set S.FrP := S.frameCls (S.fr d Λ) (S.fr' d Λ)

def wC (C : Set S.FrP) : ℝ := invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV C)

def sumCls (φ : Set S.FrP → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient S.St (Set S.FrP),
    if S.IsIntCls o.out then ENNReal.ofReal (S.wC o.out) * φ o.out else 0

def nT (d : S.Datum) (C : Set S.FrP) (P : Submodule L.O S.V → Prop) : ℝ≥0∞ :=
  ({Λ | S.IsTerm d Λ ∧ P Λ ∧ S.Fr d Λ = C} : Set (Submodule L.O S.V)).encard

def massSig (Mh : Submodule L.O S.V) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V),
    if IsSD L S.Hm o.out ∧ S.sat o.out = Mh then
      ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0

def IsMove (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (x x' u : S.V) (s : E) : Prop :=
  x ∈ S.spanTo S.f J ∧ x' ∈ S.spanTo S.f' J ∧ S.InTh Λ (x + x') ∧
    S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = J ∧ u ∈ Λ ∧
    u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) ∧
    (∃ c ∈ L.O, s = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ s + L.cj s = S.h u u

def moved (Λ : Submodule L.O S.V) (x u : S.V) (s : E) : Set S.V := {v | eich L S.Hm x u s v ∈ Λ}

end Frames

end GlobalTheory.HL
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

def GoodSub {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) (S : Set W) : Prop :=
  A.relIndex W0 ≠ 0 ∧ W0.relIndex A ≠ 0 ∧ (∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) ∧
    ((QuotientAddGroup.mk : W → W ⧸ A) '' S).Finite

def IsCO {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : Prop := ∃ A, GoodSub W0 A S

def relVol {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) : ℝ :=
  (W0.relIndex A : ℝ) / (A.relIndex W0 : ℝ)

def cont {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : ℝ :=
  if h : IsCO W0 S then
    (((QuotientAddGroup.mk : W → W ⧸ h.choose) '' S).ncard : ℝ) * relVol W0 h.choose else 0

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def gramT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) :
    Matrix (Fin m) (Fin m) E := Matrix.of fun a b => hf L Hm (x b) (x a)

def rmul {n m : ℕ} (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • x i

def IsUni {N : ℕ} (s : Matrix (Fin N) (Fin N) E) : Prop := (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1

def congK (L : LocE F E) (ϖ : 𝒪[F]) (m i : ℕ) : Set (Matrix (Fin m) (Fin m) E) :=
  {A | ∀ a b, ∃ c ∈ L.O, A a b - (1 : Matrix (Fin m) (Fin m) E) a b = algebraMap F E ((ϖ : F) ^ i) * c}

def thick (L : LocE F E) (ϖ : 𝒪[F]) {n m : ℕ} (Ω : Set (Fin m → Fin n → E)) (i : ℕ) :
    Set (Fin m → Fin n → E) := {x | ∃ y ∈ Ω, ∃ A ∈ congK L ϖ m i, x = rmul y A}

def horb (L : LocE F E) (ϖ : 𝒪[F]) {m : ℕ} (Γ : Matrix (Fin m) (Fin m) E) (i : ℕ) :
    Set (Matrix (Fin m) (Fin m) E) := {X | ∃ A ∈ congK L ϖ m i, X = cT L A * Γ * A}

def tupLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (m : ℕ) :
    AddSubgroup (Fin m → Fin n → E) := AddSubgroup.pi Set.univ fun _ => Λ.toAddSubgroup

def hermLat (L : LocE F E) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
  AddSubgroup.closure {X | IsHerm L X ∧ IsIntM L X}

def IsPrimT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E))
    (x : Fin m → Fin n → E) : Prop :=
  (∀ a, x a ∈ Λ) ∧ ∃ y : Fin m → Fin n → E, (∀ a, y a ∈ Λ) ∧
    ∀ a b, hf L Hm (x a) (y b) = if a = b then 1 else 0

def fixG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := isomG L Hm ⊓ unipOn Y ⊥

abbrev stabL (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ

def torb {n m : ℕ} (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E) :
    Set (Fin m → Fin n → E) := {y | ∃ g ∈ K, y = fun a => g (x a)}

def CongId (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (N : ℕ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = algebraMap F E ((ϖ : F) ^ N) • w

def sigMass (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E))
    (Λ0 Mh : Submodule L.O (Fin n → E)) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)),
    if IsSD L Hm o.out ∧ o.out ⊓ Y.restrictScalars L.O = Mh then
      ENNReal.ofReal (invVol (fixG L Hm Y ⊓ stabL L Λ0) (fixG L Hm Y ⊓ stabL L o.out)) else 0

def IsQRefl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : Fin n → E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  IsUnit (hf L Hm a a) ∧ g ∈ isomG L Hm ∧ ∃ c : E, ∀ v, g v = v + (c * hf L Hm v a) • a

end GlobalTheory.HL
end
end
