module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot

open Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf
open scoped TensorProduct

section Adeles

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def IsRealIn : Prop := ∀ a : F, cc (algebraMap F E a) = algebraMap F E a

abbrev AdE : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def IsIntF (a : FiniteAdeleRing (𝓞 F) F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F

def intAdE : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o : 𝓞 E, z = a ⊗ₜ (o : E)}

variable {E}

def diagE : E →+* AdE F E := Algebra.TensorProduct.includeRight.toRingHom

def vecA {r : ℕ} (v : Fin r → E) : Fin r → AdE F E := fun i => diagE F (v i)

def latHat {r : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ x : La, z = fun i => a ⊗ₜ ι x i}

def IsUnitaryQ {r : ℕ} (Gm γ : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ x y, herm Gm (γ.mulVec x) (γ.mulVec y) = herm Gm x y

variable [hF : Fact (IsRealIn F E)]

def conjF : E →ₐ[F] E where
  toRingHom := (IsCMField.complexConj E).toRingEquiv.toRingHom
  commutes' := hF.out

def conjA : AdE F E →ₐ[F] AdE F E := Algebra.TensorProduct.map (AlgHom.id F _) (conjF F)

variable {F}

def IsUnitaryA {r : ℕ} (Gm : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  g.transpose * Gm.map (diagE F) * g.map (conjA F) = Gm.map (diagE F)

def IsDetRootA {r : ℕ} (g : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ) : Prop :=
  (x : AdE F E) = g.det * conjA F (x : AdE F E)

def IsTwist (ξ : (AdE F E)ˣ →* Circle) (N : ℕ) : Prop :=
  (∃ m : ℕ, 0 < m ∧ ∀ x, ξ x ^ m = 1) ∧
  (∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1) ∧
  (∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1) ∧
  ∀ x : (AdE F E)ˣ, (x : AdE F E) ∈ intAdE F E → ((x⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E →
    (∃ y ∈ intAdE F E, (x : AdE F E) - 1 = N • y) → ξ x = 1

end Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r : ℕ}

section Clauses

variable {La' : Type} [AddCommGroup La'] [Module (𝓞 E) La']

def IsomEmb (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (Di : Datum H) (φ : Di.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  Function.Injective φ ∧ ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ0 * herm Gm (φ a) (φ b))

def LatAt (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ v : Fin r → E, (∃ b, φ b = v) ↔ ∃ z ∈ latHat F ι, vecA F v = g.mulVec z

def MarkAt (l : Level H) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (t : Dw.La →ₗ[𝓞 E] La')
    (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ z ∈ latHat F ι,
    vecA F (φ (t a)) - g.mulVec (vecA F (ι a)) = l.M • g.mulVec z

def AtClass (l : Level H) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E))
    (t : Dw.La →ₗ[𝓞 E] La') (h : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∃ γ : Matrix (Fin r) (Fin r) E, IsUnitaryQ Gm γ ∧
    LatAt ι φ (γ.map (diagE F) * h) ∧ MarkAt l ι φ t (γ.map (diagE F) * h)

end Clauses

section Value

variable [Fact (IsRealIn F E)] {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def sig0 : c.F →+* ℂ := c.F.val.toRingHom

variable {Xo c}

def AllMarked (F : Type) [Field F] [NumberField F] [Algebra F E] [Fact (IsRealIn F E)]
    (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ i, IsomEmb Gm ξ0 (Fu.Di i) (φ i) ∧ ∃ (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h ∧ AtClass l Gm ι (φ i) (Fu.t i) h ∧ IsDetRootA h x

variable (Xo c)

end Value

section Action

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l}

end Action

section Row

variable {l : Level H} (Xo : Moduli Dw l) {c c' : Coeff l} {n : ℕ}

variable {Pt : Type} {G : Type} [Group G] {Tup : Type*} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open scoped TensorProduct

section Adeles

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idHat (𝔞 : Ideal (𝓞 E)) : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o ∈ 𝔞, z = a ⊗ₜ ((o : 𝓞 E) : E)}

variable {F}

def IsIntUnit (y : (AdE F E)ˣ) : Prop :=
  (y : AdE F E) ∈ intAdE F E ∧ ((y⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E

def TrivMod (ξ : (AdE F E)ˣ →* Circle) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∀ y : (AdE F E)ˣ, IsIntUnit y → (y : AdE F E) - 1 ∈ idHat F 𝔞 → ξ y = 1

def RamExactly (ξ : (AdE F E)ˣ →* Circle) (𝔣 : Ideal (𝓞 E)) : Prop :=
  𝔣 ≠ ⊥ ∧ TrivMod ξ 𝔣 ∧ ∀ P 𝔤 : Ideal (𝓞 E), P.IsPrime → 𝔣 = P * 𝔤 → ¬ TrivMod ξ 𝔤

def Generates (x : AdE F E) (𝔠 : Ideal (𝓞 E)) : Prop :=
  ∀ y, y ∈ idHat F 𝔠 ↔ ∃ z ∈ intAdE F E, y = x * z

end Adeles

section Lattices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r n : ℕ}

def barI (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

def InLevel (r M : ℕ) (PQ : Ideal (𝓞 E)) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map cc).transpose * γ = 1 ∧ OneMod M γ ∧
    ∃ k : ℕ, Nat.Coprime k (Ideal.absNorm PQ) ∧ ∀ i b : Fin n, r ≤ i.val → b.val < r →
      ∃ o ∈ PQ, (k : E) * γ i b = ((o : 𝓞 E) : E)

def Carries (γ : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v, v ∈ L' ↔ ∃ u ∈ L, v = γ.mulVec u

end Lattices

section Record

variable {D : D7}

abbrev IdF (D : D7) : Type := (AdE D.host.F D.host.E)ˣ

def finU (D : D7) : (AE D)ˣ →* IdF D := Units.map (finPart D).toMonoidHom

variable (T : CoreJ D) {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ)

variable {T} {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)

variable (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

def MarkedBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (h γ : 𝔾) : Prop :=
  γ ∈ Γ ∧
    ((U.X (dict h).1).Λ : Set (Fin r → E)) =
      (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)


variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)


variable (Xo) in
def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

section Covers

variable [Fact (IsRealIn F E)] (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E))
  (AA : Set E) {Th : Type} (arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ) (IsInf : (E →+* ℂ) → Th → Prop)

variable {Γ fin L0 AA arch IsInf} {gram : Matrix (Fin r) (Fin r) E} {xi0 : E}

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : 𝔾 → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin Fu.n} {φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ} {th : ∀ k, (U.X k).Ψ → Th}

end One

variable {c : Coeff l} {σ0 : c.F →+* ℂ} {Tup : Type*} {dδ : Tup → DeltaDat Xo c n}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle} {c0 : ℂ}

end Covers

section Comparison₂

section Act

variable (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l} (hle : c.F ≤ c'.F)

end Act

variable (Γ : Subgroup 𝔾)



variable {c c' : Coeff l} (hle : c.F ≤ c'.F) {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

variable (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
  (dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
  (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)] (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
  (La : ∀ t, Cl' t → GenLat E n) (Nc gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F)
  (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
  (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
  (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)

end Comparison₂

section Whole

variable [Fact (IsRealIn F E)] {Γ : Subgroup 𝔾} {fin : 𝔾 →* GL (Fin r) (AdE F E)} {L0 : Submodule (𝓞 E) (Fin r → E)}
  {AA : Set E} {Th : Type} {arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ} {IsInf : (E →+* ℂ) → Th → Prop}
  {gram : Matrix (Fin r) (Fin r) E} {xi0 : E} {c c' : Coeff l} {hle : c.F ≤ c'.F} {Vs : Type} [AddCommGroup Vs]
  [Module c'.F Vs] {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
  {dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r} {mu : 𝔾 → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)} {Tup : Type*} {dδ : Tup → DeltaDat Xo c' n}
  {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)] {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F}
  {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F}
  {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop}
  {cst : (U (sig0 c)).Comp → ℂ} {ph : ℂ}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((sig0 c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle}

end Whole

end GlobalTheory.XiDetCompare
end
end

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

section Diag

variable {V} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ V.rank} {dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {g : ℕ}

end Diag

section Compare

variable {V hr} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end Compare

end Value

section Record

variable {D : D7} {T : CoreJ D} {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ) {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)
  (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)
  (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (B : D.what₂.Tup → Ideal (𝓞 D.host.E) → c'.F)
  (epF : D.what₂.Tup → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E) → c'.F) (cond : ℕ) (hw : VVc c' lam)
  (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((sig0 c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
  (dict₂ : ∀ t, GA D (T.V j (sig0 T.Q.c)) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : D.what₂.Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ)

variable {Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi}

variable (Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi)

end Record

end GlobalTheory.ClassTieCompare
