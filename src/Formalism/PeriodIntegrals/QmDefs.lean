module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.HermitianCurvature.StatementTA

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.QmDefs
open Matrix Finset

noncomputable section

namespace PI

open Formalism.REAL

def skip1 {t : ℕ} (i : Fin t) (j : Fin (t - 1)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩ else ⟨j.val + 1, by have := j.isLt; omega⟩

def skip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩
  else if j.val + 1 < i'.val then ⟨j.val + 1, by have := j.isLt; omega⟩
  else ⟨j.val + 2, by have := j.isLt; omega⟩

def SkipSucc : Prop := ∀ (t : ℕ) (i : Fin (t + 1)) (j : Fin t), skip1 i j = i.succAbove j

def SkipSucc2 : Prop :=
  ∀ (t : ℕ) (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t), i.val ≤ i'.val →
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j)

def qminorRow {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod

def RowForm : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ), qminor E a b u = qminorRow E a b u

def ExpFirstCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Tm E u (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1))

def ExpLastCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u * Tm E (u - (t : ℂ)) (a l) (b (Fin.last t)))

def ExpFirstRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a 0) (b l) * qminor E (a ∘ Fin.succ) (b ∘ l.succAbove) u)

def ExpLastRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l))

def MoveVec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (y : Fin n → A), GlRel E →
    (∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0) → (∀ a b, y a * y b = y b * y a) →
    ∀ (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ),
      ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) =
        ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j))

def MoveCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (η : Fin n → A), GlRel E →
    (∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0) → (∀ a b, η a * η b = η b * η a) →
    ∀ (a : Fin (t + 1) → Fin n) (b : Fin t → Fin n) (w : ℂ),
      ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
        ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (qminor E (a ∘ i.succAbove) b w * η (a i))

def StarMinor : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (ε : Fin n → ℤˣ), GlRel E → (∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) →
    ∀ (a b : Fin t → Fin n) (w : ℂ),
      star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * qminor E b a (star w)

def bE {n m : ℕ} (e : Fin n) (v : Fin m → Fin n) : Fin (m + 1) → Fin n := Fin.cons (α := fun _ => Fin n) e v

def bS {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : Fin (m + 1) → Fin n := Fin.snoc (α := fun _ => Fin n) v es

def sg2 {m : ℕ} (w w' : Fin m) : ℤ :=
  if w'.val < w.val then (-1) ^ (w.val + w'.val) else (-1) ^ (w.val + w'.val + 1)

def IsBorder {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : Prop :=
  Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es

def BorderE : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e v) (bE e v) u = Tm E u e e * qminor E v v (u - 1) -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x))

def BorderS : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bS v es) (bS v es) u = qminor E v v u * Tm E (u - (m : ℂ)) es es -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es)

def BorderFull : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e (bS v es)) (bE e (bS v es)) u =
        Tm E u e e * qminor E v v (u - 1) * Tm E (u - (m : ℂ) - 1) es es
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * Tm E u e e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es))
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1))
        + ∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.ProdFormulaE
noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

def ProdFormulaE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p),
  (∀ M : ∀ p, Formalism.MainNotions.S.Loc.Model (L p).Fp (L p).Ep, (∀ p, (M p).OK) →
    ∀ x : E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : E,
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
    ∏ᶠ p, (L p).psiE ((L p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))))

end PI.ProdFormulaE
end
end

section -- merged from Formalism.PeriodIntegrals.LocHerm
noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def LocGlue : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (abelian₂ : Submodule M.L.O V),
    H.IsSelfDual abelian₂ → ∀ (U : Submodule E V) (hU : IsCompl U (H.perp U)),
    (∀ u : V, u ∈ U → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl U (H.perp U) hU x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ U → H.h u y ∈ M.L.O)) ∧
    (∀ u : V, u ∈ H.perp U → ((∃ x ∈ abelian₂,
        (Submodule.linearProjOfIsCompl (H.perp U) U hU.symm x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ H.perp U → H.h u y ∈ M.L.O))

def LocOProj : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG → Module.Projective M.L.O P

end PI.LocHerm
end
end

section -- merged from Formalism.PeriodIntegrals.NUnimodLoc
noncomputable section

open Matrix MeasureTheory

namespace PI.NUnimodLoc

abbrev uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

structure IsFrameJ {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z0 = 0
  fz : ∀ a, hJ ε (f a) z0 = 0
  zz : hJ ε z0 z0 = -1
  ww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (wf a) = 0
  fw : ∀ c a, hJ ε (f c) (wf a) = 0
  zw : ∀ a, hJ ε z0 (wf a) = 0

def NUnimodLoc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => x * s) = μ

end PI.NUnimodLoc
end
end

section -- merged from Formalism.PeriodIntegrals.LocDensCorank
open ValuativeRel Classical

noncomputable section

namespace PI.LocDensCorank

open Formalism.MainNotions.S

def LocDensCorank : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (if ∀ x : E, x ≠ 0 → IsUnit x then -1 else 1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card

end PI.LocDensCorank
end
end

section -- merged from Formalism.PeriodIntegrals.CdHaarScale
noncomputable section

open MeasureTheory

namespace PI.CdHaarScale

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def CdTieAt (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool) (c : NNReal) : Prop :=
  ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((c : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

end PI.CdHaarScale

namespace PI

def CdHaarScale : Prop :=
  ∀ (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool), ∃ c : NNReal, 0 < c ∧ PI.CdHaarScale.CdTieAt cd n ε c

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.LocDualGen
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen

def DualAtL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (δ : A.Fp) : Prop :=
  ∀ x : A.Ep, (∀ y ∈ A.O, A.psiE (-(x * y * algebraMap A.Fp A.Ep δ⁻¹)) = 1) ↔ x ∈ A.O

def UnramL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) : Prop :=
  ∀ ϖ : 𝒪[A.Fp], Irreducible ϖ → ∀ x ∈ A.O,
    x * x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)} →
      x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)}

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    (IsReduced A.Ep → UnramL A → ∃ δ : A.Fp, δ ≠ 0 ∧ DualAtL A δ) ∧
    (∀ (δ : A.Fp) (u : 𝒪[A.Fp]), IsUnit u → DualAtL A δ → DualAtL A (δ * (u : A.Fp))) ∧
    (IsReduced A.Ep → UnramL A → Irreducible ((resChar p : ℕ) : 𝒪[A.Fp]) → DualAtL A 1)

end PI.LocDualGen
end
end

section -- merged from Formalism.PeriodIntegrals.RTTIndependence
open Matrix Finset

noncomputable section

namespace PI

open Formalism Formalism.FourierDecayAlt

def RTTSandwich : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (p c ci p' c' ci' : A),
    YangianSpanCharacter.T.WeylRel p c ci → YangianSpanCharacter.T.WeylRel p' c' ci' →
    (∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), x * y = y * x) →
    (∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ Y a b, x * QQ Y a b = QQ Y a b * x) →
    ∀ Y Y' : ℂ,
      let C : ℂ → A := fun y => (YangianSpanCharacter.T.Tm y p' c' ci' * QQ y * YangianSpanCharacter.T.Tm y p c ci) 0 0
      let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A) * YangianSpanCharacter.T.E1 (QQ Y') * YangianSpanCharacter.T.E2 (QQ Y) -
          YangianSpanCharacter.T.E2 (QQ Y) * YangianSpanCharacter.T.E1 (QQ Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A)
      algebraMap ℂ A (Y' - Y - 1) * (C Y' * C Y - C Y * C Y') =
        ((YangianSpanCharacter.T.T2 Y p' c' ci' * YangianSpanCharacter.T.T1 Y' p' c' ci') * X * (YangianSpanCharacter.T.T1 Y' p c ci * YangianSpanCharacter.T.T2 Y p c ci)) (0, 0) (0, 0)

def RTTIndependence : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (x : Fin 2 × Fin 2 → Fin 2 × Fin 2 → V) (Y Y' : ℂ), Y' ≠ Y + 1 →
    (∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) • x A B = 0) →
    ∀ A B, x A B = 0

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.QuotProdK
noncomputable section

open MeasureTheory

namespace PI.QuotProdK

def QuotProdK : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (ε : ∀ v, Fin (n v) → Bool)
    (N H : ∀ v, Set (Formalism.REAL.UJ (ε v))),
    (∀ v, IsClosed (N v)) → (∀ v, IsCompact (H v)) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ N v ∧ (∀ a ∈ N v, ∀ b ∈ N v, a * b ∈ N v) ∧ ∀ a ∈ N v, a⁻¹ ∈ N v) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ H v ∧ (∀ a ∈ H v, ∀ b ∈ H v, a * b ∈ H v) ∧ ∀ a ∈ H v, a⁻¹ ∈ H v) →
    (∀ v, ∀ h ∈ H v, ∀ m ∈ N v, h * m * h⁻¹ ∈ N v) →
    (∀ v (μ : Measure (Formalism.REAL.UJ (ε v))), SigmaFinite μ → μ ≠ 0 → μ (N v)ᶜ = 0 →
      (∀ s ∈ N v, μ.map (fun x => s * x) = μ) → ∀ s ∈ N v, μ.map (fun x => x * s) = μ) →
    ∀ muN muH nuQ : Measure (∀ v, Formalism.REAL.UJ (ε v)),
      (SigmaFinite muN ∧ muN ≠ 0 ∧ muN (Set.pi Set.univ N)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ N, muN.map (fun x => s * x) = muN) →
      (SigmaFinite muH ∧ muH ≠ 0 ∧ muH (Set.pi Set.univ H)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ H, muH.map (fun x => s * x) = muH) →
      (∀ f : (∀ v, Formalism.REAL.UJ (ε v)) → ENNReal, Measurable f →
        ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
          ∫⁻ x, (∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2))) ∂nuQ) →
      ∃ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (ε v))) (C : ENNReal), C ≠ 0 ∧ C ≠ ⊤ ∧
        (∀ v, (SigmaFinite (μS v) ∧ μS v ≠ 0 ∧ μS v {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}ᶜ = 0 ∧
          ∀ s ∈ {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}, (μS v).map (fun x => s * x) = μS v) ∧
          ∀ F : Formalism.REAL.UJ (ε v) → ENNReal, Measurable F →
            ∫⁻ x, F x ∂(Formalism.REAL.muG (ε v)) = ∫⁻ x, (∫⁻ s, F (s * x) ∂(μS v)) ∂(νl v)) ∧
        ∀ F : ∀ v, Formalism.REAL.UJ (ε v) → ENNReal, (∀ v, Measurable (F v)) →
          (∀ v, ∀ m ∈ N v, ∀ h ∈ H v, ∀ x, F v (m * h * x) = F v x) →
          ∫⁻ x, ∏ v, F v (x v) ∂nuQ = C * ∏ v, ∫⁻ y, F v y ∂(νl v)

end PI.QuotProdK
end
end

section -- merged from Formalism.PeriodIntegrals.AlgebraMapMemO
noncomputable section

open ValuativeRel MeasureTheory
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.SlopeTestRemainingChoices

open Polynomial Topology

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem mem_O_of_quad (L : LocE F E) (z : E) (t n : 𝒪[F])
    (h : z * z - algebraMap F E t * z + algebraMap F E n = 0) : z ∈ L.O := by
  rw [L.O_def]
  refine ⟨(X ^ 2 + (C (-t) * X + C n) : Polynomial 𝒪[F]), ?_, ?_⟩
  · monicity!
  · have ht : algebraMap 𝒪[F] E t = algebraMap F E t := rfl
    have hn : algebraMap 𝒪[F] E n = algebraMap F E n := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_neg, eval₂_X_pow, eval₂_X, eval₂_C, map_neg, ht, hn]
    linear_combination h

theorem algebraMap_mem_O (L : LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O :=
  mem_O_of_quad L _ a 0 (by simp)

theorem mem_OF_of_mem_O [Nontrivial E] (L : LocE F E) (a : F) (h : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have hE : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  rw [L.O_def] at h
  have hF : IsIntegral 𝒪[F] a := by
    obtain ⟨p, hp, he⟩ := h
    refine ⟨p, hp, ?_⟩
    apply hE
    have hc : (algebraMap F E).comp (algebraMap 𝒪[F] F) = algebraMap 𝒪[F] E := by
      ext r
      rfl
    rw [Polynomial.hom_eval₂, map_zero, hc, he]
  exact (Valuation.integer.integers _).mem_of_integral hF

theorem cj_mem_O (L : LocE F E) (x : E) (h : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at h ⊢
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, ?_⟩
  have hc : L.cj.toRingEquiv.toRingHom.comp (algebraMap 𝒪[F] E) = algebraMap 𝒪[F] E := by
    ext r
    show L.cj (algebraMap F E (r : F)) = algebraMap F E (r : F)
    exact L.cj.commutes _
  have h2 := congrArg L.cj.toRingEquiv.toRingHom he
  rw [Polynomial.hom_eval₂, map_zero, hc] at h2
  exact h2

end Top

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem inv_mem_OF (a : F) (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' := h
  rw [Valuation.mem_integer_iff] at h'
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h'))

theorem exists_scale (a : F) : ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ (r : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, by simp, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
    refine ⟨⟨a⁻¹, inv_mem_OF a ha⟩, ?_, ?_⟩
    · show a⁻¹ ≠ 0
      exact inv_ne_zero ha0
    · show a⁻¹ * a ∈ 𝒪[F]
      rw [inv_mul_cancel₀ ha0]
      exact one_mem _

variable (L : LocE F E)

theorem tr_ex (x : E) : ∃ a : F, algebraMap F E a = x + L.cj x :=
  (L.cj_fix _).1 (by rw [map_add (f := _), L.cj_cj, add_comm])

theorem nm_ex (x : E) : ∃ a : F, algebraMap F E a = x * L.cj x :=
  (L.cj_fix _).1 (by rw [map_mul, L.cj_cj, mul_comm])

theorem nontrivial_E (L : LocE F E) : Nontrivial E := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h2 := L.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega

theorem exists_theta : ∃ θ ∈ L.O, L.cj θ = -θ ∧ ∃ D : 𝒪[F], (D : F) ≠ 0 ∧ θ * θ = algebraMap F E D := by
  have hx : ∃ x : E, L.cj x ≠ x := by
    by_contra hex
    have hall : ∀ w : E, L.cj w = w := fun w => not_not.mp (not_exists.mp hex w)
    have hle : Module.finrank F E ≤ 1 := by
      have := L.free
      have hw : ∀ w : E, ∃ c : F, c • (1 : E) = w := by
        intro w
        obtain ⟨a, ha⟩ := (L.cj_fix w).1 (hall w)
        exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
      exact finrank_le_one (1 : E) hw
    have h2 := L.rank
    omega
  obtain ⟨x, hx⟩ := hx
  have hc0 : L.cj (x - L.cj x) = -(x - L.cj x) := by
    rw [map_sub, L.cj_cj]
    ring
  have hθ0ne : x - L.cj x ≠ 0 := by
    intro h0
    apply hx
    exact (sub_eq_zero.mp h0).symm
  obtain ⟨D0, hD0⟩ := (L.cj_fix ((x - L.cj x) * (x - L.cj x))).1 (by rw [map_mul, hc0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    have := L.reduced
    exact hθ0ne (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hD0.symm⟩)
  obtain ⟨r, hr0, hrD⟩ := exists_scale D0
  refine ⟨algebraMap F E r * (x - L.cj x), ?_, ?_, ⟨r * ⟨(r : F) * D0, hrD⟩, ?_, ?_⟩⟩
  · apply mem_O_of_quad L _ 0 (-(r * ⟨(r : F) * D0, hrD⟩))
    have e : ((-(r * ⟨(r : F) * D0, hrD⟩) : 𝒪[F]) : F) = -((r : F) * ((r : F) * D0)) := rfl
    have e0 : ((0 : 𝒪[F]) : F) = 0 := rfl
    rw [e, e0, map_zero, map_neg, map_mul, map_mul]
    linear_combination (-(algebraMap F E r) ^ 2) * hD0
  · rw [map_mul, L.cj.commutes, hc0, mul_neg]
  · show (r : F) * ((r : F) * D0) ≠ 0
    exact mul_ne_zero hr0 (mul_ne_zero hr0 hD0ne)
  · show _ = algebraMap F E ((r : F) * ((r : F) * D0))
    rw [map_mul, map_mul, hD0]
    ring

end Top2

section Top3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem decomp (L : LocE F E) (θ : E) (hθc : L.cj θ = -θ) (D : F) (hD : θ * θ = algebraMap F E D) (x : E) :
    ∃ t c : F, algebraMap F E t = x + L.cj x ∧ algebraMap F E c = (x - L.cj x) * θ ∧
      algebraMap F E (2 * D) * x = algebraMap F E (D * t) + algebraMap F E c * θ := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
  obtain ⟨c, hc⟩ := (L.cj_fix ((x - L.cj x) * θ)).1 (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)
  refine ⟨t, c, ht, hc, ?_⟩
  rw [map_mul, map_mul, map_ofNat, ht, hc]
  linear_combination (-(x - L.cj x)) * hD

end Top3

end PI.LocHerm.SlopeTestRemainingChoices
end
end
