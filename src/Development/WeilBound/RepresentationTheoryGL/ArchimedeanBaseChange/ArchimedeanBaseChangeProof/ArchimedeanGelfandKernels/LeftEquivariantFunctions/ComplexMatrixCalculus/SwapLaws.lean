module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
noncomputable section

open Matrix
open scoped ComplexConjugate Kronecker

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

abbrev Md (n : ℕ) := Fin (n * n)

def hbM (m : Md n) : Mat n := hb (finProdFinEquiv.symm m)

def cf (n : ℕ) : Mat n →ₗ[ℝ] (Md n → ℂ) where
  toFun H m := (((H * hbM m).trace).re : ℂ)
  map_add' H H' := by ext m; simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' r H := by ext m; simp [Matrix.trace_smul]

def Mt (y : Mat n) : Matrix (Md n) (Md n) ℂ := fun p q => cf n (y * hbM q * yᴴ) p

abbrev abelian₂ (n : ℕ) := ExteriorAlgebra ℂ (Md n → ℂ)

def fb (n : ℕ) : Module.Basis (Finset (Md n)) ℂ (abelian₂ n) := (Pi.basisFun ℂ (Md n)).ExteriorAlgebra

def matL (n : ℕ) : (abelian₂ n →ₗ[ℂ] abelian₂ n) ≃ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ := LinearMap.toMatrix (fb n) (fb n)

def dualOf (w : Md n → ℂ) : Module.Dual ℂ (Md n → ℂ) where
  toFun v := w ⬝ᵥ v
  map_add' v v' := dotProduct_add w v v'
  map_smul' c v := dotProduct_smul c w v

def creL (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ :=
  (matL n).toLinearMap ∘ₗ (LinearMap.mul ℂ (abelian₂ n)) ∘ₗ ExteriorAlgebra.ι ℂ

def annL (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ where
  toFun w := matL n (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf w))
  map_add' w w' := by
    rw [← map_add (f := _), ← map_add (f := _)]; congr 2; ext v; simp [dualOf, add_dotProduct]
  map_smul' c w := by
    rw [RingHom.id_apply, ← map_smul, ← map_smul]; congr 2; ext v; simp [dualOf, smul_dotProduct]

def gamM (g : Matrix (Md n) (Md n) ℂ) : Matrix (Finset (Md n)) (Finset (Md n)) ℂ :=
  matL n (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap

def dw (lam : Fin n → ℤ) : Formalism.BasicNotions.DomWeight n :=
  if h : Antitone lam then ⟨lam, h⟩ else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

abbrev Jd (n : ℕ) (lam : Fin n → ℤ) := Fin (Module.finrank ℂ (Formalism.BasicNotions.nablaSq ℂ n (dw lam)))

def wb (lam : Fin n → ℤ) : Module.Basis (Jd n lam) ℂ (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) := Module.finBasis ℂ _


open Classical in
def Rm (lam : Fin n → ℤ) (x : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  if h : IsUnit x.det then LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h))
  else 0

def rhoW (lam : Fin n → ℤ) (x : Mat n) : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ :=
  ((Rm lam x)⁻¹)ᵀ ⊗ₖ (Rm lam xᴴ)ᵀ

def swapJ (lam : Fin n → ℤ) : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

abbrev Ix (n : ℕ) (lam : Fin n → ℤ) := Finset (Md n) × (Jd n lam × Jd n lam)

abbrev EV (n : ℕ) (lam : Fin n → ℤ) := EuclideanSpace ℂ (Ix n lam)

def clm (lam : Fin n → ℤ) (A : Matrix (Ix n lam) (Ix n lam) ℂ) : EV n lam →L[ℂ] EV n lam := Matrix.toEuclideanCLM (𝕜 := ℂ) A

def fr0 (lam : Fin n → ℤ) (x : Mat n) : Matrix (Ix n lam) (Ix n lam) ℂ := gamM (Mt x⁻¹)ᵀ ⊗ₖ rhoW lam x

instance instMeasUK : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _
instance instBorelUK : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

def gramQ (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  ∫ k : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (clm lam (fr0 lam k.1)) * clm lam (fr0 lam k.1)
    ∂MeasureTheory.Measure.haar

def sqQ (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam := CFC.sqrt (gramQ lam)

def cjL (lam : Fin n → ℤ) : Matrix (Ix n lam) (Ix n lam) ℂ →ₗ[ℂ] (EV n lam →L[ℂ] EV n lam) :=
  (LinearMap.mulLeft ℂ (sqQ lam) ∘ₗ LinearMap.mulRight ℂ (Ring.inverse (sqQ lam))) ∘ₗ
    { toFun := clm lam, map_add' := fun A B => map_add _ A B, map_smul' := fun c A => map_smul _ c A }

def krL (n : ℕ) (lam : Fin n → ℤ) :
    Matrix (Finset (Md n)) (Finset (Md n)) ℂ →ₗ[ℂ] Matrix (Ix n lam) (Ix n lam) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)
  map_add' A B := Matrix.add_kronecker A B _
  map_smul' c A := by simp [Matrix.smul_kronecker]

def lefFr (n : ℕ) (lam : Fin n → ℤ) (x : Mat n) : EV n lam →L[ℂ] EV n lam := cjL lam (fr0 lam x)

def lefε (n : ℕ) (lam : Fin n → ℤ) : Mat n →ₗ[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  ((cjL lam ∘ₗ krL n lam ∘ₗ
    creL n).restrictScalars ℝ) ∘ₗ cf n

def lefι (n : ℕ) (lam : Fin n → ℤ) : Mat n →ₗ[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  ((cjL lam ∘ₗ krL n lam ∘ₗ
    annL n).restrictScalars ℝ) ∘ₗ cf n

def lefS (n : ℕ) (lam : Fin n → ℤ) (s : ℝ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam (gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ))

def lefΓ (n : ℕ) (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam (gamM (-1 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ))

def lefT (n : ℕ) (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam)

end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
noncomputable section

open Matrix
open scoped ComplexConjugate Kronecker ContDiff

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HbOrtho : Prop := ∀ n : ℕ, (∀ p q : Md n, (hbM p * hbM q).trace = if p = q then 1 else 0) ∧ ∀ p : Md n, (hbM p).IsHermitian

def HbExp : Prop := ∀ (n : ℕ) (H : Mat n), H.IsHermitian → H = ∑ m, cf n H m • hbM m

def CfPair : Prop := ∀ (n : ℕ) (H H' : Mat n), H.IsHermitian → H'.IsHermitian → ∑ m, cf n H m * cf n H' m = (H * H').trace

def MtLaws : Prop := ∀ n : ℕ, Mt (1 : Mat n) = 1 ∧ (∀ x y : Mat n, Mt (x * y) = Mt x * Mt y) ∧
  (∀ (x H : Mat n), H.IsHermitian → Mt x *ᵥ cf n H = cf n (x * H * xᴴ)) ∧
  (∀ (x H : Mat n), H.IsHermitian → (Mt x)ᵀ *ᵥ cf n H = cf n (xᴴ * H * x))

def GamMul : Prop := ∀ n : ℕ, gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 ∧ ∀ g h : Matrix (Md n) (Md n) ℂ, gamM (g * h) = gamM g * gamM h

def Car : Prop := ∀ (n : ℕ) (v w : Md n → ℂ), annL n w * creL n v + creL n v * annL n w = (w ⬝ᵥ v) • 1

def GamCre : Prop := ∀ (n : ℕ) (g : Matrix (Md n) (Md n) ℂ) (v w : Md n → ℂ),
  gamM g * creL n v = creL n (g *ᵥ v) * gamM g ∧ annL n w * gamM g = gamM g * annL n (gᵀ *ᵥ w)

def GamScal : Prop := ∀ (n : ℕ) (s : ℂ), gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) = Matrix.diagonal fun A => s ^ A.card

def Number : Prop := ∀ (n : ℕ) (s : ℂ),
  ∑ m : Md n, creL n (Pi.single m 1) * gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) * annL n (Pi.single m 1) =
    Matrix.diagonal fun A => (A.card : ℂ) * s ^ (A.card - 1)

def GamDer : Prop := ∀ n : ℕ, ContDiff ℂ ∞ (gamM (n := n)) ∧
  ∀ B : Matrix (Md n) (Md n) ℂ, fderiv ℂ (gamM (n := n)) 1 B = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1))

def RmLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Rm lam (1 : Mat n) = 1 ∧
  (∀ x y : Mat n, IsUnit x.det → IsUnit y.det → Rm lam (x * y) = Rm lam x * Rm lam y) ∧ ContDiffOn ℝ ∞ (Rm lam) (GLs n)

def RmChar : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ t : Fin n → ℂ, (∀ a, t a ≠ 0) → Function.Injective t →
  (Rm lam (diagonal t)).trace = weylChar lam t

def RmHol : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (M : Matrix (Jd n lam) (Jd n lam) ℂ) (i j : Jd n lam),
  ∀ g ∈ GLs n, (∀ m, gel true m (fun x => (Rm lam x * M) i j) g = GlobalTheory.Dec.gelfVal (infOf lam true) m * (Rm lam g * M) i j) ∧
    ∀ a b, Eu false a b (fun x => (Rm lam x * M) i j) g = 0

def RmAnti : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (M : Matrix (Jd n lam) (Jd n lam) ℂ) (i j : Jd n lam),
  ∀ g ∈ GLs n, (∀ m, gel false m (fun x => (Rm lam (x⁻¹)ᴴ * M) i j) g = GlobalTheory.Dec.gelfVal (infOf lam false) m * (Rm lam (g⁻¹)ᴴ * M) i j) ∧
    ∀ a b, Eu true a b (fun x => (Rm lam (x⁻¹)ᴴ * M) i j) g = 0

def EigProd : Prop := ∀ (n : ℕ) (χ : Inf n) (ι V : Type) [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
  (h a : ι → Mat n → ℂ) (v : ι → V), (∀ i, ContDiffOn ℝ ∞ (h i) (GLs n)) → (∀ i, ContDiffOn ℝ ∞ (a i) (GLs n)) →
  (∀ i, ∀ g ∈ GLs n, (∀ m, gel true m (h i) g = GlobalTheory.Dec.gelfVal (χ true) m * h i g) ∧ ∀ b c, Eu false b c (h i) g = 0) →
  (∀ i, ∀ g ∈ GLs n, (∀ m, gel false m (a i) g = GlobalTheory.Dec.gelfVal (χ false) m * a i g) ∧ ∀ b c, Eu true b c (a i) g = 0) →
  IsEig χ fun x => ∑ i, (h i x * a i x) • v i

def Avg : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), IsUnit (sqQ lam) ∧ IsSelfAdjoint (sqQ lam) ∧ sqQ lam * sqQ lam = gramQ lam ∧
  (∀ k : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (clm lam (fr0 lam k.1)) * gramQ lam * clm lam (fr0 lam k.1) = gramQ lam) ∧
  ∀ U : Matrix (Ix n lam) (Ix n lam) ℂ, U ∈ Matrix.unitaryGroup (Ix n lam) ℂ →
    (∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U) → clm lam U * sqQ lam = sqQ lam * clm lam U

def MatrixFrechetDerivativeAtZeroLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), fr0 lam (1 : Mat n) = 1 ∧
  (∀ x y : Mat n, IsUnit x.det → IsUnit y.det → fr0 lam (x * y) = fr0 lam x * fr0 lam y) ∧ ContDiffOn ℝ ∞ (fr0 lam) (GLs n)

def SwapLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), swapJ lam * swapJ lam = 1 ∧ swapJ lam ∈ Matrix.unitaryGroup _ ℂ ∧
  (∀ x : Mat n, IsUnit x.det → swapJ lam * rhoW lam (xᴴ)⁻¹ = rhoW lam x * swapJ lam) ∧
  (∀ X : Mat n, X.IsHermitian → swapJ lam * fderiv ℝ (rhoW lam) 1 X = -(fderiv ℝ (rhoW lam) 1 X * swapJ lam)) ∧
  ∀ A B : Matrix (Jd n lam) (Jd n lam) ℂ, ((A ⊗ₖ B) * swapJ lam).trace = (A * B).trace

def WedgeDer : Prop := ∀ n : ℕ, ∑ p : Fin n × Fin n, creL n (cf n (hb p)) *
  fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p) = 0

end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK
noncomputable section

namespace PositivityTheory.RgBcC

variable {n : ℕ}

def FrOne : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), lefFr n lam 1 = 1

def FrMulK : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ),
  lefFr n lam (k * k').1 = lefFr n lam k.1 * lefFr n lam k'.1

def FrIso : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) (v : EV n lam), ‖lefFr n lam k.1 v‖ = ‖v‖

def FrCont : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => lefFr n lam k.1

end PositivityTheory.RgBcC
end
end
