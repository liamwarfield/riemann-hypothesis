module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tauB (B : Base F E) : InfinitePlace F → (E →+* ℂ) := fun w => (B.emb w).1

structure Ctx (σ : E →ₐ[F] E) (B : Base F E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E) : Prop where
  good : B.IsGood σ
  hS : IsHermND σ JS
  hT : IsHermND σ JT
  h0 : ξ₀ ≠ 0
  hξ : σ ξ₀ = -ξ₀
  inf : IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ
  chart : IsChartF θ ι


variable (F E) in
def finIdem : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 0 1)

theorem infPartF_finIdem : infPartF F E (finIdem F E) = 0 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem finIdem_smul_fin {nS nT : ℕ} (x : WOF F E nS nT) : (finIdem F E • x).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E (finIdem F E * x i j) = 0
  rw [map_mul, infPartF_finIdem, zero_mul]


variable (F) in
def finRatF {nS nT : ℕ} : Matrix (Fin nT) (Fin nS) E →ₗ[𝓞 E] XFF F E nS nT where
  toFun y := XFF.mk (finIdem F E • ratWF (F := F) y) (finIdem_smul_fin _)
  map_add' x y := XFF.ext (by
    show finIdem F E • ratWF (F := F) (x + y) = finIdem F E • ratWF (F := F) x + finIdem F E • ratWF (F := F) y
    rw [← smul_add]
    congr 1
    funext i j
    exact (incAF F E).map_add (x i j) (y i j))
  map_smul' r x := XFF.ext (by
    show finIdem F E • ratWF (F := F) (r • x) = intAF F r • finIdem F E • ratWF (F := F) x
    rw [smul_comm]
    congr 1
    funext i j
    exact (incAF F E).map_mul (r : E) (x i j))

def infRatF {nS nT : ℕ} (τ : InfinitePlace F → (E →+* ℂ)) : Matrix (Fin nT) (Fin nS) E →+ (IxF F nS nT → ℂ) where
  toFun y := fun p => τ p.2 (y p.1.1 p.1.2)
  map_zero' := funext fun p => (τ p.2).map_zero
  map_add' x y := funext fun p => (τ p.2).map_add _ _

def piWA {nS nT : ℕ} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) : WOF F E nS nT →+ (IxF F nS nT → ℂ) where
  toFun := piWF θ
  map_zero' := funext fun p => by simp [piWF]
  map_add' x y := funext fun p => by simp [piWF]

def iotaA {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

section Lin

variable {κ : Type} [Fintype κ]

def omV (H : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by rw [mulVec_add, dotProduct_add, Complex.add_im]; ring)
    (fun c x y => by rw [mulVec_smul, dotProduct_smul, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)
    (fun x y y' => by rw [star_add, add_dotProduct, Complex.add_im]; ring)
    (fun c x y => by rw [star_smul, star_trivial, smul_dotProduct, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)

theorem omV_apply (H : Matrix κ κ ℂ) (x y : κ → ℂ) : omV H x y = -(star y ⬝ᵥ H *ᵥ x).im := rfl

def jV (s : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) where
  toFun v := Complex.I • s *ᵥ v
  map_add' x y := by rw [mulVec_add, smul_add]
  map_smul' c x := by rw [mulVec_smul, smul_comm]; rfl

theorem jV_apply (s : Matrix κ κ ℂ) (v : κ → ℂ) : jV s v = Complex.I • s *ᵥ v := rfl

def gaussV (H s g : Matrix κ κ ℂ) (v : κ → ℂ) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omV H (g *ᵥ v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omV H (g *ᵥ v - v) (jV s (g *ᵥ v - v)) : ℝ))

end Lin

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)

def IsRatF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (a : Matrix (Fin n) (Fin n) E) : Prop :=
  mtF σ J g = a.map (incAF F E)

def gamQF (ψ : AddChar (AF F) ℂ) (x y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  gamFF σ JS JT ξ₀ ψ (finRatF F x) (finRatF F y)

structure CartF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) : Prop where
  sq : s * s = 1
  pos : (HMF JS JT ξ₀ (tauB B) * s).PosDef
  cen : ∀ (k : GAF σ JT) (t : E), IsRatF σ JT k (t • 1) → s * mMF σ JS JT θ (1, k) = mMF σ JS JT θ (1, k) * s

def IsVacF (ψ : AddChar (AF F) ℂ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (f : WOF F E nS nT → ℂ) : Prop :=
  ∀ x z, deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) f x) 0 +
    Complex.I * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • jV s z)) f x) 0 = 0

def chiLatF (ψ : AddChar (AF F) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E) (x : WOF F E nS nT) : ℂ :=
  if finIdem F E • x ∈ latOF F E nS nT Λ then
    ψ (symplOHF σ JS JT ξ₀ (intAF F w • finIdem F E • x) (finIdem F E • x)) else 0

def serF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E)
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (a : IxF F nS nT → ℂ) : WOF F E nS nT → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WOF F E nS nT) (piWA θ) (iotaA ι) (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y))
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) (chiLatF σ JS JT ξ₀ B.ψ Λ w) a

def zF (η : (AEF F E)ˣ →* Circle) (ε : AEF F E) (h : ε * ε = ε) (p : GAF σ JS × GAF σ JT) : Circle :=
  ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε h p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε h p.2)

structure IsHalfF (ε : AEF F E) : Prop where
  idem : ε * ε = ε
  orth : ε * cAF σ ε = 0
  fin : infPartF F E ε = 0
  split : ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e)

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ModulusDerivativeNormalisation

open PositivityTheory.ThKW.ModulusFactorDefinition

def dCdE {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin n) E :=
  (Matrix.fromRows ((1 / 2 : E) • J⁻¹) (-((1 / 2 : E) • J⁻¹))).submatrix finSumFinEquiv.symm id

def dCd (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  (dCdE J).map (incAF F E)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phase (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (y v : WOF F E nS nT) : ℂ :=
  ψ (symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * y))

def nrm (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) (v : WOF F E nS nT) : ℂ :=
  GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
               (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (dCd F JT * v) f) *
    starRingEnd ℂ (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (dCd F JT * v) f))

end PositivityTheory.ThKW.ModulusDerivativeNormalisation

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def LatH (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) : Prop :=
  ∃ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ ∧ RatSD σ JS JT ξ₀ Λ

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SetIntegralAddRight
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section aux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hOF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (a b : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (dC F E nT * a) (dC F E nT * b) = 0 := by
  have ha : dC F E nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq a
  have hb : dC F E nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq b
  rw [ha, hb]
  unfold hOF
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem symplOHF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (a b : WOF F E nS nT) :
    symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC F E nT * a) (dC F E nT * b) = 0 := by
  simp only [symplOHF, symplOF, hOF_dC, mul_zero, map_zero]

theorem dC_mul_ratWF {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    (dC F E nT * (ratWF γ : WOF F E nS nT) : WOF F E nS (nT + nT)) = ratWF (GlobalTheory.LagrThetaInv.dC E nT * γ) :=
  GlobalTheory.LagrThetaInv.dC_mul_rat γ

theorem setIntegral_add_right {nS nT : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    [ν.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (g : WOF F E nS nT → ℂ)
    (h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v) (u : WOF F E nS nT) :
    ∫ v in 𝓕, g (v + u) ∂ν = ∫ v in 𝓕, g v ∂ν := by
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2

end aux

theorem lagrInt_heis_dC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f → ∀ v : WOF F E nS nT,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
                     (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * v) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ ν 𝓕 _ h𝓕 f hf u
  set g : WOF F E nS nT → ℂ := fun v => f (dC F E nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * u) f
      (dC F E nT * v) = g (v + u) := by
    intro v
    simp only [hg, heisOF]
    rw [symplOHF_dC, AddChar.map_zero_eq_one, one_mul, Matrix.mul_add]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    show f (dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (dC F E nT * v)
    have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * v)
    rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
    rw [Matrix.mul_add, hq]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  exact setIntegral_add_right ν 𝓕 h𝓕 g h2 u

end GlobalTheory.SplitLagrF

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section Alg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem levi_alg (c : R →+* R) (hcc : ∀ x, c (c x) = x) (r : R) (hr : 2 * r = 1) (J : Matrix ι ι R)
    (hJ : (J.map c)ᵀ = J) (hJu : IsUnit J.det) (a : R) (ha : c a = a) (t t' : Matrix ι ι R)
    (h1 : t * t' = 1) (h2 : t' * t = 1) (hs : a • (t - 1) = t - 1) :
    ∃ H H' : Matrix (ι ⊕ ι) (ι ⊕ ι) R, H * H' = 1 ∧ H' * H = 1 ∧
      (H.map c)ᵀ * Matrix.fromBlocks J 0 0 (-J) * H = Matrix.fromBlocks J 0 0 (-J) ∧
      H * Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) * t ∧
      a • (H - 1) = H - 1 ∧
      (∃ M : Matrix ι ι R, IsUnit M.det ∧
        H' * Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) * M) ∧
      H.det * c t.det = t.det := by
  have hcr : c r = r := by
    have := congrArg c hr
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination r * this - c r * hr
  have hT : ∀ {κ : Type} [Fintype κ] (x y : Matrix κ κ R), ((x * y).map c)ᵀ = (y.map c)ᵀ * (x.map c)ᵀ := by
    intro κ _ x y
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hT1 : ((1 : Matrix ι ι R).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one]
  have hTT : ∀ x : Matrix ι ι R, (((x.map c)ᵀ).map c)ᵀ = x := by
    intro x; ext i j; exact hcc _
  have j1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have j2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  obtain ⟨u, hu⟩ : ∃ u, u = (t.map c)ᵀ := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = (t'.map c)ᵀ := ⟨_, rfl⟩
  have u1 : u * u' = 1 := by rw [hu, hu', ← hT, h2, hT1]
  have u2 : u' * u = 1 := by rw [hu, hu', ← hT, h1, hT1]
  obtain ⟨s, hs1⟩ : ∃ s, s = J⁻¹ * u' * J := ⟨_, rfl⟩
  obtain ⟨s', hs2⟩ : ∃ s', s' = J⁻¹ * u * J := ⟨_, rfl⟩
  have s1 : s * s' = 1 := by
    rw [hs1, hs2]
    calc J⁻¹ * u' * J * (J⁻¹ * u * J) = J⁻¹ * (u' * (J * J⁻¹) * u) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [j1, Matrix.mul_one, u2, Matrix.mul_one, j2]
  have s2 : s' * s = 1 := mul_eq_one_comm.1 s1
  have k1 : u * J * s = J := by
    rw [hs1]
    calc u * J * (J⁻¹ * u' * J) = u * (J * J⁻¹) * u' * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [j1, Matrix.mul_one, u1, Matrix.one_mul]
  have k2 : (s.map c)ᵀ * J * t = J := by
    have := congrArg (fun x : Matrix ι ι R => (x.map c)ᵀ) k1
    simp only [hT, hJ] at this
    rw [hu, hTT] at this
    rw [Matrix.mul_assoc, this]
  have a1 : a • (t' - 1) = t' - 1 := by
    have e : t' - 1 = -t' * (t - 1) := by rw [Matrix.mul_sub, Matrix.neg_mul, h2]; simp [sub_eq_add_neg, add_comm]
    rw [e, ← Matrix.mul_smul, hs]
  have a2 : a • (u' - 1) = u' - 1 := by
    ext i j
    have := congrArg c (congrFun (congrFun a1 j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, map_mul, map_sub, ha] at this ⊢
    have e : c ((1 : Matrix ι ι R) j i) = (1 : Matrix ι ι R) i j := congrFun (congrFun hT1 i) j
    rw [e] at this
    rw [hu']
    exact this
  have a3 : a • (s - 1) = s - 1 := by
    have e : s - 1 = J⁻¹ * (u' - 1) * J := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, j2, hs1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, a2]
  have d1 : s.det * c t.det = 1 := by
    have e : c t.det = u.det := by
      rw [hu, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
    have := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul] at this
    refine hJu.mul_left_cancel ?_
    rw [e]
    linear_combination this
  obtain ⟨P, hP⟩ : ∃ P : Matrix (ι ⊕ ι) (ι ⊕ ι) R, P = Matrix.fromBlocks 1 1 1 (-1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (ι ⊕ ι) (ι ⊕ ι) R, Q = r • P := ⟨_, rfl⟩
  have hrr : r • (1 : Matrix ι ι R) + r • 1 = 1 := by
    rw [← add_smul, ← two_mul, hr, one_smul]
  have p1 : P * Q = 1 := by
    rw [hQ, Matrix.mul_smul, hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one]
    simp [hrr]
  have p2 : Q * P = 1 := mul_eq_one_comm.1 p1
  have pT : (P.map c)ᵀ = P := by
    rw [hP]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite c, eq_comm]
  have qT : (Q.map c)ᵀ = Q := by
    ext i j
    have := congrFun (congrFun pT i) j
    simp only [hQ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcr] at this ⊢
    rw [this]
  have c1 : P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have c2 : P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have conj : ∀ X Y : Matrix (ι ⊕ ι) (ι ⊕ ι) R, X * Y = 1 → P * X * Q * (P * Y * Q) = 1 := by
    intro X Y h
    calc P * X * Q * (P * Y * Q) = P * (X * (Q * P) * Y) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p2, Matrix.mul_one, h, Matrix.mul_one, p1]
  refine ⟨P * Matrix.fromBlocks t 0 0 s * Q, P * Matrix.fromBlocks t' 0 0 s' * Q, conj _ _ ?_, conj _ _ ?_, ?_, ?_, ?_,
    ⟨s', ?_, ?_⟩, ?_⟩
  · rw [Matrix.fromBlocks_multiply, h1, s1]; simp
  · rw [Matrix.fromBlocks_multiply, h2, s2]; simp
  · have e1 : P * Matrix.fromBlocks J 0 0 (-J) * P = Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp
    have e2 : ((Matrix.fromBlocks t 0 0 s).map c)ᵀ = Matrix.fromBlocks u 0 0 (s.map c)ᵀ := by
      rw [hu, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]; simp
    have e3 : Matrix.fromBlocks u 0 0 (s.map c)ᵀ * Matrix.fromBlocks 0 (J + J) (J + J) 0 * Matrix.fromBlocks t 0 0 s =
        Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [Matrix.mul_add, Matrix.add_mul, k1, k2]
    rw [hT, hT, pT, qT, e2]
    calc Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * P) * Matrix.fromBlocks J 0 0 (-J) *
          (P * Matrix.fromBlocks t 0 0 s * Q)
        = Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * (P * Matrix.fromBlocks J 0 0 (-J) * P) *
            Matrix.fromBlocks t 0 0 s) * Q := by simp only [Matrix.mul_assoc]
      _ = (Q * P) * Matrix.fromBlocks J 0 0 (-J) * (P * Q) := by
          rw [e1, e3, ← e1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [p1, p2, Matrix.one_mul, Matrix.mul_one]
  · rw [← c1]
    calc P * Matrix.fromBlocks t 0 0 s * Q * (P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t 0 0 s * ((Q * P) * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e : P * Matrix.fromBlocks t 0 0 s * Q - 1 = P * Matrix.fromBlocks (t - 1) 0 0 (s - 1) * Q := by
      have e0 : Matrix.fromBlocks (t - 1) 0 0 (s - 1) = Matrix.fromBlocks t 0 0 s - 1 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg (Matrix.fromBlocks t 0 0 s), Matrix.fromBlocks_neg,
          Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [e0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, p1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.fromBlocks_smul, hs, a3, smul_zero]
  · exact Matrix.isUnit_det_of_left_inverse s1
  · rw [← c2]
    calc P * Matrix.fromBlocks t' 0 0 s' * Q * (P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t' 0 0 s' * ((Q * P) * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e := congrArg Matrix.det p1
    rw [Matrix.det_mul, Matrix.det_one] at e
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
    linear_combination t.det * s.det * c t.det * e + t.det * d1

end Alg

theorem cAF_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rw [hs, hs, GlobalTheory.SplitDetCharF.sig_invol h]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) →
      ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC F E nT = dC F E nT * t.1 ∧
        SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h ∧
        (∃ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det ∧ ∀ (nS : ℕ) (y : WOF F E nS nT),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h⁻¹ * (aC F E nT * y) = aC F E nT * (M * y)) ∧
        ∃ x : (AF F ⊗[F] E)ˣ, IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h x ∧
          ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (m : ℕ), ResEtaF χ m → χ x = χ (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB n JT hT e he t ht
  have hc : IsCMExt F E σ := hB.cm
  have hcc := cAF_invol hc
  obtain ⟨r, hr⟩ : ∃ r : AEF F E, 2 * r = 1 := by
    have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
    rw [map_ofNat] at h
    exact h.exists_right_inv
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have ha : cAF σ (e + cAF σ e) = e + cAF σ e := by rw [RingHom.map_add (f := _), hcc, add_comm]
  obtain ⟨H, H', g1, g2, g3, g4, g5, ⟨M, hM, g6⟩, g7⟩ := levi_alg (cAF σ) hcc r hr _ hJ hu _ ha t.1 (t⁻¹).1
    t.mul_inv t.inv_mul (by ext i j; exact ht i j)
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  let G : GL (Fin (n + n)) (AF F ⊗[F] E) :=
    ⟨H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      by rw [Matrix.submatrix_mul_equiv, g1, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, g2, Matrix.submatrix_one_equiv]⟩
  have hG : G ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    show ((H.map (cAF σ))ᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) *
      H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    rw [eJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, g3]
  obtain ⟨h, m1, m2⟩ : ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
      mtF σ _ h = H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      mtF σ _ h⁻¹ = H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := ⟨⟨G, hG⟩, rfl, rfl⟩
  have sub : ∀ (X : Matrix (Fin n ⊕ Fin n) (Fin n) (AEF F E)) (Y : Matrix (Fin n) (Fin n) (AEF F E)),
      (X * Y).submatrix (finSumFinEquiv (m := n) (n := n)).symm id = X.submatrix finSumFinEquiv.symm id * Y :=
    fun X Y => rfl
  have e1 : e * e = e := he.1
  have e2 : e * cAF σ e = 0 := he.2.1
  have e3 : cAF σ e * cAF σ e = cAF σ e := by rw [← RingHom.map_mul, e1]
  have hd : (1 - (e + cAF σ e)) * (t.1.det - 1) = 0 :=
    GlobalTheory.SplitDetCharF.mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, ht i j, sub_self]
  refine ⟨h, ?_, ?_, ⟨M, hM, fun nS y => ?_⟩,
    GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h, ?_, fun χ m hχ => ?_⟩
  · rw [m1, dC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id) g4
  · intro i j
    rw [m1, ← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm]
    exact congrFun (congrFun g5 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  · rw [m2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, aC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id * y) g6
  · exact add_comm _ _
  · let w : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut (cAF σ e) e3) (Matrix.GeneralLinearGroup.det t)
    let u : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut e e1) (Matrix.GeneralLinearGroup.det t)
    have hw : (w : AEF F E) = (1 - cAF σ e) + cAF σ e * t.1.det := rfl
    have hu' : (u : AEF F E) = (1 - e) + e * t.1.det := rfl
    have huw : Matrix.GeneralLinearGroup.det t = u * w := by
      refine Units.ext ?_
      rw [Units.val_mul, hw, hu', Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination hd - (t.1.det - 1) ^ 2 * e2
    obtain ⟨w', hw'⟩ : IsUnit (cAF σ (w : AEF F E)) := w.isUnit.map (cAF σ)
    have hx : GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h * w' = u := by
      refine Units.ext ?_
      rw [Units.val_mul, hw', hw, hu', GlobalTheory.SplitDetCharF.cutDet_val, m1, Matrix.det_submatrix_equiv_self,
        RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hcc]
      linear_combination (H.det - 1) * (cAF σ t.1.det - 1) * e1 + e * g7
    have hy := GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hc hχ w'⁻¹ w (by rw [← hw', Units.inv_mul])
    rw [huw, map_mul, ← hy, ← map_mul, ← hx, mul_inv_cancel_right]

end GlobalTheory.SplitLagrF

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
noncomputable section

open scoped TensorProduct Matrix Topology nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_trace_one (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ b : 𝓞 E, Algebra.trace F E (b : E) = 1 := by
  classical
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have e := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [htop, FractionalIdeal.coeIdeal_top] at e
    exact inv_eq_one.mp e.symm
  let J : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  by_cases hJ : J = ⊤
  · have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have := Algebra.algebraMap_intTrace (K := F) (L := E) (A := 𝓞 F) b
    rw [hb, map_one] at this
    exact this.symm
  · exfalso
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hJ
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)
    obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    have hmem : algebraMap F E t ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      have hb : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hJp ⟨b, rfl⟩
      have hp0' : (p : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
      have h2 : t * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) b) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        have := FractionalIdeal.mul_mem_mul ht ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
        rwa [inv_mul_cancel₀ hp0'] at this
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h2
      refine ⟨c, ?_⟩
      rw [hc, Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
        Algebra.algebraMap_intTrace (L := E)]
    rw [hd] at hmem
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (B := E), ← hc]
      exact RingOfIntegers.isIntegral_coe c
    exact ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, hint⟩, rfl⟩)

theorem exists_w (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ w : 𝓞 E, w + sgOF σ w = 1 := by
  obtain ⟨b, hb⟩ := exists_trace_one hu
  refine ⟨b, RingOfIntegers.ext ?_⟩
  show (b : E) + σ b = 1
  rw [← PositivityTheory.ThKG.Tow.Pln.trace_cm h, hb, map_one]

theorem sg_comm (h : IsCMExt F E σ) (g : E ≃ₐ[ℚ] E) (x : E) : g (σ x) = σ (g x) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  have h1 := h.2.2.2 (τ.comp (g : E →+* E)) x
  have h2 := h.2.2.2 τ (g x)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h1
  rw [h2]
  exact h1

theorem sg_sg (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sg_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  have := h.2.1
  by_contra hn
  push Not at hn
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hn y] at this
  simpa using this.symm

theorem inertQ_of_fix (h : IsCMExt F E σ) [IsGalois ℚ E] {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hfix : ∀ r ∈ P, sgOF σ r ∈ P) : InertQF σ q := by
  intro Q hQ hqQ r hr
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP.isPrime hqP
  haveI := key Q hQ.isPrime hqQ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr ⊢
  have e : g⁻¹ • sgOF σ r = sgOF σ (g⁻¹ • r) := RingOfIntegers.ext (sg_comm h g⁻¹ r)
  rw [e]
  exact hfix _ hr

theorem exists_move (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {P : Ideal (𝓞 E)}
    (hP : P.IsMaximal) : ∃ r, sgOF σ r - r ∉ P := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := sg_sg h
  haveI : P.IsMaximal := hP
  have : (P.under (𝓞 F)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (P.under (𝓞 F)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => by
    obtain ⟨x, hx⟩ := sg_ne h
    exact hx (congrArg (fun t : E ≃ₐ[F] E => t x) hs)
  by_contra hn
  push Not at hn
  have hs : s ∈ P.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 fun x => hn x
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hs1 hs

theorem exists_goodNorm (h : IsCMExt F E σ) [IsGalois ℚ E] (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) :
    ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  classical
  obtain ⟨lam, h0, h1, h2⟩ := GlobalTheory.FinWeil.exists_lam (InertQF σ)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  obtain ⟨q, hq, hqP, hf, hc⟩ := GlobalTheory.FinWeil.exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun hfix => ⟨?_, exists_move h hu hP⟩⟩
  · rw [hc]
    by_cases hI : InertQF σ q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · rw [hc]
    exact h1 q hq hf (inertQ_of_fix h hP hq hqP hfix)

end PositivityTheory.ThKW.LatB

end
end
