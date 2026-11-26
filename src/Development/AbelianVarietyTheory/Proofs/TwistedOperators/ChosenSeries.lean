module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LPol (b a : ℕ) : Type := MvPolynomial (Fin b × Fin a) ℂ

section Local

variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

def rai (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (i, j))
    else -(MvPolynomial.pderiv (i, j)).toLinearMap)

def low (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (i, j)))

def locS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def locT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def IsPolyIso {p q r s : ℕ} (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b) (κ : LPol b a ≃ₗ[ℂ] Pol p q r s) : Prop :=
  (∀ (Z : Mat p q) (P : LPol b a), κ (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (κ P)) ∧
    ∀ (Z : Mat r s) (P : LPol b a), κ (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (κ P)

end Local

structure IsCoverIt {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) : Prop where
  bdd : ∀ P, ∃ c : ℝ, ∀ y, ‖B P y‖ ≤ c * ‖y‖
  kfin : ∀ P y, B P y ∈ Set.range R₁.ι
  ne : ∀ y, y ≠ 0 → ∃ P, B P y ≠ 0
  src : ∀ Z ∈ upq p q, ∀ P y,
    HasDerivAt (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) (B (fockAct1 p q r s Z P) y) 0
  tgt : ∀ Z ∈ upq r s, ∀ P y,
    HasDerivAt (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) (-B (fockAct2 p q r s Z P) y) 0

variable {D : D7}

def glue {a b : ℕ} (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)


open Classical in
def GlueLaw (D : D7) (a b : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ ∧
    ∀ (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : D.what₂.Tau → LPol b a),
      (∀ X, fockS τ ε ε' X (glue P) = glue (Function.update P τ (locS ε ε' X (P τ)))) ∧
        ∀ Y, fockT τ ε ε' Y (glue P) = glue (Function.update P τ (locT ε ε' Y (P τ)))

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure LocIt (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ) : Prop where
  sm : ∀ P y, A P y ∈ M.sm τ
  ne : ∃ P, ∃ y ∈ M'.sm τ, A P y ≠ 0
  adj : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (A P y))
    (A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y) 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P y, HasDerivAt (fun t : ℝ => A P (M'.rep τ (NormedSpace.exp (t • Y)) y))
    (-A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y) 0

def srcOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tgtOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure GlobIt (aS aT : D.what₂.Tau → ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) : Prop where
  incl : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v)
  ne : It ≠ 0
  adj : ∀ φ w, ellT M w ∘ₗ I φ ∈ Submodule.span ℂ (Set.range (ellT M'))
  src : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (I φ x)))
      (ellT M w (I (srcOp M M' τ (aT τ) X φ) x)) 0
  tgt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (I φ (actT M' τ (NormedSpace.exp (t • Y)) x)))
      (-ellT M w (I (tgtOp M M' τ (aS τ) Y φ) x)) 0

structure TensorLaw : Prop where
  sep : ∀ x : ⨂[ℂ] τ, M.H τ, (∀ w, ellT M w x = 0) → x = 0
  inj : Function.Injective (inclT M)
  one : ∀ τ, actT M τ 1 = LinearMap.id
  mul : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actT M τ (g * g') = actT M τ g ∘ₗ actT M τ g'
  adj : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, ∃ w', ellT M w ∘ₗ actT M τ g = ellT M w'

def ChosenSeries (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam

end GlobalTheory.Chain.RealIt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7}

theorem blkGL_mem (V V₁ : HSp D) (g : GA D V × GA D V₁) :
    blkGL finSumFinEquiv (g.1.1, g.2.1) ∈ HR (AF D.host.F) D.sp.cm.sig (hsum V V₁).gram := by
  have hJ : JR (F := D.host.F) (AF D.host.F) (hsum V V₁).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) V.gram) (JR (F := D.host.F) (AF D.host.F) V₁.gram) := by
    unfold JR
    rw [gram_hsum]
    exact blkMat_map _ _ (map_zero _) _ _
  unfold HR
  rw [hJ]
  exact (blkGL_mem_UJ finSumFinEquiv).2 ⟨g.1.2, g.2.2⟩

def blk (V V₁ : HSp D) : GA D V × GA D V₁ →* GA D (hsum V V₁) where
  toFun g := ⟨blkGL finSumFinEquiv (g.1.1, g.2.1), blkGL_mem V V₁ g⟩
  map_one' := Subtype.ext (map_one (blkGL finSumFinEquiv))
  map_mul' g h := Subtype.ext (map_mul (blkGL finSumFinEquiv) (g.1.1, g.2.1) (h.1.1, h.2.1))

theorem mt_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    Formalism.L2.Theta.mt (hsum V V₁) (blk V V₁ (g, g₁)) =
      blkMat finSumFinEquiv (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁) := rfl

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]; exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases h : a = b
        · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
        · simp [Formalism.REAL.Jm, h]
      show (A.fr τ)ᴴ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = gramAt D (neg V) τ
      rw [e, e', ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

def frSum {V V₁ : HSp D} (A : Fr V) (B : Fr V₁) : Fr (hsum V V₁) where
  ε τ := Fin.append (A.ε τ) (B.ε τ)
  fr τ := blkMat finSumFinEquiv (A.fr τ) (B.fr τ)
  fr_unit τ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_blkMat]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)).mul ((Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ))
  fr_gram τ := by
    have e : gramAt D (hsum V V₁) τ = blkMat finSumFinEquiv (gramAt D V τ) (gramAt D V₁ τ) := by
      unfold gramAt
      rw [gram_hsum]; exact blkMat_map _ _ (map_zero _) _ _
    have e' : Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) =
        blkMat finSumFinEquiv (Formalism.REAL.Jm (A.ε τ)) (Formalism.REAL.Jm (B.ε τ)) := by
      refine submatrix_inj finSumFinEquiv ?_
      rw [submatrix_blkMat]
      ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega
    have e'' : (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))ᴴ = blkMat finSumFinEquiv (A.fr τ)ᴴ (B.fr τ)ᴴ := by
      simp [GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
    rw [e, e', e'', blkMat_mul, blkMat_mul, A.fr_gram, B.fr_gram]

section Vec

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)

def IsFinF (f : WO M X → ℂ) : Prop := IsVacF ψ θ (frSgn ε A) B f

def fockF (f : WO M X → ℂ) : PolF D X.rank M.rank →ₗ[ℂ] (WO M X → ℂ) :=
  pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart A.onb B.onb f

def algF : Submodule ℂ (WO M X → ℂ) := Submodule.span ℂ {Φ | ∃ f P, IsFinF ψ θ ε A B f ∧ Φ = fockF ψ θ ε A B f P}

end Vec

def IsHaarFD (M : HSp D) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ M) 𝓕 ν

def thetaInt {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) (h : GA D X) : ℂ :=
  ∫ g in 𝓕, thetaKO ω g h Φ ∂ν

def ModInt (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) : Prop :=
  ∃ (N : ℕ) (C : ℝ), ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν ∧
    ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N

def finRel {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) : Submodule ℂ (WO M X → ℂ) :=
  Submodule.span ℂ {Φ | ∃ u ∈ GfC M, ∃ Ψ ∈ S, Φ = ω (u, 1) Ψ - Ψ}

structure IsTriple (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle) : Prop where

  hecA : IsHeckeChar D α

  hecB : IsHeckeChar D β

  resA : ResEta D α W₁.rank

  resB : ResEta D β W.rank

  rank : X.rank = W.rank + W₁.rank

  even : Even X.rank

  sig : ∃ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) ∧
    W₁.rank + 2 * (2 * (p + q) + 1) < W.rank ∧ 2 * (p + q) + 1 < W₁.rank

  gap : ∀ τ, ∃ a b : ℚ, HasInfExp D α τ a ∧ HasInfExp D β τ b ∧ 2 * (a - b) < -(X.rank : ℚ)

  ram : ∀ v e, IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e α ∧ GlobalTheory.WeilParts.UnramAt e β) ∨
    (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (α / β) ∧
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F))

structure IsMatch (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil ψ true W X β (β / α) ωA

  weilB : IsWeil ψ false W₁ X α (α / β) ωB

  irred : IsIrred X Pi rf rl

  mapA : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p

  mapB : IsCoinvMap θ ωB (algF ψ θ false A₁ B) Pi rf rl p'

end GlobalTheory.SquareComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.IwahoriInj ValuativeRel

namespace GlobalTheory.JacInj

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π₁ : Representation ℂ G V} {π : Representation ℂ G W}

theorem map_apply' (f : π₁.IntertwiningMap π) (g : G) (v : V) : f (π₁ g v) = π g (f v) := by
  have h := LinearMap.congr_fun (f.isIntertwining' g) v
  simpa using h

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_map (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : f v ∈ twKer π H 1) :
    v ∈ twKer π₁ H 1 := by
  have h₁ : IsSmooth π₁ := by
    intro w
    have hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← map_apply' f g w]
      exact hf.eq_iff.symm
    rw [hset]
    exact hπ (f w)
  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix h₁ hH v
  letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hUf : ∀ u ∈ U, π (u : H) (f v) = f v := fun u hu => by rw [← map_apply', hUv u hu]
  rw [← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]
  apply hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]
  simp only [map_apply']
  rw [← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]
  exact (GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def wt (e : (Σ a, m a) ≃ n) (M : ℕ) (i j : n) : ℤ :=
  M * (((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card)

theorem conc_wt (e : (Σ a, m a) ≃ n) (M : ℕ) : Conc (wt e M) := by
  unfold GlobalTheory.IwahoriInj.Conc
  refine ⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩
  simp only [wt]
  ring

private theorem eventually_valuation_le_uniformizer_pow_of_mem_unipRad (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ unipRad k e) (i j : n) :
    ∀ᶠ M : ℕ in Filter.atTop, valuation k ((g : Matrix n n k) i j) ≤ uniformizer k ^ wt e M i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hP
  have hmono : ∀ a b : ℤ, a ≤ b → uniformizer k ^ b ≤ uniformizer k ^ a := by
    intro a b hab
    exact zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab
  rcases lt_trichotomy (blk e i) (blk e j) with h | h | h
  ·
    obtain ⟨N, hN⟩ := MulArchimedean.arch (valuation k ((g : Matrix n n k) i j))
      ((one_lt_inv₀ uniformizer_pos).2 uniformizer_lt_one)
    have hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j) := by
      refine (Finset.ssubset_iff_of_subset (fun x hx => ?_)).2 ⟨blk e i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h
      · simp [h]
      · simp
    have hlt := Finset.card_lt_card hss
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hM' : (N : ℤ) ≤ M := by exact_mod_cast hM
    have hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) -
        (Finset.univ.filter (· < blk e j)).card ≤ -1 := by omega
    have hw : wt e M i j ≤ -(N : ℤ) := by
      simp only [wt]
      nlinarith
    refine hN.trans (le_trans (le_of_eq ?_) (hmono _ _ hw))
    rw [zpow_neg, zpow_natCast, inv_pow]
  ·
    refine Filter.Eventually.of_forall fun M => ?_
    have hw : wt e M i j = 0 := by simp [wt, h]
    rw [hw, zpow_zero]
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at h
    cases h
    rw [hD _ i' j', Matrix.one_apply]
    split_ifs <;> simp
  ·
    exact Filter.Eventually.of_forall fun M => by
      rw [hP i j h, map_zero]
      exact zero_le'

theorem eventually_mem_grp (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, u ∈ grp k (conc_wt e M) := by
  unfold GlobalTheory.IwahoriInj.grp
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  unfold GlobalTheory.IwahoriInj.Deep
  have hu' : u⁻¹ ∈ unipRad k e := inv_mem hu
  exact (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)

private theorem t2Space_localField : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x}, ?_, fun h => lt_irrefl (valuation k x) (by simpa using h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((valuation k).ne_zero_iff.2 hx), fun y hy => by simpa using hy⟩

theorem isClosed_unipRad (e : (Σ a, m a) ≃ n) : IsClosed (unipRad k e : Set (GL n k)) := by
  have : T2Space k := t2Space_localField
  have hv : Continuous fun g : GL n k => (g : Matrix n n k) := Units.continuous_val
  have hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j := fun i j => hv.matrix_elem i j
  have hset : (unipRad k e : Set (GL n k)) =
      {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩
        {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eventually_mem_twKer_inf (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {v : V}
    (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, v ∈ twKer π (grp k (conc_wt e M) ⊓ unipRad k e) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_grp e u.2] with M hM
    exact Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩
  | zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  | smul c x _ hx =>
    filter_upwards [hx] with M h
    exact Submodule.smul_mem _ c h

private theorem twKer_one_mono' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H K : Subgroup G} (hHK : H ≤ K) : twKer ρ H 1 ≤ twKer ρ K 1 := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, w, rfl⟩
  exact ⟨⟨h, hHK h.2⟩, w, rfl⟩

theorem jacMap_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W)
    (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f) :
    Function.Injective (jacMap e f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u) :=
    fun _ => rfl
  rw [hmk, hmk, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨M, hM⟩ := (eventually_mem_twKer_inf e hxy).exists
  have hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)
  exact twKer_one_mono' inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)

end GlobalTheory.JacInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjectiveStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_map_injective_of_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W) (f : π₁.IntertwiningMap π), IsSmooth π → Function.Injective f → Function.Injective (jacMap e f) := by
  first | exact @GlobalTheory.JacInj.jacMap_injective | exact GlobalTheory.JacInj.jacMap_injective | (intros; apply GlobalTheory.JacInj.jacMap_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.UnramFixed

theorem occursTimes_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ θ η : G →* ℂˣ} (h : ∀ g v, τ g v = (δ g : ℂ) • ρ g v)
    (hη : ∀ g, η g = θ g * δ g) {r : ℕ} (hr : OccursTimes (ofChar θ) ρ r) :
    OccursTimes (ofChar η) τ r := by
  obtain ⟨S, T, h1, h2, h3⟩ := hr
  have hst : ∀ (P : Subrepresentation ρ) (g : G) (v : V), v ∈ P.toSubmodule → τ g v ∈ P.toSubmodule :=
    fun P g v hv => by
      rw [h]
      exact P.toSubmodule.smul_mem _ (P.apply_mem_toSubmodule g hv)
  refine ⟨fun i => ⟨(S i).toSubmodule, hst (S i)⟩, fun i => ⟨(T i).toSubmodule, hst (T i)⟩,
    fun i => h1 i, fun i j hij => h2 i j hij, fun i => ?_⟩
  obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
  refine step_iff.2 ⟨f, hsurj, fun g v hv => ?_, hker⟩
  have e := hint g v hv
  rw [ofChar_apply] at e
  show f (τ g v) = ofChar η g (f v)
  rw [h, map_smul, e, ofChar_apply, hη, Units.val_mul, smul_eq_mul]
  ring

theorem jhMult_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ : G →* ℂˣ} (θ : G →* ℂˣ)
    (h : ∀ g v, τ g v = (((δ g)⁻¹ : ℂˣ) : ℂ) • ρ g v) :
    jhMult (ofChar θ) τ = jhMult (ofChar (θ * δ)) ρ := by
  have key : ∀ r, OccursTimes (ofChar θ) τ r ↔ OccursTimes (ofChar (θ * δ)) ρ r := fun r =>
    ⟨occursTimes_of_twist (δ := δ)
        (fun g v => by rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
        (fun g => MonoidHom.mul_apply θ δ g),
      occursTimes_of_twist (δ := δ⁻¹) (fun g v => by rw [MonoidHom.inv_apply]; exact h g v)
        (fun g => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right])⟩
  simp only [jhMult, key]

private lemma pres_iterate_zero {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) (S : Subrepresentation ρ)
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = ofChar θ g (f v)) (v : V)
    (hv : v ∈ S.toSubmodule) : ∃ u ∈ fixed ρ H, u ∈ S.toSubmodule ∧ f u = f v := by

  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix hρ hH v
  haveI : U.FiniteIndex := hU
  letI : Fintype (H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨GlobalTheory.LocGL.idem hρ hH v, GlobalTheory.LocGL.idem_mem hρ hH v, ?_, ?_⟩
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv]
    exact S.toSubmodule.smul_mem _ (S.toSubmodule.sum_mem fun q _ => S.apply_mem_toSubmodule _ hv)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv, map_smul, map_sum]
      have hq : ∀ q : H ⧸ U, f (ρ (q.out : H) v) = f v := fun q => by
        rw [hf _ v hv, ofChar_apply, hθ _ (q.out).2, Units.val_one, one_mul]
      have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
      simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem jhMult_onFixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) :
    jhMult (ofChar θ) ρ = jhMult (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) := by
  let ι : (onFixed ρ H (MonoidHom.id G) hn).IntertwiningMap ρ :=
    { toLinearMap := (fixed ρ H).subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have key : ∀ r, OccursTimes (ofChar θ) ρ r ↔
      OccursTimes (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) r := by
    intro r
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      refine ⟨fun i => subComap ι (S i), fun i => subComap ι (T i), fun i => subComap_mono ι (h1 i),
        fun i j hij => subComap_mono ι (h2 i j hij), fun i => ?_⟩
      obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
      refine step_iff.2 ⟨f ∘ₗ (fixed ρ H).subtype, fun w => ?_, fun g u hu => hint g u.1 hu,
        fun u hu => hker u.1 hu⟩
      obtain ⟨v, hv, rfl⟩ := hsurj w
      obtain ⟨u, huF, huS, hfu⟩ := pres_iterate_zero hρ hH hθ (S i) f hint v hv
      exact ⟨⟨u, huF⟩, huS, hfu⟩
    · rintro ⟨S, T, h1, h2, h3⟩
      exact ⟨fun i => subMap ι (S i), fun i => subMap ι (T i), fun i => subMap_mono ι (h1 i),
        fun i j hij => subMap_mono ι (h2 i j hij),
        fun i => step_iff.2 (step_map ι hι (step_iff.1 (h3 i)))⟩
  simp only [jhMult, key]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_unitsO : IsCompact {x : kˣ | valuation k (x : k) = 1} := by
  haveI : T1Space k := IsTopologicalAddGroup.t1Space k (by
    first
      | exact isClosed_singleton
      | (convert (Valuation.isClosed_sphere (v := valuation k) 0) using 1
         ext x
         simp))
  have hS : IsCompact (((valuation k).integer.toSubmonoid : Submonoid k) : Set k) :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  convert Submonoid.units_isCompact hS using 1
  ext x
  have h0 : valuation k (x : k) ≠ 0 := by simp
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨h1, h2⟩
    rw [inv_le_one₀ (zero_lt_iff.2 h0)] at h2
    exact le_antisymm h1 h2

theorem isCompact_torusO (n : Type) : IsCompact (torusO k n : Set (n → kˣ)) :=
  isCompact_pi_infinite fun _ => isCompact_unitsO k

theorem deltaHalf_torusO {n : Type} [Fintype n] [LinearOrder n] {t : n → kˣ} (ht : t ∈ torusO k n) :
    deltaHalf k (fun _ : n => Unit) (leviTorus k n t) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hdet : Matrix.GeneralLinearGroup.det (leviTorus k n t a) = t a :=
    congrFun ((leviTorus k n).symm_apply_apply t) a
  have hv : valuation k (t a : k) = 1 := (show ∀ i, valuation k (t i : k) = 1 from ht) a
  apply Units.ext
  rw [hdet, val_absPow, nabs_eq_one k hv, Units.val_one]
  simp

variable {k} {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]

theorem jacB_apply (π : Representation ℂ (GL n k) V) (g : n → kˣ) (v : Jacquet π (unipB k n)) :
    jacB π g v = (((((deltaHalf k fun _ : n => Unit).comp
      (leviTorus k n).toMonoidHom) g)⁻¹ : ℂˣ) : ℂ) • jacBU π g v := by
  first
    | exact twist_apply (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v
    | (show twist (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v = _
       rw [twist_apply]
       rfl)

theorem jhMult_jacBU_eq_expMult {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    {θ : (n → kˣ) →* ℂˣ} (hθ : ∀ t ∈ torusO k n, θ t = 1) :
    jhMult (ofChar θ) (jacBU π) = expMult π θ := by
  unfold expMult jacBUFixed
  exact jhMult_onFixed (isSmooth_jacBU hπ) (isCompact_torusO k n) _ hθ

theorem jhMult_jacB_eq_expMult : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  intro k _ _ _ _ n V _ _ π hπ θ hθ
  rw [jhMult_of_twist θ (fun g v => jacB_apply π g v)]
  refine jhMult_jacBU_eq_expMult hπ fun t ht => ?_
  rw [MonoidHom.mul_apply, hθ t ht, one_mul]
  exact deltaHalf_torusO k ht

end GlobalTheory.SmGL.UnramFixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUnStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_normalizedBorelJacquet_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  first | exact @GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | exact GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | (intros; apply GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIdemDict

open GlobalTheory.AdelicU

variable {D : D7} {v : FinPl D}

theorem exists_eq_splitProj (φ : SplitProj D v) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, φ = splitProj τ := by
  refine ⟨(φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight, ?_⟩
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>

    have hax : a ⊗ₜ[D.host.F] x = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [splitProj_tmul, hax, map_smul, smul_eq_mul]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem isProjAt_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (PP : Formalism.L2.DIV.Pl D.host.E) :
    IsProjAt (D := D) (v := v) (splitProj τ) PP ↔ PP = splitPrime τ := by

  have hred : ∀ x : 𝓞 D.host.E, rdQ (D := D) (v := v) (splitProj τ) (x : D.host.E) = τ x := fun x => by
    simp only [rdQ, splitProj_tmul, one_mul]
  unfold IsProjAt
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [h x, hred, mem_splitPrime]
  · rintro rfl x
    rw [hred, mem_splitPrime]

theorem sigR_compFin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    sigR _ σ (compFin F E v z) = compFin F E v (sigR _ σ z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => simp [sigR, compFin]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem compFin_cA (z : AE D) :
    sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) = compFin D.host.F D.host.E v (cA D z) := by

  have h := sigR_compFin D.sp.cm.sig v z
  exact h

private theorem idem_inl_eq_tensAt_one (D : D7) (v : FinPl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
  rw [Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eq_idem {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {e : AE D} (he : IsIdemOf (D := D) (v := v) (splitProj τ) e) :
    e = GlobalTheory.EmbChart.idem τ := by
  obtain ⟨⟨hee, hce, -⟩, hsum, hone⟩ := he
  have hone' : splitProj τ (compFin D.host.F D.host.E v e) = 1 := hone
  have hε := idem_inl_eq_tensAt_one D v

  have h1 : e = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v e) := by
    calc e = GlobalTheory.EmbChart.tensAt D.host.E v 1 * e := by
          rw [← hε, ← hsum, add_mul, hee, mul_comm (cA D e) e, hce, add_zero]
      _ = _ := by rw [GlobalTheory.EmbChart.tensAt_mul_right, one_mul]
  have hc : cA D e = GlobalTheory.EmbChart.tensAt D.host.E v 1 - e := by
    rw [← hε, ← hsum, add_sub_cancel_left]

  have h2 : compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) τ := by
    apply split_ext (isCMExt_host D) τ
    · rw [splitProj_splitIdem, hone']
    · rw [splitProj_comp_splitIdem, splitProj_comp, compFin_cA, hc, map_sub, GlobalTheory.EmbChart.compFin_tensAt,
        map_sub, map_one, hone', sub_self]
  rw [h1, h2]
  rfl

private theorem eq_of_isIdemAt_of_isIdemAt' {e : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem exists_emb {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP) :
    ∃ (v : FinPl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), IsIdemOf (D := D) (v := v) (splitProj τ) e ∧ PP = splitPrime τ := by
  obtain ⟨⟨hee, hce, w, ε, ⟨α, rfl, hαw, hαo⟩, hsum⟩, -⟩ := id he

  have hα : α = singleV D.host.F w 1 := by
    classical
    apply RestrictedProduct.ext
    intro u
    by_cases hu : u = w
    · subst hu
      rw [singleV, RestrictedProduct.single_eq_same]
      exact hαw
    · rw [singleV, RestrictedProduct.single_eq_of_ne _ _ hu]
      exact hαo u hu
  subst hα
  have hsum' : e + cA D e = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl w) := hsum
  have hε := idem_inl_eq_tensAt_one D w

  set y := compFin D.host.F D.host.E w e with hy
  have hy1 : y * y = y := by rw [hy, ← map_mul, hee]
  have hy2 : y + sigR _ D.sp.cm.sig y = 1 := by
    rw [hy, compFin_cA, ← map_add (f := _), hsum', hε, GlobalTheory.EmbChart.compFin_tensAt]
  have hσy : sigR _ D.sp.cm.sig y = 1 - y := eq_sub_of_add_eq' hy2

  have hnf : ¬ IsField (Fv D.host.F w ⊗[D.host.F] D.host.E) := by
    intro hf
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, add_zero] at hy2
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, ← hy2, mul_zero, mul_zero])
    · obtain ⟨z, hz⟩ := hf.mul_inv_cancel hy0
      have hy1' : y = 1 := by
        calc y = y * (y * z) := by rw [hz, mul_one]
          _ = y * y * z := by rw [mul_assoc]
          _ = 1 := by rw [hy1, hz]
      rw [hy1', map_one] at hy2
      have h10 : (1 : Fv D.host.F w ⊗[D.host.F] D.host.E) = 0 := add_left_cancel (hy2.trans (add_zero 1).symm)
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  have hfin : Module.finrank (Fv D.host.F w) (Fv D.host.F w ⊗[D.host.F] D.host.E) = 2 := by
    rw [Module.finrank_baseChange]
    exact (isCMExt_host D).2.2.1
  obtain ⟨φ₀⟩ := nonempty_algHom_of_not_isField hfin hnf
  obtain ⟨τ₀, rfl⟩ := exists_eq_splitProj (D := D) (v := w) φ₀

  have hτ : ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F w, splitProj τ y = 1 := by
    have hp : IsIdempotentElem (splitProj τ₀ y) := by
      unfold IsIdempotentElem
      rw [← map_mul, hy1]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hp with h0 | h1
    · refine ⟨τ₀.comp D.sp.cm.sig, ?_⟩
      rw [splitProj_comp, hσy, map_sub, map_one, h0, sub_zero]
    · exact ⟨τ₀, h1⟩
  obtain ⟨τ, hτ⟩ := hτ
  have hi : IsIdemOf (D := D) (v := w) (splitProj τ) e := ⟨he.1, hsum', hτ⟩
  refine ⟨w, τ, hi, ?_⟩

  have he' := he
  rw [eq_idem hi] at he'
  exact eq_of_isIdemAt_of_isIdemAt' he' (GlobalTheory.EmbChart.isIdemAt_idem τ)

theorem idem_dictionary : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  intro D
  refine ⟨fun e PP he => ?_, fun v φ PP hφ => ?_⟩
  · obtain ⟨w, τ, hi, rfl⟩ := exists_emb he
    exact ⟨w, splitProj τ, hi, (isProjAt_iff τ _).2 rfl⟩
  · obtain ⟨τ, rfl⟩ := exists_eq_splitProj φ
    obtain rfl : PP = splitPrime τ := (isProjAt_iff τ PP).1 hφ
    refine ⟨(splitPrime_liesOver τ).over.symm, fun PP' h' => (isProjAt_iff τ PP').1 h', fun e he => ?_⟩
    obtain rfl := eq_idem he
    refine ⟨GlobalTheory.EmbChart.isIdemAt_idem τ, fun e' he' => ?_, fun φ' hφ' => ?_⟩
    ·
      obtain ⟨w, τ', hi', hP'⟩ := exists_emb he'
      have hw : w = v := by
        calc w = (splitPrime τ').under (𝓞 D.host.F) := (splitPrime_under τ').symm
          _ = (splitPrime τ).under (𝓞 D.host.F) := by rw [hP']
          _ = v := splitPrime_under τ
      subst hw
      rw [eq_idem hi', splitPrime_injective (isCMExt_host D) hP'.symm]
    ·
      obtain ⟨τ'', rfl⟩ := exists_eq_splitProj φ'
      have h2 := GlobalTheory.EmbChart.isIdemAt_idem τ''
      rw [← eq_idem hφ'] at h2
      rw [splitPrime_injective (isCMExt_host D) (eq_of_isIdemAt_of_isIdemAt' h2 (GlobalTheory.EmbChart.isIdemAt_idem τ))]

end GlobalTheory.SplitIdemDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitIdempotent_prime_projection_correspondence : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  first | exact @GlobalTheory.SplitIdemDict.idem_dictionary | exact GlobalTheory.SplitIdemDict.idem_dictionary | (intros; apply GlobalTheory.SplitIdemDict.idem_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem witt_anisotropic_group_normalizes_flag_unipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∀ n ∈ flagN d, ∀ h : GA D S₀,
    d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  intro D S S₀ ρ d n hn h
  have he : Formalism.L2.Theta.mt S (d.emb0 h) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX h
  have he' := GlobalTheory.BesselChar.inv_fix_cols (GlobalTheory.BesselChar.mt_inv_mul S (d.emb0 h)) he
  unfold flagN at hn ⊢
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1] at hn ⊢
  rw [GlobalTheory.BesselChar.mt_mul, GlobalTheory.BesselChar.mt_mul]
  exact hn.conj he he' (GlobalTheory.BesselChar.mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end GlobalTheory.MixPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
noncomputable section

namespace GlobalTheory.HoweGlobalPair

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def opInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Set (Module.End ℂ ↥(M.Pol ψ emb)) :=
  {g | (∃ k ∈ KInf σ W emb, ∀ f : ↥(M.Pol ψ emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin n × Fin d)) ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ W, ∀ f : ↥(M.Pol ψ emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin n × Fin d))
        ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)}

def relInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Submodule ℂ ↥(M.Pol ψ emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ X, ∃ f ∈ M.Pol ψ emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin n × Fin d))) ∨
    ∃ k ∈ KInf σ X emb, ∃ f f₁ : ↥(M.Pol ψ emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin n × Fin d)) ⇑(f₁ : SInf F (Fin n × Fin d)) ∧ x = f₁ - f}

def opFin (om : Rep σ X W) (v : Pl F) : Set (Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))) :=
  {g | ∃ h ∈ UAt σ W (evFin F v), ∀ φ : ↥(SB (Fin n × Fin d → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ)}

def relFin (om : Rep σ X W) (v : Pl F) : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
  (augAt om v).comap (SB (Fin n × Fin d → Fv F v)).subtype

end GlobalTheory.HoweGlobalPair

end
end
