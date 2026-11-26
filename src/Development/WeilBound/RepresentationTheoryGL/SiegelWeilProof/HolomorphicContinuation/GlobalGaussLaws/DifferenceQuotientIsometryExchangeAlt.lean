module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def aC (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  Matrix.fromBlocks (Matrix.diagonal fun j => Complex.exp (z * X j)) 0 0 (Matrix.diagonal fun j => Complex.exp (-(z * X j)))

def stripS (X : Fin n → ℝ) : Set ℂ := {z | ∀ j, |z.im * X j| < Real.pi / 4}

def ptZ (y : GR n) (X : Fin n → ℝ) (z : ℂ) (sgnI : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let M := mR y * aC X z
  (M.toBlocks₁₁ * (sgnI • 1) + M.toBlocks₁₂) * (M.toBlocks₂₁ * (sgnI • 1) + M.toBlocks₂₂)⁻¹

def jC (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) : ℂ :=
  let M := mR y * aC X z
  M.det ^ e * (M.toBlocks₂₁ * (Complex.I • 1) + M.toBlocks₂₂).det ^ (-(p : ℤ)) *
    (M.toBlocks₂₁ * ((-Complex.I) • 1) + M.toBlocks₂₂).det ^ (-(q : ℤ))

def gC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace)

def famC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

def DReal : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ s : ℝ, famC ε t c e y X s = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) (y * a s) (Complex.I • 1) *
      gZf ε t c (actZ (y * a s) (Complex.I • 1)) u

def DBound : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famC ε t c e y X z u) (stripS X)) ∧
    ContinuousOn (fun p : GR n × ℂ × (Fin m → Fin n → ℂ) => famC ε t c e p.1 X p.2.1 p.2.2) (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p ∈ N, p.2 ∈ stripS X → ∀ u, ‖famC ε t c e p.1 X p.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

def DCalc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ (s : ℝ) (r : ℕ) (u : Fin m → Fin n → ℂ),
      iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s = (Real.exp (s * (m : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j))) ∧
    ∀ (r : ℕ) (s : ℝ), Filter.Tendsto (fun h : ℝ => ∫ u : Fin m → Fin n → ℂ,
        ‖(iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) (s + h) - iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s) / h -
          iteratedDeriv (r + 1) (fun s' : ℝ => famC ε t c e 1 X s' u) s‖ ^ 2) (𝓝[≠] 0) (𝓝 0)

def DifferenceQuotientIsometryExchange : Prop :=
  ∀ (m n : ℕ) (T : ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (κ : ℝ), 0 < κ →
    (∀ f, IsSch f → IsSch (T f)) → (∀ f g, IsSch f → IsSch g → T (f - g) = T f - T g) →
    (∀ a f, IsSch f → T (fun u => a * f u) = fun u => a * T f u) →
    (∀ f, IsSch f → ∫ u, ‖T f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) →
    ∀ (G : ℝ → (Fin m → Fin n → ℂ) → ℂ) (G' E' : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ), (∀ s', IsSch (G s')) → IsSch G' →
      Continuous E' → Filter.Tendsto (fun h : ℝ => ∫ u, ‖(G (s + h) u - G s u) / h - G' u‖ ^ 2) (𝓝[≠] 0) (𝓝 0) →
      (∀ u, Filter.Tendsto (fun h : ℝ => (T (G (s + h)) u - T (G s) u) / h) (𝓝[≠] 0) (𝓝 (E' u))) → T G' = E'

def DHol : Prop :=
  GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure →
  ∀ (P : Type) [TopologicalSpace P] [FirstCountableTopology P] (U : Set ℂ), IsOpen U → ∀ φ : P → ℂ → Mx D V.rank n → ℂ,
    (∀ p z, z ∈ U → φ p z ∈ schwartzA θ V.rank n) → (∀ p x, DifferentiableOn ℂ (fun z => φ p z x) U) →
    (∀ x, ContinuousOn (fun pz : P × ℂ => φ pz.1 pz.2 x) (Set.univ ×ˢ U)) →
    (∀ p, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ p zx.1 zx.2) (U ×ˢ Set.univ)) →
    (∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧ M ∈ schwartzA θ V.rank n ∧
      ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖) →
    let F : P → ℂ → ℂ := fun p z =>
      ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ p z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν
    ContinuousOn (fun pz : P × ℂ => F pz.1 pz.2) (Set.univ ×ˢ U) ∧ (∀ p, DifferentiableOn ℂ (F p) U) ∧
      ∀ p (r : ℕ) z, z ∈ U → iteratedDeriv r (F p) z =
        ⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ p w (GlobalTheory.SiegelFormula.invPt V h ξ)) z) q ∂autMeasure V ν

def DSieg : Prop :=
  ∀ (n : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ), z ∈ stripS X →
    IsSiegel (ptZ y X z Complex.I) ∧ IsSiegel (ptZ y X z (-Complex.I))ᴴ ∧
    ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 ∧
    ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0

def GCSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z Z' : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSiegel Z'ᴴ →
    IsSch (gC ε t c Z Z')

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def chN {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * t * (b * gramX ε u).trace)

def levF {m : ℕ} (e : ℤ) (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a)

def vac {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) : (Fin m → Fin n → ℂ) → ℂ := gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))

def TensInj : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ f g : (Fin V.rank → Fin n → ℂ) → ℂ,
    (∀ Ψ, AwayCls θ τ fr Ψ → tens θ τ fr f Ψ = tens θ τ fr g Ψ) → f = g

def LawN : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSch f →
      L y f = fun u => chN ε (tLoc l τ) b u * f u

def LawM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f

def LawNbar : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbar c → ∀ f, IsSch f →
      L y f = fun u => ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) *
        ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) u

def VacK : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L → ∀ e : ℤ,
    (∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f) →
    ∀ k : GR n, InK (mR k) → L k (vac ε (tLoc l τ) (cLoc l τ)) =
      fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) *
        vac ε (tLoc l τ) (cLoc l τ) u

def IwaGR : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ p k : GR n, y = p * k ∧ (mR p).toBlocks₂₁ = 0 ∧ InK (mR k)

def SiegelOrb : Prop :=
  ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z → ∃ q : GR n, (mR q).toBlocks₂₁ = 0 ∧ actZ q (Complex.I • 1) = Z

def CocycleZ : Prop :=
  ∀ (n : ℕ) (e : ℤ) (p q : ℕ) (y y' : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
    IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det ∧ IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det ∧
    IsSiegel (actZ y' Z) ∧ actZ (y * y') Z = actZ y (actZ y' Z) ∧ jF e p q (y * y') Z = jF e p q y (actZ y' Z) * jF e p q y' Z

def LocMul : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y y' : GR n) f, IsSch f → L (y * y') f = L y (L y' f)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
noncomputable section

open MeasureTheory Real
open scoped FourierTransform Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

abbrev V (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n × Fin 2)

def creL : (Fin m → Fin n → ℂ) →ₗ[ℝ] V m n where
  toFun u := WithLp.toLp 2 fun p : Fin m × Fin n × Fin 2 => if p.2.2 = 0 then (u p.1 p.2.1).re else (u p.1 p.2.1).im
  map_add' u v := by
    ext p; simp only [PiLp.add_apply, WithLp.toLp_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl
  map_smul' c u := by
    ext p; simp only [PiLp.smul_apply, WithLp.toLp_smul, Pi.smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> rfl

def cimL : V m n →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun w a j := ⟨w (a, j, 0), w (a, j, 1)⟩
  map_add' w w' := by funext a j; apply Complex.ext <;> simp
  map_smul' c w := by funext a j; apply Complex.ext <;> simp

def Lc : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n :=
  (LinearEquiv.ofLinearMap creL cimL
    (by
      ext w p
      obtain ⟨a, j, k⟩ := p
      fin_cases k <;> simp [creL, cimL])
    (by
      ext u a j <;> simp [creL, cimL])).toContinuousLinearEquiv

theorem inner_Lc (y v : Fin m → Fin n → ℂ) :
    inner ℝ (Lc y) (Lc v) = ∑ a, ∑ j, ((starRingEnd ℂ) (v a j) * y a j).re := by
  have hL : ∀ z : Fin m → Fin n → ℂ, Lc z = creL z := fun _ => rfl
  rw [hL, hL, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_congr rfl]
  intro a _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [creL, Fin.sum_univ_two, Complex.mul_re]

def Dlin (ε : Fin m → Bool) : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
  (LinearEquiv.ofLinearMap
    { toFun := fun u a j => sgn ε a * u a j
      map_add' := fun u v => by funext a j; simp [mul_add]
      map_smul' := fun c u => by funext a j; simp [Complex.real_smul]; ring }
    { toFun := fun u a j => sgn ε a * u a j
      map_add' := fun u v => by funext a j; simp [mul_add]
      map_smul' := fun c u => by funext a j; simp [Complex.real_smul]; ring }
    (by ext u a j <;> simp [sgn] <;> split_ifs <;> simp)
    (by ext u a j <;> simp [sgn] <;> split_ifs <;> simp)).toContinuousLinearEquiv

theorem Dlin_apply (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    Dlin ε u a j = sgn ε a * u a j := rfl

def Mt (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n :=
  ((Dlin ε).trans Lc).trans
    (LinearEquiv.smulOfNeZero ℝ (V m n) (-t / Real.pi)
      (div_ne_zero (neg_ne_zero.2 ht) Real.pi_pos.ne')).toContinuousLinearEquiv

theorem Mt_apply (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (u : Fin m → Fin n → ℂ) :
    Mt ε t ht u = (-t / Real.pi) • Lc (Dlin ε u) := rfl

theorem re_trace_eq (ε : Fin m → Bool) (u y : Fin m → Fin n → ℂ) :
    (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace).re = inner ℝ (Lc y) (Lc (Dlin ε u)) := by
  rw [inner_Lc, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Dlin_apply, map_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := by
    simp only [sgn]; split_ifs <;> simp
  rw [hs, ← Complex.star_def]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring_nf

theorem haar_Lc : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℂ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (Lc y) = (c : ℂ) * ∫ w, F w := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (Measure.map (Lc (m := m) (n := n)) volume).IsAddHaarMeasure :=
    (Lc (m := m) (n := n)).isAddHaarMeasure_map volume
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map (Lc (m := m) (n := n)) volume)
    (volume : Measure (V m n))
  set c := (Measure.map (Lc (m := m) (n := n)) volume).addHaarScalarFactor (volume : Measure (V m n)) with hc
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F _ => ?_⟩
  calc ∫ y, F (Lc y) = ∫ w, F w ∂(Measure.map (Lc (m := m) (n := n)) volume) :=
        (integral_map_equiv (Lc (m := m) (n := n)).toHomeomorph.toMeasurableEquiv F).symm
    _ = ∫ w, F w ∂(c • (volume : Measure (V m n))) := by rw [← hmap]
    _ = (c : ℂ) * ∫ w, F w := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem ftLoc_eq (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : SchwartzMap (Fin m → Fin n → ℂ) ℂ) (u : Fin m → Fin n → ℂ),
      ftLoc ε t (⇑S) u = (c : ℂ) * 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S)
        (Mt ε t ht u) := by
  obtain ⟨c, hc, hH⟩ := haar_Lc (m := m) (n := n)
  refine ⟨c, hc, fun S u => ?_⟩
  rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← hH (fun v => Complex.exp (↑(-2 * π * inner ℝ v (Mt ε t ht u)) * Complex.I) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S) v) ?_]
  · simp only [ftLoc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [re_trace_eq, Mt_apply, real_inner_smul_right, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    field_simp
  · fun_prop

theorem isSch_ftLoc (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (κ : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    IsSch (fun u => κ * ftLoc ε t f u) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨c, -, h⟩ := ftLoc_eq (n := n) ε t ht
  refine ⟨(κ * c) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Mt ε t ht)
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S)), ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h,
    smul_eq_mul]
  ring

theorem ftLoc_surj (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : IsSch g) :
    ∃ f, IsSch f ∧ (fun u => ftLoc ε t f u) = g := by
  obtain ⟨T, rfl⟩ := hg
  obtain ⟨c, hc, hH⟩ := ftLoc_eq ε t ht
  set G : SchwartzMap (V m n) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Mt ε t ht).symm T with hG
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)) (𝓕⁻ (((c : ℂ)⁻¹) • G)), ⟨_, rfl⟩, ?_⟩
  funext u
  rw [hH]
  have h1 : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)) (𝓕⁻ (((c : ℂ)⁻¹) • G))) =
      𝓕⁻ (((c : ℂ)⁻¹) • G) := by
    ext w
    simp
  rw [h1, FourierInvPair.fourier_fourierInv_eq]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [SchwartzMap.smul_apply, hG, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
  field_simp

theorem ftLoc_neg (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε t f (-u) = ftLoc ε (-t) f u := by
  simp only [ftLoc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hm : Matrix.of (-u) = -Matrix.of u := rfl
  simp only [hm, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re]
  push_cast
  ring_nf

end PositivityTheory.Rg.Sw.Glob.FTD
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenSt
noncomputable section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.Glob

def SchOps : Prop :=
  ∀ (m n : ℕ), (∀ f g : (Fin m → Fin n → ℂ) → ℂ, IsSch f → IsSch g → IsSch (fun u => f u + g u)) ∧
    (∀ (c : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsSch f → IsSch (fun u => c * f u)) ∧
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsUnit a.det → IsSch f →
      IsSch (fun u => f (Matrix.of u * a))) ∧
    (∀ (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), bᴴ = b → IsSch f →
      IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u)) ∧
    ∃ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f ∧ f 0 = 1

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasTemperateGrowthEvalPoly
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem trace_frame {m : ℕ} {M fr : Matrix (Fin m) (Fin m) ℂ} (h1 : IsUnit fr.det) (h2 : frᴴ * M * fr = 1)
    (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (zᴴ * M * z) = ((∑ a, ∑ i, ‖(fr⁻¹ * z) a i‖ ^ 2 : ℝ) : ℂ) := by
  set y := fr⁻¹ * z with hy
  have hz : z = fr * y := by rw [hy, Matrix.mul_nonsing_inv_cancel_left _ _ h1]
  have e : zᴴ * M * z = yᴴ * y := by
    rw [hz, Matrix.conjTranspose_mul]
    calc yᴴ * frᴴ * M * (fr * y) = yᴴ * (frᴴ * M * fr) * y := by simp only [Matrix.mul_assoc]
      _ = yᴴ * y := by rw [h2, Matrix.mul_one]
  rw [e, Matrix.trace]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, ← Complex.conj_mul']
  rfl

theorem gauss_split {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (l : D.what₂.Tau → ℝ)
    (hfr : IsTauFrame V τ s ε fr) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s z = gs (cLoc l τ) (fr⁻¹ * z τ) * gAway V l s τ z := by
  classical
  unfold gauss gAway gs cLoc
  rw [← Complex.exp_add]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ τ), trace_frame hfr.1 hfr.2.2 (z τ)]
  have hf : (Finset.univ.filter fun τ' => τ' ≠ τ) = Finset.univ.erase τ := by
    ext x; simp
  rw [hf]
  push_cast
  ring

theorem evalPoly_add {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_mul {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p * q) z = evalPoly p z * evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_C {m : ℕ} (a : ℂ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.C a : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z = a := by
  simp [evalPoly]

theorem evalPoly_X {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.X v : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z =
      if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1 := by
  simp [evalPoly]

theorem eval_bind₁' {σ ι : Type*} (f : σ → ℂ) (g : ι → MvPolynomial σ ℂ) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ g p) = MvPolynomial.eval (fun i => MvPolynomial.eval f (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

def polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin m × Fin n × Bool => if k.2.2 then
      ∑ a, MvPolynomial.C (star ((fr⁻¹) k.1 a)) * MvPolynomial.X (τ, a, k.2.1, true)
    else ∑ a, MvPolynomial.C ((fr⁻¹) k.1 a) * MvPolynomial.X (τ, a, k.2.1, false)) P

theorem evalPoly_polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (polyAt τ fr P) z = evX P (fr⁻¹ * z τ) := by
  unfold evalPoly polyAt evX
  refine (eval_bind₁' _ _ _).trans (congrArg (fun f => MvPolynomial.eval f P) (funext fun k => ?_))
  obtain ⟨c, i, b⟩ := k
  cases b <;> simp [Matrix.mul_apply, star_sum]

theorem poly_split {m : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ (k : ℕ) (Pi : Fin k → PX m n) (pi : Fin k → MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ),
      (∀ i, ∀ v ∈ (pi i).vars, v.1 ≠ τ) ∧
      ∀ z, evalPoly p z = ∑ i, evX (Pi i) (fr⁻¹ * z τ) * evalPoly (pi i) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨1, fun _ => MvPolynomial.C a, fun _ => 1, by simp, fun z => ?_⟩
    simp [evalPoly, evX]
  | add p q hp hq =>
    obtain ⟨k1, P1, p1, h1, e1⟩ := hp
    obtain ⟨k2, P2, p2, h2, e2⟩ := hq
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append p1 p2, ?_, fun z => ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h1 j
      · simpa using h2 j
    · rw [Fin.sum_univ_add, evalPoly_add, e1, e2]
      simp
  | mul_X p v hp =>
    obtain ⟨k, Pi, pi, h, e⟩ := hp
    by_cases hv : v.1 = τ
    · refine ⟨k, fun i => Pi i * (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
          else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)), pi, h, fun z => ?_⟩
      have hz : z τ = fr * (fr⁻¹ * z τ) := (Matrix.mul_nonsing_inv_cancel_left _ _ hfr).symm
      have hw : (if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1) =
          evX (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
            else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)) (fr⁻¹ * z τ) := by
        rw [hv]
        conv_lhs => rw [hz]
        split_ifs <;> simp [evX, Matrix.mul_apply, map_sum]
      rw [evalPoly_mul, e, evalPoly_X, hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [evX, map_mul]
      ring
    · refine ⟨k, Pi, fun i => pi i * MvPolynomial.X v, fun i w hw => ?_, fun z => ?_⟩
      · have := MvPolynomial.vars_mul (pi i) (MvPolynomial.X v) hw
        rw [Finset.mem_union, MvPolynomial.vars_X] at this
        rcases this with h' | h'
        · exact h i w h'
        · rw [Finset.mem_singleton] at h'
          rw [h']
          exact hv
      · rw [evalPoly_mul, e, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [evalPoly_mul]
        ring

theorem splitFock : SplitFock := by
  intro D n V θ l s τ ε fr _ hfr Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, rfl⟩ := hφ
    obtain ⟨k, Pi, pi, hpi, e⟩ := poly_split τ hfr.1 p
    refine ⟨k, Pi, fun i x => evalPoly (pi i) (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j)), fun i => Submodule.subset_span ⟨pi i, g, hg, hpi i, rfl⟩, ?_⟩
    funext x
    rw [Finset.sum_apply, e, gauss_split l hfr, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [tens, fP]
    ring
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2,
      fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using h2 j) i, ?_⟩
    rw [Fin.sum_univ_add, e1, e2]
    simp
  | smul a x _ hx =>
    obtain ⟨k, Qs, Ψi, h, e⟩ := hx
    refine ⟨k, Qs, fun i => a • Ψi i, fun i => Submodule.smul_mem _ a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul]
    ring

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
  funext x; simp [tens]

theorem tens_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ Ψ' : Mx D m n → ℂ) : tens θ τ fr f (Ψ + Ψ') = tens θ τ fr f Ψ + tens θ τ fr f Ψ' := by
  funext x; simp [tens, mul_add]

theorem tens_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx D m n → ℂ) : tens θ τ fr f (a • Ψ) = a • tens θ τ fr f Ψ := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem tensMem_fock {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (P : PX V.rank n) :
    tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, -, rfl⟩ := hφ
    refine Submodule.subset_span ⟨polyAt τ fr P * p, g, hg, ?_⟩
    funext x
    simp only [tens, fP, evalPoly_mul, evalPoly_polyAt, gauss_split l hfr]
    ring
  | zero => rw [tens_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [tens_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [tens_smul]; exact Submodule.smul_mem _ a hx

def coordCLM {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) v.2.2.1).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) v.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) v.1))

theorem hasTemperateGrowth_evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (w τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (MvPolynomial.C a) (fun τ => Matrix.of (w τ))) =
        fun _ => a := funext fun w => evalPoly_C a _
    rw [e]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) + fun w => evalPoly q (fun τ => Matrix.of (w τ)) :=
      funext fun w => evalPoly_add p q _
    rw [e]
    exact hp.add hq
  | mul_X p v hp =>
    have hc : Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1) := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp (coordCLM v)).hasTemperateGrowth
      · exact (coordCLM v).hasTemperateGrowth
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X v) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) *
          fun w => if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1 :=
      funext fun w => by rw [evalPoly_mul, evalPoly_X]; rfl
    rw [e]
    exact hp.mul hc

theorem fockA_le_schwartzA {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} (hl : ∀ τ, l τ ≠ 0)
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine Submodule.subset_span ⟨SchwartzMap.smulLeftCLM ℂ (fun w => evalPoly p (fun τ => Matrix.of (w τ))) f, g, hg, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_evalPoly p), hf, smul_eq_mul]
  rfl

theorem tensMem : TensMem := by
  intro D n V θ l s τ ε fr _ hl hs hfr Ψ hΨ P
  have h := tensMem_fock hfr hΨ P
  exact ⟨fockA_le_schwartzA hl hs h, h⟩

end PositivityTheory.Rg.Sw.Glob
end
end
