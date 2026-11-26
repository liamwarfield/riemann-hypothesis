module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UniformModerateGrowthLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar}

def pMinus (M : DSModel W S) (τ : D.what₂.Tau) : Set (Matrix (Fin W.rank) (Fin W.rank) ℂ) :=
  {Z | ∀ a b, ¬ (M.ε τ a = false ∧ M.ε τ b = true) → (M.fr τ * Z * (M.fr τ)⁻¹) a b = 0}

abbrev KMap (M : DSModel W S) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => lowT M τ) (GA D W → ℂ)


variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable (W) in
def IsSmoothFn (φ : GA D W → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin W.rank) (Fin W.rank) ℂ),
    (∀ i, Xs i ∈ lieAt W (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ W (τs i) (Xs i) (t i)).prod)


variable (W) in
def IsUnifModGrowth (φ : GA D W → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt W p.1) →
    ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC W,
      ‖(l.foldr (fun p f => Rder θ W p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ W g ^ N


def RestrictsTo (M : DSModel W S) (T : Formalism.IndefR.Mult.MMap M) (U : KMap M) : Prop :=
  ∀ e : ∀ τ, lowT M τ, T (fun τ => (e τ : M.sm τ)) = U e

theorem single_mem_pMinus (M : DSModel W S) (τ : D.what₂.Tau) {a b : Fin W.rank} (ha : M.ε τ a = false)
    (hb : M.ε τ b = true) : (M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ ∈ pMinus M τ := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h : M.fr τ * ((M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ) * (M.fr τ)⁻¹ = Matrix.single a b 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  intro c d hcd
  rw [h, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact hcd ⟨ha, hb⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

variable {D : D7}

def lift {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (Φ : GA D S → WO S T → ℂ) : GA D T → ℂ :=
  fun g => ∫ h in 𝓕, thetaKO om h g (Φ h) ∂ν

def along (S T : HSp D) (ξ : Fin T.rank → D.host.E) (a : Fin S.rank → AE D) : WO S T :=
  Matrix.vecMulVec (fun i => incA D (ξ i)) a


open Classical in
def KEquiv (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) : Prop :=
  ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (e : ∀ τ', lowT M τ') (w : lowT M τ),
    ((w : M.sm τ) : M.H τ) = M.σ τ k ((e τ : M.sm τ) : M.H τ) →
      U (Function.update e τ w) = rTr V (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ)) (U e)

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem eq_top_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (τ : D.what₂.Tau) (N : Submodule ℂ (lowT M τ))
    (v : lowT M τ) (hv : v ≠ 0)
    (hN : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ u : lowT M τ,
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v : M.sm τ) : M.H τ) → u ∈ N) : N = ⊤ := by
  have hU := (M.ds τ).2.2.1
  let P : Submodule ℂ (M.H τ) := Submodule.span ℂ {y | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), y = M.σ τ k ((v : M.sm τ) : M.H τ)}
  have hvL : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  have hPle : P ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact (h2 τ).2.1 k hk _ hvL)
  have hmul : ∀ a ∈ Formalism.REAL.Kset (M.ε τ), ∀ b ∈ Formalism.REAL.Kset (M.ε τ), a * b ∈ Formalism.REAL.Kset (M.ε τ) := by
    intro a ha b hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := ⟨one_mem _, by simp⟩
  have hst : IsKStableOn (M.ε τ) (M.σ τ) P := by
    intro g hg y hy
    refine Submodule.span_induction (p := fun y _ => M.σ τ g y ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨k, hk, rfl⟩
      refine Submodule.subset_span ⟨g * k, hmul g hg k hk, ?_⟩
      rw [hU.1.2 _ (kset_uj hg) _ (kset_uj hk)]
      rfl
    · rw [map_zero]; exact P.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact P.add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact P.smul_mem a hx
  have hP : P = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
    refine ((h2 τ).2.2.1 P hPle hst).resolve_left fun h0 => hv ?_
    have : M.σ τ 1 ((v : M.sm τ) : M.H τ) ∈ P := Submodule.subset_span ⟨1, hone, rfl⟩
    rw [h0, hU.1.1] at this
    exact Subtype.ext (Subtype.ext this)
  rw [eq_top_iff]
  intro u _
  have hu : ((u : M.sm τ) : M.H τ) ∈ P := hP ▸ u.2
  have key : ∀ y (hy : y ∈ P), (⟨⟨y, h1 τ (hPle hy)⟩, hPle hy⟩ : lowT M τ) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, e⟩ := hy
      exact hN k hk _ e
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx => exact N.smul_mem a hx
  exact key _ hu


open Classical in
theorem mem_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) Y) (N : Submodule ℂ Y) (v₀ : ∀ τ, lowT M τ) (h0 : ∀ τ, v₀ τ ≠ 0)
    (hB : B v₀ ∈ N)
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → B v ∈ N → B (Function.update v τ u) ∈ N)
    (v : ∀ τ, lowT M τ) : B v ∈ N := by
  have key : ∀ s : Finset D.what₂.Tau, B (s.piecewise v v₀) ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hB
    | insert τ s hτ ih =>
      have e0 : s.piecewise v v₀ τ = v₀ τ := Finset.piecewise_eq_of_notMem _ _ _ hτ
      have := eq_top_of_translates h1 h2 τ (N.comap (B.toLinearMap (s.piecewise v v₀) τ)) (v₀ τ) (h0 τ)
        fun k hk u hu => hK τ k hk _ u (by rw [e0]; exact hu) ih
      rw [Finset.piecewise_insert]
      exact (this.ge Submodule.mem_top : v τ ∈ N.comap (B.toLinearMap (s.piecewise v v₀) τ))
  simpa using key Finset.univ

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Mem.Chr

namespace GlobalTheory.DefU.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjPl_self (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ConjPl (IsCMField.complexConj E).toRingEquiv w w := fun k => by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
      w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
  have h3 := hv (algebraMap E (w.adicCompletion E) k)
  rw [hs, h1, h2] at h3
  exact h3

theorem eq_of_under_eq {w u : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  rcases (under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one E) w u).1 hu with h | h
  · exact h
  · exact (existsUnique_conjPl _ w).unique h hw

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem mat_ext {A B : Matrix (Fin n) (Fin n) (Ad E)} (h1 : A.map (pInf E) = B.map (pInf E))
    (h2 : ∀ v, A.map ((pLoc E v).comp (pFin E)) = B.map ((pLoc E v).comp (pFin E))) : A = B := by
  ext i j
  refine ad_ext (congrFun (congrFun h1 i) j) (FiniteAdeleRing.ext _ fun v => ?_)
  exact congrFun (congrFun (h2 v) i) j

theorem map_finGL (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n k) = GeneralLinearGroup.map (pLoc E v) k :=
  Units.ext (congrArg (fun g : GL (Fin n) (v.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion E)))
    (congrArg (GeneralLinearGroup.map (pLoc E v)) (pFin_finGL k)))

theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = star (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E))
    (hg : g ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  have hg' : cT s g.val * g.val = 1 := by
    have h : cT s g.val * 1 * g.val = 1 := hg
    rwa [Matrix.mul_one] at h
  have hw := conjPl_self w s hs hv
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  generalize hh : finGL E n (locGL E n w g) = h
  have hI : h.val.map (pInf E) = 1 := by
    rw [← hh]
    exact congrArg Units.val (pInf_finGL (locGL E n w g))
  have hL : ∀ v, h.val.map ((pLoc E v).comp (pFin E)) =
      (GeneralLinearGroup.map (pLoc E v) (locGL E n w g)).val := fun v => by
    rw [← hh]
    exact congrArg Units.val (map_finGL v (locGL E n w g))
  refine mat_ext ?_ fun v => ?_
  · have hc : (cT (conjAd E) h.val).map (pInf E) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 : pInf E (h.val j i) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) j i := congrFun (congrFun hI j) i
      change pInf E (conjAd E (h.val j i)) = _
      rw [pInf_conjAd, h1]
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply, e, Ne.symm e]
    rw [Matrix.map_mul, hc, hI, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases eq_or_ne v w with rfl | hvw
    · have h0 := hL v
      rw [pLoc_locGL] at h0
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = cT s g.val := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E v (pFin E (h.val j i)) = g.val j i := congrFun (congrFun h0 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = s (g.val j i)
        rw [pLoc_conjFin_eq _ v s hs hv, h1]
      rw [Matrix.map_mul, hc, h0, hg', Matrix.map_one _ (map_zero _) (map_one _)]
    · have h0 := hL v
      rw [pLoc_locGL_of_ne hvw] at h0
      have hne : conjSrc (IsCMField.complexConj E).toRingEquiv v ≠ w := fun e =>
        hvw ((existsUnique_conjPl _ w).unique (e ▸ conjPl_conjSrc _ v) hw)
      have h2 := hL (conjSrc (IsCMField.complexConj E).toRingEquiv v)
      rw [pLoc_locGL_of_ne hne] at h2
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = 1 := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv v) (pFin E (h.val j i)) =
            (1 : Matrix (Fin n) (Fin n) _) j i := congrFun (congrFun h2 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = _
        rw [pLoc_conjFin, h1]
        by_cases e : i = j
        · subst e; simp
        · simp [Matrix.one_apply, e, Ne.symm e]
      have h0' : h.val.map ((pLoc E v).comp (pFin E)) = 1 := h0
      rw [Matrix.map_mul, hc, h0', Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mem_locU {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (g : GL (Fin n) (w.adicCompletion E)) (hU : finGL E n (locGL E n w g) ∈ UA E n) :
    (⟨_, hU⟩ : UA E n) ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨pInf_finGL _, ?_⟩
  simp only [Subgroup.mem_iInf]
  intro u hu
  have hne : u ≠ w := fun e => hu (by rw [e])
  exact (map_finGL u _).trans (pLoc_locGL_of_ne hne g)

theorem finGL_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (x : locU n w) : finGL E n (locGL E n w (cLoc w (x : UA E n))) = (x : UA E n).1 := by
  have hx := Subgroup.mem_inf.1 x.2
  have hx2 := hx.2
  simp only [Subgroup.mem_iInf] at hx2
  refine Units.ext (mat_ext ?_ fun v => ?_)
  · have h1 : GeneralLinearGroup.map (pInf E) (x : UA E n).1 = 1 := hx.1
    have h2 := pInf_finGL (locGL E n w (cLoc w (x : UA E n)))
    exact congrArg Units.val (h2.trans h1.symm)
  · have h1 : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n (locGL E n w (cLoc w (x : UA E n)))) =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (x : UA E n).1 := by
      refine (map_finGL v _).trans ?_
      rcases eq_or_ne v w with rfl | hvw
      · exact pLoc_locGL v _
      · rw [pLoc_locGL_of_ne hvw]
        have := hx2 v fun e => hvw (eq_of_under_eq hw e)
        exact (MonoidHom.mem_ker.1 this).symm
    exact congrArg Units.val h1

theorem locU_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) →
    ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  intro E _ _ _ n w s hs hv
  have hw := conjPl_self w s hs hv
  have hf : ∀ x : locU n w, cLoc w (x : UA E n) ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := fun x => by
    change cT s _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact cT_cLoc w s hs hv _
  refine ⟨{ toFun := fun x => ⟨cLoc w (x : UA E n), hf x⟩
            invFun := fun g => ⟨⟨finGL E n (locGL E n w g.1), finGL_mem w s hs hv g.1 g.2⟩,
              finGL_mem_locU hw g.1 _⟩
            left_inv := fun x => Subtype.ext (Subtype.ext (finGL_cLoc hw x))
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext (map_mul (cLoc w) (x : UA E n) y)
            continuous_toFun := Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
              (continuous_finGL.comp ((CuspSub.continuous_locGL w).comp continuous_subtype_val)) _) _ }, fun _ => rfl⟩
  exact (map_finGL w _).trans (pLoc_locGL w _)

end GlobalTheory.DefU.Inert

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGroStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.DefU.Inert.locU_equiv | exact GlobalTheory.DefU.Inert.locU_equiv | (intros; apply GlobalTheory.DefU.Inert.locU_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefReal

open GlobalTheory.CoefModel

theorem vact_eq_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK g) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Pi.inv_apply, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem continuous_coeff_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {X : Type} [TopologicalSpace X]
    (A : X → ι → GL (Fin n) ℂ) (hA : ∀ τ, Continuous fun x => (A x τ : Matrix (Fin n) (Fin n) ℂ)) (F : Pol ℂ ι n)
    (m : ι × Fin n × Fin n →₀ ℕ) : Continuous fun x => AddMonoidAlgebra.coeff (actP lam (A x) F) m := by
  simp only [actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul, detTw_eq, AlgHom.toLinearMap_apply, trAct]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hA τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_coeff_blockAct _ (fun τ => (hA τ).matrix_transpose) _ m)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (A x τ).isUnit).ne_zero

theorem exists_scalarExt {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    {W : Type} [AddCommGroup W] [Module ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] W, ∀ v, e (mapVV φ lam v) = c0 v := by
  let b1 := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  let b2 := Module.Basis.mk h1 h2.ge
  refine ⟨b1.equiv b2 (Equiv.refl _), fun v => ?_⟩
  have : (b1.equiv b2 (Equiv.refl _)).toLinearMap.comp (mapVV φ lam) = c0 := by
    refine (bVV K lam).ext fun i => ?_
    have h := b1.equiv_apply i b2 (Equiv.refl _)
    simpa [b1, b2] using h
  exact LinearMap.congr_fun this v

variable {D : D7}

theorem exists_real_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W) (hθ : IsInfFam θ) (hc : c.Is)
    (ht : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam)) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, (∀ v, e (mapVV D.what₂.embLL lam v) = c0 v) ∧
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK (realGL θ V u)) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV D.what₂.embLL lam v) = c0 v :=
    exists_scalarExt D.what₂.embLL lam c0 ht.2.1 ht.2.2
  refine ⟨e, he, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam), c.ρ γ.1 (e v) = e (rhoK lam (invTrK (realGL θ V γ.1)) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap = e.toLinearMap.comp (rhoK lam (invTrK (realGL θ V γ))) := by
      refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (invTrK (realGL θ V γ)) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (ht.1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let L : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => L (c.ρ h (e v)) := L.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V h)) v.1) m := by
    refine continuous_coeff_actP lam _ (fun τ => ?_) _ m
    refine (((realGL_laws hθ V).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show L (c.ρ (γ * k) (e v)) = AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V (γ * k))) v.1) m
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [L, rhoK_coe]

theorem exists_poly_model : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  intro D V θ c lam c0 hθ hc ht BS hBS
  obtain ⟨e, -, he⟩ := exists_real_model V θ c lam c0 hθ hc ht
  choose B hB using hBS
  refine ⟨(VV ℂ lam).subtype ∘ₗ rhoK lam (invTrK B⁻¹) ∘ₗ e.symm.toLinearMap, ?_, fun u hu w => ?_⟩
  · have hs : Function.Surjective (rhoK lam (invTrK B⁻¹)) := fun x => ⟨rhoK lam (invTrK B) x, by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]⟩
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_eq_top.2 hs, Submodule.map_top,
      Submodule.range_subtype]
  · obtain ⟨v, rfl⟩ := e.surjective w
    have e1 : (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) =
        fun τ => (((B⁻¹ * realGL θ V u * B) τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      rw [← hB τ, ← Matrix.coe_units_inv]
      rfl
    rw [e1, vact_eq_actP, he u hu v]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    rw [← rhoK_coe, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_inv_cancel_right]

end GlobalTheory.CoefReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialModel_coefficientSpace_realPoints : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  first | exact @GlobalTheory.CoefReal.exists_poly_model | exact GlobalTheory.CoefReal.exists_poly_model | (intros; apply GlobalTheory.CoefReal.exists_poly_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


open Classical in
def twist (τ : E →+* ℂ) : ℂ →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then RingHom.id ℂ else starRingEnd ℂ

theorem twist_twist (τ : E →+* ℂ) (z : ℂ) : twist τ (twist τ z) = z := by
  unfold twist; split_ifs <;> simp

theorem twist_star (τ : E →+* ℂ) (z : ℂ) : twist τ (star z) = star (twist τ z) := by
  unfold twist; split_ifs <;> simp

theorem continuous_twist (τ : E →+* ℂ) : Continuous (twist τ) := by
  unfold twist; split_ifs
  · exact continuous_id
  · exact Complex.continuous_conj

theorem twist_embedding (w : InfinitePlace E) : twist w.embedding = RingHom.id ℂ := by
  unfold twist; rw [if_pos (by rw [InfinitePlace.mk_embedding])]

theorem coord_eq (τ : E →+* ℂ) (z : Cinf E) : coord τ z = twist τ (z (InfinitePlace.mk τ)) := by
  unfold coord twist; split_ifs <;> rfl

open Classical in
theorem atEmb_apply (τ : E →+* ℂ) (z : ℂ) (w : InfinitePlace E) :
    atEmb τ z w = if w = InfinitePlace.mk τ then twist τ z else 0 := by
  unfold atEmb twist
  rw [Pi.single_apply]
  split_ifs <;> simp_all

def sN (τ : E →+* ℂ) : ℂ →ₙ+* Cinf E where
  toFun := atEmb τ
  map_mul' z z' := (atEmb_mul τ z z').symm
  map_zero' := funext fun w => by classical simp [atEmb_apply]
  map_add' z z' := funext fun w => by
    classical
    simp only [atEmb_apply, Pi.add_apply]
    split_ifs <;> simp

theorem sN_apply (τ : E →+* ℂ) (z : ℂ) : sN τ z = atEmb τ z := rfl

theorem continuous_sN (τ : E →+* ℂ) : Continuous (sN τ) := by
  classical
  refine continuous_pi fun w => ?_
  simp only [sN_apply, atEmb_apply]
  split_ifs
  · exact continuous_twist τ
  · exact continuous_const

def yG (τ : E →+* ℂ) : GL (Fin n) ℂ →* GL (Fin n) (Cinf E) := cornerGL n (sN τ)

open Classical in
theorem yG_apply (τ : E →+* ℂ) (g : GL (Fin n) ℂ) (i j : Fin n) (w : InfinitePlace E) :
    (yG τ g).val i j w =
      if w = InfinitePlace.mk τ then twist τ (g.val i j) else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  change (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j w - sN τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) w +
    sN τ (g.val i j) w = _
  simp only [sN_apply, atEmb_apply, Matrix.one_apply]
  split_ifs <;> simp_all

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_mem (τ : E →+* ℂ) (x : UA E n) : (cEmb τ x).val ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 := congrArg (RingHom.mapMatrix ((coord τ).comp (pInf E))) hx
  rw [mul_one, map_mul, map_one] at h1
  rw [Matrix.mem_unitaryGroup_iff', ← h1]
  congr 1
  ext i j
  exact (GlobalTheory.DefiniteBC.coord_conjAd τ _).symm

theorem cEmb_infGL (τ' : E →+* ℂ) (y : GL (Fin n) (Cinf E)) (h : infGL E n y ∈ UA E n) (i j : Fin n) :
    (cEmb τ' ⟨_, h⟩).val i j = coord τ' (y.val i j) := by
  have e : cEmb τ' ⟨_, h⟩ = GeneralLinearGroup.map (coord τ') y := by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E n y)) = _
    rw [pInf_infGL]
  rw [e]
  rfl

theorem yG_unitary (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (yG τ (GlobalTheory.Branching.unitaryIncl n u)).valᴴ * (yG τ (GlobalTheory.Branching.unitaryIncl n u)).val = 1 := by
  classical
  have hu : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  refine Matrix.ext fun i j => funext fun w => ?_
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply, yG_apply]
  split_ifs with hw
  · have h2 := congrFun₂ hu i j
    simp only [Matrix.mul_apply, Matrix.star_apply] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← twist_star, ← map_mul, ← map_sum]
    change twist τ (∑ k, star ((u : Matrix (Fin n) (Fin n) ℂ) k i) * (u : Matrix (Fin n) (Fin n) ℂ) k j) = _
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · by_cases h : i = j
    · subst h; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem infGL_yG_mem_UA (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)) ∈ UA E n :=
  infGL_mem_UA _ (yG_unitary τ u)

theorem twist_one_apply (τ : E →+* ℂ) (i j : Fin n) :
    twist τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem mem_embU (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (⟨_, infGL_yG_mem_UA τ u⟩ : UA E n) ∈ embU n τ := by
  classical
  refine ⟨pFin_infGL _, ?_⟩
  refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [cEmb_infGL, coord_eq, yG_apply, if_neg h, twist_one_apply]
  rfl

def inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : embU n τ :=
  ⟨⟨_, infGL_yG_mem_UA τ u⟩, mem_embU τ u⟩

def fwd (τ : E →+* ℂ) (x : embU n τ) : Matrix.unitaryGroup (Fin n) ℂ := ⟨(cEmb τ x.1).val, cEmb_mem τ x.1⟩

theorem fwd_inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : fwd τ (inv τ u) = u := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change (cEmb τ ⟨_, infGL_yG_mem_UA τ u⟩).val i j = _
  rw [cEmb_infGL, coord_eq, yG_apply, if_pos rfl, twist_twist]
  rfl

theorem inv_fwd (τ : E →+* ℂ) (x : embU n τ) : inv τ (fwd τ x) = x := by
  classical
  have hx := Subgroup.mem_inf.1 x.2
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · change GeneralLinearGroup.map (pInf E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    rw [yG_apply]
    split_ifs with hw
    · subst hw
      change twist τ (coord τ (pInf E (x.1.1.val i j))) = _
      rw [coord_eq, twist_twist]
      rfl
    · have h1 : InfinitePlace.mk w.embedding ≠ InfinitePlace.mk τ := by
        rw [InfinitePlace.mk_embedding]; exact hw
      have hk := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) h1)
      have h2 := congrArg (fun g : GL (Fin n) ℂ => g.val i j) hk
      change coord w.embedding (pInf E (x.1.1.val i j)) = _ at h2
      rw [coord_eq, twist_embedding, InfinitePlace.mk_embedding] at h2
      exact h2.symm
  · change GeneralLinearGroup.map (pFin E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pFin_infGL]
    exact (MonoidHom.mem_ker.1 hx.1).symm

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  have : (coord τ : Cinf E → ℂ) = fun z => twist τ (z (InfinitePlace.mk τ)) := funext (coord_eq τ)
  rw [this]
  exact (continuous_twist τ).comp (continuous_apply _)

theorem continuous_fwd (τ : E →+* ℂ) : Continuous (fwd τ : embU n τ → Matrix.unitaryGroup (Fin n) ℂ) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun x : embU n τ => (x.1.1.val).map (fun a => coord τ (pInf E a))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_map
    ((continuous_coord τ).comp continuous_pInf')

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

def phi (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Ad E) :=
  corner (matN n (sInf E)) (corner (matN n (sN τ)) M)

theorem continuous_phi (τ : E →+* ℂ) : Continuous (phi (n := n) τ) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) ℂ => 1 - matN n (sInf E) 1 +
    (1 - matN n (sN τ) 1 + M.map (sN τ)).map (sInf E)
  exact continuous_const.add ((continuous_const.add (continuous_id.matrix_map (continuous_sN τ))).matrix_map
    continuous_sInf)

theorem continuous_inv (τ : E →+* ℂ) : Continuous (inv τ : Matrix.unitaryGroup (Fin n) ℂ → embU n τ) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => phi τ (u : Matrix (Fin n) (Fin n) ℂ)
    exact (continuous_phi τ).comp continuous_subtype_val
  · have e : ∀ u : Matrix.unitaryGroup (Fin n) ℂ,
        ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val =
          phi τ (star (u : Matrix (Fin n) (Fin n) ℂ)) := fun u => by
      rw [← map_inv, ← map_inv]
      rfl
    change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val
    simp only [e]
    exact (continuous_phi τ).comp (continuous_star.comp continuous_subtype_val)

def equiv (τ : E →+* ℂ) : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ where
  toFun := fwd τ
  invFun := inv τ
  left_inv := inv_fwd τ
  right_inv := fwd_inv τ
  map_mul' x y := Subtype.ext (by
    change (cEmb τ (x.1 * y.1)).val = (cEmb τ x.1).val * (cEmb τ y.1).val
    rw [map_mul]
    rfl)
  continuous_toFun := continuous_fwd τ
  continuous_invFun := continuous_inv τ

theorem exists_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ,
      GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  intro E _ _ _ n τ
  exact ⟨equiv τ, fun x => Units.ext rfl⟩

end GlobalTheory.EmbUnitary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ, GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  first | exact @GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | exact GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | (intros; apply GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairInfTypes

theorem hasInfQ_tauE (D : D7) {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) (fun τ => a (D.eTau τ)) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Fintype.prod_equiv D.eTau _ _ fun _ => rfl).symm

theorem infTypesAt : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  intro D T L μ0 hL i t τ
  have h1 : HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 i) (hasInfQ_tauE D (L.C.isMu0 i).inf) τ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (hasInfQ_tauE D (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 : HasInfExp D (L.xi t) τ 0 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t) ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
    rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
    simp
  have h4 : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h3
    rw [add_zero] at h
    exact h
  refine ⟨h4, h2, h4, ?_⟩
  rw [sub_eq_add_neg]
  exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul h4 (GlobalTheory.Mem.HeckeExp.hasInfExp_inv h2)

end GlobalTheory.PairInfTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  first | exact @GlobalTheory.PairInfTypes.infTypesAt | exact GlobalTheory.PairInfTypes.infTypesAt | (intros; apply GlobalTheory.PairInfTypes.infTypesAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CuspRep.GASplit
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_infEq_symm : Continuous (infEq E).symm := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    (continuous_apply w)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_infEq_symm E).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_sInf : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  continuous_const.prodMk continuous_id

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

def splitMulEquiv : GA E a ≃* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toFun g := (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g)
  invFun p := infGL E a p.1 * finGL E a p.2
  left_inv g := infGL_mul_finGL g
  right_inv p := by
    obtain ⟨y, k⟩ := p
    refine Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by simp

def splitEquiv : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toMulEquiv := splitMulEquiv E a
  continuous_toFun :=
    ((continuous_glMap a (pInf E) (continuous_pInf E))).prodMk (continuous_glMap a (pFin E) (continuous_pFin E))
  continuous_invFun :=
    ((continuous_cornerGL a (sInf E) (continuous_sInf E)).comp continuous_fst).mul
      ((continuous_cornerGL a (sFin E) (continuous_sFin E)).comp continuous_snd)

theorem exists_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E),
      ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) :=
  fun E _ _ _ a => ⟨splitEquiv E a, fun _ => rfl⟩

end GlobalTheory.CuspRep.GASplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFiniteStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicGL_homeomorph_infinite_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E), ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) := by
  first | exact @GlobalTheory.CuspRep.GASplit.exists_split | exact GlobalTheory.CuspRep.GASplit.exists_split | (intros; apply GlobalTheory.CuspRep.GASplit.exists_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

def TwistConeVanishing {X : Scheme.{0}} (A N : LB X) (F : X.Modules) : Prop :=
  ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p →
    Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p)

end GlobalTheory
end
end
