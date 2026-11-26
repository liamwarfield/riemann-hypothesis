module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open scoped ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adj (D : D7) {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A

structure IsIsoSplit (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) : Prop where
  frame : IsIsoFrame V C
  isom : adj D B * V.gram * B = V'.gram
  orth : adj D C * V.gram * B = 0
  rank : V.rank = V'.rank + 2 * r

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D W.rank r) : WO V W :=
  HMul.hMul (y : Matrix (Fin W.rank) (Fin r) (AE D)) ((adj D C * V.gram).map (incA D))

def midPart (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (x : WO V' W) : WO V W :=
  HMul.hMul (x : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) ((V'.gram⁻¹ * adj D B * V.gram).map (incA D))

def res (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (f : WO V W → ℂ) : WO V' W → ℂ :=
  fun x => ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ

def Compatible (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)) : Prop :=
  ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 →
    ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = ω' (1, h) (res V V' W C B μ 𝓨 f)

def ConstTermFormula (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)) : Prop :=
  ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
  ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ →
  ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
  ∀ f, IsThetaFunO ψ V W f → ∀ g : GA D V,
    κ 𝓝 ≠ ∞ ∧
    (∀ x, IntegrableOn (fun y => ω (g, 1) f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧
    IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (g, 1) f)) ∧
    (∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * F h) 𝓕 ν) ∧
    IntegrableOn (fun h => thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) * F h) 𝓕 ν ∧
    IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f F ((n : GA D V) * g)) 𝓝 κ ∧
    ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f F ((n : GA D V) * g) ∂κ =
      ((κ 𝓝).toReal : ℂ) * Lift.liftInt ν 𝓕 (thetaKO ω') (res V V' W C B μ 𝓨 (ω (g, 1) f)) F 1

def TowerConstTermOfCompatible (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → Compatible ψ V V' W C B ω ω' →
    ConstTermFormula ψ V V' W C B ω ω'

def CompatibleOfSameChar (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → Compatible ψ V V' W C B ω ω'

def TowerConstTerm (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ConstTermFormula ψ V V' W C B ω ω'

def spaceThree (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 3 ![false, true, false] 2 1

def spaceOne (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 1 ![false] 1 0

theorem isIsoSplit_three (D : D7) :
    IsIsoSplit (spaceThree D) (spaceOne D) (r := 1)
      (Matrix.of fun (i : Fin 3) _ => (![1, 1, 0] : Fin 3 → D.host.E) i)
      (Matrix.of fun (i : Fin 3) _ => (![0, 0, 1] : Fin 3 → D.host.E) i) := by
  have hg : ∀ i j : Fin 3, (spaceThree D).gram i j =
      if i = j then (Examples₂.sgn (![false, true, false] i) : D.host.E) else 0 :=
    Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 3 ![false, true, false] 2 1
  have hg' : ∀ i j : Fin 1, (spaceOne D).gram i j = if i = j then (Examples₂.sgn (![false] i) : D.host.E) else 0 :=
    Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 1 ![false] 1 0
  refine ⟨⟨one_pos, ?_, ?_⟩, ?_, ?_, rfl⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 3)
    exact one_ne_zero this
  · funext a b
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![1, 1, 0] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![1, 1, 0] : Fin 3 → D.host.E) j = 0
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]
  · funext (a : Fin 1) (b : Fin 1)
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![0, 0, 1] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![0, 0, 1] : Fin 3 → D.host.E) j = _
    rw [hg', Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]
  · funext a b
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![1, 1, 0] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![0, 0, 1] : Fin 3 → D.host.E) j = 0
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)

def stdParabolic (k : Type) [Field k] (r a : ℕ) : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j : Fin r, j.val < a → a ≤ i.val → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := fun i j hj hi => Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' := fun {g h} hg hh i j hj hi => by
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < a
    · rw [hg i l hl hi, zero_mul]
    · rw [hh l j hj (not_lt.1 hl), mul_zero]
  inv_mem' := fun {g} hg i j hj hi => by
    have hb : (g : Matrix (Fin r) (Fin r) k).BlockTriangular fun l => if l.val < a then (0 : ℕ) else 1 := by
      intro i j h
      by_cases h1 : j.val < a <;> by_cases h2 : i.val < a <;> simp [h1, h2] at h
      exact hg i j h1 (not_lt.1 h2)
    letI := g.invertible
    have := Matrix.blockTriangular_inv_of_blockTriangular hb
    rw [Matrix.coe_units_inv]
    exact this (by simp [hj, not_lt.2 hi])

def InConjParabolic {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k)) (a : ℕ) : Prop :=
  ∃ g : GL (Fin r) k, ∀ p ∈ H, g⁻¹ * p * g ∈ stdParabolic k r a

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parAt {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) : Subgroup (GL (Fin V.rank) (Fv D.host.F v)) :=
  (PLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))

def ParabolicAtSplitPlaces : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (T : TypeDataG V) (𝔉 : IsoFlag V), 𝔉.Proper →
    ∃ a : ℕ, 0 < a ∧ 2 * a + 1 ≤ V.rank ∧ ∀ v : T.S,
      InConjParabolic (parAt 𝔉 (T.frame v)) a ∧ InConjParabolic (parAt 𝔉 (T.frame v)) (V.rank - a)

def UnipIntegralsVanish {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (f : GA D V → ℂ) : Prop :=
  ∀ (ν : Measure (NA 𝔉)) [ν.IsHaarMeasure] (x y : GA D V),
    Integrable (fun n : NA 𝔉 => f (x * n * y)) ν ∧ ∫ n : NA 𝔉, f (x * n * y) ∂ν = 0

def TestFnConstTermVanish : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V), HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (U : AuxiliaryPlaceHermitianSpace V)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (f : GA D V → ℂ), IsTestFnG M T U μa μf f →
    ∀ 𝔉 : IsoFlag V, 𝔉.Proper → UnipIntegralsVanish 𝔉 f ∧ UnipIntegralsVanish 𝔉 (starFn f)

def ParabolicAndConstTerm : Prop := ParabolicAtSplitPlaces ∧ TestFnConstTermVanish

end GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def kFin (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.H τ) :=
  GlobalTheory.KFiniteVectors.kFiniteVectors (M.ε τ) (M.σ τ)

abbrev KVec (M : DSModel V S) : Type := ∀ τ : D.what₂.Tau, kFin M τ

abbrev KMap (M : DSModel V S) : Type := (∀ τ : D.what₂.Tau, kFin M τ) →ₘₗ[ℂ] (GA D V → ℂ)

def maxCpt (M : DSModel V S) (τ : D.what₂.Tau) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)}


open Classical in
def IsGKMap (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : KMap M) : Prop :=
  (∀ u, IsAutFun V (T₀ u)) ∧
  (∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) ∧
  (∀ u, IsCuspFun V (T₀ u)) ∧
  (∀ u, MemLp (T₀ u) 2 (μ.restrict 𝓕)) ∧
  (∀ u, GlobalTheory.Grow.UnifModGrowth V θ (T₀ u)) ∧
  (∀ u, ∀ k ∈ J, ∀ g, T₀ u (g * k) = χ k * T₀ u g) ∧
  (∀ τ, ∀ k ∈ maxCpt M τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = M.rep τ k (u τ) →
    T₀ (Function.update u τ w) = rTr V (atTau θ V τ k) (T₀ u)) ∧
  (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = dRep (M.rep τ) X (u τ) →
    T₀ (Function.update u τ w) = Rder θ V τ X (T₀ u))

def Extends {M : DSModel V S} (T : MMap M) (T₀ : KMap M) : Prop :=
  ∀ (v : M.Vec) (u : KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u

def ExtExists (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ T₀ : KMap M, IsGKMap θ M J χ μ 𝓕 T₀ → ∃! T : MMap M, IsMultMap θ M J χ T ∧ Extends T T₀

def RestrInj (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ kFin M τ) → T v = 0) → T = 0

def GKExtension (D : D7) : Prop := ExtExists D ∧ RestrInj D

theorem maxCpt_subset (M : DSModel V S) (τ : D.what₂.Tau) : maxCpt M τ ⊆ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  intro g hg
  have h1 : (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc _ (Formalism.REAL.Jm (M.ε τ)), ← hg.2, ← Matrix.mul_assoc]
    have := (Matrix.mem_unitaryGroup_iff').1 hg.1
    rw [Matrix.star_eq_conjTranspose] at this
    rw [this, Matrix.one_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have e : M.fr τ * g * (M.fr τ)⁻¹ * M.fr τ = M.fr τ * g := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  show gᴴ * gramAt D V τ * g = gramAt D V τ
  rw [← M.fr_gram τ]
  calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
      = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)) * M.fr τ := by
        conv_lhs => rw [← e]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]

theorem rep_mem_kFin (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ)
    {v : M.H τ} (hv : v ∈ kFin M τ) : M.rep τ k v ∈ kFin M τ := by
  obtain ⟨A, hA, ha, hs⟩ := hv
  exact ⟨A, hA, hs _ hk v ha, hs⟩

theorem kFin_ne_bot (M : DSModel V S) (τ : D.what₂.Tau) : kFin M τ ≠ ⊥ := by
  obtain ⟨A, hA, hs, -, ⟨v, hv, h0, -⟩, -⟩ := (M.ds τ).2.2.2.2.2.1
  exact fun h => h0 ((Submodule.mem_bot ℂ).1 (h ▸ (show v ∈ kFin M τ from ⟨A, hA, hv, hs⟩)))

end GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x

def IsWittStep (B B' : HSp D) (t : ℕ) (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) : Prop :=
  B'.rank + 2 * t = B.rank ∧ HSpace.IsIsomEmb B' B ι ∧ IsIsoSub B C ∧ ct (frameMat B B' ι) * B.gram * C = 0

theorem isWittLower_iff (B B' : HSp D) (t : ℕ) : IsWittLower B B' t ↔ ∃ ι C, IsWittStep B B' t ι C :=
  ⟨fun ⟨h, ι, h1, C, h2, h3⟩ => ⟨ι, C, h, h1, h2, h3⟩, fun ⟨ι, C, h, h1, h2, h3⟩ => ⟨h, ι, h1, C, h2, h3⟩⟩

theorem exists_isWittStep_iff (B : HSp D) (t : ℕ) :
    (∃ B' ι C, IsWittStep B B' t ι C ∧ B'.SigOK) ↔ t ≤ GlobalTheory.Cusp.wittIndex B := by
  rw [← GlobalTheory.Cusp.exists_isWittLower_iff]
  exact ⟨fun ⟨B', ι, C, h, h'⟩ => ⟨B', (isWittLower_iff _ _ _).2 ⟨ι, C, h⟩, h'⟩,
    fun ⟨B', h, h'⟩ => let ⟨ι, C, h⟩ := (isWittLower_iff _ _ _).1 h; ⟨B', ι, C, h, h'⟩⟩

def IsLeviElt (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E)
    (a : GL (Fin t) (AE D)) (h' : GA D B') (m : GA D B) : Prop :=
  HMul.hMul (Formalism.L2.Theta.mt B m) (adel C) = HMul.hMul (adel C) a.val ∧
    HMul.hMul (Formalism.L2.Theta.mt B m) (adel (frameMat B B' ι)) =
      HMul.hMul (adel (frameMat B B' ι)) (Formalism.L2.Theta.mt B' h')

def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)

def resT (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ :=
  fun w' => ∫ y in 𝓖, φ (adel C * (y : Matrix (Fin t) (Fin S.rank) (AE D)) +
    adel (frameMat T T' ι) * (w' : Matrix (Fin T'.rank) (Fin S.rank) (AE D))) ∂μ

end Target

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)

def resS (μ : Measure (Mx D T.rank t)) (𝓖 : Set (Mx D T.rank t)) (φ : WO S T → ℂ) : WO S' T → ℂ :=
  fun w' => ∫ y in 𝓖, φ ((y : Matrix (Fin T.rank) (Fin t) (AE D)) * adel (ct C * S.gram) +
    (w' : Matrix (Fin T.rank) (Fin S'.rank) (AE D)) * adel (S'.gram⁻¹ * ct (frameMat S S' ι) * S.gram)) ∂μ

end Source

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace
open scoped ENNReal NNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

variable {D : D7}

section Defs

variable (θ : InfFam D) {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
  (ν : Measure (GA D W)) (𝓕 : Set (GA D W))

def lift (f : WO V W → ℂ) (F : GA D W → ℂ) : GA D V → ℂ := Lift.liftInt ν 𝓕 (thetaKO ω) f F

def dOmS (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ) : WO V W → ℂ :=
  fun z => deriv (fun t : ℝ => ω (oneP θ V τ X t, 1) f z) 0

def dOmT (τ : D.what₂.Tau) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : WO V W → ℂ :=
  fun z => deriv (fun t : ℝ => ω (1, oneP θ W τ Y t) f z) 0

def decayInt (A : ℕ) (F : GA D W → ℂ) : ℝ≥0∞ := ∫⁻ h in 𝓕, ENNReal.ofReal (‖F h‖ * quotHeight W h ^ A) ∂ν

end Defs

structure LiftLaws (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D}
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W))
    (cls : (GA D W → ℂ) → Prop) : Prop where

  integ : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ g h₀,
    IntegrableOn (fun h => thetaKO ω g h f * rTr W h₀ F h) 𝓕 ν

  integ_der : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ Y ∈ lieAt W τ, ∀ g,
    IntegrableOn (fun h => thetaKO ω g h f * Rder θ W τ Y F h) 𝓕 ν

  aut : ∀ f F, IsThetaFunO ψ V W f → cls F → IsAutFun V (lift ω ν 𝓕 f F)

  equiv : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ g₀ h₀,
    lift ω ν 𝓕 (ω (g₀, h₀) f) (rTr W h₀ F) = rTr V g₀ (lift ω ν 𝓕 f F)

  smooth : ∀ f F, IsThetaFunO ψ V W f → cls F → lift ω ν 𝓕 f F ∈ SmFun θ V

  dS : ∀ f, IsThetaFunO ψ V W f → ∀ τ, ∀ X ∈ lieAt V τ, IsThetaFunO ψ V W (dOmS θ ω τ X f) ∧
    ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) f z) (dOmS θ ω τ X f z) 0

  dT : ∀ f, IsThetaFunO ψ V W f → ∀ τ, ∀ Y ∈ lieAt W τ, IsThetaFunO ψ V W (dOmT θ ω τ Y f) ∧
    ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) f z) (dOmT θ ω τ Y f z) 0

  derS : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ X ∈ lieAt V τ,
    Rder θ V τ X (lift ω ν 𝓕 f F) = lift ω ν 𝓕 (dOmS θ ω τ X f) F

  derT : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ Y ∈ lieAt W τ, ∀ g,
    HasDerivAt (fun s : ℝ => lift ω ν 𝓕 (ω (1, oneP θ W τ Y s) f) (rTr W (oneP θ W τ Y s) F) g)
      (lift ω ν 𝓕 f (Rder θ W τ Y F) g + lift ω ν 𝓕 (dOmT θ ω τ Y f) F g) 0

  growth : ∀ f F, IsThetaFunO ψ V W f → cls F → UnifModGrowth V θ (lift ω ν 𝓕 f F)

  decay_ne_top : ∀ F, cls F → ∀ A, decayInt ν 𝓕 A F ≠ ∞

  bound : ∃ A : ℕ, ∀ k : ℕ, ∃ d : ℕ, ∀ (μ : Measure (WO V W)) (𝓓 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓓 μ → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ f ∈ GlobalTheory.Size.thetaLevel ψ V W U, ∀ F, cls F →
        growthSob θ V k A (lift ω ν 𝓕 f F) ≤ C * sobO ψ θ μ 𝓓 d f * decayInt ν 𝓕 A F

def LiftPropsOn (D : D7) (cls : InfFam D → (W : HSp D) → (GA D W → ℂ) → Prop) : Prop :=
  ∀ (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
      LiftLaws θ ψ ω ν 𝓕 (cls θ W)

def LiftProps (D : D7) : Prop := LiftPropsOn D fun θ W F => IsAutFunSm θ W F ∧ IsCuspFun W F

def LiftPropsRapid (D : D7) : Prop := LiftPropsOn D fun θ W F => RapidDecSm θ W F

theorem LiftLaws.mono {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls cls' : (GA D W → ℂ) → Prop} (h : LiftLaws θ ψ ω ν 𝓕 cls) (hc : ∀ F, cls' F → cls F) :
    LiftLaws θ ψ ω ν 𝓕 cls' := by
  refine
    { integ := fun f F hf hF => h.integ f F hf (hc F hF)
      integ_der := fun f F hf hF => h.integ_der f F hf (hc F hF)
      aut := fun f F hf hF => h.aut f F hf (hc F hF)
      equiv := fun f F hf hF => h.equiv f F hf (hc F hF)
      smooth := fun f F hf hF => h.smooth f F hf (hc F hF)
      dS := h.dS
      dT := h.dT
      derS := fun f F hf hF => h.derS f F hf (hc F hF)
      derT := fun f F hf hF => h.derT f F hf (hc F hF)
      growth := fun f F hf hF => h.growth f F hf (hc F hF)
      decay_ne_top := fun F hF => h.decay_ne_top F (hc F hF)
      bound := ?_ }
  obtain ⟨A, hA⟩ := h.bound
  refine ⟨A, fun k => (hA k).imp fun d hd μ 𝓓 h1 h2 U hU => ?_⟩
  exact (hd μ 𝓓 h1 h2 U hU).imp fun C hC f hf F hF => hC f hf F (hc F hF)

theorem liftProps_of_rapid (hP : GlobalTheory.Published.CuspRapidDecay) (h : LiftPropsRapid D) : LiftProps D :=
  fun V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 => (h V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕).mono fun _ hF =>
    rapidDecSm_of_cuspForm hP hθ hF.1 hF.2

theorem decayInt_le {W : HSp D} (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (A : ℕ) (F : GA D W → ℂ) :
    decayInt ν 𝓕 A F ≤ decaySize W A F * ν 𝓕 := by
  rw [← setLIntegral_const]
  exact lintegral_mono fun h => le_iSup (fun g => ENNReal.ofReal (‖F g‖ * quotHeight W g ^ A)) h

theorem LiftLaws.derT_add {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (h : LiftLaws θ ψ ω ν 𝓕 cls) {f : WO V W → ℂ} {F : GA D W → ℂ}
    (hf : IsThetaFunO ψ V W f) (hF : cls F) (τ : D.what₂.Tau) {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hY : Y ∈ lieAt W τ) (g : GA D V) :
    lift ω ν 𝓕 f (Rder θ W τ Y F) g + lift ω ν 𝓕 (dOmT θ ω τ Y f) F g = 0 := by
  have := h.derT f F hf hF τ Y hY g
  simp only [h.equiv f F hf hF] at this
  exact this.unique (hasDerivAt_const _ _)

end GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

end
end
