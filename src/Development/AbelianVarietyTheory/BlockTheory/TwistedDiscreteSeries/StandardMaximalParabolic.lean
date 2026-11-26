module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

section Groups

variable (R : Type) [CommRing R] {a b r : ℕ}

def stdMaxParab (h : a + b = r) : Subgroup (GL (Fin r) R) := parab R (two (stdSum h))

def stdMaxRad (h : a + b = r) : Subgroup (GL (Fin r) R) := unipRad R (two (stdSum h))

variable {R}

def conjBy {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

def IsParabRad (P N : Subgroup (GL (Fin r) R)) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (h : ∑ i, d i = r) (g : GL (Fin r) R),
    P = conjBy g (parab R (stdBlocks d h)) ∧ N = conjBy g (unipRad R (stdBlocks d h))

def NoFixed {Q W : Type} [Group Q] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ Q W) (H : Subgroup Q) : Prop :=
  ∀ w : W, (∀ u ∈ H, τ u w = w) → w = 0

end Groups

def idemGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    [MeasurableSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W) : GL (Fin r) k → ℂ :=
  GlobalTheory.Orb.typeIdem μ (GlobalTheory.LocGL.redK k (Fin r)) τ

def TypeConstTermVanish : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r a b : ℕ) (h : a + b = r), 0 < a → 0 < b →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W),
    τ.IsIrreducible → NoFixed τ (stdMaxRad 𝓀[k] h) →
  ∀ [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure],
  ∀ φ ∈ SB (GL (Fin r) k), ∀ f : GL (Fin r) k → ℂ,
    (f = GlobalTheory.AutomorphicL2Unitary.conv μ (idemGL k μ τ) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ (idemGL k μ τ)) →
  ∀ P N : Subgroup (GL (Fin r) k), IsParabRad P N → (∃ g₀, P ≤ conjBy g₀ (stdMaxParab k h)) →
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k),
    Integrable (fun u : N => f (x * u * y)) ν ∧ ∫ u : N, f (x * u * y) ∂ν = 0

theorem mem_conjBy {G : Type} [Group G] {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H :=
  ⟨by rintro ⟨u, hu, rfl⟩; simpa [mul_assoc] using hu, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩

theorem mem_stdMaxParab {R : Type} [CommRing R] {a b r : ℕ} (h : a + b = r) {g : GL (Fin r) R} :
    g ∈ stdMaxParab R h ↔ ∀ i j : Fin r, (j : ℕ) < a → a ≤ (i : ℕ) → (g : Matrix (Fin r) (Fin r) R) i j = 0 := by
  rw [stdMaxParab, mem_parab_two]
  refine ⟨fun H i j hj hi => ?_, fun H j i => H _ _ (by simp) (by simp)⟩
  have := H ⟨i - a, by omega⟩ ⟨j, hj⟩
  have e1 : stdSum h (Sum.inr ⟨i - a, by omega⟩) = i := Fin.ext (by simp; omega)
  have e2 : stdSum h (Sum.inl ⟨j, hj⟩) = j := Fin.ext (by simp)
  rwa [e1, e2] at this

end GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

abbrev Chr (D : D7) : Type := (AE D)ˣ →* Circle

def prodSpan {X X₁ X₂ : Type} (e : X → X₁ × X₂) (P₁ : (X₁ → ℂ) → Prop) (P₂ : (X₂ → ℂ) → Prop) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ f₁ f₂, P₁ f₁ ∧ P₂ f₂ ∧ g = fun w => f₁ (e w).1 * f₂ (e w).2}

def UnifLimit {X : Type} (M : Submodule ℂ (X → ℂ)) (f : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ M, ∀ w, ‖f w - g w‖ ≤ ε

structure TensorSource (ψ : AddChar (AF D.host.F) ℂ) {S A B : HSp D} (d : OrthDec S A B) (T : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (d.boxS T fA fB)

  box_zero : ∀ fA fB, d.boxS T fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resS T).symm (u, 0)) (d.boxS T fA fB) = d.boxS T (heisO ψ A T u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resS T).symm (0, v)) (d.boxS T fA fB) = d.boxS T fA (heisO ψ B T v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f

  om_box : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB →
      omS (d.emb (a, b), h) (d.boxS T fA fB) = d.boxS T (omA (a, h) fA) (omB (b, h) fB)

  om_slice : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ A T (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) ∧
      ∀ u, omS (d.emb (a, b), h) f ((d.resS T).symm (u, v)) =
        omA (a, h) (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) u

structure TensorTarget (ψ : AddChar (AF D.host.F) ℂ) {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB → IsThetaFunO ψ S T (d.boxT S fA fB)

  box_zero : ∀ fA fB, d.boxT S fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resT S).symm (u, 0)) (d.boxT S fA fB) = d.boxT S (heisO ψ S A u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resT S).symm (0, v)) (d.boxT S fA fB) = d.boxT S fA (heisO ψ S B v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ S B fun v => f ((d.resT S).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resT S) (IsThetaFunO ψ S A) (IsThetaFunO ψ S B)) f

  om_box : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB →
      omT (g, d.emb (a, b)) (d.boxT S fA fB) = d.boxT S (omA (g, a) fA) (omB (g, b) fB)

  om_slice : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ S A (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) ∧
      ∀ u, omT (g, d.emb (a, b)) f ((d.resT S).symm (u, v)) =
        omA (g, a) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) u

def cj {X Y : Type} (e : Y → X) (f : X → ℂ) : Y → ℂ := fun y => starRingEnd ℂ (f (e y))

theorem cj_cj {X Y : Type} (e : Y → X) (e' : X → Y) (h : ∀ x, e (e' x) = x) (f : X → ℂ) : cj e' (cj e f) = f := by
  funext x; simp [cj, h]

def cjEnd {X Y : Type} (e : Y ≃ X) : Module.End ℂ (X → ℂ) →* Module.End ℂ (Y → ℂ) where
  toFun L :=
    { toFun := fun f => cj e (L (cj e.symm f))
      map_add' := fun f f' => by
        have : cj e.symm (f + f') = cj e.symm f + cj e.symm f' := by funext x; simp [cj]
        rw [this, map_add (f := _)]; funext y; simp [cj]
      map_smul' := fun c f => by
        have : cj e.symm (c • f) = starRingEnd ℂ c • cj e.symm f := by funext x; simp [cj]
        rw [this, map_smul]; funext y; simp [cj] }
  map_one' := LinearMap.ext fun f => cj_cj e.symm e e.symm_apply_apply f
  map_mul' L L' := LinearMap.ext fun f => by
    show cj e (L (L' (cj e.symm f))) = cj e (L (cj e.symm (cj e (L' (cj e.symm f)))))
    rw [cj_cj e e.symm e.apply_symm_apply]

theorem cjEnd_cj {X Y : Type} (e : Y ≃ X) (L : Module.End ℂ (X → ℂ)) (f : X → ℂ) : cjEnd e L (cj e f) = cj e (L f) := by
  show cj e (L (cj e.symm (cj e f))) = _
  rw [cj_cj e e.symm e.apply_symm_apply]

def conjTarget {S T : HSp D} (om : Rep S T) : Rep S (negSp T) :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((MonoidHom.id _).prodMap (negGA T).symm.toMonoidHom))

def conjSource {S T : HSp D} (om : Rep S T) : Rep (negSp S) T :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).symm.toMonoidHom.prodMap (MonoidHom.id _)))

def dagger (S T : HSp D) (x : WO S T) : WO T S := giA S ⬝ (adj x ⬝ gA T)

theorem dagger_dagger (S T : HSp D) (x : WO S T) : dagger T S (dagger S T x) = x := by
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]

def daggerEquiv (S T : HSp D) : WO T S ≃ WO S T where
  toFun := dagger T S
  invFun := dagger S T
  left_inv := dagger_dagger T S
  right_inv := dagger_dagger S T

def conjAdjoint {S T : HSp D} (om : Rep S T) : Rep T S :=
  (cjEnd (daggerEquiv S T)).comp (om.comp (MulEquiv.prodComm : GA D T × GA D S ≃* GA D S × GA D T).toMonoidHom)

structure ConjAdjoint (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where

  theta_neg : ∀ f : WO S T → ℂ, (IsThetaFunO ψ S (negSp T) (cj id f) ↔ IsThetaFunO ψ S T f) ∧
    (IsThetaFunO ψ (negSp S) T (cj id f) ↔ IsThetaFunO ψ S T f)

  heis_neg : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (negSp T) w (cj id f) = cj id (heisO ψ S T w f) ∧
    heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f)

  conj_target : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) ∧
    ∀ om' : Rep S (negSp T), IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (g, negGA T h) (cj id f) = cj id (om (g, h) f)

  conj_source : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) ∧
    ∀ om' : Rep (negSp S) T, IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (negGA S g, h) (cj id f) = cj id (om (g, h) f)

  sympl_dagger : ∀ x y : WO S T, symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y

  act_dagger : ∀ g h (x : WO S T), dagger S T (actO S T g h x) = actO T S h g (dagger S T x)

  theta_dagger : ∀ f : WO S T → ℂ, IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f

  heis_dagger : ∀ (w : WO S T) (f : WO S T → ℂ),
    heisO ψ T S (dagger S T w) (cj (dagger T S) f) = cj (dagger T S) (heisO ψ S T w f)

  conj_adjoint : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ T S χT χS (conjAdjoint om) ∧
    ∀ om' : Rep T S, IsWeilDatumO ψ T S χT χS om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f)

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hermAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  ((gramAt D V τ)⁻¹ * wᴴ * gramAt D W τ * z).trace

def symplAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hermAt V W τ z w).re


open Classical in
def commScalar (V W : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  if τ = τ' then -(2 * Real.pi * Complex.I) * (symplAt V W τ z w : ℂ) else 0

def Cocompact (V W : HSp D) : Prop := CompactSpace (WO V W ⧸ (ratL W V : AddSubgroup (WO V W)))

def SquareIntegrable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ f, IsThetaFunO ψ V W f →
    (∀ γ ∈ ratL W V, ∀ x : WO V W, ‖f (γ + x)‖ = ‖f x‖) ∧
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      MemLp f 2 (μ.restrict 𝓕)

def HeisUnitary (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  (∀ (u v : WO V W) (f : WO V W → ℂ),
    heisO ψ V W u (heisO ψ V W v f) = ψ (symplOH V W u v) • heisO ψ V W (u + v) f) ∧
  (∀ (u : WO V W) (f : WO V W → ℂ), heisO ψ V W (-u) (heisO ψ V W u f) = f) ∧
  (∀ u f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (heisO ψ V W u f)) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
    ∀ u f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f') ∧
  ∀ γ ∈ ratL W V, ∀ f, IsThetaFunO ψ V W f → heisO ψ V W γ f 0 = f 0

def DerSkew (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ f, IsThetaFunO ψ V W f → ∀ x, HasDerivAt (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) f x)
      (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f x) 0) ∧
    (∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f)) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
        ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) f' =
          -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f')

def DerComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ s t : ℝ, ψ (symplO V W (lineAt θ τ z s) (lineAt θ τ' w t)) =
      Complex.exp (s * t * commScalar V W τ τ' z w)) ∧
    ∀ f, IsThetaFunO ψ V W f →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w f) -
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
          commScalar V W τ τ' z w • f

def FinRealComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ u : WO V W, u.map (infPart D) = 0 →
    (∀ v : WO V W, v.map (finPart D) = 0 → ∀ f : WO V W → ℂ,
      heisO ψ V W u (heisO ψ V W v f) = heisO ψ V W v (heisO ψ V W u f)) ∧
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      heisO ψ V W u (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (heisO ψ V W u f)

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ V W : HSp D, Cocompact V W ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      SquareIntegrable ψ V W ∧ HeisUnitary ψ V W ∧
        ∀ θ : InfFam D, IsInfFam θ → DerSkew ψ θ V W ∧ DerComm ψ θ V W ∧ FinRealComm ψ θ V W

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7}

def IsRealParam {m n k : ℕ} (L : (Fin k → ℝ) →+ Mx D m n) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

structure IsSchwartzBruhat {m n : ℕ} (φ : Mx D m n → ℂ) : Prop where

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, φ (x + u) = φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, φ x ≠ 0 → x.map (finPart D) ∈ K

  schwartz : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), IsRealParam L → Function.Injective L →
    ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t)

end GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KernelBound {D : D7} (V W : HSp D) (A d : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω →
        ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
          ∀ f ∈ GlobalTheory.Size.thetaLevel ψ V W U, ∀ (g : GA D V) (h : GA D W),
            ‖thetaKO ω g h f‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f * ENNReal.ofReal ((height V g * height W h) ^ A)

def ThetaGrowth (D : D7) : Prop :=
  ∀ m n : ℕ, ∃ A d : ℕ, ∀ V W : HSp D, V.rank = m → W.rank = n → KernelBound V W A d

def ThetaGrowthUnif : Prop :=
  ∀ r N : ℕ, ∃ A d : ℕ, ∀ (D : D7) (V W : HSp D), Module.finrank ℚ D.host.F = r → V.rank * W.rank = N →
    KernelBound V W A d

theorem ThetaGrowthUnif.thetaGrowth (H : ThetaGrowthUnif) (D : D7) : ThetaGrowth D := fun m n =>
  (H _ (m * n)).imp fun _ h => h.imp fun _ h V W hV hW => h D V W rfl (by rw [hV, hW])

theorem KernelBound.real {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d)
    (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω →
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
        ∀ f ∈ GlobalTheory.Size.thetaLevel ψ V W U, sobO ψ θ μ 𝓕 d f ≠ ∞ ∧ ∀ (g : GA D V) (h : GA D W),
          ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := by
  obtain ⟨C, hC⟩ := H ψ θ hθ U hU
  refine ⟨C, C.2, fun χS χT ω hω μ 𝓕 hμ f hf => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf.1 d
  refine ⟨hs, fun g h => ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)
    (hC χS χT ω hω μ 𝓕 hμ f hf g h)
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (pow_nonneg (mul_pos (height_pos V g) (height_pos W h)).le A)] at this

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain
open GlobalTheory.Ker (ipO)

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def creOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') l g

def annOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  (-(fockScale D l.1 : ℂ)⁻¹) •
    annih (heisO ψ V W) θ l.1 (cplxO (cart M l.1) (cart M' l.1)) (unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2) g

def multiFact {ι : Type} (α : ι →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial


open Classical in
def FockLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : Prop :=
  (∀ P : PolF D W.rank V.rank, IsThetaFunO ψ V W (ptOf ψ θ M M' f P)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    creOp ψ θ M M' l (creOp ψ θ M M' l' g) = creOp ψ θ M M' l' (creOp ψ θ M M' l g)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    annOp ψ θ M M' l (creOp ψ θ M M' l' g) - creOp ψ θ M M' l' (annOp ψ θ M M' l g) = if l = l' then g else 0) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ α β : FVar D W.rank V.rank →₀ ℕ,
      ipO μ 𝓕 (ptOf ψ θ M M' f (MvPolynomial.monomial α 1)) (ptOf ψ θ M M' f (MvPolynomial.monomial β 1)) =
        if α = β then (multiFact α : ℂ) * ipO μ 𝓕 f f else 0) ∧
  Function.Injective (ptOf ψ θ M M' f)

def VacuumFock (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO V W → ℂ, IsVacVec ψ θ M M' f → FockLaws ψ θ M M' f

theorem ptOf_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : ptOf ψ θ M M' f 1 = f := by
  have h : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  unfold ptOf pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Real

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField
open GlobalTheory.Size (l2O)
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

variable {V W}

variable (V W)

def IsVac (θ : InfFam D) (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (sW τ)) f

end Defs

section Basic₂

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {θ : InfFam D}

theorem exists_isVac_ne_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) (hW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) :
    ∃ f, IsVac ψ V W θ sV sW f ∧ f ≠ 0 := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ hV hW _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h := hf 1
  simp only [one_mul] at h
  exact ⟨f, ⟨h.1, h.2.2⟩, f0⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

end
end
