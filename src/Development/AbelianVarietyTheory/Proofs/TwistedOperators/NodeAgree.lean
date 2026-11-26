module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

structure NodeAgree (N : GlobalTheory.Grid.Node D) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (X : GlobalTheory.ChiGrid.Node) :
    Prop where

  sp : N.V = G'.V X

  lat : HEq N.Λ (G'.Λ X)

  cart : HEq (Formalism.IndefR.Links.cart N.M) (W.cart X)

  onb : HEq (Formalism.IndefR.Links.onb N.M) (W.onb X)

structure SpAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  vert : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → NodeAgree (G.V i j) W (.grid i j)

  core : ∀ i, i ≤ D.R.m → NodeAgree (G.P i) W (.core i)

  top : ∀ j, j ≤ D.R.m → NodeAgree (G.Xp j) W (.top j)

  q0 : G.q0 = GlobalTheory.ChiGrid.q0 D

  w0 : G.w0 = G'.pl.w G'.pl.v0

  e0 : G.e0 = G'.pl.depth sc G'.pl.v0

  places : G.toPlaceDat.W R.Pg = G'.pl.W0

  lvl : G.lvl R = G'.modul

  chiH : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chiH i = G'.ch.chiH i

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chi i = G'.ch.chi i

structure ArrAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  omX : ∀ i j, i < D.R.m → j ≤ D.R.m → HEq ((G.X i j).ω.toSgn true) (W.om (.chi i j))

  omT : ∀ t i j, i ≤ D.R.m → j < D.R.m → HEq (G.th t i j).ω (W.om (.mu t i j))

  omC : ∀ t j, j < D.R.m → HEq (G.col t j).ω (W.om (.top t j))

  omD : ∀ i, i < D.R.m → HEq ((G.dn i).ω.toSgn true) (W.om (.core i))

  vacX : ∀ i, i < D.R.m → HEq (G.X i 0).vac (W.vac i)

  cos : ∀ i, i < D.R.m → (∀ c, ∃ κ, HEq (G.vC i c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (G.vC i c) (W.cosVec i κ)

def Agree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop :=
  SpAgree G W ∧ ArrAgree G W

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def withArr (G : GridPre R) (X : ∀ i j, ArrS (G.V (i + 1) j) (G.V i j))
    (ωT : T → ∀ i j, WRep (G.nV i j).V (G.nV i (j + 1)).V) (vacT : ∀ i j, WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
    (ItT : ∀ i j, Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M)
    (ωC : T → ∀ j, WRep (G.Xp j).V (G.nX j).V) (vacC : ∀ j, WO (G.Xp j).V (G.nX j).V → ℂ)
    (ItC : ∀ j, Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M)
    (dn : ∀ i, ArrT (G.P (i + 1)) (G.P i))
    (ItU : ∀ i, Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M)
    (vC : ∀ i, G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ)) : GridPre R :=
  { G with X := X, ωT := ωT, vacT := vacT, ItT := ItT, ωC := ωC, vacC := vacC, ItC := ItC, dn := dn, ItU := ItU, vC := vC }

def withMeas (G : GridPre R) (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat) (mP : ∀ i, (G.P i).MeasDat)
    (mX : ∀ j, (G.nX j).MeasDat) : GridPre R :=
  { G with m00 := m00, mV := mV, mP := mP, mX := mX }

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceComm

open GlobalTheory.PointAtPlace GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice

theorem atTau_comm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  intro D θ hθ V τ τ' hne g hg g' hg'
  have ha := atTau_spec hθ V τ hg
  have hb := atTau_spec hθ V τ' hg'
  set a := atTau θ V τ g
  set b := atTau θ V τ' g'
  have k : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x * infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  have triv : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x = 1 → infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x h => by
    have := k φ x
    rwa [h, Matrix.one_mul] at this
  have hc : IsAtTau θ V τ 1 (a * b * a⁻¹ * b⁻¹) := by
    have all : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (a * b * a⁻¹ * b⁻¹) = 1 := fun ρ => by
      simp only [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have hB : infMat D.sp.cm.sig V.gram (θ ρ) b = 1 := hb.2.2 ρ hne
        rw [hB, triv _ _ hB, Matrix.mul_one, Matrix.mul_one, k]
      · have hA : infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := ha.2.2 ρ c
        rw [hA, triv _ _ hA, Matrix.one_mul, Matrix.mul_one, k]
    exact ⟨mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1), all τ, fun ρ _ => all ρ⟩
  have h1 : IsAtTau θ V τ 1 (1 : GA D V) := ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩
  have e : a * b * a⁻¹ * b⁻¹ = 1 :=
    (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique hc h1
  have e2 : a * b * a⁻¹ = b := mul_inv_eq_one.1 e
  exact mul_inv_eq_iff_eq_mul.1 e2

end GlobalTheory.PointAtPlaceComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlaceStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlacePoint_commute_of_ne_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  first | exact @GlobalTheory.PointAtPlaceComm.atTau_comm | exact GlobalTheory.PointAtPlaceComm.atTau_comm | (intros; apply GlobalTheory.PointAtPlaceComm.atTau_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.LinRed
open scoped InnerProductSpace

namespace GlobalTheory.LeviDense

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem exists_iteratedDeriv_inner_semigroup_eq {T : ℝ → V →L[ℂ] V} (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0) (w : V) (k : ℕ) :
    ∀ v ∈ S, ∃ u ∈ S, iteratedDeriv k (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t u⟫_ℂ := by
  induction k with
  | zero => intro v hv; exact ⟨v, hv, by simp⟩
  | succ k ih =>
    intro v hv
    obtain ⟨v', hv', hder⟩ := hd v hv
    have hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ := by
      funext t
      have h3 : HasDerivAt (fun s => T (s - t) v) v' t :=
        HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)
      have h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t :=
        ((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
      have h1 : HasDerivAt (fun s => T s v) (T t v') t := by
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show T s v = T t (T (s - t) v)
        rw [← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]
      exact ((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv
    obtain ⟨u, hu, hk⟩ := ih v' hv'
    exact ⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩

theorem oneParameter_mem_closure {T : ℝ → V →L[ℂ] V} (h0 : T 0 = 1) (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0)
    (ha : ∀ v ∈ S, ∀ w, AnalyticOnNhd ℝ (fun t => ⟪w, T t v⟫_ℂ) Set.univ) (t : ℝ) :
    ∀ v ∈ S.topologicalClosure, T t v ∈ S.topologicalClosure := by
  have key : ∀ v ∈ S, T t v ∈ S.topologicalClosure := by
    intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    have hf := ha v hv w
    have hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0 := by
      intro k
      obtain ⟨u, hu, hk⟩ := exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv
      rw [hk]
      simp only [h0, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hu hw
    have htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1)
        (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)
      rw [← hm] at hle
      have : m + 1 ≤ m := by exact_mod_cast hle
      omega
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
      (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)
  intro x hx
  have hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V)) :=
    S.isClosed_topologicalClosure.preimage (T t).continuous
  have hx' : x ∈ closure (S : Set V) := by rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal (fun v hv => key v hv) hcl hx'

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem mul_Jm_comm_of_unitary_of_preserves {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hu : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (hJ : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) :
    A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
  have h2 : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 hu
  calc A * Formalism.REAL.Jm ε = A * (Aᴴ * Formalism.REAL.Jm ε * A) := by rw [hJ]
    _ = (A * Aᴴ) * Formalism.REAL.Jm ε * A := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * A := by rw [h2, Matrix.one_mul]

end


omit [CompleteSpace V] in
theorem isKFinOn_of_isKFinIn {n : ℕ} {ε : Fin n → Bool} {M : Subgroup (UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {v : V} (h : IsKFinIn M σ v) : IsKFinOn (mats M) σ v := by
  obtain ⟨U, hU, hv, hk⟩ := h
  refine ⟨U, hU, hv, ?_⟩
  rintro _ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw
  refine hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw
  show toM g ∈ Kset ε
  show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g
  exact ⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩

end GlobalTheory.LeviDense

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open GlobalTheory.UnifPoint

noncomputable section

namespace GlobalTheory.HeckeLift

theorem int_eq_of_exp_eq_coprime {m n : ℤ} {p : ℕ} (hp : 0 < p)
    (h : ∀ k : ℕ, 0 < k → k.Coprime p → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set K : ℕ := 1 + (n - m).natAbs * p with hK
  have hk : 0 < K := by omega
  have hcop : K.Coprime p := by
    rw [hK]
    first
      | exact (Nat.coprime_add_mul_right_left 1 p _).2 (Nat.coprime_one_left p)
      | exact (Nat.coprime_add_mul_left_left 1 p _).2 (Nat.coprime_one_left p)
      | simp
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hk hcop)
  have h0 : ((K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = (((K : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize ((K : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have hlt : (n - m).natAbs < K := by
    have : (n - m).natAbs ≤ (n - m).natAbs * p := Nat.le_mul_of_pos_right _ hp
    omega
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact hlt)
  omega

theorem exists_linearMap_of_isHkIsog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hk
  obtain ⟨-, -, hfib, hact, hsurj, hker, hweil, -⟩ := hk
  obtain ⟨e, he⟩ : ∃ e : (Fin g → ℂ) → (Over.mk (F.u j P') ⟶ Xo.univ.t.G), ∀ z, e z = ψp (F.ex i P z) :=
    ⟨_, fun _ => rfl⟩
  have hpow : ∀ (n : ℕ) z, F.ex i P (n • z) = F.ex i P z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (F.ex_ker i P hP 0).2 ⟨0, map_zero P⟩
    | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hkerC : ∀ z, e z = 1 → ∃ a, P a = (p ^ 2) • z := fun z hz => by
    have hmem : F.ex i P z ∈ C := by rw [← hker, MonoidHom.mem_ker, ← he, hz]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 ((hpow _ z).trans (hC _ hmem))
    exact ⟨a, ha⟩
  have hhol : IsHolTo Set.univ (fun z => (e z).left) := by
    have h1 := (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G _ g (F.ex i P)
      (GlobalTheory.ClassUniq.isHolTo_ex F i P hP)).2 _ (ψ ≫ pullback.fst _ _)
    convert h1 using 2 with z
    rw [← Category.assoc, hfib, he]
    unfold fibPt
    exact (pullback.lift_fst _ _ _).symm
  have hc : {z | e z = 1}.Countable := by
    refine ((countable_periods hP).image fun w => ((p ^ 2 : ℕ) : ℂ)⁻¹ • w).mono fun z hz => ?_
    obtain ⟨a, ha⟩ := hkerC z hz
    refine ⟨P a, ⟨a, rfl⟩, ?_⟩
    have h0 : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
    simp only [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]
  have hexp : IsExp (F.ex j P') := ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP',
    (F.ex_diff j P' hP').1, (F.ex_diff j P' hP').2⟩
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' hexp (F.ex_ker j P' hP') (e₀ := e)
    (fun z w => by rw [he, he, he, F.ex_add i P hP, map_mul]) (fun y => by
      obtain ⟨z, hz⟩ := hsurj.comp (F.ex_onto i P hP) y
      exact ⟨z, (he z).trans hz⟩) hhol hc
  have hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a := fun a z => by
    rw [he, he, F.ex_lin i P hP, hact]
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (F.ex_ker j P' hP' _).1 ((eq_iff_sub_of_add (F.ex_add j P' hP') _ _).1
          (((hh _).trans (hlin a x)).trans (by rw [← hh]; exact (F.ex_lin j P' hP' a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a =>
    (F.ex_ker j P' hP' _).1 ((hh _).trans (by rw [he, (F.ex_ker i P hP _).2 ⟨a, rfl⟩, map_one]))
  choose r₀ hr₀ using hmem
  let r₁ : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  refine ⟨r₁, h, fun a b => ?_, hr₀, fun b => ?_, fun z => (hh z).trans (he z)⟩
  · refine int_eq_of_exp_eq_coprime hp.pos fun k hk hcop => ?_
    have w := F.ex_weil i P hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w1 := hweil k _ _ _ hcop w
    have w' := F.ex_weil j P' hP' k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh, he, he] at w'
    have := congrArg Units.val (weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ (F.u j P') k _ _ _ _ w' w1)
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    rw [show r₁ a = r₀ a from rfl, show r₁ b = r₀ b from rfl, this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · obtain ⟨a, ha⟩ := hkerC (h.symm (P' b)) (by
      rw [← hh, h.apply_symm_apply]; exact (F.ex_ker j P' hP' _).2 ⟨b, rfl⟩)
    refine ⟨a, hP'.2.1 ?_⟩
    change P' (r₀ a) = _
    rw [hr₀, ha, map_nsmul, h.apply_symm_apply, map_nsmul]

end GlobalTheory.HeckeLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingFormsStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → IsHkIsog p (F.u i P) (F.u j P') C ψ ψp → ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ ∀ z, F.ex j P' (h z) = ψp (F.ex i P z) := by
  first | exact @GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog | exact GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog | (intros; apply GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.SplitCosetCount

section Grp

open Classical

variable {G : Type} [Group G]

theorem card_le_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card ≤ B.card := by
  classical
  have f : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * a ∈ J := fun a ha => (hB.2 a (hA.1 a ha)).exists
  choose! φ hφB hφJ using f
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a₁ ha₁ a₂ ha₂ he
  have h1 : a₁⁻¹ * a₂ ∈ J := by
    have h := J.mul_mem (J.inv_mem (hφJ a₁ ha₁)) (hφJ a₂ ha₂)
    have e : ((φ a₁)⁻¹ * a₁)⁻¹ * ((φ a₂)⁻¹ * a₂) = a₁⁻¹ * a₂ := by rw [he]; group
    rwa [e] at h
  exact (hA.2 a₂ (hA.1 a₂ ha₂)).unique ⟨ha₁, h1⟩ ⟨ha₂, by simp⟩

theorem card_eq_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card = B.card :=
  le_antisymm (card_le_of_isDC hA hB) (card_le_of_isDC hB hA)

variable {H : Type} [Group H] {ρ : G →* H} {S : G → Prop} {K : Set G} {K' : Subgroup H}

theorem lift_isReps (hm : ∀ x y, S x → S y → S (x * y)) (hi : ∀ x, S x → S x⁻¹)
    (hinj : ∀ x y, S x → S y → ρ x = ρ y → x = y) (hK : ∀ g, S g → (g ∈ K ↔ ρ g ∈ K'))
    {g : G} (hg : S g) {R₀ : Finset H} (hR : Formalism.IndefR.Fin.HCount.IsReps K' (ρ g) R₀)
    (ψ : H → G) (hψs : ∀ a, S (ψ a)) (hψ : ∀ a, ρ (ψ a) = a) :
    (∀ γ ∈ R₀.image ψ, ∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R₀.image ψ ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ S k} := by
  classical
  have hex : ∀ a, ∃ g, S g ∧ ρ g = a := fun a => ⟨ψ a, hψs a, hψ a⟩
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact GlobalTheory.SplitPlace.lift_dc hm hex hinj hK hg (hψs a) (by rw [hψ]; exact hR.1 a ha)
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hx := hm _ _ (hm _ _ hk₁.2 hg) hk₂.2
    have key : ∀ a, (ψ a)⁻¹ * (k₁ * g * k₂) ∈ {k | k ∈ K ∧ S k} ↔ a⁻¹ * ρ (k₁ * g * k₂) ∈ K' := by
      intro a
      have hs := hm _ _ (hi _ (hψs a)) hx
      have := hK _ hs
      rw [map_mul, map_inv, hψ] at this
      exact ⟨fun h => this.1 h.1, fun h => ⟨this.2 h, hs⟩⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := hR.2 (ρ (k₁ * g * k₂)) ⟨_, (hK _ hk₁.2).1 hk₁.1, _, (hK _ hk₂.2).1 hk₂.1,
      by rw [map_mul, map_mul]⟩
    refine ⟨ψ a, ⟨Finset.mem_image_of_mem _ ha, (key a).2 ha'⟩, ?_⟩
    rintro γ ⟨hγ, h⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    rw [hu b ⟨hb, (key b).1 h⟩]

theorem card_image_section {R₀ : Finset H} (ψ : H → G) (hψ : ∀ a, ρ (ψ a) = a) :
    (R₀.image ψ).card = R₀.card := by
  classical
  refine Finset.card_image_of_injective _ fun a b h => ?_
  rw [← hψ a, ← hψ b, h]

end Grp

theorem gaussBinom_eq (κ : Type) [Field κ] [Fintype κ] (n k : ℕ) :
    Formalism.G0.gaussBinom (Fintype.card κ) n k = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Fintype.card κ) n k := by
  have h1 := Formalism.G0.Top.subspaceCount (F := κ) (W := Fin n → κ) k
  have h2 := GlobalTheory.GaussCount.subspaceCount κ (Fin n → κ) k
  rw [Module.finrank_fin_fun] at h1 h2
  rw [Nat.card_eq_fintype_card (α := κ)] at h2
  rw [← h1, ← h2]
  unfold Formalism.G0.countBelow
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun U => by simp

end GlobalTheory.SplitCosetCount

namespace GlobalTheory.SplitCosetCount

open Classical
open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta


set_option maxHeartbeats 1000000 in
theorem card_cosets : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hk hα hRc
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, ϖ, he, h1, h2, hαe⟩ := hα
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨v, π, s, c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis (Wc D i) e v π s he.1.1 c2 c3 c4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module (Wc D i)).2
  obtain ⟨hex, hinj⟩ := GlobalTheory.SplitPlace.comp_bij (V := Wc D i) (B := B) he.1 c1 c2
  have hKc := fun g => GlobalTheory.SplitPlace.K_iff (V := Wc D i) (g := g) he.1 c2 c3 hB
  have hu := GlobalTheory.SplitPlace.isUnif he c4 c5 ϖ h1 h2
  obtain ⟨hu0, hu1⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hH := (GlobalTheory.SplitPlace.hecke_iff he.1 c1 c2 c3 c4 hB hu0 k α).1 hαe

  obtain ⟨w, hw⟩ : ∃ w, π (finPart D (incA D (ϖ : D.host.E))) = w := ⟨_, rfl⟩
  rw [hw] at hu hu0 hu1 hH
  have hirr : Irreducible (⟨w, hu1⟩ : Formalism.UG.Ov D.host.F v) :=
    Formalism.IndefR.Fin.HCount.irreducible_of_unif D.host.F v ⟨w, hu1⟩ hu
  have hv0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have htype : Formalism.IndefR.Fin.HCount.IsType (Formalism.UG.Ov D.host.F v) ⟨w, hu1⟩ k
      (GlobalTheory.SplitPlace.comp (Wc D i) π B α) := by
    refine ⟨fun a b => hH.2.1 a b, fun a b => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact hH.2.2.1 a b
    · obtain ⟨d, hd⟩ : ∃ d, (GlobalTheory.SplitPlace.comp (Wc D i) π B α).1.det = d := ⟨_, rfl⟩
      have hdv' := hH.2.2.2
      rw [hd] at hdv'
      have hdv : Valued.v (d / w ^ k) = 1 := by
        rw [map_div₀, map_pow, hdv', div_self (pow_ne_zero _ hv0)]
      have hne : d / w ^ k ≠ 0 := fun h => by rw [h, map_zero] at hdv; exact zero_ne_one hdv
      have hm : d / w ^ k ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)) ≤ 1; exact le_of_eq hdv
      have hmi : (d / w ^ k)⁻¹ ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)⁻¹) ≤ 1; rw [map_inv₀, hdv, inv_one]
      refine ⟨⟨d / w ^ k, hm⟩, isUnit_iff_exists_inv.2 ⟨⟨_, hmi⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩, ?_⟩
      show _ = w ^ k * (d / w ^ k)
      rw [hd, mul_div_cancel₀ _ (pow_ne_zero _ hu0)]

  obtain ⟨R₀, hR₀⟩ := GlobalTheory.SplitPlace.exists_reps (Formalism.UG.Final.GLintComm D.host.F v (Wc D i).rank)
    (GlobalTheory.SplitPlace.comp (Wc D i) π B α)
  have hc0 := Formalism.IndefR.Fin.HCount.card_reps (Formalism.UG.Ov D.host.F v) hirr htype (R := R₀) hR₀
  choose ψ hψs hψ using hex
  have hl := lift_isReps (ρ := GlobalTheory.SplitPlace.comp (Wc D i) π B) (S := SuppAt e (Wc D i))
    (K := (KsphC (Wc D i) ∅ : Set (GA D (Wc D i)))) (fun _ _ => GlobalTheory.SplitPlace.suppAt_mul)
    (fun _ => GlobalTheory.SplitPlace.suppAt_inv) hinj hKc hH.1 hR₀ ψ hψs hψ
  have hdc : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α (R₀.image ψ) := by
    refine isDC_of_splits hs levG_le_flag ((hLp α).2 hH.1) (fun a ha => ?_) hK hl.1 hl.2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    exact (hLp _).2 (hψs b)
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, c4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Fintype.card (IsLocalRing.ResidueField (Formalism.UG.Ov D.host.F v)) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.SplitUnif.card_residueField v φ P c5 hP
  rw [card_eq_of_isDC hRc hdc, card_image_section ψ hψ, hc0, gaussBinom_eq, hq, rank_Wc]

end GlobalTheory.SplitCosetCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinomStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_hecke_doubleCoset_card_gaussBinom : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  first | exact @GlobalTheory.SplitCosetCount.card_cosets | exact GlobalTheory.SplitCosetCount.card_cosets | (intros; apply GlobalTheory.SplitCosetCount.card_cosets <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.WeilConj

variable {D : D7}

theorem dag_dag {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ T S) (f : WO T S → ℂ) :
    dag S T (dag T S f) = f := by
  funext y
  simp only [dag, Complex.conj_conj, h.invol y]

theorem dag_add (S T : HSp D) (f f' : WO S T → ℂ) : dag S T (f + f') = dag S T f + dag S T f' := by
  funext y; simp [dag]

theorem dag_smul (S T : HSp D) (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext y; simp [dag]

def conjE (S T : HSp D) (A : Module.End ℂ (WO S T → ℂ)) : Module.End ℂ (WO T S → ℂ) where
  toFun f := dag S T (A (dag T S f))
  map_add' f f' := by simp only [dag_add, map_add (f := _)]
  map_smul' c f := by simp only [dag_smul, map_smul, Complex.conj_conj, RingHom.id_apply]

def conjRep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) (ω : WRep S T) :
    WRep T S where
  toFun p := conjE S T (ω (p.2, p.1))
  map_one' := by
    apply LinearMap.ext; intro f
    show dag S T (ω 1 (dag T S f)) = f
    rw [map_one, Module.End.one_apply, dag_dag hTS]
  map_mul' p q := by
    apply LinearMap.ext; intro f
    show dag S T (ω ((p * q).2, (p * q).1) (dag T S f)) = dag S T (ω (p.2, p.1) (dag T S (dag S T (ω (q.2, q.1) (dag T S f)))))
    rw [dag_dag hST]
    have : ((p * q).2, (p * q).1) = (p.2, p.1) * (q.2, q.1) := rfl
    rw [this, map_mul, Module.End.mul_apply]

theorem conjRep_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (ω : WRep S T) (h : GA D T) (g : GA D S) (f : WO T S → ℂ) :
    conjRep hST hTS ω (h, g) f = dag S T (ω (g, h) (dag T S f)) := rfl

theorem adjO_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ S T) : adjO S T 0 = 0 := by
  have := h.add 0 0
  rw [add_zero] at this
  simpa using this

theorem unit_transport {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (μ : Measure (WO T S)) (𝓕 : Set (WO T S)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL S T) 𝓕 μ) :
    ∃ (μ' : Measure (WO S T)) (𝓕' : Set (WO S T)), μ'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕' μ' ∧
      ∀ G : WO S T → ENNReal, ∫⁻ w in 𝓕, G (adjO S T w) ∂μ = ∫⁻ v in 𝓕', G v ∂μ' := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (WO T S) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, hHaar, hF, fun G => ?_⟩
  symm
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  rfl

theorem enorm_dag (S T : HSp D) (f : WO S T → ℂ) (y : WO T S) : ‖dag S T f y‖ₑ = ‖f (adjO S T y)‖ₑ := by
  simp only [dag]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hε, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]

theorem suppAt_cA {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem exists_detAt_cA {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : ∃ x' : (AE D)ˣ, IsDetAt (cA D e) V g x' ∧
      ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → χ x' = χ x := by
  have hi : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
  refine ⟨GlobalTheory.SplitDetCharacter.cutDet (cA D e) hi V g, ?_, fun χ n hχ => ?_⟩
  · show _ = _
    rw [GlobalTheory.SplitDetCharacter.cutDet_val]; ring
  · refine GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hχ _ _ ?_
    rw [GlobalTheory.SplitDetCharacter.cutDet_val, hx, map_add (f := _), map_mul, map_sub, map_one]
    have hd := GlobalTheory.SplitDetCharacter.det_mul_conj V g
    linear_combination (1 - cA D (Formalism.L2.Theta.mt V g).det + (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det
      - (Formalism.L2.Theta.mt V g).det) * hi + cA D e * hd

theorem exists_conj_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  intro D ψ S T χS χT ω H
  have hST : AdjLaw ψ S T := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std S T
  have hTS : AdjLaw ψ T S := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std T S
  refine ⟨conjRep hST hTS ω, ?_, fun g h f => by rw [conjRep_apply, dag_dag hST]⟩
  refine
    { std := H.std
      hecS := H.hecT
      hecT := H.hecS
      resS := H.resT
      resT := H.resS
      om_pres := fun p f hf => hST.theta _ (H.om_pres _ _ (hTS.theta f hf))
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro h g w₀ f hf
    rw [conjRep_apply, conjRep_apply]
    have e1 := hTS.Heisenberg₂ (adjO S T w₀) f
    rw [hTS.invol] at e1
    rw [← e1, H.om_heis g h (adjO S T w₀) _ (hTS.theta f hf), ← hST.act, hST.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [conjRep_apply]
    simp only [dag]
    rw [adjO_zero hST, H.om_aut γ' hγ' γ hγ _ (hTS.theta f hf)]
    simp only [dag]
    rw [adjO_zero hTS, Complex.conj_conj]
  · intro f hf w
    exact Complex.continuous_conj.comp ((H.om_cont _ (hTS.theta f hf) (adjO S T w)).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨μ', 𝓕', hμ', h𝓕', hG⟩ := unit_transport hST hTS μ 𝓕 hμ h𝓕
    have e1 : ∀ w, ‖conjRep hST hTS ω p f w‖ₑ ^ 2 = (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show ‖dag S T (ω (p.2, p.1) (dag T S f)) w‖ₑ ^ 2 = _
      rw [enorm_dag]
    have e2 : ∀ w, ‖f w‖ₑ ^ 2 = (fun v => ‖dag T S f v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show _ = ‖dag T S f (adjO S T w)‖ₑ ^ 2
      rw [enorm_dag, hTS.invol]
    simp only [e1, e2]
    exact (hG (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2)).trans
      ((H.om_unit μ' 𝓕' hμ' h𝓕' _ _ (hTS.theta f hf)).trans (hG (fun v => ‖dag T S f v‖ₑ ^ 2)).symm)
  · intro e he h g hTh hSg y x hy hx
    obtain ⟨x', hx', hxx⟩ := exists_detAt_cA he hx
    obtain ⟨y', hy', hyy⟩ := exists_detAt_cA he hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split (cA D e) (isSplitIdem_cA he) g h (suppAt_cA hSg) (suppAt_cA hTh) x' y' hx' hy'
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    let ℓω : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun F F' => by simp only [dag_add, map_add (f := _)]
        map_smul' := fun c F => by simp only [dag_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
    have hinvω : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓω (heisO ψ S T u F) = ℓω F := by
      intro u hu F hF
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      have e1 := hST.Heisenberg₂ (adjO T S u) F
      rw [hST.invol] at e1
      have hh : IsHalf (cA D (cA D (cA D e))) (adjO T S u) := hTS.half _ u hu
      rw [GlobalTheory.DualPairCheck.cA_cA] at hh
      rw [← e1, hinv _ hh _ (hST.theta F hF)]
    have key := hℓ ℓω hinvω (dag T S f) (hTS.theta f hf)
    have k1 : ℓω (ω (g, h) (dag T S f)) = starRingEnd ℂ (ℓ (conjRep hST hTS ω (h, g) f)) := rfl
    have k2 : ℓω (dag T S f) = starRingEnd ℂ (ℓ f) := by
      show starRingEnd ℂ (ℓ (dag S T (dag T S f))) = _
      rw [dag_dag hTS]
    rw [k1, k2] at key
    have hsf : (starRingEnd ℂ) ((splitFacO χS χT x' y' : Circle) : ℂ) = ((splitFacO χT χS y x : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj]
      congr 1
      unfold splitFacO
      rw [hxx χT _ H.resT, hyy χS _ H.resS, _root_.mul_inv_rev, inv_inv]
    have key' := congrArg (starRingEnd ℂ) key
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hsf] at key'
    exact key'

end GlobalTheory.WeilConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_weilDatum_exchangedPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  first | exact @GlobalTheory.WeilConj.exists_conj_weilDatum | exact GlobalTheory.WeilConj.exists_conj_weilDatum | (intros; apply GlobalTheory.WeilConj.exists_conj_weilDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines
open scoped InnerProductSpace

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta
open GlobalTheory.SmoothGlob (lieSet)

namespace GlobalTheory.GKLie

theorem dRep_conj_Kset (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) :
    ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H,
      Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v →
      Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  intro κ hκ X hX v hv
  have h1 : κᴴ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ.1
  have h2 : κ * κᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ.1
  have hu : IsUnit κ := IsUnit.of_mul_eq_one _ h2
  have hinv : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det κ).1 hu)
  have hκU : κ ∈ UJset ε := by
    change κᴴ * Jm ε * κ = Jm ε
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    change (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']
  have hE : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε := fun t =>
    GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t
  have hinvU : κ⁻¹ ∈ UJset ε := by
    have hκinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h1
    rw [hκinv]
    change κᴴᴴ * Jm ε * κᴴ = Jm ε
    rw [Matrix.conjTranspose_conjTranspose, hκ.2, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfun : (fun t : ℝ => ρ (NormedSpace.exp (t • (κ * X * κ⁻¹))) (ρ κ v)) =
      fun t : ℝ => ρ κ (ρ (NormedSpace.exp (t • X)) v) := by
    funext t
    have hc : NormedSpace.exp (t • (κ * X * κ⁻¹)) = κ * NormedSpace.exp (t • X) * κ⁻¹ := by
      rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc]
    have hA : κ * NormedSpace.exp (t • X) * κ⁻¹ ∈ UJset ε := hmul _ (hmul _ hκU _ (hE t)) _ hinvU
    rw [← ContinuousLinearMap.comp_apply, ← hρ.2 _ hA _ hκU, Matrix.mul_assoc _ κ⁻¹ κ, hinv, Matrix.mul_one,
      hρ.2 _ hκU _ (hE t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [hfun]
  have hd := (differentiableAt_orbit hv hX).hasDerivAt
  have hL : HasFDerivAt (ρ κ) ((ρ κ).restrictScalars ℝ) (ρ (NormedSpace.exp ((0 : ℝ) • X)) v) :=
    ((ρ κ).restrictScalars ℝ).hasFDerivAt
  exact (hL.comp_hasDerivAt (0 : ℝ) hd).deriv

end GlobalTheory.GKLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedRep_conj_maxCompact_intertwines : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v → Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  first | exact @GlobalTheory.GKLie.dRep_conj_Kset | exact GlobalTheory.GKLie.dRep_conj_Kset | (intros; apply GlobalTheory.GKLie.dRep_conj_Kset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaRule_exchange_pair_members : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), (Formalism.MainNotions.SchurIrreducible.ARiiiUp X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiv X (r := r) (s := s) lam → NoLow X r s lam) := by
  first | exact @GlobalTheory.SwapRule.swap_rule | exact GlobalTheory.SwapRule.swap_rule | (intros; apply GlobalTheory.SwapRule.swap_rule <;> assumption)
end
