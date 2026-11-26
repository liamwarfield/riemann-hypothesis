module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

@[expose] public section

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
noncomputable section

namespace Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def vec22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    e N N' L L' ∈ Th D T L L' ∧ e N N' L L' ≠ 0 ∧
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def per22 (D : D7) (T : Tor D) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D T M →
    ∀ τ : D.what₂.Tau, meanLogOm D T.abelian₂ M τ = logOmVal D

def th22 (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')) ∧
  (∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc) ∧
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))) ∧
  (∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L'))

def eq22 (D : D7) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => (χ (detId D L'.1 L''.1)) ^ (-((N / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => (χ (detId D L.1 L₁.1)) ^ (((N' / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

def chiQ (D : D7) : D.Dt ⧸ D.UO →* ℂˣ :=
  QuotientGroup.lift D.UO D.chiD (fun x hx => MonoidHom.mem_ker.mpr (D.chiD_UO x hx))

def RelDetPinned (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : Prop :=
  letI := D.host.cmStar
  Function.Injective idl ∧ (∀ 𝔞, N1 D 𝔞 ↔ ∃ x, idl x = 𝔞) ∧ (∀ x y, idl (x * y) = idl x * idl y) ∧
  (∀ z : unitary D.host.E, idl (QuotientGroup.mk (D.e1Dt z)) =
    Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) ∧
  ∀ N (L L' : SDLat D.host.E N), idl (D.relDet N L L') = detId D L.1 L'.1

def chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : IdE D → ℂ :=
  fun 𝔞 => if h : ∃ x, idl x = 𝔞 then ((chiQ D h.choose : ℂˣ) : ℂ) else 0

theorem chiRec_idl (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : Function.Injective idl) (x : D.Dt ⧸ D.UO) :
    chiRec D idl (idl x) = ((chiQ D x : ℂˣ) : ℂ) := by
  have hx : ∃ y, idl y = idl x := ⟨x, rfl⟩
  unfold chiRec
  rw [dite_eq_left hx, h hx.choose_spec]

def DualB (D : D7) {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ τ, ((P (tauSg D τ)).map D.host.conj).transpose * P τ = 1

def zB (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (τ : D.what₂.Tau) (a : Fin N') (b : Fin N) : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ i : Fin N', ∑ j : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
      ((((P' τ).map (tauEmb D lam τ))⁻¹) a i * ((P τ).map (tauEmb D lam τ)) j b) * MvPowerSeries.X (τ, i, j)

def QdB (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (u : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ τ : D.what₂.Tau, ∑ a : Fin N', ∑ b : Fin N,
    algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (u τ) *
      zB D lam P P' τ a b * zB D lam P P' (tauSg D τ) a b

def int22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    (p ≠ D.host.d → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        Orthonormal D b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)) ∧
      JetsInt D lam (YYl D L L') F ∧
      ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F))) ∧
    (p = D.host.d →
      ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧
        ∃ u : D.what₂.Tau → ℂ_[p], (∀ τ, ‖u τ‖ = 1) ∧ (∀ τ, u (tauSg D τ) = u τ) ∧
          ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
            (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
          (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ)) →
          DualB D P → DualB D P' →
          ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
          ∃ F₀, F = expMv (-(algebraMap ℂ_[p] _ S) * QdB D lam u P P') * F₀ ∧
            JetsInt D lam (YYl D L L') F₀)

def mom22 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D (tor0 D cc δ) δ p L L' b →
      ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
        (∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) →
          jet D lam y (pSer D lam (e N N' L L')) = μ g) ∧
        ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
          IsIdem D lam (2 * n + 2) ε → (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
          ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
            (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
            jet D lam y (pSer D lam (XiF D (tor0 D cc δ) δ p n ε b Φ (e N N' L L'))) = μ g

def LargerSupportMomentCondition (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → Fin r → D.host.K),
      admitted D N N' L L' → admitted D N N' L₁ L₂ → EqAway D p L L₁ → EqAway D p L' L₂ →
      NNBasis D (tor0 D cc δ) δ p L L' b → NNBasis D (tor0 D cc δ) δ p L₁ L₂ b₁ →
      (∀ j, b j = ∑ i, ((c i j : D.host.K) : D.host.E) • b₁ i) →
      (∀ i j, ‖lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E)))‖ ≤ 1) →
      ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
        IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
        (∀ a, Φ a = if ∃ x : Fin r → ℤ_[p], ∀ i, zc (a i) =
            ∑ j, lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E))) * zc (x j)
          then 1 else 0) →
        ∃ κ : ℂ, κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 ∧
          XiF D (tor0 D cc δ) δ p n ε b₁ Φ (e N N' L₁ L₂) = fun z => κ * e N N' L L' z

def sE (D : D7) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d) (v : {v // v ∈ Po.V}) (e : ZMod d)
    (a : Fin N) (b : Fin N') : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  fun α => ∑ l ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single ((e - 2 * (l : ZMod d), (v, a, b)) : TVar D Po N N') ((p ^ 2) ^ l)
    then (-1 : ℂ_[p]) ^ l else 0

def hh (D : D7) {N N' p d : ℕ} [Fact p.Prime] [NeZero d] (Po : Pos D p d) (v : {v // v ∈ Po.V})
    (u : ZMod d → ℂ_[p]) : MvPowerSeries (TVar D Po N N') ℂ_[p] :=
  ∑ s : ZMod d, algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (u s) *
    ∑ a : Fin N, ∑ b : Fin N', sE D Po v s a b ^ p * sE D Po v (s + 1) a b

def InProd (D : D7) {N N' p d : ℕ} [Fact p.Prime] (Po : Pos D p d)
    (h : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p])
    (F : MvPowerSeries (TVar D Po N N') ℂ_[p]) : Prop :=
  ∃ g : ({v // v ∈ Po.V} → ℕ) → MvPowerSeries (TVar D Po N N') ℂ_[p], (∀ i, IntegralMv (g i)) ∧
    ∀ α, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : {v // v ∈ Po.V} => Finset.range ((α.sum fun _ k => k) + 1)),
        MvPowerSeries.coeff α
          (algebraMap ℂ_[p] (MvPowerSeries (TVar D Po N N') ℂ_[p]) (∏ v, ((p : ℂ_[p]) ^ i v)⁻¹) *
            (∏ v, h v ^ i v) * g i)

def str22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∃ ep : ℂ_[p], InW ep ∧ ‖ep‖ = 1 ∧
    ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ϖ : ℂ_[p]),
      admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
      ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) →
      ∃ u : {v // v ∈ Po.V} → ZMod d → ℂ_[p], (∀ v s, IsIntP (u v s)) ∧
        ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
        ∀ h' : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p],
          (∀ v, ∃ G : MvPowerSeries (TVar D Po N N') ℂ_[p], IntegralMv G ∧ MvPowerSeries.constantCoeff G = 0 ∧
            h' v = hh D Po v (u v) + algebraMap ℂ_[p] _ (p : ℂ_[p]) * G) →
          InProd D Po h' (atLin (fun k j => ep * chg D lam Po P P' k j * ϖ)
            (fun j => MvPowerSeries.X j) F)

def adm1 (D : D7) : Prop :=
  (∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.ramificationIdxIn (𝓞 D.host.E) = 1) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN →
    ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (Ideal.span {(p : ℤ)}) →
      (Ideal.primesOver 𝔭 (𝓞 D.host.E)).ncard = 2) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.QS * D.host.q →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2) ∧
  (∀ 𝔭 : Ideal (𝓞 D.host.K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 1 < 𝔭.ramificationIdxIn (𝓞 D.host.E) →
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.K) ∈ 𝔭) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (D.host.d : 𝓞 D.host.E) ∈ P →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      ((∀ x : 𝓞 D.host.E, ∃ y ∈ P, (y : D.host.E) = σ (x : D.host.E) - (x : D.host.E)) ↔
        (D.host.galE σ = 1 ∨
          D.host.galE σ = ((1, -1), 1))))

def AdmittedStatements (D : D7) : Prop := adm1 D

theorem isChi_chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) :
    IsChi D (chiRec D idl) := by
  obtain ⟨hinj, hN, hmul, hz, -⟩ := h
  refine ⟨?_, ?_⟩
  · intro 𝔞 𝔟 ha hb
    obtain ⟨x, rfl⟩ := (hN 𝔞).1 ha
    obtain ⟨y, rfl⟩ := (hN 𝔟).1 hb
    rw [← hmul, chiRec_idl D idl hinj, chiRec_idl D idl hinj, chiRec_idl D idl hinj, map_mul]
    simp
  · intro z
    rw [← hz z, chiRec_idl D idl hinj]
    exact D.rest_detCharacter_on_unitary_eq z

def aux₃ (D : D7) (C : ℝ) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    per22 D (tor0 D cc δ) ∧ (∃ χ, IsChi D χ) ∧
    ∀ χ, IsChi D χ →
    ∃ e : FamE D, vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ eq22 D (tor0 D cc δ) χ e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e

def Stmt (D : D7) (C : ℝ) : Prop := AdmittedStatements D → aux₃ D C

end Formalism.MainNotions.TaylorLogMetric
end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def lamCol (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k then hcToWeightQ (D.hcW u τ).u ⟨i, h⟩ else 0

def wJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : ℚ :=
  if h : j < D.R.m then wG D.R ((D.hcW u τ).e ⟨j, h⟩) (j + 1) else 0

def lamLiftN (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if i < D.R.k then lamCol D u τ i else - wJ D u τ ((i - D.R.k) / (D.R.t + 1))

def plc (D : D7) (τ : D.what₂.Tau) : D.R.GG := ((D.eTau τ : D.R.Psi) : _)

def IsTop (D : D7) (τ : D.what₂.Tau) : Prop := plc D τ ∈ D.host.topPlaces

def IsThick (D : D7) (τ : D.what₂.Tau) : Prop := plc D τ ∈ D.host.thickPlaces

def Nums (D : D7) (T g1 g2 : ℕ) (Cn x b L b' Sc eta : ℝ) : Prop :=
  0 < b ∧ Real.log (x * b * D.host.v) ≤ L ∧
  Real.log T ≤ Cn * D.R.m * L ∧ Real.log g1 ≤ Cn * L ∧ Real.log g2 ≤ Cn * L ∧
  b' ≤ x * b / x ∧ 1 ≤ Sc ∧ 1 ≤ eta ∧ Sc + eta + D.R.m * D.R.t ≤ b' / x ∧
  (D.R.N D.R.m : ℝ) ^ 2 * (L + Real.log T) ≤ D.R.N D.R.m * b' ∧
  (D.R.N D.R.m : ℝ) * L + Real.log T ≤ b' ∧
  (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * (L + Real.log T + Real.log ((g1 : ℝ) * g2)) ≤ D.R.N D.R.m * b' * L ∧
  |dlogL D 1| ≤ Cn * L ∧ 2 ≤ x ∧ 1 ≤ D.host.v ∧
  (1 + 2 * (2 * Cn + 4)) * (D.R.m : ℝ) ^ 3 * D.R.N D.R.m ≤ b'

def Wts (D : D7) (u : D.what₂.Word) (Cn x b b' Sc eta : ℝ) : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ i < D.R.k, ∃ z : ℤ, lamCol D u τ i = z) ∧
    (IsTop D τ → x * b ≤ (lamCol D u τ 0 : ℝ) ∧ (lamCol D u τ 0 : ℝ) ≤ 2 * (x * b) ∧
      b' ≤ -(lamCol D u τ (D.R.k - 1) : ℝ) ∧ -(lamCol D u τ (D.R.k - 1) : ℝ) < 2 * b' ∧
      ∀ i, 0 < i → i < D.R.k - 1 → 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ Sc) ∧
    (¬ IsTop D τ → ∀ i < D.R.k, 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ Cn * Sc) ∧
    (∀ j, j + 1 < D.R.m → wJ D u τ j ≤ wJ D u τ (j + 1)) ∧
    (¬ IsThick D τ → ∀ j < D.R.m, (wJ D u τ j : ℝ) ≤ 2 * b') ∧
    (IsThick D τ → ∀ j < D.R.m, b - D.R.N D.R.m ≤ (wJ D u τ j : ℝ) ∧ (wJ D u τ j : ℝ) ≤ b + eta + 1) ∧
    - lamCol D u τ (D.R.k - 1) ≤ wJ D u τ 0 ∧
    ((wJ D u τ (D.R.m - 1) - wJ D u τ 0 : ℚ) : ℝ) ≤ eta

def Tu (D : D7) (u : D.what₂.Word) : ℕ := (D.mem u).A.T

def dualSub {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    AddSubgroup S.V where
  carrier := {x | ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range}
  zero_mem' := fun y _ => by rw [map_zero]; exact zero_mem _
  add_mem' := fun {a b} ha hb y hy => by
    rw [(S.hT y).map_add]
    exact add_mem (ha y hy) (hb y hy)
  neg_mem' := fun {a} ha y hy => by rw [map_neg]; exact neg_mem (ha y hy)

def LatT {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) : Prop :=
  (∀ x ∈ L, x ∈ dualSub S L) ∧ L.toAddSubgroup.relIndex (dualSub S L) = q

def SameCls {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (M : ℕ) {n : ℕ}
    (L L' : Submodule (𝓞 E) S.V) (e e' : Fin n → S.V) : Prop :=
  ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ (∀ x, x ∈ L ↔ γ x ∈ L') ∧
    ∀ a, ∃ z ∈ dualSub S L', γ (e a) - e' a = (M : E) • z

def ClsTie (D : D7) (u : D.what₂.Word) : Prop :=
  (∀ i ≤ D.R.m, (∀ c, LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.clsLat u i c)) ∧
    ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
      (∀ c a, e c a ∈ dualSub (D.sp.X i) (D.clsLat u i c)) ∧
      ∀ c c', SameCls (D.sp.X i) (Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c) (D.clsLat u i c')
        (e c) (e c') → c = c') ∧
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ dualSub D.sp.X' (LP c)) ∧
      ∀ c c', SameCls D.sp.X' (Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') → c = c'

def adm3 (D : D7) : Prop := ∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0), Subsingleton ((D.mem u).C.stab 0 c)

def aT (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ := (lamCol D u τ 0 : ℝ)

def bT (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ := -(lamCol D u τ (D.R.k - 1) : ℝ)

def tops (D : D7) : Finset D.what₂.Tau := topsOf D.host D.eTau

abbrev Gx (D : D7) (i : ℕ) : Type := D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N (i + 1))

def Hherm (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z w : Gx D i → ℂ) : ℂ :=
  ∑ g, z g * star (w g) / ((Real.pi * D.gx.Om g.1 s : ℝ) : ℂ)

def Hq (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z : Gx D i → ℂ) : ℝ :=
  ∑ g, ‖z g‖ ^ 2 / (Real.pi * D.gx.Om g.1 s)

def dz (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : MeasureTheory.Measure (Gx D i → ℂ) :=
  ENNReal.ofReal (∏ g : Gx D i, (Real.pi * D.gx.Om g.1 s)⁻¹) • MeasureTheory.volume

def dens (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) (z : Gx D i → ℂ) : ℝ :=
  ‖Th z‖ ^ 2 * Real.exp (-Real.pi * Hq D i s z)

def trans (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (x : Gx D i → ℂ) (Th : (Gx D i → ℂ) → ℂ) :
    (Gx D i → ℂ) → ℂ :=
  fun z => Th (z - x) * Complex.exp (Real.pi * Hherm D i s z x - ((Real.pi * Hq D i s x / 2 : ℝ) : ℂ))

structure Torus (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) where
  La : AddSubgroup (Gx D i → ℂ)
  F : Set (Gx D i → ℂ)
  fund : MeasureTheory.IsAddFundamentalDomain La F (dz D i s)
  covol : dz D i s F = 1
  Hmin : ∀ y ∈ La, y ≠ 0 → ∃ β : D.host.E, β ≠ 0 ∧
    (∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (β * (a : D.host.E)) = (n : ℚ)) ∧
    Hq D i s y = 2 * ∑ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖

def Torus.Admis {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) : Prop :=
  Differentiable ℂ Th ∧ (∀ y ∈ T.La, ∀ z, dens D i s Th (z + y) = dens D i s Th z) ∧
  MeasureTheory.IntegrableOn (dens D i s Th) T.F (dz D i s)

def Torus.l2Sq {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) : ℝ :=
  ∫ z in T.F, dens D i s Th z ∂(dz D i s)

structure KerData (D : D7) (u : D.what₂.Word) where

  embS : ∀ i (s : D.what₂.LL →+* ℂ), ((D.fm u).lat i).V →ₛₗ[s] ((D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)

  ipS : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i →
    (((D.mem u).C.Y i → ℂ) →ₗ⋆[ℂ] ((D.mem u).C.Y i → ℂ) →ₗ[ℂ] ℂ)
  tor : ∀ i (s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → Torus D i s

  Th : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i → ℂ) → ℂ

  cf : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i →₀ ℕ) → ℂ
  cf_sum : ∀ i < D.R.m, ∀ s L L' z, HasSum (fun e => cf i s L L' e * e.prod fun g n => z g ^ n) (Th i s L L' z)

  e0 : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → (Gx D i → ℂ) → ℂ
  initial_theta_admissible : ∀ i < D.R.m, ∀ s L L', (tor i s L L').Admis (e0 i s L L')

  levelZeroComparison_norm : ∀ i < D.R.m, ∀ s L L', (D.fm u).thFree i s L L' ^ 2 = (tor i s L L').l2Sq (e0 i s L L')

  Q : ∀ i (_s : D.what₂.LL →+* ℂ), (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) →
    ((D.fm u).lat i).V → ((D.fm u).lat (i + 1)).V → MvPolynomial (Gx D i) ℂ

namespace KerData

variable {D : D7} {u : D.what₂.Word} (X : KerData D u)

end KerData

section Tensor

variable {ι : Type} [Fintype ι]

def ten {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def TSpan (K : Type) [Field K] {n : ℕ} (lam : ι → DomWeight n) :
    Submodule K (MvPolynomial (ι × Fin n × Fin n) K) :=
  Submodule.span K {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ delSq K n (lam τ)) ∧ p = ten f}

def actAll {K : Type} [Field K] {n : ℕ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) : MvPolynomial (ι × Fin n × Fin n) K :=
  (∏ τ, (g τ).det ^ (lam τ).detShift) •
    MvPolynomial.aeval (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2)) p

def nfAll {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

end Tensor

def IntSpanAt (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW D.what₂.places w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = r • ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ))}

def LocBasis (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) : Prop :=
  IsUnit γ.det ∧ locW D.what₂.places w Q.L =
    Submodule.span (intW D.what₂.places w) (Set.range fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i))

structure ColVal (D : D7) (u : D.what₂.Word) where

  ne : Nonempty ((D.mem u).C.cls 0)
  rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)
  Q : (D.mem u).C.cls 0 → D.what₂.Tau → HLat D.what₂.LL
  Q_good : ∀ c τ, (Q c τ).Good
  eQ : ∀ c τ, (Q c τ).ι ≃ Fin (D.R.N 0)

  bc : ∀ c τ, (D.sp.X 0).V →+ (Q c τ).V
  bc_smul : ∀ c τ (a : D.host.E) y, bc c τ (a • y) = rho τ a • bc c τ y

  bc_L : ∀ c τ, (Q c τ).L = Submodule.span (𝓞 D.what₂.LL) (bc c τ '' (D.clsLat u 0 c : Set (D.sp.X 0).V))

  bc_norm : ∀ c τ (v : InfinitePlace D.what₂.LL) y,
    (Formalism.HermitianLatticesTheory.majAt (Q c τ).b (Q c τ).X v (bc c τ y) (bc c τ y)).re =
      (v.embedding (rho τ ((D.sp.X 0).hT y y))).re

  latT : ∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)

  co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
    ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
  co_inj : Function.Injective co

  co_range : ∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)

  fin : ∀ (w : D.what₂.places.Pl)
    (γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL),
    (∀ c τ, LocBasis D w (Q c τ) (eQ c τ) (γ c τ)) →
    ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
      ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)

  inf : ∀ (v : InfinitePlace D.what₂.LL) x,
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
      ∑ c, (nfAll ((D.fm u).lam 0)
        (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))
        (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))).re

def Conclusion5 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ColVal D u →
    -(∑ t ∈ tops D, aT D u t / D.R.k * Real.log (Tu D u)) - C * D.host.TT.card * (x * b) * Real.log D.R.k -
        C * D.R.f * D.R.k * (b' + Sc) * Real.log D.R.k - C * D.R.f * Sc * Real.log (Tu D u) -
        C * D.R.f * (D.R.k : ℝ) ^ 2 * L ≤ ((D.fm u).lat 0).mu

def Conclusion6 (D : D7) (Cn C x : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ColVal D u →
    ((D.fm u).lat 0).muMax ≤ C * D.host.TT.card * (x * b) * Real.log (D.R.k * D.host.v) +
      C * D.R.f * (b' + Sc) * (D.R.k * Real.log (D.R.k * D.host.v) + Real.log (Tu D u)) +
      C * D.R.f * (D.R.k : ℝ) ^ 2 * L

def famC {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (P : D7 → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cn : ℝ, ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P (Fm.D x i) Cn C x

def fam0 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (P : D7 → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P (Fm.D x i)

def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm adm3

def ConclusionF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm Conclusion5
def ConclusionF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := famC Fm Conclusion6

end Formalism.MainNotions.flipTwoThree
end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField Filter Topology MeasureTheory

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-(c * Real.log X / Real.log B)) + C * Real.exp (-(c * Real.sqrt (Real.log X)))

section RayClass

variable (K0 : Type) [Field K0] [NumberField K0]

def CoprimeTo (qq I : Ideal (𝓞 K0)) : Prop := I ≠ ⊥ ∧ I ⊔ qq = ⊤

def RayRel (qq I J : Ideal (𝓞 K0)) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I = Ideal.span {b} * J

def Bmod (qq : Ideal (𝓞 K0)) : ℝ := 4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

def nDeg1 (qq I0 : Ideal (𝓞 K0)) (X h : ℝ) : ℕ :=
  Set.ncard {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
    (Ideal.absNorm P).Prime ∧ X < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ X * (1 + h)}

def ShortIntervalLowerBound (cQ C0 Cr cr c1 c2 : ℝ) : Prop :=
  ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ → ∀ X : ℝ, Bmod K0 qq ^ C0 ≤ X →
    (∀ (be : ℝ) (th : ℤ), (th = -1 ∨ th = 0 ∨ th = 1) → 1 / 2 ≤ be → be < 1 →
      cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be →
      c1 * Bmod K0 qq ^ (-5 : ℝ) * X / Real.log X ≤ Li X - (th : ℝ) * Li (X ^ be)) ∧
    (∀ I0, CoprimeTo K0 qq I0 → ∀ h : ℝ, rhoErr Cr cr (Bmod K0 qq) X ≤ h / 100 → h ≤ 1 →
      Bmod K0 qq ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c2 * h * Bmod K0 qq ^ (-6 : ℝ) * X / Real.log X ≤ (nDeg1 K0 qq I0 X h : ℝ))

end RayClass

def NormOneMod (D : D7) (M g : ℕ) : Prop :=
  ∃ π ρ : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (ρ : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) - 1 = (M : D.host.E) * ρ ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E)

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

abbrev ZPt : Type := Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ

def zOrd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def adm6 (_D : D7) (C1 c : ℝ) : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset ZPt,
    (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) →
    ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤
      C1 * Q ^ ((1 : ℝ) / 4)) ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ,
    DirichletCharacter.LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re →
    IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 ∧
      ∀ ρ' : ℂ, DirichletCharacter.LFunction χ ρ' = 0 →
        1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
  (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3))

def adm7 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖)

def adm11 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (zOrd χ ρ : ℝ) ≤ C * Real.log (N * (|t| + 2))

theorem factorsThrough_inv {N : ℕ} {χ : DirichletCharacter ℂ N} {d : ℕ}
    (h : χ.FactorsThrough d) : χ⁻¹.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive DirichletCharacter.conductor at *
  have hs : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.mem_conductorSet_iff]
    exact ⟨fun h' => by simpa using factorsThrough_inv h', factorsThrough_inv⟩
  rw [hs]
  exact h

theorem zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hprim := isPrimitive_inv hχ
  have hρ0 : ρ ≠ 0 := fun h => by
    rw [h] at h0
    simp at h0
  have h1ρ : (1 - ρ) ≠ 0 := fun h => by
    have e := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at e
    linarith
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have e := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) ρ (Or.inl hρ0)
    rw [hz, eq_comm, div_eq_zero_iff] at e
    exact e.resolve_right hg
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (1 - ρ) (Or.inl h1ρ),
    hprim.completedLFunction_one_sub ρ, inv_inv, hc]
  simp


def GoodAll (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M → GoodFor Q χ

def BoundsII (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M →
    ‖gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChoiceOfModulusAndDiscriminant (n : ℕ) (x eps C : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 x eps) < q ∧ (q : ℝ) ≤ X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 x eps) < d ∧ (d : ℝ) ≤ X2 x eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1) ∧

  GoodAll (8 * X1 x eps) (psDir q) (8 * q * d) ∧
  GoodAll (8 * X1 x eps) (fun a => chi8 a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (chDir d) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chDir d a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a * psDir q a) (8 * q * d) ∧

  BoundsII x eps C (psDir q) (8 * q * d) ∧ BoundsII x eps C (chDir d) (8 * q * d) ∧
  BoundsII x eps C (fun a => chDir d a * psDir q a) (8 * q * d) ∧

  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PairAt (Y eps : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 Y eps) < q ∧ (q : ℝ) ≤ X1 Y eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 Y eps) < d ∧ (d : ℝ) ≤ X2 Y eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1)

def PropTwoSixBoxHypothesis (D : D7) (x eps : ℝ) : Prop :=
  (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ BoxE D Y eps) ∧ Real.log (NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PropTwoSixThinScales (D : D7) (x eps c : ℝ) : Prop :=
  PropTwoSixBoxHypothesis D x eps →
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

section Family

variable {eps : ℝ}

def FamilySixthHypothesis (Fm : FamP eps) : Prop :=
  ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm6 (Fm.D x i) C1 c
def adm7F (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm7 (Fm.D x i) C
def ComplementTwoFamily (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm11 (Fm.D x i) C

def FamilyPropTwoSixCongruenceForm (Fm : FamP eps) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PropTwoSixThinScales (Fm.D x i) x eps c

end Family

end Formalism.MainNotions.ShortIntervalPrimes

end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Finset
open scoped Pointwise ComplexConjugate

open Classical

abbrev Chr (D : D7) : Type := D.R.GG →* ℂˣ

def sgnC : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ).toMonoidHom

abbrev chC (D : D7) : Chr D := D.R.chC

def psC (D : D7) : Chr D := sgnC.comp D.R.chQ

def Unram (D : D7) (p : ℕ) : Prop := p.Prime ∧ ¬ ((p : ℤ) ∣ discr D.host.E)

def InertK (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ (D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass)

def Reads (D : D7) (ψ : Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N) : Prop :=
  χ.2.IsPrimitive ∧ ∀ p : ℕ, Unram D p → χ.2 (p : ZMod χ.1) = ((ψ (frob D p) : ℂˣ) : ℂ)

def prim (D : D7) (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  if h : ∃ χ, Reads D ψ χ then h.choose else ⟨1, 1⟩

def Gc (D : D7) (ψ : Chr D) (y : ℝ) : ℂ := gChi (prim D ψ).2 y

def Lp (D : D7) (ψ : Chr D) : ℂ := logDerivativeAtOne (prim D ψ).2

def iner (D : D7) : D.R.GG := (sgc0, 1)

def askP (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) (p : ℕ) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi then
    max (a / (p : ℝ) ^ i - w (rho D τ (frob D p ^ i))) 0 else 0

def gD (D : D7) (i : ℕ) : D.R.GG :=
  if frob D D.host.d ^ i ∉ D.R.Psi then frob D D.host.d ^ i else frob D D.host.d ^ i * iner D

def askD (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i then max (a / (D.host.d : ℝ) ^ i - w (rho D τ (gD D i))) 0 else 0

def ASKjt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  (∑' p : ℕ, if InertK D p then 2 * Real.log p * askP D a w τ p else 0) +
    Real.log D.host.d * askD D a w τ

def adm5 (D : D7) (s : Scale) (c : ℝ) : Prop :=
  ∀ ψ : Chr D, ∀ y : ℝ, s.X' / 3 ≤ y → ‖Gc D ψ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

def adm10 (D : D7) : Prop := ∀ ψ : Chr D, ∃ χ, Reads D ψ χ

def SizesAt (D : D7) (s : Scale) (δ : ℝ) : Prop :=
  s.x ^ (2 + 8 * s.eps - δ) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ s.x ^ (2 + 8 * s.eps + δ) ∧
  (s.x * s.delta1) ^ ((1 : ℝ) / 2 - δ) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ (s.x * s.delta1) ^ ((1 : ℝ) / 2 + δ) ∧
  s.x ^ ((9 : ℝ) / 2 + 10 * s.eps - δ) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps + δ)

end Formalism.MainNotions.ZetaZeroFreeRegion

end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.Chosen
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def GamL : ℝ := Real.exp (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L)

def ThickSetLowerBound (_L : SizeData₂ D) : Prop := D.host.secondSet_card_lower_bound

def ChTT_at : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n


open Classical in
def largeOrderResiduePrimes : Finset ℕ :=
  (Finset.range ⌈L.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ G.IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (G.hP D p) : ℝ))

variable {L}


open Classical in
def badTops (X : G.Inst D L) (p : ℕ) : Finset (G.HH D) :=
  D.host.TT.filter (fun t => ¬ G.Good X p (X.bs (G.stepP D p) t))

def ChBad_at (X : G.Inst D L) (Cb : ℝ) : Prop :=
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

def BoundsAtX (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ f M →
    ‖GlobalTheoryTheory.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChQD_at (D : D7) (x eps C : ℝ) : Prop :=
  BoundsAtX x eps C (GlobalTheoryTheory.psDir D.host.q) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (GlobalTheoryTheory.chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d)

def ChThin_at (D : D7) (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

variable (L)

def ChProviso_at (C0 : ℝ) : Prop :=
  ∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ≤ C0

def ChCode_at (C0 CH : ℝ) : Prop :=
  C0 * GamL L ^ 2 * L.sc.x ^ CH ≤ (Fintype.card D.what₂.Word : ℝ)

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ThickSetEventually : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ThickSetLowerBound (Fm.L x i)

def ChosenTT : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChTT_at (Fm.L x i)

def ChosenBad (Cb : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChBad_at (Fm.Gx x i) Cb

def ChosenQD (C5 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChQD_at (Fm.D x i) x eps C5

def ChosenThin (c6 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChThin_at (Fm.D x i) x eps c6

def ChosenProviso (C0 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChProviso_at (Fm.L x i) C0

def ChosenCode (C0 CH : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChCode_at (Fm.L x i) C0 CH

def Chosen (CH C0 C5 c6 Cb : ℝ) : Prop :=
  ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def ChosenE (C0 CH : ℝ) : Prop :=
  ∃ C5 c6 Cb : ℝ, 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ Chosen Fm CH C0 C5 c6 Cb

end Family

end Formalism.MainNotions

end
end
