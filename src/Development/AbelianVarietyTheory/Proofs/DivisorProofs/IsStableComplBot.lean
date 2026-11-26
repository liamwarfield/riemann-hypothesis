module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.DefTransfer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KP [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) : Set (UA D.host.E n) :=
  {x | x ∈ locU n P ∧ cLoc P x ∈ GlobalTheory.LFun.KGL P (n := n)}

def cj [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) :
    UA D.host.E V.rank ≃* GA D V :=
  j.toMulEquiv.trans (MulAut.conj h₀⁻¹)

theorem cj_apply [IsCMField D.host.E] {V : HSp D} (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (x : UA D.host.E V.rank) : cj j h₀ x = h₀⁻¹ * j x * h₀ := by
  simp [cj, MulAut.conj_apply]
  rfl

def IsTransfer [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V) : Prop :=
  h₀ ∈ GfC V ∧
  (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
  (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) ∧
  (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
  (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
    ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
      A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x,
    x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f (cj j h₀ x)) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) ∧
  ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
    (∀ γ ∈ R, (cj j h₀).symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P ((cj j h₀).symm γ))) ∧
    ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
      ∃! γ, γ ∈ R ∧ ((cj j h₀).symm γ)⁻¹ * x ∈ KP V.rank P

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

variable {θ M}

end GlobalTheory.DefTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

variable {p : ℕ} [Fact p.Prime]

def InT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β y : G.C) (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R (z.1 : R ⊗[ℚ] G.C)).unop =
      algebraMap R (R ⊗[ℚ] G.C) (z.2 : R) * inC G R β ∧
    Commute (z.1 : R ⊗[ℚ] G.C) (inC G R y)

def psiAway (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
  (MulAut.conj x).toMonoidHom.prodMap (MonoidHom.id _)

def psiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gr G 1 :=
  (inclG G 1).comp ((MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _)))

@[simp] theorem psiAway_apply (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :
    psiAway G x z = (x * z.1 * x⁻¹, z.2) := rfl

def dg (D : Type) [Ring D] [Algebra ℚ D] (p : ℕ) [Fact p.Prime] :
    Dˣ × ℚˣ →* ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
  ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] AfP p ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).prod
    ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] ℚ_[p] ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom))

theorem toAfF_eq_psiAway (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) :
    ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x ((dg G.C p (y : G.Cˣ × ℚˣ)).1) := rfl

theorem formGroupToPadicPointsDegreeOne_eq_unitaryPoints (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    toP1 G β y = psiP G ((dg G.C p (y : G.Cˣ × ℚˣ)).2) := by
  simp only [toP1, psiP, MonoidHom.comp_apply]
  congr 1
  refine Prod.ext rfl (funext fun w => Units.ext ?_)
  change G.rho w _ = G.locW w ((1 : ℚ_[p]) ⊗ₜ _)
  change _ = (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) * (G.rho w).toRatAlgHom _
  rw [map_one, one_mul]
  rfl

theorem form_mul_inv {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β : D) (a e : Dˣ) (α η : ℚˣ)
    (ha : (a : D) * β * (σ a).unop = algebraMap ℚ D α * β) (he : (e : D) * β * (σ e).unop = algebraMap ℚ D η * β) :
    ((a * e⁻¹ : Dˣ) : D) * β * (σ ((a * e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((α * η⁻¹ : ℚˣ) : ℚ) * β := by
  have hs : (σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hs' : (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (e : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have hη : algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ D (η : ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * β := by
    calc ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop
        = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * (((e⁻¹ : Dˣ) : D) * (algebraMap ℚ D (η : ℚ) * β) *
            (σ ((e⁻¹ : Dˣ) : D)).unop) := by
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
          rw [show (η : ℚ) * ((η⁻¹ : ℚˣ) : ℚ) = 1 by simp, one_smul]
      _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((((e⁻¹ : Dˣ) : D) * e) * β *
            ((σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop)) := by
          rw [← he]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs, one_mul, mul_one]
  have hsm : (σ ((a * e⁻¹ : Dˣ) : D)).unop = (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  rw [hsm, Units.val_mul, Units.val_mul, map_mul]
  calc (a : D) * ((e⁻¹ : Dˣ) : D) * β * ((σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop)
      = (a : D) * (((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop) * (σ (a : D)).unop := by
        simp only [mul_assoc]
    _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((a : D) * β * (σ (a : D)).unop) := by
        rw [key, ← mul_assoc (a : D), ← Algebra.commutes ((η⁻¹ : ℚˣ) : ℚ) (a : D)]; simp only [mul_assoc]
    _ = _ := by
        rw [ha, ← mul_assoc, ← map_mul, mul_comm ((η⁻¹ : ℚˣ) : ℚ), map_mul]

theorem conj_back {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x g : Sˣ)
    (t c : A) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hg : (g : S) * (σ g).unop = algebraMap A S c) :
    ((x⁻¹ * g * x : Sˣ) : S) * b * (σ ((x⁻¹ * g * x : Sˣ) : S)).unop = algebraMap A S c * b := by
  have h1 : (σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = algebraMap A S t * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ (x : S)).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by rw [hx, ← Algebra.commutes, mul_assoc]
  have hσ : (σ ((x⁻¹ * g * x : Sˣ) : S)).unop =
      (σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop := by
    simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [hσ]
  calc ((x⁻¹ * g * x : Sˣ) : S) * b * ((σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)
      = ((x⁻¹ : Sˣ) : S) * ((g : S) * ((x : S) * b * (σ (x : S)).unop) * (σ (g : S)).unop) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = ((x⁻¹ : Sˣ) : S) * (algebraMap A S t * ((g : S) * (σ (g : S)).unop)) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        rw [hx, ← Algebra.commutes t (g : S)]; simp only [mul_assoc]
    _ = algebraMap A S (c * t) * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
        rw [hg, ← map_mul, ← Algebra.commutes, mul_assoc, mul_comm t c]
    _ = algebraMap A S c * b := by rw [hb, map_mul, mul_assoc]

theorem inT_psiAway_inv_of_commute : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y₀ : grp G β) (c : G.GAf), c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c →
    InT G (AfP p) β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (psiAway G x⁻¹ (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
  intro p _ G β x t hx y₀ c hc
  have hxx : ((x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) = x := inv_inv x
  refine ⟨?_, ?_⟩
  · have hg : (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (starT G.star (AfP p) (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
          AfP p ⊗[ℚ] G.C)).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) := c.2
    have h := conj_back (starT G.star (AfP p)) (inC G (AfP p) β) x _ (t : AfP p) _ hx hg
    simp only [psiAway_apply, hxx]
    exact h
  · have hU := congrArg (fun g : G.GAf => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)) hc
    simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
    rw [toAfF_eq_psiAway, psiAway_apply] at hU
    simp only [psiAway_apply, hxx]
    set c1 := (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    set Y := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).1.1
    have hUU : (x⁻¹ * c1 * x) * Y = Y * (x⁻¹ * c1 * x) := by
      calc (x⁻¹ * c1 * x) * Y = x⁻¹ * (c1 * (x * Y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * Y * x⁻¹) * c1) * x := by rw [hU]
        _ = Y * (x⁻¹ * c1 * x) := by group
    exact congrArg Units.val hUU

end GlobalTheory.TorCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory

theorem unitary_diag_one_mem_dbl : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type)
    [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  intro R E _ _ _ c β _ _ J g
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  have h1 : ((g : GL β E) : Matrix β β E) * (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) = 1 := Units.mul_inv _
  have h2 : (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((g : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hm1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hm0 : (0 : Matrix β β E).map c = 0 := Matrix.map_zero _ (map_zero c)
  refine ⟨⟨⟨Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    Matrix.fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1, Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]; simp [h2, Matrix.fromBlocks_one]
  · show (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
        (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, hm0, hm1, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryDoubled_blockDiag_one : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J), ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  first | exact @GlobalTheory.unitary_diag_one_mem_dbl | exact GlobalTheory.unitary_diag_one_mem_dbl | (intros; apply GlobalTheory.unitary_diag_one_mem_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.UnitaryAdelicTop

theorem isClosed_UG {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [T2Space B] (c : B →ₐ[A] B) (hc : Continuous c) {n : ℕ} (J : Matrix (Fin n) (Fin n) B) :
    IsClosed (UG c J : Set (GL (Fin n) B)) := by
  have hv : Continuous fun g : GL (Fin n) B => (g : Matrix (Fin n) (Fin n) B) := Units.continuous_val
  exact isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hc)) continuous_const

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧
      SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.secondCountableTopology
  haveI : T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc := isClosed_UG (cA σ) hσ (incM F J)
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

end GlobalTheory.UnitaryAdelicTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

def intAfP (p : ℕ) : Set (AfP p) :=
  {a | ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mem (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  _root_.natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.2 hb0, ?_⟩
  have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (|b|) := by
    rw [← Int.natCast_natAbs, map_natCast]
  rw [e]
  rcases abs_choice b with h | h
  · rw [h, mul_comm]; exact hbx
  · rw [h, map_neg, neg_mul, mul_comm]; exact neg_mem hbx

theorem eval_natCast_mul {p : ℕ} (v : AwayP p) (n : ℕ) (a : AfP p) :
    AfP.eval v ((n : AfP p) * a) = (n : v.1.adicCompletion ℚ) * AfP.eval v a := by
  rw [map_mul, map_natCast]

theorem exists_nat_adele {p : ℕ} (a : AfP p) : ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 (AfP.eval v a)
  have hS : {v : AwayP p | ¬ AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (a : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [eval_natCast_mul]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem w.1 k) (hm w)
  · have hw' : AfP.eval w a ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem w.1 _) hw'

theorem exists_pow_of_integral_away (p : ℕ) [Fact p.Prime] (r : ℚ)
    (h : ∀ v : AwayP p, (v.1.valuation ℚ r) ≤ 1) : ∃ (k : ℤ) (e : ℕ), r * (p : ℚ) ^ e = k := by
  have hden : r.den = p ^ r.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd r.den_nz fun {ℓ} hℓ hdvd => ?_
    by_contra hne
    have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)}, (Ideal.span_singleton_prime hℓ'.ne_zero).2 hℓ',
      by simpa using hℓ.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro h'
      have h'' : Associated (ℓ : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.1 h'
      exact hne (by simpa using Int.natAbs_eq_iff_associated.2 h'')
    have h1 := Rat.valuation_le_one_iff_den.1 (h ⟨v, hv⟩)
    exact h1 (Ideal.mem_span_singleton.2 (by exact_mod_cast hdvd))
  refine ⟨r.num, r.den.primeFactorsList.length, ?_⟩
  have : ((p : ℚ) ^ r.den.primeFactorsList.length) = (r.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.mul_den_eq_num]

theorem den_bounded_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧
    ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ Ω hΩ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun q hq => ?_⟩
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hqa' : (m a : AfP p) * algebraMap ℚ (AfP p) q ∈ intAfP p := hqa
  have hint : ∀ v : AwayP p, v.1.valuation ℚ (((∏ a ∈ t, m a : ℕ) : ℚ) * q) ≤ 1 := by
    intro v
    have h2 : AfP.eval v (algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q)) ∈
        v.1.adicCompletionIntegers ℚ := by
      have e : algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q) =
          (k : AfP p) * ((m a : AfP p) * algebraMap ℚ (AfP p) q) := by
        rw [map_mul, map_natCast, hk, Nat.cast_mul]; ring
      rw [e, eval_natCast_mul]
      exact mul_mem (natCast_mem v.1 k) (hqa' v)
    rw [AlgHom.commutes] at h2
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    exact h2
  obtain ⟨z, e, hz⟩ := exists_pow_of_integral_away p _ hint
  exact ⟨z, e, by rw [← hz]; ring⟩

end GlobalTheory.DenAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.WeylGL

section Abstract

variable {G : Type} [Group G] {K : Subgroup G}

theorem mem_doset {g x : G} :
    x ∈ DoubleCoset.doubleCoset g (K : Set G) K ↔ ∃ a ∈ K, ∃ b ∈ K, x = a * g * b := by
  simpa using DoubleCoset.mem_doubleCoset (s := (K : Set G)) (t := (K : Set G)) (a := g) (b := x)

theorem dosetInd_of_mem {g x : G} (h : ∃ a ∈ K, ∃ b ∈ K, x = a * g * b) : dosetInd ℂ K g x = 1 := by
  unfold dosetInd; rw [Set.indicator_of_mem (mem_doset.2 h)]; rfl

theorem dosetInd_of_not {g x : G} (h : ¬ ∃ a ∈ K, ∃ b ∈ K, x = a * g * b) : dosetInd ℂ K g x = 0 := by
  unfold dosetInd; rw [Set.indicator_of_notMem (fun h' => h (mem_doset.1 h'))]

theorem dosetInd_congr {g x : G} (h : ∃ a ∈ K, ∃ b ∈ K, x = a * g * b) : dosetInd ℂ K x = dosetInd ℂ K g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  funext y
  by_cases hy : ∃ c ∈ K, ∃ d ∈ K, y = c * g * d
  · rw [dosetInd_of_mem hy, dosetInd_of_mem]
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    exact ⟨c * a⁻¹, K.mul_mem hc (K.inv_mem ha), b⁻¹ * d, K.mul_mem (K.inv_mem hb) hd, by group⟩
  · rw [dosetInd_of_not hy, dosetInd_of_not]
    rintro ⟨c, hc, d, hd, rfl⟩
    exact hy ⟨c * a, K.mul_mem hc ha, b * d, K.mul_mem hb hd, by group⟩

theorem biInv_apply {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {g x : G} (hx : ∃ a ∈ K, ∃ b ∈ K, x = a * g * b) : h x = h g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact hh.1 ⟨a, ha⟩ ⟨b, hb⟩ g

theorem mem_of_supp (A : Submodule ℂ (G → ℂ)) {h : G → ℂ} (hh : h ∈ Hecke ℂ K)
    (hs : ∀ g, h g ≠ 0 → dosetInd ℂ K g ∈ A) : h ∈ A := by
  classical
  obtain ⟨S, hS⟩ := hh.2
  induction S using Finset.induction_on generalizing h with
  | empty =>
    have : h = 0 := funext fun g => by
      by_contra h0
      obtain ⟨s, hs, _⟩ := hS g h0
      simp at hs
    rw [this]; exact A.zero_mem
  | insert s S _ ih =>
    have h1 : h s • dosetInd ℂ K s ∈ A := by
      by_cases h0 : h s = 0
      · rw [h0, zero_smul]; exact A.zero_mem
      · exact A.smul_mem _ (hs s h0)
    have key : ∀ g, (h - h s • dosetInd ℂ K s) g ≠ 0 → h g ≠ 0 ∧ ¬ ∃ a ∈ K, ∃ b ∈ K, g = a * s * b := by
      intro g hg
      by_cases hx : ∃ a ∈ K, ∃ b ∈ K, g = a * s * b
      · exact absurd (by simp [dosetInd_of_mem hx, biInv_apply hh hx]) hg
      · exact ⟨by simpa [dosetInd_of_not hx] using hg, hx⟩
    have h2 : h - h s • dosetInd ℂ K s ∈ A := by
      refine ih (Submodule.sub_mem _ hh (Submodule.smul_mem _ _ (Final.DosetIndMem G K ℂ s)))
        (fun g hg => hs g (key g hg).1) fun g hg => ?_
      obtain ⟨t, ht, a, b, e⟩ := hS g (key g hg).1
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd ⟨a, a.2, b, b.2, e⟩ (key g hg).2
      · exact ⟨t, ht, a, b, e⟩
    simpa using A.add_mem h1 h2

theorem dosetInd_mem_of_top (A : Submodule ℂ (G → ℂ)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) (hA : f ∈ A) {s : G} (h0 : f s ≠ 0)
    (hs : ∀ g, f g ≠ 0 → (∃ a ∈ K, ∃ b ∈ K, g = a * s * b) ∨ dosetInd ℂ K g ∈ A) : dosetInd ℂ K s ∈ A := by
  have h2 : f - f s • dosetInd ℂ K s ∈ A := by
    refine mem_of_supp A (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (Final.DosetIndMem G K ℂ s))) fun g hg => ?_
    by_cases hx : ∃ a ∈ K, ∃ b ∈ K, g = a * s * b
    · exact absurd (by simp [dosetInd_of_mem hx, biInv_apply hf hx]) hg
    · exact (hs g (by simpa [dosetInd_of_not hx] using hg)).resolve_left hx
  have h3 := A.smul_mem (f s)⁻¹ (A.sub_mem hA h2)
  simpa [smul_smul, inv_mul_cancel₀ h0] using h3

theorem conv_supp (hK : IsCommensurated K) {a b g : G} (h : conv K (dosetInd ℂ K a) (dosetInd ℂ K b) g ≠ 0) :
    ∃ x y, (∃ c ∈ K, ∃ d ∈ K, x = c * a * d) ∧ (∃ c ∈ K, ∃ d ∈ K, y = c * b * d) ∧ g = x * y := by
  rw [Final.ConvCount G K ℂ hK, Nat.cast_ne_zero, Nat.card_ne_zero] at h
  obtain ⟨⟨x, h1, h2⟩, -⟩ := h
  exact ⟨x.out, x.out⁻¹ * g, mem_doset.1 h1, mem_doset.1 h2, by group⟩

theorem conv_top (hK : IsCommensurated K) (a b : G) : conv K (dosetInd ℂ K a) (dosetInd ℂ K b) (a * b) ≠ 0 := by
  rw [Final.ConvCount G K ℂ hK, Nat.cast_ne_zero, Nat.card_ne_zero]
  constructor
  · obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul K a
    refine ⟨⟨(a : G ⧸ K), mem_doset.2 ⟨1, K.one_mem, κ, κ.2, by rw [hκ, one_mul]⟩,
      mem_doset.2 ⟨κ⁻¹, K.inv_mem κ.2, 1, K.one_mem, ?_⟩⟩⟩
    rw [hκ]; group
  · refine Set.Finite.to_subtype
      ((Formalism.UG.P.finite_supp K hK _ (Final.DosetIndMem G K ℂ a)).subset fun x hx => ?_)
    show dosetInd ℂ K a x.out ≠ 0
    rw [dosetInd_of_mem (mem_doset.1 hx.1)]; exact one_ne_zero

end Abstract

section Gen

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {ϖ : P.adicCompletion E}

def tor (h0 : ϖ ≠ 0) (a : Fin n → ℤ) : GL (Fin n) (P.adicCompletion E) where
  val := Matrix.diagonal fun i => ϖ ^ a i
  inv := Matrix.diagonal fun i => ϖ ^ (-a i)
  val_inv := by simp [Matrix.diagonal_mul_diagonal, zpow_ne_zero _ h0]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, zpow_ne_zero _ h0]

theorem tor_val (h0 : ϖ ≠ 0) (a : Fin n → ℤ) :
    (tor h0 a : Matrix (Fin n) (Fin n) (P.adicCompletion E)) = Matrix.diagonal fun i => ϖ ^ a i := rfl

theorem tor_add (h0 : ϖ ≠ 0) (a b : Fin n → ℤ) : tor h0 (a + b) = tor h0 a * tor h0 b := by
  ext1
  simp [tor_val, Matrix.diagonal_mul_diagonal, zpow_add₀ h0]

theorem tor_const_comm (h0 : ϖ ≠ 0) (c : ℤ) (g : GL (Fin n) (P.adicCompletion E)) :
    tor h0 (fun _ => c) * g = g * tor h0 (fun _ => c) := by
  ext i j
  simp [tor_val, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem Tj_eq (h0 : ϖ ≠ 0) (j : ℕ) :
    Tj ℂ n (Ov E P) ϖ j = dosetInd ℂ (GLint (Fin n) (Ov E P)) (tor h0 fun i => if (i : ℕ) < j then 1 else 0) := by
  have e : diagJ n ϖ j = (tor h0 fun i : Fin n => if (i : ℕ) < j then 1 else 0 : GL _ _) := by
    rw [tor_val, diagJ]; congr 1; funext i; split_ifs <;> simp
  unfold Tj dosetInd
  congr 1
  ext g
  rw [mem_doset, e]
  simp only [Set.mem_setOf_eq, ← Units.val_mul, Units.val_inj]

theorem cartan (h0 : ϖ ≠ 0) (hu : IsUnifV E P ϖ) (g : GL (Fin n) (P.adicCompletion E)) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ c ∈ GLint (Fin n) (Ov E P), ∃ d ∈ GLint (Fin n) (Ov E P), g = c * tor h0 a * d := by
  have hm : ϖ ∈ Ov E P := by
    show Valued.v ϖ ≤ 1
    rw [hu]; exact le_of_lt (by decide)
  obtain ⟨a, ha, c, hc, d, hd, e⟩ := Final.CartanDecomp E P n ϖ hm hu g
  exact ⟨a, ha, c, hc, d, hd, Units.ext e⟩

def IntM (g : GL (Fin n) (P.adicCompletion E)) : Prop :=
  ∀ i j, (g : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j ∈ Ov E P

theorem IntM.mul {g h : GL (Fin n) (P.adicCompletion E)} (hg : IntM g) (hh : IntM h) : IntM (g * h) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hg i k) (hh k j)

theorem intM_of_mem {g : GL (Fin n) (P.adicCompletion E)} (hg : g ∈ GLint (Fin n) (Ov E P)) : IntM g := by
  obtain ⟨x, rfl⟩ := hg
  intro i j
  exact ((x : Matrix (Fin n) (Fin n) (Ov E P)) i j).2

theorem v_zpow (hu : IsUnifV E P ϖ) (m : ℤ) : ϖ ^ m ∈ Ov E P ↔ 0 ≤ m := by
  show Valued.v (ϖ ^ m) ≤ 1 ↔ _
  rw [map_zpow₀, hu]
  have h1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by decide
  exact zpow_le_one_iff_right_of_lt_one₀ (by decide) h1

theorem intM_tor (h0 : ϖ ≠ 0) (hu : IsUnifV E P ϖ) (a : Fin n → ℤ) : IntM (tor h0 a) ↔ ∀ i, 0 ≤ a i := by
  constructor
  · intro h i
    have := h i i
    rwa [tor_val, Matrix.diagonal_apply_eq, v_zpow hu] at this
  · intro h i j
    rw [tor_val, Matrix.diagonal_apply]
    split_ifs
    · exact (v_zpow hu _).2 (h i)
    · exact Subring.zero_mem _

theorem intM_doset {g x : GL (Fin n) (P.adicCompletion E)} (hg : IntM g)
    (hx : ∃ c ∈ GLint (Fin n) (Ov E P), ∃ d ∈ GLint (Fin n) (Ov E P), x = c * g * d) : IntM x := by
  obtain ⟨c, hc, d, hd, rfl⟩ := hx
  exact ((intM_of_mem hc).mul hg).mul (intM_of_mem hd)

theorem flip {g x : GL (Fin n) (P.adicCompletion E)} {M : Matrix (Fin n) (Fin n) (P.adicCompletion E)} (hg : (g : Matrix _ _ _) = M)
    (hx : ∃ c ∈ GLint (Fin n) (Ov E P), ∃ d ∈ GLint (Fin n) (Ov E P), x = c * g * d) :
    ∃ c ∈ GLint (Fin n) (intL (P.adicCompletion E)), ∃ d ∈ GLint (Fin n) (intL (P.adicCompletion E)),
      ((c * x * d : GL (Fin n) (P.adicCompletion E)) : Matrix _ _ _) = M := by
  have e : intL (P.adicCompletion E) = Ov E P := rfl
  rw [e]
  obtain ⟨c, hc, d, hd, rfl⟩ := hx
  refine ⟨c⁻¹, Subgroup.inv_mem _ hc, d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
  rw [← hg]; congr 1; group

theorem gen_nat (h0 : ϖ ≠ 0) (hu : IsUnifV E P ϖ) (A : Submodule ℂ (GL (Fin n) (P.adicCompletion E) → ℂ))
    (hT : ∀ j ≤ n, Tj ℂ n (Ov E P) ϖ j ∈ A)
    (hc : ∀ f ∈ A, ∀ f' ∈ A, conv (GLint (Fin n) (Ov E P)) f f' ∈ A) :
    ∀ (s q : ℕ) (d : Fin n → ℕ), Antitone d → ∑ i, d i = s → ∑ i, d i ^ 2 = q →
      dosetInd ℂ (GLint (Fin n) (Ov E P)) (tor h0 fun i => (d i : ℤ)) ∈ A := by
  have hK := Final.GLintComm E P n
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ihq =>
  intro d hd hs hq
  set k := (Finset.univ.filter fun i => 0 < d i).card with hk
  have hkn : k ≤ n := by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => 0 < d i
  have hdk : ∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k := fun i =>
    (Fin.lt_card_filter_univ_iff_apply_of_imp (fun i => 0 < d i) fun a b hab ha => lt_of_lt_of_le ha (hd hab)).symm
  have ha := hT k hkn
  rw [Tj_eq h0] at ha
  by_cases hz : ∀ i, d i = 0
  · convert ha using 3
    funext i
    have := hdk i
    rw [if_neg (by rw [← this, hz i]; simp), hz i]; rfl
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  have hlt : ∑ i, (d i - 1) < s := by
    rw [← hs]
    exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _) ⟨i₀, Finset.mem_univ _, by omega⟩
  have hg := ihs _ hlt _ (fun i => d i - 1) (fun a b hab => Nat.sub_le_sub_right (hd hab) 1) rfl rfl
  have hf := hc _ hg _ ha
  have e : (tor h0 fun i => (d i : ℤ)) = (tor h0 fun i => ((d i - 1 : ℕ) : ℤ)) *
      tor h0 fun i : Fin n => if (i : ℕ) < k then 1 else 0 := by
    rw [← tor_add]; congr 1; funext i
    have := hdk i
    simp only [Pi.add_apply]
    split_ifs <;> omega
  refine dosetInd_mem_of_top A (Final.HeckeConvMem _ _ ℂ hK _ (Final.DosetIndMem _ _ ℂ _) _ (Final.DosetIndMem _ _ ℂ _)) hf
    (by rw [e]; exact conv_top hK _ _) fun g hg => ?_
  obtain ⟨x, y, hx, hy, rfl⟩ := conv_supp hK hg
  obtain ⟨a, haa, hxy⟩ := cartan h0 hu (x * y)
  have hI : IntM (x * y) := (intM_doset ((intM_tor h0 hu _).2 fun i => by positivity) hx).mul
    (intM_doset ((intM_tor h0 hu _).2 fun i => by split_ifs <;> simp) hy)
  have ha0 : ∀ i, 0 ≤ a i := by
    obtain ⟨c, hc, c', hc', e'⟩ := hxy
    refine (intM_tor h0 hu a).1 (intM_doset hI ⟨c⁻¹, Subgroup.inv_mem _ hc, c'⁻¹, Subgroup.inv_mem _ hc', ?_⟩)
    rw [e']; group
  obtain ⟨d', rfl⟩ : ∃ d' : Fin n → ℕ, a = fun i => (d' i : ℤ) :=
    ⟨fun i => (a i).toNat, funext fun i => (Int.toNat_of_nonneg (ha0 i)).symm⟩
  have hd' : Antitone d' := fun a b hab => Int.ofNat_le.1 (haa hab)
  rcases GlobalTheory.T.elementaryDivisors_mul_minuscule_top_term (P.adicCompletion E) ϖ n hu d k hd hdk x y
    (flip (by simp [tor_val]) hx) (flip (by rw [tor_val]; congr 1; funext i; split_ifs <;> simp) hy) d' hd'
    (flip (by simp [tor_val]) hxy) with rfl | ⟨h1, h2⟩
  · exact Or.inl hxy
  · right
    rw [dosetInd_congr hxy]
    exact ihq _ (hq ▸ h2) d' hd' (h1.trans hs) rfl

end Gen

end GlobalTheory.WeylGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoAtEqZero
open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coAt (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
  -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
    (1 : GL (Fin (a + a')) (Fv F v)).1)

theorem coAt_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h : u.map (piW (t.comp σ)) = 0) : coAt G t u = 0 := by
  unfold coAt; rw [h]; simp

end GlobalTheory.LinBarAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem grp_similitude_herm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : grp G β), ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * herm G v β *
      (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β := by
  intro p _ G v β y
  obtain ⟨⟨u, s⟩, hy, _⟩ := y
  change (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β at hy
  have hV : ((toV G v β ⟨(u, s), hy, ‹_›⟩ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (u : G.C) := rfl
  rw [hV]
  change (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
    ((s : ℚ) : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C))
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hu : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u =
      algebraMap ℚ G.C (s : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (u * β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (u : G.C) * β * (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u)
        = ((u : G.C) * β * sh G (u : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) * u := by
          simp only [mul_assoc]
      _ = (s : ℚ) • ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
          rw [hy, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (s : ℚ) • ((u : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (u : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (u : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((s : ℚ) : ℚ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime]

def PLv (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := Projectivization ℂ (Fin G.n → ℂ)

theorem toV_injective (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) :
    Function.Injective (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) := by
  intro a b h
  have h' := congrArg (Matrix.toLin' (((toV G v β y)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ)) h
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h'

instance (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : MulAction (grp G β) (PLv G v β) where
  smul y l := Projectivization.map (Matrix.toLin' (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))
    (toV_injective G v β y) (l : Projectivization ℂ (Fin G.n → ℂ))
  one_smul l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = l
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply]
  mul_smul y y' l := by
    change Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.map _ _ (Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)))
    induction (l : Projectivization ℂ (Fin G.n → ℂ)) using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk, Projectivization.map_mk, Projectivization.map_mk]
      congr 1
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

abbrev Ys (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  LeftCosets ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') × PLv G v β

def cxF (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (a : Ys G v β x t hx Kf K') (y : grp G β) : ℂ :=
  if 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) then
    f ((LeftCosets.rep _ _ a.1).1⁻¹ * toAfF G β x t hx y * (LeftCosets.rep _ _ a.1).1) *
      f' ((LeftCosets.rep _ _ a.1).2⁻¹ * toP1 G β y * (LeftCosets.rep _ _ a.1).2) *
      wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
  else 0

end GlobalTheory.CxUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigPull

theorem pull_top_injective {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) (g : Y ⟶ X) (hg : Dense (Set.range g)) (B : LB X) (hB : B.IsLB) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨σ, rfl⟩ := (H0.bijective_ofSec_top (p := p) (B := B)).2 f
  by_contra hne
  have hσ : σ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hgen := (sec_ne_zero_iff σ).1 hσ
  obtain ⟨y, hy⟩ : ∃ y, g y ∈ nonzeroLocus σ := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := hg.inter_open_nonempty _ (nonzeroLocus σ).isOpen ⟨_, hgen⟩
    exact ⟨y, hy⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hB.cover.ge (trivial : g y ∈ (⊤ : X.Opens)))
  have hj : y ∈ (B.pull g).U (fun _ => i) := mem_pull.2 hi
  have e := H0.germ_pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top (fun _ => i) y trivial hj
    (H0.ofSec p ⊤ σ)
  rw [hf, map_zero] at e
  have hu : IsUnit ((g.stalkMap y).hom (H0.germ (p := p) (O := ⊤) i (g y) (show g y ∈ (⊤ : X.Opens) from trivial) hi (H0.ofSec p ⊤ σ))) :=
    IsUnit.map _ ((H0.germ_ofSec (p := p) (O := ⊤) _ _ (show g y ∈ (⊤ : X.Opens) from trivial) hi σ).symm ▸ (isUnit_ger_iff σ hi).2 hy)
  rw [← e] at hu
  exact not_isUnit_zero hu

theorem finite_H0_top {E : Type} [Field E] {Y : Scheme.{0}} (p : Y ⟶ Sp E) (B : LB Y) :
    letI := algebraΓOfHom p
    Module.Finite E (coh (twist (structureModule Y) B) 0) → Module.Finite E (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  intro h
  letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))
  haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  exact Module.Finite.equiv (((cohZeroTwistEquiv B).restrictScalars E).trans
    (LinearEquiv.ofBijective { H0.ofSec p ⊤ with
      map_smul' := fun c σ => (e c ▸ H0.ofSec_smul c σ :) } H0.bijective_ofSec_top))

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X →
    Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) →
    (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := by
  intro k _ X Y _ p g hp hd hg N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (g ≫ p)
  have hL : ∀ m, (lbPow (N.pull g) m).IsLB := fun m => isLB_lbPow (LB.isLB_pull hN.isLB g) m
  have hfin : ∀ m, Module.Finite k (coh (twist (structureModule Y) (lbPow (N.pull g) m)) 0) :=
    fun m => finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp (hL m)
  have hle : ∀ m, lbH0 k (lbPow N m) ≤ lbH0 k (lbPow (N.pull g) m) := by
    intro m
    have hB := isLB_lbPow hN.isLB m
    have hB' := LB.isLB_pull hB g
    have ec := (cls_eq_iff (hL m) hB').2 (lbIso_lbPow_pull hN.isLB g m)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (hL m) hB' ec, ← H0.finrank_top p, ← H0.finrank_top (g ≫ p)]
    haveI := finite_H0_top (g ≫ p) ((lbPow N m).pull g)
      (finite_coh_zero_twist_congr hB' (hL m) ec.symm (hfin m))
    exact LinearMap.finrank_le_finrank_of_injective (pull_top_injective p g hg _ hB)
  obtain ⟨D, hD, c, hc, hm⟩ := hN.growth
  exact ⟨LB.isLB_pull hN.isLB g, hfin, D, hd.trans hD, c, hc,
    hm.mono fun m h => h.trans (by exact_mod_cast hle m)⟩

end GlobalTheory.BigPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffine
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier


end GlobalTheory.Cartier
end
end
