module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {f f' : G → ℂ} {x : V}

theorem hAct_orbit (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) (x : V) (g : G) :
    hAct K f (fun y => ρ y x) g = ρ g (heckeVec ρ K f x) := by
  refine Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))
  simp

theorem orbit_mem_amf (hx : x ∈ fixed ρ K) :
    (fun y => ρ y x) ∈ AMF ℂ ⊥ K (Representation.trivial ℂ (⊥ : Subgroup G) V) := by
  intro γ g κ
  have : (γ : G) = 1 := Subgroup.mem_bot.1 γ.2
  simp [this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]

theorem heckeVec_mem_fixed (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K f x ∈ fixed ρ K := by
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
  have := Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩
  simpa [hAct_orbit hK hf] using this

theorem heckeVec_conv (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f f') x = heckeVec ρ K f (heckeVec ρ K f' x) := by
  have := congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1
  rw [funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf,
    hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')] at this
  simpa using this

theorem heckeVec_one (hK : IsCommensurated K) (hx : x ∈ fixed ρ K) : heckeVec ρ K (dosetInd ℂ K 1) x = x := by
  have := congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1
  rw [hAct_orbit hK (Final.DosetIndMem G K ℂ 1)] at this
  simpa using this

theorem heckeVec_add_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (x : V) :
    heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  unfold heckeVec
  rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K (c • f) x = c • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum' c (finite_heckeVec hK hf ρ x)]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_zero_left (x : V) : heckeVec ρ K 0 x = 0 := by simp [heckeVec]

def heckeLin (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ K f
  map_add' x y := by
    unfold heckeVec
    rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf ρ y)]
    exact finsum_congr fun c => by simp
  map_smul' c x := (map_heckeVec hK hf (c • LinearMap.id) (fun g y => by simp) x).symm

@[simp] theorem heckeLin_apply (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (x : V) :
    heckeLin hK hf ρ x = heckeVec ρ K f x := rfl

theorem heckeVec_smul (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K f (c • x) = c • heckeVec ρ K f x := (heckeLin hK hf ρ).map_smul c x

end GlobalTheory.LFun.SatCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp TensorProduct
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsUnram (ν : ℚ_[g]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, ν (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1

def MapsToProd {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W') : Prop :=
  n = a + b ∧ ∃ (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W'), IsUnram ν₁ ∧ IsUnram ν₂ ∧ Λ ≠ 0 ∧
    ∀ (p : GL (Fin n) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) →
    (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j) →
    (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      TensorProduct.map (σ x) (ρ y) (Λ v)

abbrev GLRep (g : ℕ) [Fact g.Prime] : Type 1 := Σ n : ℕ, Rep.{0} ℂ (GL (Fin n) ℚ_[g])

inductive InInd : GLRep g → List (GLRep g) → Prop
  | nil (π : GLRep g) : π.1 = 0 → IsIrrRep π.2.ρ → InInd π []
  | cons (π σ ρ : GLRep g) (S : List (GLRep g)) : IsIrrRep π.2.ρ → IsIrrRep ρ.2.ρ → InInd σ S →
      MapsToProd π.2.ρ σ.2.ρ ρ.2.ρ → InInd π (ρ :: S)

end GlobalTheory.GLp.Supp
end
end
