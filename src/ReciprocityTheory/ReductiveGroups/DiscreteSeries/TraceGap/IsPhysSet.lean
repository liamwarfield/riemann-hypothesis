module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockWeights
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def physFock (ε : Fin n → Bool) : Submodule ℂ (Fock n) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmFock i a)

section
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def khwSub (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) : Submodule ℂ W :=
  (⨅ a, LinearMap.ker (F a a - ((γ a : ℝ) : ℂ) • (1 : Module.End ℂ W))) ⊓
    ⨅ a, ⨅ b, ⨅ (_ : a < b ∧ ε a = ε b), LinearMap.ker (F a b)
end

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.IsPhysSet
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def IsPhys (ε : Fin n → Bool) (x : Fin n × Fin n) : Prop := ε x.1 = true ∧ ε x.2 = false

instance (ε : Fin n → Bool) : DecidablePred (IsPhys ε) := fun x =>
  inferInstanceAs (Decidable (ε x.1 = true ∧ ε x.2 = false))

def adMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun x y =>
  if IsPhys ε x then (if IsPhys ε y then k x.1 y.1 * star (k x.2 y.2) else 0)
  else if x = y then 1 else 0

def adPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  Matrix.mulVecLin (adMat ε k)

def ff (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : Fock n →ₐ[ℂ] Fock n :=
  ExteriorAlgebra.map (adPhys ε k)

def cpV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v)

def dualV (v : Fin n × Fin n → ℂ) : Module.Dual ℂ (Fin n × Fin n → ℂ) :=
  ∑ x, star (v x) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) x

def cmV (v : Fin n × Fin n → ℂ) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (dualV v)

def ffMat (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (ff ε k).toLinearMap

def IsPhysSet (ε : Fin n → Bool) (S : Finset (Fin (n * n))) : Prop :=
  ∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)

instance (ε : Fin n → Bool) : DecidablePred (IsPhysSet ε) := fun S =>
  inferInstanceAs (Decidable (∀ m ∈ S, IsPhys ε (finProdFinEquiv.symm m)))

def strPhys (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ S ∈ univ.filter (IsPhysSet ε), (-1 : ℂ) ^ S.card * ffMat ε k S S

def physDet (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.det (fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
    (if x = y then 1 else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2))

def modeChar (ε : Fin n → Bool) (s : Fin n → ℂ) (x : Fin n × Fin n) : ℂ :=
  if IsPhys ε x then s x.1 * star (s x.2) else 1

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GsBasisPhys
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def sModes (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  univ.filter fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1

def sDeg (ε : Fin n → Bool) : ℕ := (sModes ε).card

def sIdx (ε : Fin n → Bool) : Finset (Fin (n * n)) := (sModes ε).map finProdFinEquiv.toEmbedding

theorem sIdx_eq (ε : Fin n → Bool) : sIdx ε = (lowerWedgeAlt ε).1 := by
  ext m
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  rw [mem_lowerWedge_iff]
  simp [sIdx, sModes]

theorem gs_basis_deg (S : Finset (Fin (n * n))) : fockBasis n S ∈ ⋀[ℂ]^S.card (Fin n × Fin n → ℂ) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  rw [hb]
  exact ExteriorAlgebra.ιMulti_range ℂ S.card ⟨_, rfl⟩

theorem sDeg_eq_sum (ε : Fin n → Bool) :
    (sDeg ε : ℝ) = ∑ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a := by
  have h1 : ∀ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a =
      ((univ.filter fun b => ε b = false ∧ b < a).card : ℝ) := by
    intro a ha
    rw [lf_rhoHol_sub_rhoN, if_pos (by simpa [plusIdx] using ha)]
  rw [Finset.sum_congr rfl h1]
  unfold sDeg sModes
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, plusIdx,
    Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ε i = true <;> simp [hi]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
