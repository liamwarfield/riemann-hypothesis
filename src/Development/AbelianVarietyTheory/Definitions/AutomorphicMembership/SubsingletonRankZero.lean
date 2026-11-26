module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr.CharModel

namespace GlobalTheory.CuspRep.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E) in
omit [_root_.NumberField.IsTotallyComplex E] in
def absC (s : ℂ) : HChar E := ⟨absHom E s, (absChar E s).2⟩

theorem logNorm_infId (u : (Cinf E)ˣ) : logNorm E (infId E u) = ∑ w, 2 * Real.log ‖(u : Cinf E) w‖ := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.finPart E (infId E u) = 1 := Units.ext (by
    change (1 : Af E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, logFin_one, sub_zero, logInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : ((infPart E (infId E u) : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) = infEq E u := by
    change (1 : InfiniteAdeleRing E) - infEq E 1 + infEq E u = _
    simp
  rw [h2, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]
  have h3 : ‖infEq E u w‖ = ‖(u : Cinf E) w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm) _
  rw [h3]; norm_num

theorem expo_absC (s : ℂ) (τ : E →+* ℂ) : expo (absC E s) τ = s := by
  classical
  refine expo_eq_of_exp _ τ s s fun z => ?_
  change Complex.exp (s * logNorm E (infId E (expU (atEmb τ z)))) = _
  rw [logNorm_infId, Finset.sum_eq_single (InfinitePlace.mk τ)]
  · change Complex.exp (s * ((2 * Real.log ‖Complex.exp (atEmb τ z _)‖ : ℝ) : ℂ)) = _
    rw [Complex.norm_exp, Real.log_exp, ← mul_add, Complex.add_conj]
    congr 3
    unfold atEmb
    split_ifs <;> simp
  · intro w _ hw
    change 2 * Real.log ‖Complex.exp (atEmb τ z w)‖ = 0
    simp [atEmb, hw]
  · simp

section CM

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

end CM

end GlobalTheory.CuspRep.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}

end GlobalTheory.IntPair

end
end
