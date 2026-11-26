module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstQuotientEqZeroIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.StepLiftG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LiftPQInv
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {r : ℕ}

theorem liftPQ (Z₁ Z₂ : M.Mat (r + 1)) (γ : IsoMbe Z₁.Z Z₂.Z) :
    ∃ P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
      (∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v)) ∧ P * Z₁.Z = Z₂.Z * Q ∧
      (∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) ∧
      (∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) := by
  classical
  have hsurj : ∀ j : Fin (r + 1), ∃ w : Fin (r + 1) → M.R,
      Submodule.Quotient.mk (p := headCols Z₂.Z) w = γ.1 (Submodule.Quotient.mk (Pi.single j 1)) ∧
      (j = Fin.last r → w = Pi.single (Fin.last r) 1) := by
    intro j
    by_cases hj : j = Fin.last r
    · subst hj
      refine ⟨Pi.single (Fin.last r) 1, ?_, fun _ => rfl⟩
      exact γ.2.2.symm
    · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk (Pi.single j 1)))
      exact ⟨w, hw, fun h => absurd h hj⟩
  choose p hp hpl using hsurj
  let P : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun i j => p j i
  have hP : ∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v) := by
    have key : γ.1.toLinearMap ∘ₗ (headCols Z₁.Z).mkQ = (headCols Z₂.Z).mkQ ∘ₗ P.mulVecLin := by
      apply LinearMap.pi_ext
      intro j x
      have h1 : (Pi.single j x : Fin (r + 1) → M.R) = x • Pi.single j 1 := by
        ext k; by_cases hk : k = j <;> simp [Pi.single_apply, hk]
      have h2 : P.mulVec (Pi.single j x) = x • p j := by
        ext i; simp [P, Matrix.mulVec_single, mul_comm]
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [h2, h1, Submodule.Quotient.mk_smul, map_smul, Submodule.Quotient.mk_smul, hp j]
    intro v
    exact LinearMap.congr_fun key v
  have ht : ∀ j, P.mulVec (fun i => Z₁.Z i j) -
      (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0) ∈ headCols Z₂.Z := by
    intro j
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hP]
    induction j using Fin.lastCases with
    | last =>
      have h := γ.2.1
      unfold bCls at h
      rw [if_pos rfl, h, sub_self]
    | cast a =>
      have hmem : (fun i => Z₁.Z i a.castSucc) ∈ headCols Z₁.Z := Submodule.subset_span ⟨a, rfl⟩
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero, if_neg (Fin.castSucc_ne_last a),
        Submodule.Quotient.mk_zero, sub_zero]
  have hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₂.Z i a.castSucc) =
      P.mulVec (fun i => Z₁.Z i j) - (if j = Fin.last r then (fun i => Z₂.Z i (Fin.last r)) else 0) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (ht j)
  choose c hc using hc
  refine ⟨P, Matrix.of fun k j => Fin.lastCases (if j = Fin.last r then (1 : M.R) else 0) (fun b => c j b) k,
    hP, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [show ∑ k, P i k * Z₁.Z k j = P.mulVec (fun i => Z₁.Z i j) i from rfl]
    rw [Fin.sum_univ_castSucc]
    simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
    have hcomm : ∑ x : Fin r, Z₂.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₂.Z i x.castSucc :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hcomm, h]
    by_cases hj : j = Fin.last r
    · subst hj
      simp
    · simp only [if_neg hj, Pi.zero_apply]
      ring
  · intro i
    simp [P, hpl _ rfl, Pi.single_apply]
  · intro j
    simp

theorem liftPQ_inv (Z₁ Z₂ : M.Mat (r + 1)) (γ : IsoMbe Z₁.Z Z₂.Z) (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hP : ∀ v, γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P.mulVec v))
    (hP' : ∀ v, γ.1.symm (Submodule.Quotient.mk v) = Submodule.Quotient.mk (P'.mulVec v))
    (hPe : ∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP'e : ∀ i, P' i (Fin.last r) = if i = Fin.last r then 1 else 0) :
    ∃ K : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R, (∀ j, K (Fin.last r) j = 0) ∧ (∀ i, K i (Fin.last r) = 0) ∧
      P' * P = 1 + Z₁.Z * K := by
  classical
  have hid : ∀ w : Fin (r + 1) → M.R, (P' * P).mulVec w - w ∈ headCols Z₁.Z := by
    intro w
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero,
      ← Matrix.mulVec_mulVec, ← hP', ← hP, LinearEquiv.symm_apply_apply]
  have hc : ∀ j, ∃ c : Fin r → M.R, ∑ a, c a • (fun i => Z₁.Z i a.castSucc) =
      (P' * P).mulVec (Pi.single j 1) - Pi.single j 1 :=
    fun j => (Submodule.mem_span_range_iff_exists_fun _).1 (hid _)
  choose c hc using hc
  refine ⟨Matrix.of fun k j => Fin.lastCases 0 (fun b => if j = Fin.last r then 0 else c j b) k, ?_, ?_, ?_⟩
  · intro j
    simp
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast b => simp
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.add_apply, Matrix.mul_apply (M := Z₁.Z), Fin.sum_univ_castSucc]
    simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
    by_cases hj : j = Fin.last r
    · subst hj
      simp only [if_pos rfl, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Matrix.mul_apply]
      simp [hPe, hP'e, Matrix.one_apply]
    · simp only [if_neg hj]
      have h := congrFun (hc j) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.mulVec_single,
        mul_one] at h
      have hcomm : ∑ x : Fin r, Z₁.Z i x.castSucc * c j x = ∑ x : Fin r, c j x * Z₁.Z i x.castSucc :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [hcomm, h, Matrix.one_apply, Pi.single_apply]
      simp [Matrix.col_apply]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjZzPlusConjEq
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section LiftM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem lift_cj_mem_R (hs : M.split = some g) (x : M.R) : M.L.cj (x : E) ∈ M.R := by
  obtain ⟨h1, h2, c, hc⟩ := comp_of_mem_R hs x.2
  refine mem_R_of hs _ ⟨_, h2⟩ ⟨_, h1⟩ (-c) ?_ ?_
  · rw [g.e_cj]; rfl
  · show (g.e (x : E)).2 - (g.e (x : E)).1 = (g.q : F) * ((-c : 𝒪[F]) : F)
    push_cast; linear_combination -hc

def sigR (hs : M.split = some g) : M.R →+* M.R where
  toFun x := ⟨M.L.cj x, lift_cj_mem_R hs x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

theorem sigR_coe (hs : M.split = some g) (x : M.R) : ((sigR hs x : M.R) : E) = M.L.cj (x : E) := rfl

theorem lift_eps_mem {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : (T - T') / (g.q : F) ∈ 𝒪[F] := by
  obtain ⟨c, hc⟩ := h
  rw [hc, pow_two, mul_assoc, mul_div_cancel_left₀ _ (q_ne g)]
  exact mul_mem g.q.2 c.2

def epsR (hs : M.split = some g) {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : M.R :=
  dgR hs ⟨_, lift_eps_mem h⟩

theorem firstProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) = ph1 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [firstProj_apply, cor, h]
  · simp [firstProj_apply, cor, h]

theorem secondProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) = -(ph2 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [secondProj_apply, cor, h]
  · simp [secondProj_apply, cor, h]

theorem secondProj_zzPlus_conj_eq (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := secondProj_zzPlus_conj hs Zh T T' a b

theorem lift_zsig (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (hG : GHyp M g T T' TT Zh Z Zσ) :
    Zσ.Z = -lstar (sigR hs) Z.Z + epsR hs hG.2.1 • liftE r := by
  have hZ : ∀ a b, ((Z.Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.1 a) b; simpa using this
  have hZσ : ∀ a b, ((Zσ.Z a b : M.R) : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.2.1 a) b; simpa using this
  have hq := q_ne g
  ext a b
  rw [eq_iff_ph (g := g)]
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, lstar_apply, Subring.coe_add,
    Subring.coe_neg, Subring.coe_mul, sigR_coe, hZ, hZσ, liftE, Matrix.of_apply, epsR, dgR_coe, map_add, map_neg,
    map_mul, firstProj_algebraMap, ph2_algebraMap_eq]
  constructor
  · rw [firstProj_zzPlus_conj hs, firstProj_conj_apply, secondProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring
  · rw [secondProj_zzPlus_conj_eq hs, secondProj_conj_apply, firstProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring

theorem lift_cancel (Z : M.Mat (r + 1)) (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (h : Z.Z * A = Z.Z * B) :
    A = B := by
  have h1 := congrArg (fun X => X.map M.R.subtype) h
  simp only [Matrix.map_mul] at h1
  have h2 : A.map M.R.subtype = B.map M.R.subtype := by
    rw [← Matrix.one_mul (A.map M.R.subtype), ← Matrix.nonsing_inv_mul _ Z.unit, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mul]
  ext i j
  exact congrFun (congrFun h2 i) j

end LiftM

section LiftK

variable {R : Type} [CommRing R] {r : ℕ}

end LiftK

def isoMbeSymm {R : Type} [CommRing R] {r : ℕ} {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (γ : IsoMbe Z₁ Z₂) :
    IsoMbe Z₂ Z₁ :=
  ⟨γ.1.symm, by rw [LinearEquiv.symm_apply_eq]; exact γ.2.1.symm,
    by rw [LinearEquiv.symm_apply_eq]; exact γ.2.2.symm⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem stepLiftG : StepLiftG := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ γ
  obtain ⟨P, Q, hP, hPQ, hPl, hQl⟩ := liftPQ Z₁ Z₂ γ
  obtain ⟨P₂, Q₂, hP₂, hPQ₂, hP₂l, hQ₂l⟩ := liftPQ Z₂ Z₁ (isoMbeSymm γ)
  obtain ⟨K, -, hKl, hK⟩ := liftPQ_inv Z₁ Z₂ γ P P₂ hP (fun v => hP₂ v) hPl hP₂l
  obtain ⟨K', -, hK'l, hK'⟩ := liftPQ_inv Z₂ Z₁ (isoMbeSymm γ) P₂ P hP₂ (fun v => hP v) hP₂l hPl
  obtain ⟨γ', hγ', hm⟩ := lift_partner (sigR hs) Z₁.Z Z₂.Z Zσ₁.Z Zσ₂.Z _ (lift_zsig hs h₁)
    (lift_zsig hs h₂) (lift_cancel Z₁) (lift_cancel Z₂) P Q P₂ Q₂ K K' hPQ hPQ₂ hK hK'
    hPl hP₂l hQl hQ₂l hKl hK'l
  refine ⟨P, Q, lstar (sigR hs) Q₂, γ', hP, hγ', hPQ, hPl, hQl, fun w => ?_⟩
  obtain ⟨m, hm0, hmw⟩ := hm w
  refine ⟨m, hm0, fun i => ?_⟩
  have hi := congrArg (fun x => ((x i : M.R) : E)) hmw
  simp only [Matrix.mulVec, dotProduct, lstar, Matrix.transpose_apply, Matrix.map_apply,
    Pi.add_apply] at hi ⊢
  push_cast at hi ⊢
  exact hi

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
