module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul {e : AE D} {l m n : ℕ} (M : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem isHalf_add {e : AE D} {m n : ℕ} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_resT_iff {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} (t : WO T S) :
    IsHalf e t ↔ IsHalf e (o.pA ⬝ t) ∧ IsHalf e (o.pB ⬝ t) := by
  refine ⟨fun h => ⟨isHalf_mul _ h, isHalf_mul _ h⟩, fun h => ?_⟩
  have := (o.resT T).symm_apply_apply t
  rw [← this, OrthDec.resT_symm_apply, OrthDec.resT_apply]
  exact isHalf_add (isHalf_mul _ h.1) (isHalf_mul _ h.2)

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_rat_pr {l m : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) : (rat M).map p.pr = M.map (p.pr.comp (incA D)) := by
  rw [rat, Matrix.map_map]; rfl

theorem sumFrame_b' {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (hs : IsSumFrame o ζ α α₀) :
    α₀.b' = fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) ((p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
        ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) := by
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  have hinj : Function.Injective ι := ι.injective
  set c := p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hζ.2
    apply hinj
    rw [map_zero]; exact h
  set M := fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) (c⁻¹ • ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) with hM
  have hcol : (fun i => p.pr (ratV (vecB o ζ) i)) = o.iB.map ι *ᵥ fun j => ι (ζ j) := by
    funext i
    simp only [ratV, vecB]
    exact (RingHom.map_mulVec ι o.iB ζ i)
  have hpA : o.pA.map p.pr = o.qA.map ι := map_rat_pr _
  have hpB : o.pB.map p.pr = o.qB.map ι := map_rat_pr _
  have hjA : o.jA.map p.pr = o.iA.map ι := map_rat_pr _
  have key : M * α₀.b = 1 := by
    rw [hs, hM, Matrix.fromRows_mul, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks,
      ← Matrix.fromBlocks_one]
    have eA : o.qA.map ι * o.iA.map ι = 1 := by rw [← Matrix.map_mul, o.qA_iA]; simp
    have eAB : o.qA.map ι * o.iB.map ι = 0 := by rw [← Matrix.map_mul, o.qA_iB]; simp
    have eBA : o.qB.map ι * o.iA.map ι = 0 := by rw [← Matrix.map_mul, o.qB_iA]; simp
    have eB : o.qB.map ι * o.iB.map ι = 1 := by rw [← Matrix.map_mul, o.qB_iB]; simp
    have hu : (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) = fun j => ι ((star ζ ᵥ* L.gram) j) := rfl
    have hdot : (fun j => ι ((star ζ ᵥ* L.gram) j)) ⬝ᵥ (fun j => ι (ζ j)) = c := by
      rw [hc, Matrix.dotProduct_mulVec, ← RingHom.comp_apply, ← hι, RingHom.map_dotProduct]; rfl
    rw [hcol, hpA, hpB, hjA, hu, ← Matrix.smul_vecMul, Matrix.replicateRow_vecMul, Matrix.replicateCol_mulVec]
    congr 1
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eA, Matrix.one_mul, α.b'b]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eAB, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eBA, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eB, Matrix.one_mul, Matrix.replicateRow_mul_replicateCol]
      ext i j
      simp only [Matrix.of_apply, smul_dotProduct, hdot, smul_eq_mul, inv_mul_cancel₀ hc0]
      fin_cases i; fin_cases j; simp
  calc α₀.b' = (M * α₀.b) * α₀.b' := by rw [key, Matrix.one_mul]
    _ = M := by rw [Matrix.mul_assoc, α₀.bb', Matrix.mul_one]

theorem rd_sumFrame {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO T S) :
    rd β α₀ t = fromRows (rd β α (o.pA ⬝ t)) (replicateRow (Fin 1) (zrow β ζ (o.pB ⬝ t))) := by
  rw [rd, sumFrame_b' o ζ hζ α α₀ hs, Matrix.fromRows_mul, Matrix.fromRows_mul]
  congr 1
  · rw [rd, Matrix.map_mul, Matrix.mul_assoc α.b']
  · rw [← Matrix.replicateRow_vecMul, ← Matrix.replicateRow_vecMul]
    congr 1
    have hv : (fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* (o.pB ⬝ t)) i)) =
        (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* (o.pB ⬝ t).map p.pr := by
      funext i; exact RingHom.map_vecMul p.pr _ _ i
    rw [zrow, hv, Matrix.map_mul]
    simp only [Matrix.smul_vecMul, Matrix.vecMul_vecMul]

theorem extFun_tensRow (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ) (α : Frame p A n')
    (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (Ψ : Matrix n' n k → ℂ)
    (b : (n → k) → ℂ) :
    extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  funext t
  simp only [OrthDec.boxT, extFun, rowFun]
  rw [OrthDec.resT_apply]
  by_cases h : IsHalf p.e t
  · have h' := (isHalf_resT_iff o t).1 h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, rd_sumFrame o ζ hζ α α₀ β hs t]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.pA ⬝ t)
    · rw [if_neg fun hB => h ((isHalf_resT_iff o t).2 ⟨hA, hB⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end Frames

end GlobalTheory.FinPl.ExtZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_target_tensor_row_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSource
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSource
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) : MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_conjHalf {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {x y : WO S T}
    (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y) : symplO S T x y = 0 := by
  have h0 : cA D e * cA D (cA D e) = 0 := (GlobalTheory.SplitScalar.isSplitIdem_conj he).2.1
  have : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D (cA D e) * cA D (y c b)) * incA D (T.gram c d) * (cA D e * x d a)
        = (cA D e * cA D (cA D e)) * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  rw [symplO, this, mul_zero, map_zero]

theorem symplO_resS_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T) (t : WO S T) :
    symplO S T ((o.resS T).symm (a, 0)) t = symplO A T a (t ⬝ o.jA) := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  have h0 : symplO L T 0 ((o.resS T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

theorem smul_isHalf {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem finPart_idem_mem {e : AE D} (he : e * e = e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO A T (LA : Set _) (LT : Set _) (· = p.v) with hΛA
  set ΛS := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hcol0 : GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zcol β ζ (0 : WO L T) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zcol, Matrix.zero_mulVec, Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero _
    have h0 : IsHalf p.e (0 : WO L T) := fun i j => by simp
    simp [GlobalTheory.FinPl.ExtZero.colFun, hz, vecInd, h0]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resS T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resS T).symm (a, 0))
    rw [OrthDec.boxS, AddEquiv.apply_symm_apply, hcol0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → t ⬝ o.jA ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxS] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resS T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D A T _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resS T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resS T).symm (u, 0)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
    exact mxAt_mul huM _
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resS_symm_left, ← hsplit u' hu'M, Matrix.add_mul, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO A T u ((p.e • u') ⬝ o.jA)) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO A T u ((cA D p.e • u') ⬝ o.jA)) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO A T (cA D p.e • u) ((cA D p.e • u') ⬝ o.jA) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, (smul_isHalf hce.1 u') i l]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resS_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_mem_completed_lattice_source : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.ExtZero.extZero_mem_latO | exact GlobalTheory.FinPl.ExtZero.extZero_mem_latO | (intros; apply GlobalTheory.FinPl.ExtZero.extZero_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowLev

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem e_left (k : X.B.I.Gf) (hk : k ∈ X.K2) (y : X.B.I.Gf) : X.B.e y = X.chi2 k * X.B.e (k * y) := by
  obtain ⟨-, hKm, hKi, hχm, hχn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2 := fun z => Iff.rfl
  rw [X.e_eq y, X.e_eq (k * y)]
  by_cases hy : y ∈ X.K2
  · have hky : k * y ∈ X.K2 := hKm k hk y hy
    rw [if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]
    change star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)
    rw [hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]
    have h1 : X.chi2 k * star (X.chi2 k) = 1 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]; simp
    rw [h1, one_mul]
  · have hky : k * y ∉ X.K2 := fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')
    rw [if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]

theorem R_comp_Re (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B
  obtain ⟨-, hT⟩ := X.B.Re_spec
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul,
    ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]
  congr 1
  funext h
  have e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ := by
    rw [← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]
    rfl
  show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)
  rw [e1, e_left X k hk h, mul_assoc]

end GlobalTheory.ConjRowLev

namespace GlobalTheory.ConjRowMult


open GlobalTheory.ConjRowLev in
theorem conjMap_lev : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  intro _ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g
  obtain ⟨-, hCL⟩ := hM
  obtain ⟨hJ, hχ⟩ := hCL k
  have hk0 := hJ.1 hk
  obtain ⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hk0
  set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'
  have hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹) := by group
  have hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA) := by
    rw [hsplit, map_mul]
    congr 1
    exact Prod.ext h1 rfl
  obtain ⟨ψ, hψ⟩ := hrep u
  have hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u)) := by
    obtain ⟨T0, -, rfl⟩ := hΦ
    have := congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)
    simpa using this
  have a := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)
  rw [hR] at a
  have key := congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))
  rw [conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]
  rfl

end GlobalTheory.ConjRowMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_evaluation_map_has_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  first | exact @GlobalTheory.ConjRowMult.conjMap_lev | exact GlobalTheory.ConjRowMult.conjMap_lev | (intros; apply GlobalTheory.ConjRowMult.conjMap_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SeeOnto

theorem see_onto : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  intro hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hM hCV φ hφ
  obtain ⟨c, hc, hv₀⟩ := hCV
  have hL := (GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuous_leftInvariant_rep_conjugateTensor hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ
  have hmult : GlobalTheory.ConjRowMult.conjMap X M c Φ h t ∈ Mult θ M J χ :=
    Submodule.subset_span
      ⟨GlobalTheory.T.conjugateIntertwiner_values_smoothAutomorphic hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugateIntertwiner_values_isCuspFun hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugate_evaluation_map_has_level hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       fun τ g hg v w hw => GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ g hg v w hw,
       fun τ v x => GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ v x⟩
  refine ⟨PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t), (mem_multT θ M J χ _).2 (by simpa using hmult), ?_⟩
  have hw : GlobalTheory.ConjRowMult.vecC X M c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X M c v₀ X.B.w hv₀
  obtain ⟨ψ, hψ⟩ := hrep v₀
  rw [hw, hΦw] at hψ
  have key : ∀ x, evS X h t (PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) (PiTensorProduct.tprod ℂ v₀)) x = star (ψ x) := by
    intro x
    rw [evS, PiTensorProduct.lift.tprod]
    refine (GlobalTheory.ConjRowMult.conjMap_apply X M c Φ h t v₀ _).trans ?_
    rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
    erw [e, ContinuousMulEquiv.apply_symm_apply]
  filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
  rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Core.SeeOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  first | exact @GlobalTheory.Core.SeeOnto.see_onto | exact GlobalTheory.Core.SeeOnto.see_onto | (intros; apply GlobalTheory.Core.SeeOnto.see_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DenseRel

variable {D : D7}

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

section Sep

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sepCont_zero : GlobalTheory.Core.Mi.SepCont M 0 := fun τ _ => ⟨0, sobCont_zero _ _, fun _ => by simp⟩

theorem sepCont_add {Λ Λ' : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) (h' : GlobalTheory.Core.Mi.SepCont M Λ') :
    GlobalTheory.Core.Mi.SepCont M (Λ + Λ') := fun τ v => by
  obtain ⟨ℓ, hℓ, e⟩ := h τ v
  obtain ⟨ℓ', hℓ', e'⟩ := h' τ v
  exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp [e, e']⟩

theorem sepCont_smul (a : ℂ) {Λ : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) : GlobalTheory.Core.Mi.SepCont M (a • Λ) :=
  fun τ v => by
    obtain ⟨ℓ, hℓ, e⟩ := h τ v
    exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by simp [e]⟩

theorem sepCont_sum {ι : Type} (s : Finset ι) (Λ : ι → SmT M →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, GlobalTheory.Core.Mi.SepCont M (Λ i)) :
    GlobalTheory.Core.Mi.SepCont M (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (GlobalTheory.Core.Mi.SepCont M) (fun _ _ => sepCont_add M) (sepCont_zero M) h

theorem kill_of_itSpans {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hS : GlobalTheory.Core.Mi.ItSpans M M' It) (Λ : SmT M →ₗ[ℂ] ℂ)
    (h : ∀ P (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y → Λ (It P (PiTensorProduct.tprod ℂ y)) = 0) :
    ∀ v : M.Vec, GlobalTheory.Core.Mi.KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  intro v hv
  have hle : Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧
      x = It P (PiTensorProduct.tprod ℂ y)} ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro x ⟨P, y, hy, rfl⟩
    exact h P y hy
  exact hle (hS v hv)

end Sep

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.SeeSaw.DenseRel


open GlobalTheory.SeeSaw.DenseRel in
theorem GlobalTheory.SeeSaw.perF_rel_of_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  intro hHC D c 𝒯 t hc j ρ h I _ s α φ G ht hφ _W W' S' M' It' hS' hrel
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega

  have hmult : ∀ i, ∃ J χ, (G i).1 ∈ MultT c.θ (c.M j) J χ := fun i => by
    obtain ⟨J, χ, hle⟩ := (ht (s i)).CC j hj
    exact ⟨J, χ, hle (G i).2⟩
  choose J χ hG using hmult
  have hcont : ∀ i x, IsContAut (c.V j) ((G i).1 x) := fun i x => isContAut_multT (hG i) x

  have hL : ∀ (i : I) (a : (t (s i)).Ch j) (g : GA D (c.V j)), ∃ Λ : SmT (c.M j) →ₗ[ℂ] ℂ, GlobalTheory.Core.Mi.SepCont (c.M j) Λ ∧
      ∀ x, Λ x = (c.B j ρ h).per c.ψ (φ i a) (rTrans g ((G i).1 x)) := fun i a g =>
    GlobalTheory.T.besselPeriod_rightTranslate_sobolevSepContinuous D c.θ c.ψ ρ (c.B j ρ h) (c.par j) (c.M j) (J i) (χ i) g (φ i a) hc.inf hc.std (hφ i a) (G i).1 (hG i)
  choose L hLs hLe using hL
  let Λ : SmT (c.M j) →ₗ[ℂ] ℂ :=
    ∑ i, α i • ∑ a, ∑ g ∈ ((t (s i)).e j a).support, ((t (s i)).e j a g) • L i a g
  have hΛ : ∀ x, Λ x = ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 x) := by
    intro x
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hLe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold Tup.perF
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B j ρ h) (φ i a) (hφ i a)).2 _ _ (hcont i x)).2]
  have hΛs : GlobalTheory.Core.Mi.SepCont (c.M j) Λ :=
    sepCont_sum _ _ _ fun i _ => sepCont_smul _ _ (sepCont_sum _ _ _ fun a _ =>
      sepCont_sum _ _ _ fun g _ => sepCont_smul _ _ (hLs i a g))
  have hK : ∀ v : (c.M j).Vec, GlobalTheory.Core.Mi.KVecP (c.M j) v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
    refine kill_of_itSpans (c.M j) (c.M (j + 1)) (c.It j) (hc.span j hj1) Λ fun P y hy => ?_
    exact kill_of_itSpans (c.M (j + 1)) M' It' hS' (Λ ∘ₗ c.It j P)
      (fun P₂ z _ => by simp only [LinearMap.comp_apply, hΛ]; exact hrel P P₂ _) y hy
  have h0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D (c.V j) (c.par j) (c.M j) Λ hΛs hK
  intro v
  rw [← hΛ v, h0, LinearMap.zero_apply]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingStepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_linear_relation_density_of_unfolding_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  first | exact @GlobalTheory.SeeSaw.perF_rel_of_steps | exact GlobalTheory.SeeSaw.perF_rel_of_steps | (intros; apply GlobalTheory.SeeSaw.perF_rel_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

theorem cA_algebraMap_place (D : D7) (ε : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show sigR _ _ _ = _
  simp [sigR]

theorem placeIdem_mul {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) ε * a = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α = singleFin v 1 := FiniteAdeleRing.ext _ fun u => by
    change evalV D.host.F u α = evalV D.host.F u (singleFin v 1)
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, h1]
    · rw [evalV_singleFin_ne e, h0 u e]
  have h2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hα, Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul]
    rfl
  rw [h2, GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem pair_mem_intL (S : HSp D) {s : Fin S.rank → D.host.E} (hs : s ∈ L0c D S)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w (frameLat S)) :
    ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * z m ∈
      Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum]
    have hX : ∑ k, s k • S.frame k ∈ S.L0 := hs
    have hY : ∑ m, y m • S.frame m ∈ S.L0 := (mem_frameLat S y).1 hy
    have hd : ∑ m, y m • S.frame m ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by rw [S.baseLattice_isUnimodular]; exact hY
    have h1 := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hd (∑ k, s k • S.frame k)) hX
    rw [Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    have e : ∑ m, (∑ k, star (s k) * S.gram k m) * y m = algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [ho]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.restrictScalars_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [starRingEnd_apply, RingHom.id_apply]
      ring
    rw [e]
    rw [GlobalTheory.InertLoc.mem_intL, GlobalTheory.Idele.valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one w o
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * (c • x) m =
        (c : w.adicCompletion D.host.E) * ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * x m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Pi.smul_apply]
      show _ * ((c : w.adicCompletion D.host.E) * x m) = _
      ring
    rw [e]
    exact mul_mem (show Valued.v (c : w.adicCompletion D.host.E) ≤ 1 from c.2) hx

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    secW hw h (piW hw h a) = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a))) = _
  rw [RingEquiv.symm_apply_apply]

theorem piW_tmul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (m : D.host.E) : piW hw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      complMap h (evalV D.host.F v α) * algebraMap D.host.E (w.adicCompletion D.host.E) m := rfl

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem latO_frame_int (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
    {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)} (hk : GlobalTheory.InertLoc.IsGen D w k)
    (haS : IsFrameAt w (frameLat S) aS) (haT : IsFrameAt w (frameLat T) aT) {u : WO S T}
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1)) i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hu using AddSubgroup.closure_induction generalizing i j with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hx
    let c0 := complMap h (evalV D.host.F v α)
    let t' : Fin T.rank → w.adicCompletion D.host.E := fun l => algebraMap D.host.E _ (t l)
    let r : Fin S.rank → w.adicCompletion D.host.E :=
      fun m => algebraMap D.host.E _ (∑ l, star (s l) * S.gram l m)
    have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T) (piW hw h) = (c0 * algebraMap D.host.E _ a) • vecMulVec t' r := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, piW_tmul, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        map_mul, map_mul]
      simp only [mul_assoc]
      rfl
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, smul_smul, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    have h1 : c0 ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := complMap_mem h (hα v)
    have h2 : k⁻¹ * algebraMap D.host.E _ a ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := hk.2.2 a ha
    have h3 : ((aT⁻¹).1 *ᵥ t') i ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      refine (haT ((aT⁻¹).1 *ᵥ t')).2 ?_ i
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, (mem_frameLat T t).2 ht, rfl⟩
    have h4 : (r ᵥ* aS.1) j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      have hcol : (fun m => aS.1 m j) ∈ latAt w (frameLat S) := by
        have := (haS (Pi.single j 1)).1 fun l => by
          by_cases e : l = j
          · subst e; simp
          · simp [e]
        rwa [Matrix.mulVec_single_one] at this
      show ∑ m, r m * aS.1 m j ∈ _
      exact pair_mem_intL S hs hcol
    have e2 : k⁻¹ * (c0 * algebraMap D.host.E (w.adicCompletion D.host.E) a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) =
        c0 * (k⁻¹ * algebraMap D.host.E _ a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) := by ring
    rw [e2]
    exact mul_mem (mul_mem h1 h2) (mul_mem h3 h4)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem exists_uPt_of_half : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  intro D v w hw h S T k aS aT hk haS haT e e' he u hu hhalf
  obtain ⟨ε, hε, -, -, hee⟩ := GlobalTheory.VacFixInert.inert_data (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h)
  obtain ⟨rfl, -⟩ := hee e e' he
  rw [h] at hε
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h1 | h1
    · exact h1
    · rwa [cA_algebraMap_place] at h1
  have hent : ∀ i j, secW hw h (piW hw h (u i j)) = u i j := fun i j => by
    rw [secW_piW, ← placeIdem_mul hε, hh i j]
  refine ⟨k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1), fun i j => latO_frame_int hw h hk haS haT hu i j, ?_⟩
  have e1 : k • ((aT.1 * (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1))) * (aS⁻¹).1) = u.map (piW hw h) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk.1, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply, Matrix.map_apply, hent]

end GlobalTheory.InertFrameLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePointStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  first | exact @GlobalTheory.InertFrameLoc.exists_uPt_of_half | exact GlobalTheory.InertFrameLoc.exists_uPt_of_half | (intros; apply GlobalTheory.InertFrameLoc.exists_uPt_of_half <;> assumption)
end
end
end
