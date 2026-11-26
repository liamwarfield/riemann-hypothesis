module

public import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdFstEqProductLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

private theorem fmFst_loc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c a a' d : ℕ) (hr : a + a' = d) (M : Matrix (Fin d) (Fin a) k) :
    GlobalTheory.StdPairCone.stdA ν ϖ c a a' ((Mᵀ).submatrix id (finCongr hr)) =
      if (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (topL a M).det else 0 := by
  subst hr
  have hb : GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) = (topL a M)ᵀ := by
    ext i j
    have : j.1 < a + a' ∧ i.1 < a := ⟨by omega, i.2⟩
    simp only [GlobalTheory.StdPairCone.blk₁, topL, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, dif_pos this]
    rfl
  have hb2 : ∀ i j, GlobalTheory.StdPairCone.blk₂ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.natAdd a j) i :=
    fun i j => rfl
  have hb1 : ∀ i j, GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.castAdd a' j) i :=
    fun i j => rfl
  have hd : (GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a')))).det = (topL a M).det := by
    rw [hb, Matrix.det_transpose]
  have hsub : ∀ x, x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) → x ∈ (ValuativeRel.valuation k).integer := by
    intro x hx
    have h1 : ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) := hx
    have h2 : ((ϖ ^ c : kˣ) : k) ∈ (ValuativeRel.valuation k).integer := by
      rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    exact (Valuation.mem_integer_iff _ _).2 (le_trans h1 ((Valuation.mem_integer_iff _ _).1 h2))
  unfold GlobalTheory.StdPairCone.stdA GlobalTheory.StdPairCone.unitInd GlobalTheory.StdPairCone.IsGLO
  simp only [hb1, hb2]
  by_cases h : (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos h]
    by_cases h' : (topL a M).det ≠ 0 ∧ ValuativeRel.valuation k (topL a M).det = 1
    · rw [dif_pos h', dif_pos ⟨hd ▸ h'.1, ⟨fun i j => h.1 _ _, hd ▸ h'.2⟩, fun i j => h.2 _ _ (by simp)⟩]
      simp only [hd]
    · rw [dite_eq_right h', dite_eq_right]
      rintro ⟨h1, ⟨-, h2⟩, -⟩
      exact h' ⟨hd ▸ h1, hd ▸ h2⟩
  · rw [if_neg h, dite_eq_right]
    rintro ⟨-, ⟨h1, -⟩, h2⟩
    refine h ⟨fun i j => ?_, fun i j => ?_⟩
    · induction i using Fin.addCases with
      | left i => exact h1 j i
      | right i => exact hsub _ (h2 j i)
    · induction i using Fin.addCases with
      | left i => intro hi; exact absurd i.2 (not_lt.2 hi)
      | right i => exact fun _ => h2 j i

theorem UpperTheory.exists_gl_stdFst_eq_product_local :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (A WW : HSp D) (a' : ℕ) (hr : A.rank + a' = WW.rank)
          (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (m : ∀ v : P, GL (Fin (A.rank + a')) (Fv D.host.F v)),
        (∀ v, (m v).1 = (βW.1.map (piF (t v))).submatrix (finCongr hr) (finCongr hr)) →
        ∃ g : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v), ∀ x : WO A WW,
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e₀ (∏ w ∈ S, w.asIdeal ^ c w) A WW βA βW x =
            if IsHalf e₀ x then ∏ v : P, GlobalTheory.StdPairCone.stdA (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) A.rank a'
              ((g v).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (t v)) * (GlobalTheory.SplitFlip.invT (m v)).1) else 0 := by
  intro D e₀ S hS P t hP ht ν c A WW a' hr βA βW m hm
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (t v)) * (G.map (incA D)).map (piW (t v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : ∀ v : P, IsUnit ((G.map (incA D)).map (piW (t v)) * βA.1.map (piF (t v)))ᵀ := fun v => by
    rw [Matrix.isUnit_transpose]
    refine IsUnit.mul (IsUnit.of_mul_eq_one_right _ (hGi v)) ?_
    refine IsUnit.of_mul_eq_one ((βA⁻¹).1.map (piF (t v))) ?_
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun v => (hu v).unit, fun x => ?_⟩
  have key : ∀ v : P, ((hu v).unit).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (t v)) * (GlobalTheory.SplitFlip.invT (m v)).1 =
      (((frMapO A WW βA βW x).map (piF (t v)))ᵀ).submatrix id (finCongr hr) := fun v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (t v)) =
        ((Matrix.map x (piW (t v)) * (G⁻¹.map (incA D)).map (piW (t v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW βA βW x).map (piF (t v)) =
        (βW⁻¹).1.map (piF (t v)) * Matrix.map x (piW (t v)) * βA.1.map (piF (t v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact piF_toEAf (t v) (x i j)
    rw [← hG, IsUnit.unit_spec, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (βW.1.map (piF (t v))) _ ?_ (m v) (hm v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hϖ : ∀ v : P, GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := fun v => (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  simp only [key, fmFst_loc _ _ (hϖ _)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hx : IsHalf e₀ x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  have hN : ∀ i j, toEAf D e₀ * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j := by
    have h1 : toEAf D e₀ • Matrix.map x (toEAf D) = Matrix.map x (toEAf D) := by
      ext i j
      show toEAf D e₀ * toEAf D (x i j) = toEAf D (x i j)
      rw [← map_mul, hx i j]
    have h2 : toEAf D e₀ • frMapO A WW βA βW x = frMapO A WW βA βW x := by
      unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, h1]
    exact fun i j => congrFun (congrFun h2 i) j
  generalize frMapO A WW βA βW x = N at hN
  have hI := fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)
  by_cases h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)
  · rw [if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ (topL A.rank N)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩]
      congr 2
      refine Matrix.ext fun i j => ?_
      simp only [topL, Matrix.map_apply]
      split_ifs
      · rfl
      · exact map_zero _
    · intro i j
      simp only [topL]
      split_ifs
      · exact h.1 _ _
      · exact zero_mem _
  · rw [if_neg fun h' => h h'.2]
    by_contra hne
    have hv := fun v : P => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)
    have hv' := fun v : P => (ite_ne_right_iff.1 (hv v)).1
    exact h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdSndEqProductLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem stdB_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) (c a a' : ℕ)
    (Y : Matrix (Fin a') (Fin (a + a')) k) :
    GlobalTheory.StdPairCone.stdB ν ϖ c a a' Y =
      if (∀ i j, Y i j ∈ (ValuativeRel.valuation k).integer) ∧
          ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (GlobalTheory.StdPairCone.blk₂ Y).det else 0 := by
  unfold GlobalTheory.StdPairCone.stdB GlobalTheory.StdPairCone.unitInd
  by_cases h : (∀ i j, Y i j ∈ (ValuativeRel.valuation k).integer) ∧
          ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos h]
    by_cases h2 : (GlobalTheory.StdPairCone.blk₂ Y).det ≠ 0 ∧ ValuativeRel.valuation k (GlobalTheory.StdPairCone.blk₂ Y).det = 1
    · rw [dite_eq_left h2, dite_eq_left ⟨h2.1, ⟨fun i j => h.1 _ _, h2.2⟩, h.2⟩]
    · rw [dite_eq_right h2, dite_eq_right fun h3 => h2 ⟨h3.1, h3.2.1.2⟩]
  · rw [if_neg h, dite_eq_right]
    rintro ⟨-, h1, h2⟩
    refine h ⟨fun i j => ?_, h2⟩
    refine Fin.addCases (fun j => ?_) (fun j => h1.1 i j) j
    have h3 : ValuativeRel.valuation k (Y i (Fin.castAdd a' j)) ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) := h2 i j
    refine (Valuation.mem_integer_iff _ _).2 (h3.trans ?_)
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' hϖ c

private theorem piW_cA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) :
    piW t (cA D w) = piW (t.comp D.sp.cm.sig) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem piW_incA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (e : D.host.E) : piW t (incA D e) = t e := by
  change GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e
  simp

private theorem coord_eq {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (A' WW : HSp D) {d : ℕ} (e : Fin d ≃ Fin WW.rank)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) :
    (βA'⁻¹).1.map (piF t) * (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ * (βW.1.map (piF t)).submatrix e e =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF t)).submatrix id e := by
  have hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.DualPairCheck.gram_star A' j i
  have h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (congrFun hG i) j
    change piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)
    rw [piW_incA', ← h]
    rfl
  have h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) =
      ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e := by
    rw [← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]
    rfl
  have h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e := by
    refine Matrix.ext fun i j => ?_
    simp
  have hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E),
      ((M.map (incA D)).map (toEAf D)).map (piF t) = M.map t := by
    intro p q M
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, piF_toEAf, piW_incA']
  have hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (piF t) =
      ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.transpose_apply, piF_toEAf, piW_cA']
  have hxi : piF t (eToEAf D D.host.xi0) = t D.host.xi0 := by
    rw [← piW_incA' t, ← piF_toEAf]
    rfl
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF t) =
      t D.host.xi0 • ((βA'⁻¹).1.map (piF t) * ((A'.gram⁻¹).map t *
        ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (piF t)) := by
    rw [← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul]
    refine Matrix.ext fun i j => ?_
    exact map_mul (piF t) _ _
  rw [h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_assoc]
  rfl

private theorem half_dual {D : D7} (e₀ : AE D) (A' WW : HSp D)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) (hy : IsHalf (cA D e₀) y) (i j) :
    toEAf D e₀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j := by
  have h1 : e₀ • ((y : Matrix _ _ (AE D)).map (cA D))ᵀ = ((y : Matrix _ _ (AE D)).map (cA D))ᵀ := by
    refine Matrix.ext fun i j => ?_
    change e₀ * cA D (y j i) = cA D (y j i)
    conv_rhs => rw [← hy j i, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  have h2 : toEAf D e₀ • frMapAdj A' WW βA' βW y = frMapAdj A' WW βA' βW y := by
    unfold frMapAdj
    conv_rhs => rw [← h1, Matrix.mul_smul, Matrix.smul_mul]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    refine Matrix.ext fun i j => ?_
    exact (map_mul (toEAf D) _ _).symm
  have h3 : toEAf D e₀ • GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
    rw [smul_comm, h2]
  exact congrFun (congrFun h3 i) j

theorem UpperTheory.exists_gl_stdSnd_eq_product_local :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (A' WW : HSp D) (a : ℕ) (hr : a + A'.rank = WW.rank)
          (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (m : ∀ v : P, GL (Fin (a + A'.rank)) (Fv D.host.F v)),
        (∀ v, (m v).1 = (βW.1.map (piF (t v))).submatrix (finCongr hr) (finCongr hr)) →
        ∃ g : ∀ v : P, GL (Fin A'.rank) (Fv D.host.F v), ∀ y : WO A' WW,
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e₀ (∏ w ∈ S, w.asIdeal ^ c w) a A' WW βA' βW y =
            if IsHalf (cA D e₀) y then ∏ v : P, GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
              ((g v).1 * (ptO (sgn false A').gram (finCongr hr) y).map (piW ((t v).comp D.sp.cm.sig)) *
                ((D.host.xi0 • (WW.gramᵀ).submatrix (finCongr hr) (finCongr hr)).map (t v))ᵀ * (m v).1) else 0 := by
  intro D e₀ S hS P t hP ht ν c A' WW a hr βA' βW m hm
  refine ⟨fun v => Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹, fun y => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  by_cases hy : IsHalf (cA D e₀) y
  swap
  · rw [if_neg fun h => hy h.1, if_neg hy]
  rw [if_pos hy]
  have hc : ∀ v : P, GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
      ((Matrix.GeneralLinearGroup.map (piF (t v)) βA'⁻¹).1 *
        (ptO (sgn false A').gram (finCongr hr) y).map (piW ((t v).comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix (finCongr hr) (finCongr hr)).map (t v))ᵀ * (m v).1) =
      GlobalTheory.StdPairCone.stdB (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) a A'.rank
        (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (piF (t v))).submatrix id (finCongr hr)) := by
    intro v
    rw [hm v, ← coord_eq]
    rfl
  refine Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (hc v).symm)
  have hN := half_dual e₀ A' WW βA' βW y hy
  generalize GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y = N at hN ⊢
  have hI := fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)
  have hϖ : ∀ v : P, ValuativeRel.valuation (Fv D.host.F v) (unifAt v.1 : (Fv D.host.F v)ˣ) ≤ 1 := fun v =>
    (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec.mem
  refine Eq.trans ?_ (Finset.prod_congr rfl fun v _ => (stdB_eq _ _ (hϖ v) _ _ _ _).symm)
  by_cases h : IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)
  · have hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N = fun i j => N i (finCongr hr (Fin.natAdd a j)) := by
      funext i j
      have hj : a + j.1 < WW.rank := hr ▸ Nat.add_lt_add_left j.2 a
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock
      rw [dite_eq_left hj]
      rfl
    rw [if_pos ⟨hy, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ _ (by rw [hb]; exact fun i j => h.1 _ _)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [if_pos ⟨fun i j => (hI _ _).1.1 (h.1 _ _) v, fun i j => (hI _ _).2.1 (h.2 _ _ j.2) v⟩, hb]
    rfl
  · rw [if_neg fun h' => h h'.2]
    symm
    by_contra h0
    refine h ⟨fun i j => (hI i j).1.2 fun v => ?_, fun i j hj => (hI i j).2.2 fun v => ?_⟩
    · have h1 := Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)
      exact (ite_ne_right_iff.1 h1).1.1 i ((finCongr hr).symm j)
    · have h1 := Finset.prod_ne_zero_iff.1 h0 v (Finset.mem_univ v)
      exact (ite_ne_right_iff.1 h1).1.2 i ⟨j.1, hj⟩
end
