module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DetALeviTorus
section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsInhabitant
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def big (δ : E) : Spc F E 3 := ⟨!![0, 0, 1; 0, δ, 0; -1, 0, 0], ⊥, fun _ => 1, fun _ => 1⟩


variable (F) in
def small (δ : E) : Spc F E 1 := ⟨!![δ], ⊥, fun _ => 1, fun _ => 1⟩



end GlobalTheory.Published.LeviCentreModel

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Published.LeviCentreModel

namespace GlobalTheory.Published.LeviInducedModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cont_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F) (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
    change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
    rw [infEmb_tmul, map_one, mul_one]; rfl

end GlobalTheory.Published.LeviInducedModel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchMatBlockEmbInfGL
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_sandwich' {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℂ) (V : Matrix (Fin d) (Fin n) ℂ) (h : V * U = 1)
    (A : Matrix (Fin d) (Fin d) ℂ) : NormedSpace.exp (U * A * V) = 1 + U * (NormedSpace.exp A - 1) * V := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  have h' : ∀ W : Matrix (Fin d) (Fin n) ℂ, V * (U * W) = W := fun W => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let f : Matrix (Fin d) (Fin d) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => U * p.1 * V + p.2 • (1 - U * V)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h', Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero,
          smul_smul, sub_zero, add_zero, zero_add]
        module
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, add_smul]; abel }
  have hf : Continuous f :=
    ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).add (continuous_snd.smul continuous_const)
  have e := NormedSpace.map_exp f hf (A, 0)
  have e1 : f (A, 0) = U * A * V := by simp [f]
  rw [e1] at e
  refine e.symm.trans ?_
  change U * (NormedSpace.exp (A, (0 : ℂ))).1 * V + (NormedSpace.exp (A, (0 : ℂ))).2 • (1 - U * V) = _
  have f1 : (NormedSpace.exp (A, (0 : ℂ))).1 = NormedSpace.exp A := Prod.fst_exp (A, (0 : ℂ))
  have f2 : (NormedSpace.exp (A, (0 : ℂ))).2 = NormedSpace.exp 0 := Prod.snd_exp (A, (0 : ℂ))
  rw [f1, f2, NormedSpace.exp_zero, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem exp_isoFrame' : ∀ (n d : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin d) ℂ),
    Xᴴ * J * X = 0 → Yᴴ * J * Y = 0 → Xᴴ * J * Y = 1 → Yᴴ * J * X = 1 →
    ∀ B : Matrix (Fin d) (Fin d) ℂ, NormedSpace.exp (X * B * (Yᴴ * J) - Y * Bᴴ * (Xᴴ * J)) =
      1 + X * (NormedSpace.exp B - 1) * (Yᴴ * J) + Y * ((NormedSpace.exp (-B))ᴴ - 1) * (Xᴴ * J) := by
  intro n d J X Y xx yy xy yx B
  have h1 : (Yᴴ * J) * X = 1 := yx
  have h2 : (Xᴴ * J) * Y = 1 := xy
  have yy' : ∀ {m : ℕ} (W : Matrix (Fin d) (Fin m) ℂ), Yᴴ * (J * (Y * W)) = 0 := fun W => by
    rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, ← Matrix.mul_assoc Yᴴ J Y, yy, Matrix.zero_mul]
  have xx' : ∀ {m : ℕ} (W : Matrix (Fin d) (Fin m) ℂ), Xᴴ * (J * (X * W)) = 0 := fun W => by
    rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ J X, xx, Matrix.zero_mul]
  have c12 : X * B * (Yᴴ * J) * (Y * (-Bᴴ) * (Xᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [yy']; simp
  have c21 : Y * (-Bᴴ) * (Xᴴ * J) * (X * B * (Yᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [xx']; simp
  have hc : Commute (X * B * (Yᴴ * J)) (Y * (-Bᴴ) * (Xᴴ * J)) := by
    unfold Commute SemiconjBy; rw [c12, c21]
  have hs : X * B * (Yᴴ * J) - Y * Bᴴ * (Xᴴ * J) = X * B * (Yᴴ * J) + Y * (-Bᴴ) * (Xᴴ * J) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
  rw [hs, Matrix.exp_add_of_commute _ _ hc, exp_sandwich' X (Yᴴ * J) h1, exp_sandwich' Y (Xᴴ * J) h2,
    ← Matrix.conjTranspose_neg, Matrix.exp_conjTranspose]
  have cross : X * (NormedSpace.exp B - 1) * (Yᴴ * J) * (Y * ((NormedSpace.exp (-B))ᴴ - 1) * (Xᴴ * J)) = 0 := by
    simp only [Matrix.mul_assoc]; rw [yy']; simp
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, cross, add_zero]
  abel

theorem infEmb_compInf_sInf' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E), Continuous Φ → Continuous Φ.symm → (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) → (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : GlobalTheory.CuspRep.Cinf E),
 infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E z))) = GlobalTheory.CuspRep.coord τ.1 z := by
  intro F E _ _ _ _ _ _ σ hcm Φ j hΦ hΦs hj hΦz w τ z
  have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
    have e := congrArg Prod.fst (hΦz (Φ.symm x))
    rw [RingEquiv.apply_symm_apply] at e
    rw [e, RingEquiv.symm_apply_apply]
  have hL : Continuous fun z : GlobalTheory.CuspRep.Cinf E =>
      infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E z))) :=
    (GlobalTheory.Published.LeviInducedModel.cont_piInf τ).comp
      (hΦs.comp ((GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const))
  have hR : Continuous (GlobalTheory.CuspRep.coord τ.1) := by
    unfold GlobalTheory.CuspRep.coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have hsymm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
    continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
        (continuous_apply v)
  have hD : DenseRange fun x : E => (GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x) :=
    ((GlobalTheory.CuspRep.infEq E).symm.surjective.denseRange).comp
      (NumberField.InfiniteAdeleRing.denseRange_algebraMap E) hsymm
  have hE : ∀ x : E, infEmb τ (compInf F E w (Φ.symm (GlobalTheory.CuspRep.sInf E
      ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x))))) =
      GlobalTheory.CuspRep.coord τ.1 ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) := by
    intro x
    have h1 : GlobalTheory.CuspRep.sInf E ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) =
        ((algebraMap E (InfiniteAdeleRing E) x, 0) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) := by
      change ((GlobalTheory.CuspRep.infEq E ((GlobalTheory.CuspRep.infEq E).symm _), 0) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) = _
      rw [RingEquiv.apply_symm_apply]
    have h2 : j.symm (algebraMap E (InfiniteAdeleRing E) x) = (1 : Ainf F) ⊗ₜ[F] x := by
      rw [← hj x, RingEquiv.symm_apply_apply]
    have hci : ∀ y : AF F ⊗[F] E, compInf F E w y =
        (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom (GlobalTheory.LFun.infTens F E y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [h1, hci]
    erw [key]
    change infEmb τ ((Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom
      (j.symm (algebraMap E (InfiniteAdeleRing E) x))) = _
    rw [h2]
    have h3 := GlobalTheory.CuspRep.coord_algebraMap τ.1 x
    change GlobalTheory.CuspRep.coord τ.1 ((GlobalTheory.CuspRep.infEq E).symm (algebraMap E (InfiniteAdeleRing E) x)) = τ.1 x at h3
    rw [h3]
    change infEmb τ ((GlobalTheory.AutFunCompare.evW w 1) ⊗ₜ[F] x) = _
    rw [map_one, infEmb_tmul, map_one, one_mul]
  exact congrFun (hD.equalizer hL hR (funext hE)) z


open GlobalTheory.CuspRep GlobalTheory.BlockArch in
theorem archMat_blockEmb_infGL' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → ∀ (y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E)), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w),
 GlobalTheory.Orb.archMat σ J τ (projArch σ J w (ι (GlobalTheory.CuspRep.infGL E d y))) =
  1 + (GlobalTheory.BlockForms.blkCols h X).map τ.1 * (y.1.map (GlobalTheory.CuspRep.coord τ.1) - 1) * (((GlobalTheory.BlockForms.blkCols h Y).map τ.1)ᴴ * J.map τ.1) + (GlobalTheory.BlockForms.blkCols h Y).map τ.1 * (((y⁻¹).1.map (GlobalTheory.CuspRep.coord τ.1))ᴴ - 1) * (((GlobalTheory.BlockForms.blkCols h X).map τ.1)ᴴ * J.map τ.1) := by
  intro F E _ _ _ _ _ _ σ hcm n J _ r X Y _ l d h ι hB y
  have hmem := ((GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb F E σ hcm n J r X Y l d h ι hB).choose_spec.2.2 y).1
  refine ⟨hmem, fun w τ => ?_⟩
  obtain ⟨Φ, j, hΦ, hΦs, hj1, hs, hform⟩ := hB
  let π : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hco : ∀ z : Cinf E, π (Φ.symm (sInf E z)) = coord τ.1 z := fun z =>
    infEmb_compInf_sInf' F E σ hcm Φ j hΦ hΦs hj1 hs w τ z
  have hp : ∀ y : GL (Fin d) (Cinf E), ((infGL E d y).1.map Φ.symm).map π = y.1.map (coord τ.1) := fun y => by
    rw [Matrix.map_map]
    exact congrArg Units.val (map_cornerGL_of_hom (sInf E) (π.comp Φ.symm.toRingHom) (coord τ.1) hco y)
  have hA : ∀ {m p : Type} (M : Matrix m p E), (adMat F M).map π = M.map τ.1 := fun M => by
    have e1 : (adMat F M).map (compInf F E w) = M.map (inclR (F := F) w.Completion) := map_inclR_map (evInf F w) M
    change (adMat F M).map (⇑(infEmb τ) ∘ ⇑(compInf F E w)) = _
    rw [← Matrix.map_map, e1, Matrix.map_map]
    ext i k
    simp [inclR]
  have hC : ∀ {m p : Type} (M : Matrix m p (AF F ⊗[F] E)), (Formalism.UG.cT (sigR (AF F) σ) M).map π = (M.map π)ᴴ := fun M => by
    have e1 : (Formalism.UG.cT (sigR (AF F) σ) M).map (compInf F E w) =
        Formalism.UG.cT (sigR w.Completion σ) (M.map (compInf F E w)) := map_cT_sigR_map (evInf F w) σ M
    change (Formalism.UG.cT (sigR (AF F) σ) M).map (⇑(infEmb τ) ∘ ⇑(compInf F E w)) = _
    rw [← Matrix.map_map, e1]
    ext i k
    exact (GlobalTheory.AdelicU.infEmb_sigR hcm τ _).symm
  rw [GlobalTheory.Orb.archMat_apply, matHom_projArch]
  change (((matHom _ σ J (ι (infGL E d y))).1).map (compInf F E w)).map (infEmb τ) = _
  rw [Matrix.map_map]
  change ((matHom _ σ J (ι (infGL E d y))).1).map π = _
  rw [hform, ← map_inv, map_blockForm, hA, hA, hA, hA, hC, hp, hp, Matrix.map_mul, Matrix.map_mul,
    GlobalTheory.CentreFin.map_cT_emb hcm, GlobalTheory.CentreFin.map_cT_emb hcm]

section Coord
open GlobalTheory.CuspRep (Cinf coord atEmb expGLi infGL)

variable {E : Type} [Field E] [NumberField E]

theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem coord_smul (τ : E →+* ℂ) (t : ℝ) (x : Cinf E) : coord τ (t • x) = (t : ℂ) * coord τ x := by
  unfold coord
  split_ifs
  · change (t • x) _ = (t : ℂ) * x _
    rw [Pi.smul_apply, Complex.real_smul]
  · change starRingEnd ℂ ((t • x) _) = (t : ℂ) * starRingEnd ℂ (x _)
    rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem map_coord_exp {d : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin d) (Fin d) (Cinf E)) :
    (NormedSpace.exp M).map (coord τ) = NormedSpace.exp (M.map (coord τ)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Continuous ((coord τ).mapMatrix : Matrix (Fin d) (Fin d) (Cinf E) → Matrix (Fin d) (Fin d) ℂ) :=
    continuous_id.matrix_map (continuous_coordE τ)
  exact NormedSpace.map_exp (coord τ).mapMatrix hc M

theorem map_coord_smul_atEmb {d : ℕ} (τ τ' : E →+* ℂ) (t : ℝ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (t • B.map (atEmb τ)).map (coord τ') = (t : ℂ) • B.map (fun z => coord τ' (atEmb τ z)) := by
  ext a b
  simp [coord_smul]

end Coord

section Line
open GlobalTheory.CuspRep (Cinf coord atEmb expGLi infGL)

theorem isLineOf_blockEmb_exp' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (B : Matrix (Fin d) (Fin d) ℂ),
 IsLineOf σ J τ ((GlobalTheory.BlockForms.blkCols h X).map τ.1 * B * (((GlobalTheory.BlockForms.blkCols h Y).map τ.1)ᴴ * J.map τ.1) - (GlobalTheory.BlockForms.blkCols h Y).map τ.1 * Bᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ.1)ᴴ * J.map τ.1))
  fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • B.map (GlobalTheory.CuspRep.atEmb τ.1)))) := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r X Y hW l d h ι hι w τ B
  classical
  have hga := archMat_blockEmb_infGL' F E σ hcm n J hJ r X Y hW l d h ι hι
  have hoff : ∀ (w' : InfinitePlace F), w' ≠ w → ∀ (τ' : EmbOver E w') (z : ℂ), coord τ'.1 (atEmb τ.1 z) = 0 := by
    intro w' hw' τ' z
    have hmk : InfinitePlace.mk τ'.1 ≠ InfinitePlace.mk τ.1 := by
      intro e
      apply hw'
      have e' := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) e
      simp only [InfinitePlace.comap_mk, τ'.2, τ.2, InfinitePlace.mk_embedding] at e'
      exact e'
    unfold coord atEmb
    split_ifs <;> simp [Pi.single_eq_of_ne hmk]
  have hinv : ∀ t : ℝ, (expGLi d (t • B.map (atEmb τ.1)))⁻¹ = expGLi d ((-t) • B.map (atEmb τ.1)) := fun t => by
    have e := GlobalTheory.CuspRep.expGLi_add_smul d (B.map (atEmb τ.1)) (-t) t
    rw [neg_add_cancel, zero_smul, GlobalTheory.CuspRep.expGLi_zero] at e
    exact (eq_inv_of_mul_eq_one_left e.symm).symm
  have hexpmap : ∀ (τ' : E →+* ℂ) (s : ℝ), (expGLi d (s • B.map (atEmb τ.1))).1.map (coord τ') =
      NormedSpace.exp ((s : ℂ) • B.map (fun z => coord τ' (atEmb τ.1 z))) := fun τ' s => by
    rw [GlobalTheory.CuspRep.val_expGLi, map_coord_exp, map_coord_smul_atEmb]
  intro t
  obtain ⟨hmem, hmat⟩ := hga (expGLi d (t • B.map (atEmb τ.1)))
  refine ⟨projArch σ J w (ι (infGL E d (expGLi d (t • B.map (atEmb τ.1))))), ?_, ?_⟩
  · refine GAd_ext σ J (fun w'' => ?_) fun v => ?_
    · by_cases e : w'' = w
      · subst e; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J e]
        obtain ⟨τ'⟩ : Nonempty (EmbOver E w'') := inferInstance
        have inj : Function.Injective (GlobalTheory.Orb.archMat σ J τ') := fun a b e => by
          rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at e
          exact (archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))
        apply inj
        have hz : B.map (fun z => coord τ'.1 (atEmb τ.1 z)) = 0 := by
          ext a b; simp [hoff w'' e τ']
        rw [hmat w'' τ', map_one, hinv, hexpmap, hexpmap, hz]
        simp
    · rw [proj_embArch, ← projFinLoc_projFin, mem_infPts.1 hmem, map_one]
  · have hb : B.map (fun z => coord τ.1 (atEmb τ.1 z)) = B := by
      ext a b; simp [GlobalTheory.CuspRep.coord_atEmb]
    rw [hmat w τ, hinv, hexpmap, hexpmap, hb]
    have hJh : (J.map τ.1)ᴴ = J.map τ.1 := conjTranspose_map hcm hJ τ.1
    obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ.1
    let f : Fin d → Fin r := fun j => ⟨l + j.val, by omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by simpa [f] using congrArg Fin.val e)
    have key : ∀ A C : Matrix (Fin n) (Fin r) E,
        ((GlobalTheory.BlockForms.blkCols h A).map τ.1)ᴴ * J.map τ.1 * (GlobalTheory.BlockForms.blkCols h C).map τ.1 =
          ((A.map τ.1)ᴴ * J.map τ.1 * C.map τ.1).submatrix f f := by
      intro A C; ext i j; rfl
    have bxx := (key X X).trans (by rw [hxx])
    have byy := (key Y Y).trans (by rw [hyy])
    have bxy := (key X Y).trans (by rw [hxy, Matrix.submatrix_one f hf])
    have byx := GlobalTheory.CentreFin.dual_swap hJh bxy
    have ha := exp_isoFrame' n d (J.map τ.1) _ _ bxx byy bxy byx ((t : ℂ) • B)
    have hneg : ((-t : ℝ) : ℂ) • B = -((t : ℂ) • B) := by push_cast; rw [neg_smul]
    rw [hneg, ← ha]
    congr 1
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.coe_smul, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

end Line


open GlobalTheory.CuspRep in
theorem lie_eq_deriv_exp' : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (d : ℕ) (f : GlobalTheory.CuspRep.Sm E d) (B : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) (x : GlobalTheory.CuspRep.GA E d),
 (GlobalTheory.CuspRep.lie E d (GlobalTheory.CuspRep.toL B) f).1 x = deriv (fun t : ℝ => f.1 (x * GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • B)))) 0 := by
  intro E _ _ _ d f B x
  have hc : HasDerivAt (fun t : ℝ => toL (expGLi d (t • B)).val) (toL B) 0 := by
    letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
    let L : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  rw [GlobalTheory.CuspRep.lie_apply]
  exact ((hasDerivAt_curve f x (fun t : ℝ => expGLi d (t • B)) (toL B) (by simp) hc).deriv).symm

end GlobalTheory.CompanionTheory.BlockEntry
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisBlockEntries
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

open GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry

theorem sandwich_single_apply {A B : Type} [Fintype A] {d : ℕ} (U : Matrix A (Fin d) ℂ) (W : Matrix (Fin d) B ℂ)
    (i j : Fin d) (z : ℂ) (a : A) (c : B) : (U * Matrix.single i j z * W) a c = U a i * z * W j c := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]

theorem rows_of_adapted {n m : ℕ} {H P : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hxx : Xᴴ * H * X = 0) (hyy : Yᴴ * H * Y = 0) (hxy : Xᴴ * H * Y = 1) (hyx : Yᴴ * H * X = 1) (hle : 2 * m ≤ n)
    (cX : ∀ (c : Fin n) (k : Fin m), c.val = k.val → ∀ a, P a c = X a k)
    (cY : ∀ (c : Fin n) (k : Fin m), c.val + k.val + 1 = n → ∀ a, P a c = Y a k)
    (pX : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Xᴴ * H * P) k c = 0)
    (pY : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Yᴴ * H * P) k c = 0) (k : Fin m) (c : Fin n) :
    (Yᴴ * H * P) k c = (if c.val = k.val then 1 else 0) ∧
      (Xᴴ * H * P) k c = (if c.val + k.val + 1 = n then 1 else 0) := by
  have hk := k.2
  have hc := c.2
  by_cases h1 : c.val < m
  · have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * X) k ⟨c.val, h1⟩ := fun M => by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [cX c ⟨c.val, h1⟩ rfl a]
    rw [e, e, hyx, hxx, Matrix.one_apply, Matrix.zero_apply]
    refine ⟨?_, ?_⟩
    · by_cases e' : c.val = k.val
      · rw [if_pos e', if_pos (Fin.ext e'.symm)]
      · rw [if_neg e', if_neg fun e'' => e' (congrArg Fin.val e'').symm]
    · rw [if_neg (by omega)]
  · by_cases h2 : c.val + m < n
    · rw [pX c (by omega) h2, pY c (by omega) h2, if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · have hk' : n - 1 - c.val < m := by omega
      have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * Y) k ⟨n - 1 - c.val, hk'⟩ := fun M => by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun a _ => by rw [cY c ⟨n - 1 - c.val, hk'⟩ (by simp only; omega) a]
      rw [e, e, hyy, hxy, Matrix.one_apply, Matrix.zero_apply]
      refine ⟨by rw [if_neg (by omega)], ?_⟩
      by_cases e' : c.val + k.val + 1 = n
      · rw [if_pos e', if_pos (Fin.ext (by simp only; omega))]
      · rw [if_neg e', if_neg fun e'' => e' (by have := congrArg Fin.val e''; simp only at this; omega)]

theorem conj_units_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin m) E} (hW : IsWittFrame σ J X Y) {l d : ℕ} (h : l + d ≤ m) {C : GL (Fin n) E}
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (τ : E →+* ℂ) (i j : Fin d) (p q p' q' : Fin n)
    (hp : p.val = l + i.val) (hq : q.val = l + j.val) (hp' : p'.val + l + j.val + 1 = n)
    (hq' : q'.val + l + i.val + 1 = n) (z : ℂ) :
    z • (C.1.map τ * Matrix.single p q 1 * (C.1.map τ)⁻¹) -
        (starRingEnd ℂ z) • (C.1.map τ * Matrix.single p' q' 1 * (C.1.map τ)⁻¹) =
      (GlobalTheory.BlockForms.blkCols h X).map τ * Matrix.single i j z * (((GlobalTheory.BlockForms.blkCols h Y).map τ)ᴴ * J.map τ) -
        (GlobalTheory.BlockForms.blkCols h Y).map τ * (Matrix.single i j z)ᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ)ᴴ * J.map τ) := by
  classical
  set P := C.1.map τ with hP
  have hdet : IsUnit P.det := by
    have e : P.det = τ C.1.det := by rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 C.isUnit).map τ
  obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ
  have hJh : (J.map τ)ᴴ = J.map τ := GlobalTheory.LeviHC.conjTranspose_map hcm hJ τ
  have hyx := GlobalTheory.CentreFin.dual_swap hJh hxy
  have perp : ∀ (A : Matrix (Fin n) (Fin m) E) (c : Fin n), (Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c) = 0 →
      ∀ k, ((A.map τ)ᴴ * J.map τ * P) k c = 0 := fun A c e k => by
    have e1 : ((Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c)) k = 0 := by rw [e]; rfl
    have e2 := congrArg τ e1
    rw [map_zero] at e2
    rw [← e2, ← GlobalTheory.CentreFin.map_cT_emb hcm τ A, ← Matrix.map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  have what₂ := rows_of_adapted (P := P) hxx hyy hxy hyx hC.le
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.colX c k e a, Matrix.map_apply])
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.columnBlock c k e a, Matrix.map_apply])
    (fun c h1 h2 => perp X c (hC.perpX c h1 h2)) (fun c h1 h2 => perp Y c (hC.perpY c h1 h2))
  set Xb := (GlobalTheory.BlockForms.blkCols h X).map τ with hXb
  set Yb := (GlobalTheory.BlockForms.blkCols h Y).map τ with hYb
  set R := Xb * Matrix.single i j z * (Ybᴴ * J.map τ) - Yb * (Matrix.single i j z)ᴴ * (Xbᴴ * J.map τ) with hR
  let f : Fin d → Fin m := fun a => ⟨l + a.val, by omega⟩
  have sY : ∀ (a : Fin d) (c : Fin n), (Ybᴴ * J.map τ * P) a c = if c.val = l + a.val then 1 else 0 := fun a c =>
    (what₂ (f a) c).1
  have sX : ∀ (a : Fin d) (c : Fin n), (Xbᴴ * J.map τ * P) a c = if c.val + (l + a.val) + 1 = n then 1 else 0 := fun a c =>
    (what₂ (f a) c).2
  have hRP : R * P = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) := by
    ext a c
    have e1 : R * P = Xb * Matrix.single i j z * (Ybᴴ * J.map τ * P) -
        Yb * Matrix.single j i (starRingEnd ℂ z) * (Xbᴴ * J.map τ * P) := by
      rw [hR, Matrix.sub_mul, Matrix.conjTranspose_single]
      simp only [Matrix.mul_assoc]
      rfl
    have e2 : P a p = Xb a i := by
      rw [hP, Matrix.map_apply, hC.colX p (f i) hp a]; rfl
    have e3 : P a p' = Yb a j := by
      rw [hP, Matrix.map_apply, hC.columnBlock p' (f j) (by simp only [f]; omega) a]; rfl
    rw [e1, Matrix.sub_apply, sandwich_single_apply, sandwich_single_apply, sY, sX, Matrix.mul_sub, Matrix.sub_apply,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply]
    have e4 : ∀ (u v : Fin n), (P * Matrix.single u v (1 : ℂ)) a c = P a u * (if c = v then 1 else 0) := fun u v => by
      by_cases e : c = v
      · subst e
        simp [Matrix.mul_single_apply_same]
      · have e' : v ≠ c := fun e'' => e e''.symm
        rw [if_neg e, mul_zero, Matrix.mul_apply]
        exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_apply_of_col_ne _ _ e' _, mul_zero]
    rw [e4, e4, e2, e3]
    have c1 : (c = q) ↔ c.val = l + j.val := by rw [Fin.ext_iff, hq]
    have c2 : (c = q') ↔ c.val + (l + i.val) + 1 = n := by rw [Fin.ext_iff]; omega
    simp only [c1, c2, smul_eq_mul]
    ring
  calc _ = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) * P⁻¹ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = R := by rw [← hRP, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]

theorem lieS_eq_derEnd : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  intro D _ θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' z x
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨e, he⟩ : ∃ e : EmbOver D.host.E (placeOf D τ), e.1 = tauE D τ := ⟨embOverOf D τ, rfl⟩
  have hline := isLineOf_blockEmb_exp' _ D.host.E D.sp.cm.sig hcm V.rank V.gram hJ m X Y hW l d h ι hι (placeOf D τ)
    e (Matrix.single i j z)
  have hmat := conj_units_eq hcm hJ hW h hC (tauE D τ) i j p q p' q' hp hq hp' hq' z
  rw [he, ← hmat] at hline
  have hsk := hline.skew hcm
  rw [he] at hsk
  have hZ : z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
      (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹) ∈ lieAt V τ := hsk
  have hγ : ∀ t : ℝ, ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • (Matrix.single i j z).map
      (GlobalTheory.CuspRep.atEmb (tauE D τ))))) = oneP θ V τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
        (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) t := fun t => by
    obtain ⟨y, e1, e2⟩ := hline t
    refine Eq.trans e1 ?_
    rw [oneP, ← e2, GlobalTheory.Orb.archMat_eq_archEquiv _ hcm, atTau_archEquiv hθ V e he]
  have h0 : GlobalTheory.CuspRep.atEmb (tauE D τ) 0 = 0 := by rw [GlobalTheory.CuspRep.atEmb_eq]; simp
  have hs : Matrix.single i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) = (Matrix.single i j z).map (GlobalTheory.CuspRep.atEmb (tauE D τ)) := by
    ext a b; simp only [Matrix.single_apply, Matrix.map_apply]; split_ifs <;> simp [h0]
  rw [GlobalTheory.CuspRep.lieS_apply, hs, lie_eq_deriv_exp' D.host.E d f _ x]
  change _ = RderC θ V τ _ F.1 (ι x)
  rw [GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hZ]
  simp only [hf, map_mul, hγ]
  rfl

end GlobalTheory.CompanionTheory.BlockEntry
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisBlockEntriesStatement
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_adapted_basis : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  first | exact @GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd | exact GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd | (intros; apply GlobalTheory.CompanionTheory.BlockEntry.lieS_eq_derEnd <;> assumption)
end
