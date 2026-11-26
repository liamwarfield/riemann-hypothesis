module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SemiAbelianHomExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvariance
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU

open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem eq_zero_of_mem_span_cols {L : Matrix (Fin b) (Fin a) R} {C : Matrix (Fin a) (Fin b) R} (hLC : L * C = 1)
    {I : Set (Fin b)} {w : Fin a → R} (hw : w ∈ Submodule.span R ((fun i => Cᵀ i) '' I))
    (h0 : ∀ i ∈ I, (L *ᵥ w) i = 0) : w = 0 := by
  classical
  have key : ∀ v ∈ Submodule.span R ((fun i => Cᵀ i) '' I), ∃ c : Fin b → R, (∀ i, i ∉ I → c i = 0) ∧ v = C *ᵥ c := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v h =>
      obtain ⟨i, hi, rfl⟩ := h
      refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne (by rintro rfl; exact hi' hi) _, ?_⟩
      rw [mulVec_single_one]
      rfl
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by rw [mulVec_add]⟩
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨t • c, fun i hi => by simp [hc i hi], by rw [mulVec_smul]⟩
  obtain ⟨c, hc, rfl⟩ := key w hw
  have e : L *ᵥ (C *ᵥ c) = c := by rw [mulVec_mulVec, hLC, one_mulVec]
  rw [e] at h0
  have : c = 0 := funext fun i => by
    by_cases hi : i ∈ I
    · exact h0 i hi
    · exact hc i hi
  rw [this, mulVec_zero]

theorem mul_eq_of_conj (s : R →+* R) {G H A : Matrix (Fin a) (Fin a) R} {C : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hHG : H * G = 1) (hU : cT s H * A * H = A) (hHC : H * C = C * B) :
    cT s C * A * G = cT s B * (cT s C * A) := by
  calc cT s C * A * G = cT s C * (cT s H * A * H) * G := by rw [hU]
    _ = cT s (H * C) * A * (H * G) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT s B * (cT s C * A) := by
      rw [hHC, hHG, Formalism.UG.cT_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem mul_eq_self_of_pair (s : R →+* R) {G A : Matrix (Fin a) (Fin a) R} {C D : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hU : cT s G * A * G = A) (hCD : cT s C * A * D = 1) (hGC : G * C = C)
    (hGD : G * D = D * B) : G * D = D := by
  have hB : B = 1 := by
    calc B = cT s C * A * D * B := by rw [hCD, Matrix.one_mul]
      _ = cT s (G * C) * A * (G * D) := by rw [hGC, hGD]; simp only [Matrix.mul_assoc]
      _ = cT s C * (cT s G * A * G) * D := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hCD]
  rw [hGD, hB, Matrix.mul_one]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mat_inv_mul (g : GAd σ J) : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem adMat_mul_eq_one {a b : ℕ} {L : Matrix (Fin a) (Fin b) E} {C : Matrix (Fin b) (Fin a) E} (h : L * C = 1) :
    adMat F L * adMat F C = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_initCols_mul (C : Matrix (Fin n) (Fin r) E) (k : Fin r) :
    cT (sigR (AF F) σ) (adMat F (initCols C k)) * adMat F J =
      (adMat F (cT (σ : E →+* E) C * J)).submatrix (Fin.castLE k.2) id := by
  have c1 : cT (sigR (AF F) σ) (adMat F (initCols C k)) = adMat F (cT (σ : E →+* E) (initCols C k)) := rfl
  rw [c1, ← Matrix.map_mul]
  rfl

theorem exists_height_lower_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {j : Fin r}
    (hj : j ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j := by
  have hκj : j < κ := by
    obtain ⟨k, hk, hjk⟩ := hj
    by_contra hc
    exact hκ ⟨k, hk, (not_lt.1 hc).trans hjk⟩
  have h1 := (Subgroup.mem_iInf.1 hu.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  have hLC : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := adMat_mul_eq_one (yx h hJ hW)
  refine sub_eq_zero.1 (eq_zero_of_mem_span_cols hLC h1 ?_)
  rintro i ⟨k, hk, hik, hkj⟩
  have hkT : k ∈ T := by
    rcases Finset.mem_insert.1 hk with rfl | hk'
    · exact absurd (hkj.trans hκj) (lt_irrefl _)
    · exact hk'
  have hl' := inv_mem hl
  simp only [levi, Subgroup.mem_iInf] at hl'
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl' k hkT)).2
  have h2 := mul_eq_of_conj (A := adMat F J) (sigR (AF F) σ) (mat_inv_mul g) (g⁻¹).2 e
  rw [cT_initCols_mul] at h2
  set L := (adMat F (cT (σ : E →+* E) Y * J)).submatrix (Fin.castLE k.2) id with hL
  have h3 : L *ᵥ (adMat F X)ᵀ j = 0 := by
    funext p
    have hp : Fin.castLE k.2 p ≠ j := fun hc => by
      have h4 : (Fin.castLE k.2 p).val ≤ k.val := Nat.le_of_lt_succ p.2
      have h5 : k.val < j.val := hkj
      rw [hc] at h4
      omega
    exact (congrFun (congrFun hLC (Fin.castLE k.2 p)) j).trans (Matrix.one_apply_ne hp)
  have h4 : L *ᵥ ((matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, h2, ← mulVec_mulVec, h3, mulVec_zero, sub_zero]
  exact congrFun h4 ⟨i.val, Nat.lt_succ_of_le hik⟩

theorem fix_y (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {i : Fin r}
    (hi : i ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F Y)ᵀ i = (adMat F Y)ᵀ i := by
  obtain ⟨k, hkT, hik⟩ := hi
  simp only [levi, Subgroup.mem_iInf] at hl
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl k hkT)).2
  have hGC : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) :=
    Matrix.ext_col fun p => exists_height_lower_bound h hJ hW hκ (by simpa only [levi, Subgroup.mem_iInf] using hl) hu
      ⟨k, hkT, Nat.le_of_lt_succ p.2⟩
  have hCD : cT (sigR (AF F) σ) (adMat F (initCols X k)) * adMat F J * adMat F (initCols Y k) = 1 := by
    rw [cT_initCols_mul]
    have h1 : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := adMat_mul_eq_one hW.xy
    exact Matrix.ext fun p q => (congrFun (congrFun h1 (Fin.castLE k.2 p)) (Fin.castLE k.2 q)).trans (by simp [Matrix.one_apply])
  have h2 := mul_eq_self_of_pair (A := adMat F J) (sigR (AF F) σ) g.2 hCD hGC e
  exact congrArg (fun M => Mᵀ ⟨i.val, Nat.lt_succ_of_le hik⟩) h2

theorem levi_inf_unip_le_uPart_general (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (T : Finset (Fin r)) {κ : Fin r} (hκ : κ ∉ upTo T) :
    levi σ J X Y T ⊓ unip σ J X (insert κ T) ≤ uPart σ J X Y T := by
  rintro g ⟨hl, hu⟩
  have key : colSpan F X (upTo T) ⊔ colSpan F Y (upTo T) ≤ LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact exists_height_lower_bound h hJ hW hκ hl hu hj
    · rintro _ ⟨j, hj, rfl⟩
      exact fix_y h hJ hW hκ hl hu hj
  exact fun y hy => key hy

end Frame

theorem levi_inf_unip_le_uPart : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y hW T κ hκ
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  exact levi_inf_unip_le_uPart_general h (hJ' V) hW T hκ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedAutomorphicInvarianceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_inf_unipotent_le_hermitian_part : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLie
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
open scoped GlobalTheory.MixModel

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {m : ℕ}
  {X : Matrix (Fin V.rank) (Fin m) D.host.E} {T : Finset (Fin m)}

theorem prM_kills_colSpan
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {z : Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ colSpan D.host.F X (upTo T)) :
    (adMat D.host.F (prM V V' ι)) *ᵥ z = 0 := by
  have hle : colSpan D.host.F X (upTo T) ≤ LinearMap.ker (adMat D.host.F (prM V V' ι)).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h0 : prM V V' ι *ᵥ (fun j => X j i) = 0 := prM_mulVec_eq_zero (h i hi)
    change (adMat D.host.F (prM V V' ι)) *ᵥ ((adMat D.host.F X)ᵀ i) = 0
    have h1 : (adMat D.host.F X)ᵀ i = fun j => inclR (F := D.host.F) (AF D.host.F) (X j i) := rfl
    rw [h1]
    funext k
    have h2 := congrArg (inclR (F := D.host.F) (AF D.host.F)) (congrFun h0 k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h2
    simpa [Matrix.mulVec, dotProduct] using h2
  exact hle hz

theorem frameMat_mem_colPerp
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    (y : Fin V'.rank → AF D.host.F ⊗[D.host.F] D.host.E) :
    (adMat D.host.F (frameMat V V' ι)) *ᵥ y ∈ colPerp D.sp.cm.sig V.gram X (upTo T) := by
  have h0 : ∀ i ∈ upTo T, ∀ l, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * frameMat V V' ι) i l = 0 := by
    intro i hi l
    have h2 := h i hi (V'.frame l)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [colPerp, Submodule.mem_iInf]
  intro i hi
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply]
  rw [Matrix.mulVec_mulVec]
  have e : adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) * adMat D.host.F (frameMat V V' ι) =
      adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * frameMat V V' ι) := Matrix.map_mul.symm
  rw [e]
  simp [Matrix.mulVec, dotProduct, h0 i hi]

theorem prM_unip_frameMat (hι : HSpace.IsIsomEmb V' V ι)
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {a : GA D V} (ha : a ∈ unip D.sp.cm.sig V.gram X T) :
    adMat D.host.F (prM V V' ι) * (matHom V a).1 * adMat D.host.F (frameMat V V' ι) = 1 := by
  have hPI : adMat D.host.F (prM V V' ι) * adMat D.host.F (frameMat V V' ι) = 1 := by
    rw [← Matrix.map_mul, prM_mul_frameMat hι]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have h1 := ha.2.2 (adMat D.host.F (frameMat V V' ι) *ᵥ Pi.single j 1) (frameMat_mem_colPerp h _)
  have h2 := prM_kills_colSpan h h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec (Pi.single j 1) (adMat D.host.F (prM V V' ι)) (adMat D.host.F (frameMat V V' ι)),
    hPI, Matrix.one_mulVec, sub_eq_zero] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.one_mulVec]
  exact h2

theorem mt_eq_of_mem (hι : HSpace.IsIsomEmb V' V ι)
    (h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0)
    {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) {v : GA D V} {u : GA D V'}
    (hvu : v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) :
    (matHom V' u).1 = adMat D.host.F (prM V V' ι) * (matHom V v).1 * adMat D.host.F (frameMat V V' ι) := by
  have hv : v = (v * (s u)⁻¹) * s u := by group
  have h1 : (matHom V v).1 = (matHom V (v * (s u)⁻¹)).1 * (matHom V (s u)).1 := by
    conv_lhs => rw [hv]
    exact congrArg Units.val (map_mul (matHom V) _ _)
  have h2 : (matHom V (s u)).1 * adMat D.host.F (frameMat V V' ι) = adMat D.host.F (frameMat V V' ι) * (matHom V' u).1 := (hs u).1
  rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    prM_unip_frameMat hι h hvu, Matrix.one_mul]

theorem exists_proj : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (N : Subgroup (GA D V)) (N₁ : Subgroup (GA D V')), (∀ p ∈ N, ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → (∀ v ∈ N, ∃ u ∈ N₁, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → ∃ π : N →* N₁, Continuous π ∧ (∀ (v : N) (u : N₁), π v = u ↔ (v : GA D V) * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) ∧ ∀ v : N, (v : GA D V) ∈ GQ V → (π v : GA D V') ∈ GQ V' := by
  intro D V m X Y hW T V' ι hι hr s hs N N₁ hN hcov
  have h : ∀ i ∈ upTo T, ∀ v' : V'.V, V.hT (V.frame.equivFun.symm fun j => X j i) (ι v') = 0 :=
    fun i hi v' => ((hr (ι v')).1 ⟨v', rfl⟩ i hi).1
  have uniq : ∀ (v : GA D V) (u u' : GA D V'), v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T →
      v * (s u')⁻¹ ∈ unip D.sp.cm.sig V.gram X T → u = u' := fun v u u' h1 h2 =>
    GlobalTheory.MixModel.mt_injective V' ((mt_eq_of_mem hι h hs h1).trans (mt_eq_of_mem hι h hs h2).symm)
  choose f hf1 hf2 using hcov
  let π : N →* N₁ := MonoidHom.mk' (fun v => ⟨f v.1 v.2, hf1 v.1 v.2⟩) fun a b => by
    apply Subtype.ext
    refine uniq (a.1 * b.1) _ _ (hf2 _ (a * b).2) ?_
    have e : a.1 * b.1 * (s (f a.1 a.2 * f b.1 b.2))⁻¹ =
        (a.1 * (b.1 * (s (f b.1 b.2))⁻¹) * a.1⁻¹) * (a.1 * (s (f a.1 a.2))⁻¹) := by
      rw [map_mul]; group
    change a.1 * b.1 * (s (f a.1 a.2 * f b.1 b.2))⁻¹ ∈ unip D.sp.cm.sig V.gram X T
    rw [e]
    exact mul_mem (hN a.1 a.2 _ (hf2 _ b.2)) (hf2 _ a.2)
  have hmat : ∀ v : N, (matHom V' (π v : GA D V')).1 =
      adMat D.host.F (prM V V' ι) * (matHom V (v : GA D V)).1 * adMat D.host.F (frameMat V V' ι) := fun v =>
    mt_eq_of_mem hι h hs (hf2 v.1 v.2)
  refine ⟨π, ?_, fun v u => ⟨fun e => e ▸ hf2 v.1 v.2, fun e => Subtype.ext (uniq v.1 _ _ (hf2 v.1 v.2) e)⟩, ?_⟩
  · refine Continuous.subtype_mk (GlobalTheory.MixModel.continuous_of_mt V' ?_) _
    haveI := (ring_facts (F := D.host.F) (E := D.host.E)).1
    have hm : Continuous fun v : N => (matHom V (v : GA D V)).1 :=
      (GlobalTheory.MixModel.continuous_mt V).comp continuous_subtype_val
    exact ((continuous_const.matrix_mul hm).matrix_mul continuous_const).congr fun v => (hmat v).symm
  · intro v hv
    refine (GlobalTheory.MixModel.mem_GQ_iff V' _).2 ?_
    refine (congrArg (· ∈ GlobalTheory.MixModel.ratMx D V'.rank V'.rank) (hmat v)).mpr ?_
    exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem _) ((GlobalTheory.MixModel.mem_GQ_iff V _).1 hv))
      (GlobalTheory.MixModel.rat_mem _)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormChangeOfBasisLieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_automorphic_invariance : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (N : Subgroup (GA D V)) (N₁ : Subgroup (GA D V')), (∀ p ∈ N, ∀ a ∈ unip D.sp.cm.sig V.gram X T, p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → (∀ v ∈ N, ∃ u ∈ N₁, v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) → ∃ π : N →* N₁, Continuous π ∧ (∀ (v : N) (u : N₁), π v = u ↔ (v : GA D V) * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T) ∧ ∀ v : N, (v : GA D V) ∈ GQ V → (π v : GA D V') ∈ GQ V' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPart
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev adV {n : ℕ} (v : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (v i)

theorem adMat_mulVec {a c : ℕ} (M : Matrix (Fin a) (Fin c) E) (v : Fin c → E) :
    adMat F M *ᵥ adV (F := F) v = adV (F := F) (M *ᵥ v) :=
  funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem core (σ : E →ₐ[F] E) {n n' r r' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {X : Matrix (Fin n) (Fin r) E} {X' Y' : Matrix (Fin n') (Fin r') E} {T : Finset (Fin r)} {e : Fin r' → Fin r}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E}
    (hmono : StrictMono e) (hrange : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPI : P * I = 1)
    (hg : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    (hPl : ∀ l ∈ upTo T, P *ᵥ Xᵀ l = 0)
    (hperp : ∀ x, ∀ l ∈ upTo T, ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0)
    (hW' : IsWittFrame σ J' X' Y') (k : Fin r') (g : GAd σ J) (b : GAd σ J')
    (hmat : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    (hgm : g ∈ unip σ J X (insert (e k) T)) : b ∈ unip σ J' X' {k} := by
  obtain ⟨M, hM⟩ : ∃ M, M = (matHom _ σ J' b).1 - 1 := ⟨_, rfl⟩
  rw [← hM] at hmat
  have hPI' : adMat F P * adMat F I = 1 := by
    rw [← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPIv : ∀ w, adMat F P *ᵥ (adMat F I *ᵥ w) = w := fun w => by rw [mulVec_mulVec, hPI', one_mulVec]
  have hGv : ∀ w, (matHom _ σ J g).1 *ᵥ (adMat F I *ᵥ w) - adMat F I *ᵥ w = adMat F I *ᵥ (M *ᵥ w) := fun w => by
    rw [hmat, Matrix.add_mulVec, one_mulVec, add_sub_cancel_left, ← Matrix.mulVec_mulVec, hPIv, ← Matrix.mulVec_mulVec]
  have hXe : ∀ i, (adMat F X)ᵀ (e i) = adMat F I *ᵥ (adMat F X')ᵀ i := fun i => by
    have h : adMat F I * adMat F X' = adMat F (X.submatrix id e) := by rw [← Matrix.map_mul, hIX]
    funext j
    exact (congrFun (congrFun h j) i).symm
  have hPX : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    change adMat F P *ᵥ adV (F := F) (Xᵀ l) = 0
    rw [adMat_mulVec, hPl l hl]
    funext i
    exact map_zero _
  have hPspan : ∀ (A : Set (Fin r)) (N : Submodule (AF F ⊗[F] E) (Fin n' → AF F ⊗[F] E)),
      (∀ i ∈ A, adMat F P *ᵥ (adMat F X)ᵀ i ∈ N) → ∀ y ∈ colSpan F X A, adMat F P *ᵥ y ∈ N := fun A N h y hy => by
    have h1 : colSpan F X A ≤ N.comap (adMat F P).mulVecLin :=
      Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact h i hi)
    exact h1 hy
  have ha : ∀ i : Fin r', i ≤ k → M *ᵥ (adMat F X')ᵀ i = 0 := fun i hi => by
    have h1 := (Subgroup.mem_iInf.1 hgm.1 (e i)).2 ((adMat F X)ᵀ (e i)) (Submodule.subset_span ⟨e i, rfl, rfl⟩)
    rw [hXe, hGv] at h1
    have h2 := hPspan _ ⊥ (fun l hl => by
      obtain ⟨k', hk', hlk, hkj⟩ := hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact absurd hkj (not_lt.2 (hmono.monotone hi))
      · exact (Submodule.mem_bot _).2 (hPX l ⟨k', h, hlk⟩)) _ h1
    rw [hPIv] at h2
    exact (Submodule.mem_bot _).1 h2
  have hfix : M * adMat F (initCols X' k) = 0 := Matrix.ext_col fun i =>
    ha (i.castLE k.2) (Nat.le_of_lt_succ i.2)
  have c1 : ∀ {a c : ℕ} (Z : Matrix (Fin a) (Fin c) E), Formalism.UG.cT (sigR (AF F) σ) (adMat F Z) = adMat F (Formalism.UG.cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have fix : (matHom _ σ J' b).1 * adMat F (initCols X' k) = adMat F (initCols X' k) := by
    rw [hM, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hfix
    exact hfix
  rw [unip_singleton hW' k]
  apply Subgroup.subset_closure
  refine ⟨hM ▸ hfix, ?_, fun x hx => ?_⟩
  · have hu : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J' b).1 * adMat F J' * (matHom _ σ J' b).1 = adMat F J' := b.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, adMat, Matrix.map_mul]
    change adMat F _ * adMat F J' * _ = adMat F _ * adMat F J'
    conv_lhs => rw [← c1, ← fix, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J'), hu, c1]
  · have h5 : Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I = Formalism.UG.cT (σ : E →+* E) X' * J' := by
      rw [← hIX, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, hg, Matrix.mul_assoc, hPI,
        Matrix.mul_one]
    have hle : ∀ l, l ∉ upTo T → (∃ k' ∈ insert (e k) T, l ≤ k') → ∃ i, i ≤ k ∧ e i = l := fun l hl ⟨k', hk', hlk⟩ => by
      obtain ⟨i, rfl⟩ := (hrange l).1 hl
      rcases Finset.mem_insert.1 hk' with rfl | h
      · exact ⟨i, hmono.le_iff_le.1 hlk, rfl⟩
      · exact absurd ⟨k', h, hlk⟩ hl
    have hz : ∀ l, (∃ k' ∈ insert (e k) T, l ≤ k') → ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (I *ᵥ x)) l = 0 := fun l hl => by
      by_cases h : l ∈ upTo T
      · exact hperp x l h
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [mulVec_mulVec]
        have h6 : ((Formalism.UG.cT (σ : E →+* E) X * J * I) *ᵥ x) (e i) = ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id e) * J * I) *ᵥ x) i := rfl
        rw [h6, h5]
        exact congrFun hx ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hp : adV (F := F) (I *ᵥ x) ∈ colPerp σ J X {i | ∃ k' ∈ insert (e k) T, i ≤ k'} := by
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro l hl
      change (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ adV (F := F) (I *ᵥ x)) l = 0
      rw [adMat_mulVec]
      change inclR (F := F) (AF F) _ = 0
      rw [hz l hl]
      exact map_zero _
    have h3 := hgm.2.2 _ hp
    rw [← adMat_mulVec, hGv] at h3
    have h4 := hPspan _ (colSpan F X' {i | i ≤ k}) (fun l hl => by
      by_cases h : l ∈ upTo T
      · rw [hPX l h]
        exact zero_mem _
      · obtain ⟨i, hi, rfl⟩ := hle l h hl
        rw [hXe, hPIv]
        exact Submodule.subset_span ⟨i, hi, rfl⟩) _ h3
    rw [hPIv] at h4
    obtain ⟨a, ha'⟩ := mem_colSpan_iff.1 h4
    exact ⟨a, by rw [← hM]; exact ha'.symm⟩

end Core

theorem mem_unip_of_image : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨hmono, hrange, hIX, -⟩ := hS
  refine core D.sp.cm.sig hmono hrange hIX (prM_mul_frameMat hι) cT_frameMat_mul_gram (fun l hl => ?_) (fun x l hl => ?_)
    hW' k (s b) b (mat_eq hι hs b) hb
  · exact prM_mulVec_eq_zero fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
  · have hv : ι (V'.frame.equivFun.symm x) = V.frame.equivFun.symm (frameMat V V' ι *ᵥ x) := by
      apply V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      have h := LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (V'.frame.equivFun.symm x)
      have h' : V'.frame.repr (V'.frame.equivFun.symm x) = x := funext fun i => repr_symm V' x i
      rw [h'] at h
      exact h.symm
    have h := ((hR (ι (V'.frame.equivFun.symm x))).1 ⟨_, rfl⟩ l hl).1
    rw [hv, hT_frame] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_) h
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviInfUnipotentLeHermitianPartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_constant_term_compatible : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b : GA D V', s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) → b ∈ unip D.sp.cm.sig V'.gram X' {k} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n n' : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) {m m' : ℕ}

theorem mulVec_col {R : Type} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (i : Fin c) : A *ᵥ Bᵀ i = (A * B)ᵀ i := by
  ext j
  rfl


omit [NumberField E] in
variable {σ J} in
theorem mem_iff_of_ptStab {A A' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {g : GAd σ J}
    (h : g ∈ ptStab σ J A) (hA : A' ≤ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A' ↔ (matHom _ σ J g).1 *ᵥ y ∈ A' := by
  refine ⟨fun hy => by rwa [h y (hA hy)], fun hy => ?_⟩
  have h1 := (inv_mem h) _ (hA hy)
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at h1
  rwa [h1]


omit [NumberField E] in
variable {σ J J'} in
theorem mem_unip_of_mat {T : Finset (Fin m)} {X : Matrix (Fin n) (Fin m) E} {X' : Matrix (Fin n') (Fin m') E}
    {I : Matrix (Fin n) (Fin n') E} {P : Matrix (Fin n') (Fin n) E} {e : Fin m' → Fin m}
    (he : StrictMono e) (hr : ∀ i, i ∉ upTo T ↔ i ∈ Set.range e)
    (hIX : I * X' = X.submatrix id e) (hPX : P * X.submatrix id e = X')
    (hPT : ∀ l ∈ upTo T, ∀ i, (P * X) i l = 0)
    (hG : Formalism.UG.cT (σ : E →+* E) I * J = J' * P)
    {g : GAd σ J} {b : GAd σ J'}
    (hg : (matHom _ σ J g).1 = 1 + adMat F I * ((matHom _ σ J' b).1 - 1) * adMat F P)
    {k : Fin m'} (hb : b ∈ unip σ J' X' {k}) : g ∈ unip σ J X (insert (e k) T) := by
  classical
  have c0 : ∀ {a c d : ℕ} (U : Matrix (Fin a) (Fin c) E) (W : Matrix (Fin c) (Fin d) E),
      adMat F U * adMat F W = adMat F (U * W) := fun U W => (Matrix.map_mul ..).symm
  have dM : ∀ y, (matHom _ σ J g).1 *ᵥ y - y =
      adMat F I *ᵥ ((matHom _ σ J' b).1 *ᵥ (adMat F P *ᵥ y) - adMat F P *ᵥ y) := fun y => by
    rw [hg, add_mulVec, one_mulVec, add_sub_cancel_left, ← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  have pe : ∀ i, adMat F P *ᵥ (adMat F X)ᵀ (e i) = (adMat F X')ᵀ i := fun i => by
    rw [mulVec_col, c0]
    conv_rhs => rw [← hPX]
    rfl
  have ie : ∀ i, adMat F I *ᵥ (adMat F X')ᵀ i = (adMat F X)ᵀ (e i) := fun i => by
    rw [mulVec_col, c0, hIX]
    rfl
  have hz : ∀ l ∈ upTo T, adMat F P *ᵥ (adMat F X)ᵀ l = 0 := fun l hl => by
    rw [mulVec_col, c0]
    ext i
    change inclR (F := F) (AF F) ((P * X) i l) = 0
    rw [hPT l hl i, map_zero]
  have ip : ∀ (S : Set (Fin m')) y, y ∈ colSpan F X' S → adMat F I *ᵥ y ∈ colSpan F X (e '' S) := fun S y hy => by
    refine (Submodule.span_le (p := (colSpan F X (e '' S)).comap (adMat F I).mulVecLin)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    change adMat F I *ᵥ _ ∈ colSpan F X (e '' S)
    rw [ie]
    exact Submodule.subset_span ⟨e i, ⟨i, hi, rfl⟩, rfl⟩
  have e0 : {i | ∃ k' ∈ ({k} : Finset (Fin m')), i ≤ k'} = {i | i ≤ k} := by simp
  have fixB : ∀ i ≤ k, (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ i = (adMat F X')ᵀ i := fun i hi => by
    have h := (Subgroup.mem_iInf.1 hb.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have e3 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < i} = ∅ := by
      ext l
      simpa using fun _ => hi
    rw [e3, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have spanB : ∀ j, k < j → (matHom _ σ J' b).1 *ᵥ (adMat F X')ᵀ j - (adMat F X')ᵀ j ∈ colSpan F X' {i | i ≤ k} :=
    fun j hj => by
      have h := (Subgroup.mem_iInf.1 hb.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
      have e2 : {l | ∃ k' ∈ ({k} : Finset (Fin m')), l ≤ k' ∧ k' < j} = {i | i ≤ k} := by simp [hj]
      rwa [e2] at h
  have perpB : ∀ w ∈ colPerp σ J' X' {i | i ≤ k}, (matHom _ σ J' b).1 *ᵥ w - w ∈ colSpan F X' {i | i ≤ k} := fun w hw => by
    have h := hb.2.2 w (by rwa [e0])
    rwa [e0] at h
  let A : Set (Fin m) := {i | ∃ k' ∈ insert (e k) T, i ≤ k'}
  have hup : ∀ i, i ∈ upTo T → i ∈ A := fun i ⟨t, ht, hi⟩ => ⟨t, Finset.mem_insert_of_mem ht, hi⟩
  have hA : ∀ i ∈ A, i ∈ upTo T ∨ ∃ i', i' ≤ k ∧ e i' = i := fun i ⟨t, ht, hi⟩ => by
    rcases Finset.mem_insert.1 ht with rfl | ht
    · by_cases h : i ∈ upTo T
      · exact Or.inl h
      · obtain ⟨i', rfl⟩ := (hr i).1 h
        exact Or.inr ⟨i', he.le_iff_le.1 hi, rfl⟩
    · exact Or.inl ⟨t, ht, hi⟩
  have fix : ∀ i ∈ A, (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i := fun i hi => by
    rw [← sub_eq_zero, dM]
    rcases hA i hi with h | ⟨i', h, rfl⟩
    · rw [hz i h, mulVec_zero, sub_zero, mulVec_zero]
    · rw [pe, fixB i' h, sub_self, mulVec_zero]
  have pt : g ∈ ptStab σ J (colSpan F X A) := fun y hy => by
    refine (Submodule.span_le (p := LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id)).2 ?_ hy
    rintro _ ⟨i, hi, rfl⟩
    exact fix i hi
  have pp : ∀ y ∈ colPerp σ J X A, adMat F P *ᵥ y ∈ colPerp σ J' X' {i | i ≤ k} := fun y hy => by
    simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
    intro i hi
    have h1 : Formalism.UG.cT (σ : E →+* E) X' * J' * P = (Formalism.UG.cT (σ : E →+* E) X * J).submatrix e id := by
      rw [Matrix.mul_assoc, ← hG, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hIX]
      rfl
    have h2 := hy (e i) ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩
    change (adMat F (Formalism.UG.cT (σ : E →+* E) X' * J') *ᵥ adMat F P *ᵥ y) i = 0
    rw [mulVec_mulVec, c0, h1]
    exact h2
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨mem_iff_of_ptStab pt ?_, fun y hy => ?_⟩,
    mem_iff_of_ptStab pt le_rfl, fun y hy => ?_⟩
  · exact Submodule.span_mono (Set.image_mono fun i ⟨k', h1, h2, _⟩ => ⟨k', h1, h2⟩)
  · suffices h : y ∈ (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin by
      rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec] at h
    refine (Submodule.span_le (p := (colSpan F X {i | ∃ k' ∈ insert (e k) T, i ≤ k' ∧ k' < j}).comap
      ((matHom _ σ J g).1 - 1).mulVecLin)).2 ?_ hy
    rintro _ ⟨j, rfl, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]
    by_cases hj : j ∈ A
    · rw [fix j hj, sub_self]
      exact zero_mem _
    · obtain ⟨j', rfl⟩ := (hr j).1 fun h => hj (hup j h)
      have hk : k < j' := lt_of_not_ge fun h => hj ⟨e k, Finset.mem_insert_self _ _, he.monotone h⟩
      rw [dM, pe]
      refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (spanB j' hk))
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi, he hk⟩
  · rw [dM]
    refine Submodule.span_mono (Set.image_mono ?_) (ip _ _ (perpB _ (pp y hy)))
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨e k, Finset.mem_insert_self _ _, he.monotone hi⟩

end Core

theorem unip_embed : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b ∈ unip D.sp.cm.sig V'.gram X' {k}, s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
  intro D V m X Y hW T V' ι hι hR m' e X' Y' hS hW' s hs k b hb
  obtain ⟨he, hr, hX, -⟩ := hS
  refine mem_unip_of_mat he hr hX ?_ ?_ cT_frameMat_mul_gram (mat_eq hι hs b) hb
  · rw [← hX, ← Matrix.mul_assoc, prM_mul_frameMat hι, Matrix.one_mul]
  · intro l hl i
    have h := prM_mulVec_eq_zero (V' := V') (ι := ι) (x := fun j => X j l) fun v' => ((hR (ι v')).1 ⟨v', rfl⟩ l hl).1
    exact congrFun h i

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedConstantTermCompatibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_cusp_constant_term_vanish : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ (m' : ℕ) (e : Fin m' → Fin m) (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.IsSliceFrame V V' ι X Y T e X' Y' → GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V'.gram X' Y' → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ k : Fin m', ∀ b ∈ unip D.sp.cm.sig V'.gram X' {k}, s b ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanish
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanish
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

theorem isIsoFrame_initCols {D : D7} {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (k : Fin m) : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := by
  have hf := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hli := GlobalTheory.CompanionTheory.UnipCocompact.linearIndependent_of_isWittFrame (GlobalTheory.SiegelSet.sigma_sigma hf.1) (hf.2 V) hW
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · exact hli.comp (Fin.castLE k.2) (Fin.castLE_injective k.2)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE k.2 a)) (Fin.castLE k.2 b)
    simpa [GlobalTheory.StdPar.initCols, Matrix.mul_apply, Formalism.UG.cT] using this

theorem isCuspFun_of_isConstAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  intro D V m X Y hW hmax f hl hc
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f := hl
  refine (GlobalTheory.Cusp.isCuspFun_iff hl').2 fun W hW' => ?_
  obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V W).1 hW'
  have hrm := hmax r C hC
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hC.1; omega⟩
  let k : Fin m := ⟨r', by omega⟩
  have hC0 : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := isIsoFrame_initCols hW k
  have hcc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := by
    rw [GlobalTheory.Cusp.NA_frameFlag hC0]
    exact (GlobalTheory.CuspDecay.Model.isClosed_NI V hC0).locallyCompactSpace
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram (GlobalTheory.StdPar.initCols X k) :=
    GlobalTheory.Cusp.NA_frameFlag hC0
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f 0 := by
    rw [e]
    exact GlobalTheory.UAut.isConstTerm_iff.1 ((GlobalTheory.StdPar.isConstAlong_singleton hW k).1 (hc k))
  have h2 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hl' g, MeasureTheory.Measure.real, b3]
    simp
  have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f = 0 := h2.unique hcc h1
  exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V (r' + 1) _ C hC0 hC f hl h0

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanishStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_function_of_constant_terms_vanish : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

theorem unip_split : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      ∀ p ∈ unip D.sp.cm.sig V.gram X T, ∃ u ∈ unip D.sp.cm.sig V.gram X S, ∃ l ∈ levi D.sp.cm.sig V.gram X Y S, p = u * l := by
  intro D V m X Y hW S T hST p hpT
  obtain ⟨hcm, hherm⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hherm V
  by_cases hS : S = ∅
  · subst hS
    exact ⟨1, one_mem _, p, by simp, by simp⟩
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ S, ∀ k ∈ S, k ≤ a := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hP := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T S a hST ha ha' hpT
  have hdec := (GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hcm _ V.gram hJ (a.val + 1) (initCols X a) (initCols Y a)
    (fun i => (S.filter fun k => k.val < i.val).card)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [initCols, initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]
        exact Matrix.submatrix_one _ (Fin.castLE_injective a.2))).1
  obtain ⟨u, hu, l, hl, rfl, -⟩ := hdec p hP
  have hflag := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW S (a.val + 1) a.2
    (fun i => ⟨fun h => ⟨a, ha, Nat.lt_succ_iff.1 h⟩, fun ⟨k, hk, hik⟩ =>
      Nat.lt_succ_iff.2 (le_trans hik (ha' k hk))⟩)
    (fun i => (S.filter fun k => k.val < i.val).card) (fun i => rfl)
  exact ⟨u, hflag.1 ▸ hu, l, hflag.2.1 ▸ hl, rfl⟩

theorem isCuspFun_slice : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → IsCuspFun V' fun h => ψ (s h * y) := by
  intro D θ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs ψ hψ y hy hyc
  obtain ⟨hcm, hJall⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJall V
  have hJ' := hJall V'
  obtain ⟨s₀, hs₀c, hs₀, hs₀Q⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have es : ∀ h, s h = s₀ h := fun h => (hs₀ h (s h)).1 (hs h)
  have hsc : Continuous s := by
    have : (s : GA D V' → GA D V) = s₀ := funext es
    rw [this]; exact hs₀c
  have hsQ : ∀ γ ∈ GQ V', s γ ∈ GQ V := fun γ hγ => es γ ▸ hs₀Q γ hγ
  obtain ⟨hup, hsurj, -⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hW T V' ι hι hr s hs
  have hψl : ∀ γ ∈ leftSub V X Y T, ∀ g, ψ (γ * g) = ψ g := hψ.1.1.left
  have hψc : Continuous ψ := hψ.1.1.cont
  have hfl : ∀ γ ∈ GQ V', ∀ g, (fun h => ψ (s h * y)) (γ * g) = (fun h => ψ (s h * y)) g := fun γ hγ g => by
    have h1 : s γ ∈ leftSub V X Y T := Subgroup.mem_sup_right ⟨hsQ γ hγ,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hup γ)⟩
    change ψ (s (γ * g) * y) = ψ (s g * y)
    rw [map_mul, mul_assoc, hψl _ h1]
  obtain ⟨m', e, X', Y', hsl, hW'⟩ := GlobalTheory.T.orthogonal_subspace_witt_frame_extension D V m X Y hW T V' ι hι hr
  refine GlobalTheory.T.cusp_function_of_constant_terms_vanish D V' m' X' Y' hW' (GlobalTheory.T.isotropic_frame_rank_le_witt_index D V' m' X' Y' hW') _ hfl fun k => ?_
  have hκ : e k ∉ upTo T := (hsl.2.1 _).2 ⟨k, rfl⟩
  have hκT : e k ∉ T := fun h => hκ ⟨_, h, le_rfl⟩
  have hTT' : T ⊂ insert (e k) T := Finset.ssubset_insert hκT
  have hψ0 := hψ.2 _ hTT'
  haveI := locallyCompact_unip hcm hJ' hW' {k}
  haveI := locallyCompact_unip hcm hJ hW (insert (e k) T)
  have hle := GlobalTheory.StdPar.unip_mono_of_subset _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW (insert (e k) T) T hTT'.1
  have hs1 := GlobalTheory.T.restricted_cusp_constant_term_vanish D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdown := GlobalTheory.T.restricted_constant_term_compatible D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdec : ∀ v ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∃ u ∈ unip D.sp.cm.sig V'.gram X' {k},
      v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun v hv => by
    obtain ⟨u, hu, l, hl, rfl⟩ := unip_split D V m X Y hW T _ hTT'.1 v hv
    have hl' : l ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
      simpa using mul_mem (inv_mem (hle hu)) hv
    obtain ⟨b, rfl⟩ := hsurj l (GlobalTheory.T.levi_inf_unipotent_le_hermitian_part D V m X Y hW T _ hκ ⟨hl, hl'⟩)
    exact ⟨b, hdown b hl', by simpa using hu⟩
  have hnorm : ∀ p ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∀ a ∈ unip D.sp.cm.sig V.gram X T,
      p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun p hp a ha =>
    conj_mem_unip_of_subset hcm hJ hW hTT'.1 hp ha
  obtain ⟨π, hπc, hπ, hπQ⟩ := GlobalTheory.T.restricted_automorphic_invariance D V m X Y hW T V' ι hι hr s hs _ _ hnorm hdec
  let s₁ : unip D.sp.cm.sig V'.gram X' {k} →* unip D.sp.cm.sig V.gram X (insert (e k) T) :=
    (s.comp (unip D.sp.cm.sig V'.gram X' {k}).subtype).codRestrict _ fun u => hs1 _ u.2
  have hs₁c : Continuous s₁ := (hsc.comp continuous_subtype_val).subtype_mk _
  have hπs : ∀ u, π (s₁ u) = u := fun u => (hπ _ _).2 (by
    change s u * (s u)⁻¹ ∈ _
    simp [one_mem])
  have hker : ∀ v, π v = 1 ↔ (v : GA D V) ∈ unip D.sp.cm.sig V.gram X T := fun v => by
    rw [hπ v 1]
    simp
  intro μ 𝓕 hμ h𝓕 h1 g
  have cN : GlobalTheory.Cusp.Cocompact (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) := cocompact_unip_std hcm hJ hW _
  have key := GlobalTheory.Cusp.constTermOn_eq_integral_semidirect (GA D V) (GA D V') (GQ V) _ _ (GQ V') _ hle cN
    (cocompact_unip_std hcm hJ hW T) (cocompact_unip_std hcm hJ' hW' {k}) s₁ π hs₁c hπc hπs hker
    (fun u hu => hsQ _ hu) (fun v hv => hπQ v hv) ψ hψc
    (fun a ha y => hψl a (Subgroup.mem_sup_left ha) y)
    (fun γ hγ hγ' y => hψl γ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, hγ'⟩) y) μ 𝓕 hμ h𝓕 h1 (s g * y)
  obtain ⟨μ₀, 𝓕₀, a1, a2, a3⟩ := exists_mass_one cN
  have hz := hψ0 μ₀ 𝓕₀ a1 a2 a3 (s g * y)
  have hct : GlobalTheory.Cusp.constTermOn (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) ψ (s g * y) = 0 := by
    haveI := a1
    have e1 := GlobalTheory.Cusp.Stages.constTermOn_eq' (Γ := GQ V) (φ := ψ) (x := s g * y) a2 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψl _ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, (γ : unip _ _ _ _).2⟩) _)
    rw [e1, ← hz]
    simp
  rw [hct] at key
  refine key.trans (MeasureTheory.integral_congr_ae (.of_forall fun u => ?_))
  change ψ (s u * (s g * y)) = ψ (s (u * g) * y)
  rw [map_mul, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
