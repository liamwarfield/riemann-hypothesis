module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem level_zero_inter_big_cell_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  unfold Q.FFl Q.SmoothLev Q.LeftEq Q.RightEq
  simp only [level_zero_inter_big_cell_eq]

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS in
theorem radial_operator_function_field : RDOpFF := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hSm hC J hJ
  rw [ffl_om_eq] at hJ ⊢
  have hDom : Q.IsDom k r D.z D.z' 0 (Q.OmPlus k r D.z D.z') :=
    Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus D.z_mem D.z'_mem
  have hPos : ∀ g ∈ Q.OmPlus k r D.z D.z', g ∈ B.GV k r → g ∈ B.GPos D := fun g hg hgG => ⟨hgG, hg.2⟩
  have hG' := germ_operators_holds k r Wp Wq Θ
  have hsupp : ∀ f' : B.Mat k r → (Wq →L[ℂ] Wp), tsupport f' ⊆ Q.OmPlus k r D.z D.z' →
      B.SuppIn (B.GPos D) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (by exact fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hC p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact adjoint_commutation_holds _ _ _ _ D Θ hSm hC f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutSE
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
open Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section heads

theorem ptDiag_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (a : Fin (D.ptSize h)) : D.ptDiag h a ≠ 0 :=
  Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt

theorem zxH_det_ne {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) (v : XH h) : (zxH h j hh.2 v).det ≠ 0 := by
  unfold zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (ptDiag_ne hh))

theorem cdOn_mat {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m n : Type} [Fintype m] [Fintype n]
    {f : X → Matrix m n ℂ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b

theorem cd_lowW_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (a b : Fin p) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => U.lowW σ v a b) := by
  unfold U.lowW
  simp only [Matrix.add_apply, Matrix.of_apply]
  refine contDiff_const.add ?_
  split_ifs
  · exact contDiff_apply ℝ (fun _ => ℂ) _
  · exact contDiff_const

theorem cd_zxH_entry (h : C.LPt) (j : ℕ) (hs : D.ptSize h = j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => zxH h j hs v a b) := by
  unfold zxH LeftFubiniLemmas.lhOf
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c' _ => ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun c'' _ => ContDiff.mul contDiff_const ?_
  exact cd_lowW_entry _ _ _

end heads

section curve

theorem cd_det {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) : ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => h (σ i) i)

theorem cd_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (M : X → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, ContDiff ℝ ∞ (fun x => M x a b)) (hd : ∀ x, (M x).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ ∞ (fun x => (M x)⁻¹ a b) := by
  have e : ∀ x, (M x)⁻¹ a b = ((M x).det)⁻¹ * (M x).adjugate a b := by
    intro x
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [e]
  refine ContDiff.mul ((cd_det M h).inv hd) ?_
  simp only [Matrix.adjugate_apply]
  refine cd_det _ fun c d => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact h _ _

theorem cd_zxHct_inv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin j) :
    ContDiff ℝ ∞ (fun v : XH h => ((zxH h j hh.2 v)ᴴ)⁻¹ a b) := by
  refine cd_inv_entry (fun v => (zxH h j hh.2 v)ᴴ) (fun c d => ?_) (fun v => ?_) a b
  · simp only [Matrix.conjTranspose_apply]
    exact Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp (cd_zxH_entry h j hh.2 d c)
  · rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (zxH_det_ne hh v)

end curve

section curve2

theorem cd_zfull_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiff ℝ ∞ (fun q : XH h × ℂ => zfull (zxH h j hh.2 q.1) q.2 a b) := by
  simp only [zfull_apply]
  split_ifs
  · exact (cd_zxH_entry h j hh.2 _ _).comp contDiff_fst
  · exact contDiff_snd
  · exact contDiff_const

theorem cdOn_zfullInv_entry (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (a b : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun q : XH h × ℂ => ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b) (Set.univ ×ˢ {τ | τ ≠ 0}) := by
  have e : ∀ q ∈ (Set.univ ×ˢ {τ : ℂ | τ ≠ 0} : Set (XH h × ℂ)),
      ((zfull (zxH h j hh.2 q.1) q.2)ᴴ)⁻¹ a b = zfull ((zxH h j hh.2 q.1)ᴴ)⁻¹ (star q.2)⁻¹ a b := by
    intro q hq
    rw [zfull_conjTranspose_inv (zxH_det_ne hh q.1) hq.2]
  refine ContDiffOn.congr ?_ e
  simp only [zfull_apply]
  split_ifs
  · exact ((cd_zxHct_inv_entry h j hh _ _).comp contDiff_fst).contDiffOn
  · intro q hq
    have hτ : star q.2 ≠ 0 := star_ne_zero.2 hq.2
    have h1 := (contDiffAt_inv ℂ (n := ∞) hτ).restrict_scalars ℝ
    exact (h1.comp q ((Formalism.FourierDecayAlt.P.PBG.contDiff_starC.comp contDiff_snd).contDiffAt)).contDiffWithinAt
  · exact contDiffOn_const

theorem curveSmooth : CurveSmooth := by
  intro k r j hj h hh γ
  refine cdOn_mat fun p' q' => ?_
  obtain ⟨P, rfl⟩ := cast_eB_surj (k := k) hj p'
  obtain ⟨Q, rfl⟩ := cast_eB_surj (k := k) hj q'
  simp only [level_point_eq_block_three, LeftFubiniLemmas.castM_apply', Fin.cast_cast, Fin.cast_eq_self, Ux3.block3_apply]
  rcases P with ((a | a) | a) <;> rcases Q with ((b | b) | b) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply] <;>
    first
    | exact contDiffOn_const
    | (simp only [Matrix.mul_apply]
       refine ContDiffOn.sum fun c _ => ?_
       first
       | exact (cdOn_zfullInv_entry h j hh _ _).mul contDiffOn_const
       | exact contDiffOn_const.mul (cd_zfull_entry h j hh _ _).contDiffOn)

end curve2

section pts

theorem dmin_mMap_hi {k J ρ : ℕ} (z z' : Fin (2 * (J + ρ) + k + 1) → ℂ) (hz : inWb k (J + ρ) z)
    (hz' : inWb k (J + ρ) z') (Z : Matrix (Fin J) (Fin J) ℂ) (γ : B.Mat k ρ) (l : ℕ) (hl : l ≤ ρ + 1) :
    Dmin k (J + ρ) z z' (U.mMap k J ρ Z γ) ⟨J + l, by omega⟩ =
      Z.det * Dmin k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ ⟨l, by omega⟩ := by
  have hZ : Zhat k (J + ρ) z z' (U.mMap k J ρ Z γ) =
      Matrix.reindex (Ux3.eC J ρ) (Ux3.eC J ρ)
        (Matrix.fromBlocks Z 0 0 (Zhat k ρ (U.lowV k J ρ z) (U.lowV k J ρ z') γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 z z' hz hz', Formalism.QuantumDeterminants.Zhat_eq]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  unfold Dmin
  rw [hZ]
  exact Ux3.minor_blocks _ _ l hl _

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem dmin_castM' {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (l : ℕ)
    (hl : l < b + 2) :
    Dmin k b z z' (D.castM e g) ⟨l, hl⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨l, by omega⟩ := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem lowV_base {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {k r : ℕ} (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r)
    (e : j + 1 + (r - (j + 1)) = r) :
    U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z) = (T.bs (j + 1)).z ∧
      U.lowV k (j + 1) (r - (j + 1)) (D.castV e.symm T.base.z') = (T.bs (j + 1)).z' := by
  unfold D.LevTower.base
  rw [← T.z_lev (j + 1) hj, ← T.z'_lev (j + 1) hj, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩
where
  castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
      D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
    subst h1 h2; rfl

theorem pts : Pts := by
  intro Wp Wq _ _ _ _ _ _ P p j hj h hh γ hγ hΩ v
  have hZ := zxH_det_ne hh v
  refine ⟨hZ, fun τ hτ => ?_⟩
  set Z := zxH h j hh.2 v
  have e : j + 1 + (P.r - (j + 1)) = P.r := by omega
  have hz := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
  have hz' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
  obtain ⟨hl1, hl2⟩ := lowV_base p.T j hj e
  have hdf : (zfull Z τ).det ≠ 0 := by rw [zfull_det]; exact mul_ne_zero hZ hτ
  have hx : x0 P.k P.r j hj Z τ γ = D.castM e (U.mMap P.k (j + 1) (P.r - (j + 1)) (zfull Z τ) γ) := rfl
  refine ⟨fun l hl1' hl2' => ?_, ?_⟩
  · by_cases hlj : l.val = j
    · have := (Formalism.FourierDecayAlt.P.CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' Z τ γ hZ hτ hγ).1
      have hl : l = ⟨j, by omega⟩ := Fin.ext hlj
      rw [hl, this]; exact hZ
    · obtain ⟨l', hl'⟩ : ∃ l', l.val = j + 1 + l' := ⟨l.val - (j + 1), by omega⟩
      have hl : l = ⟨j + 1 + l', by omega⟩ := Fin.ext hl'
      rw [hl, hx, dmin_castM' e, dmin_mMap_hi _ _ hz hz' _ _ l' (by omega), hl1, hl2]
      refine mul_ne_zero hdf ?_
      exact hΩ.1 ⟨l', by omega⟩ (by simp; omega)
  · rw [hx, gf_castM e]
    have hG := Formalism.FourierDecayAlt.P.level_function_slice P.k (j + 1) (P.r - (j + 1)) _ _ hz hz' 0 0 (zfull Z τ) γ
    rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG
    rw [hG, hl1, hl2]
    exact mul_pos (Complex.normSq_pos.2 hdf) hΩ.2

end pts

section head

theorem leading_block_of_base_point {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (e : r = j + (r - j)) : U.Zh k j (r - j) (D.castM e (x0 k r j hj Z τ γ)) = Z := by
  ext a b
  unfold U.Zh x0
  rw [LeftFubiniLemmas.castM_apply', LeftFubiniLemmas.castM_apply']
  simp only [Fin.cast_cast]
  have key : ∀ q : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1), q.val = 2 * (j + (r - j)) + k - a.val →
      q = U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    intro q hq; ext; rw [Ux3.block_index_last_val]; simp only [Fin.val_mk]; omega
  rw [key (Fin.cast _ _) (by simp), LeftFubiniLemmas.embedding_map_apply_last_block, dite_eq_left (by simp only [Fin.val_cast]; omega), zfull_apply,
    dite_eq_left (by simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk]; omega)]
  congr 1 <;> ext <;> simp only [Fin.val_rev, Fin.val_cast, Fin.val_mk] <;> omega

end head

end Formalism.FourierDecayAlt.P.CutHB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateTopBound
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem germ_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vec : C.LPt → H) (b s : ℕ) (hs : 2 ≤ s) (hbs : b + s - 1 = S.G.r + 1) (h : C.LPt)
    (x D : ℂ) (hD : D ≠ 0) :
    utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
        mainD s (betaL S) 1 (fun z => (fun _ => (1 : ℂ)) z • btOf s (KB.dlB S b s) Vec h z) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s D), coJ S b s x j • Vec (ptJ s h x D j) := by
  rw [Finset.sum_insertNone, hbs, sub_eq_add_neg]
  have hz : ∀ z ∈ G.rootSet s D, z ≠ 0 := by
    intro z hz h0
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [h0, zero_pow (by omega)] at hz
    exact hD hz.symm
  congr 1
  · simp only [utOf, vOf, ptX, coJ, ptJ, smul_smul, List.append_assoc, List.singleton_append]
    push_cast
    rfl
  · unfold mainD
    rw [one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hzm => ?_
    simp only [btOf, if_neg (hz z hzm), one_smul, coJ, ptJ, smul_smul, neg_smul, one_mul]

end

end Formalism.FourierDecayAlt.P.GermRateSplit

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Formalism.FourierDecayAlt.P.GermRateSplit Finset
open scoped ComplexConjugate InnerProductSpace

theorem germ_rate_top_bound : Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB := by
  intro hA Cb
  obtain ⟨c1, hc1⟩ := GermFibreKernels.cutSeq_cpt Cb
  refine ⟨c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hF := hc1 c1 le_rfl E Wp Wq S p f χ A₀ hB n
  intro ε hε b s hb hs hbs a ha H _ _ _ Vec hVec
  refine ⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩
  intro h hsz K hK hK0
  have hbs' : b + s = S.G.r + 2 := hbs
  have hb1 : b + s - 1 = S.G.r + 1 := by omega
  obtain ⟨I, hI, c, Fi, L, hc, hFi, hgram⟩ :=
    gN_top_gram hB (PBASM.cutSeq S p f χ n) (fun v ε hε => hF v ε hε) v ε hε a ha
  choose Ci hCi using fun i => top_core hB v (Fi i) (hFi i) a.length b s hb hs hbs' h hsz K hK hK0
  refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  rw [germ_sum (PBL.setC S p (PBASM.cutSeq S p f χ n)) Vec b s hs hb1 h x D hD0]
  have hk : ∀ j ∈ Finset.insertNone (G.rootSet s D), ∀ l ∈ Finset.insertNone (G.rootSet s D),
      KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a (ptJ s h x D j) (ptJ s h x D l) =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length (ptJ s h x D l) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D l))),
          (omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))⟫_ℂ := by
    intro j _ l _
    rw [hb1]
    exact hgram _ _
  have h2 := norm_sum_le_of_gram (fun P Q => KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a P Q)
    Vec hVec c hc (fun i P => (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P)))
    (Finset.insertNone (G.rootSet s D)) (ptJ s h x D) hk (coJ S b s x)
  refine h2.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∑ j ∈ Finset.insertNone (G.rootSet s D), conj (coJ S b s x j) •
        ((omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))) =
      L i (∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) •
        (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul]
  rw [e]
  have h3 := hCi i x hx D hD
  have hsq := Real.sqrt_nonneg (c i)
  calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))‖
      ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
    _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
    _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rdb_glev0_inter_om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem rdb_ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  simp only [Q.FFl, Q.SmoothLev, Q.LeftEq, Q.RightEq, rdb_glev0_inter_om]

private theorem conjTranspose_mul_H_mul_preserved_of_preserved {n : ℕ} (H a b : Matrix (Fin n) (Fin n) ℂ)
    (ha : a.conjTranspose * H * a = H) (hb : b.conjTranspose * H * b = H) :
    (a * b).conjTranspose * H * (a * b) = H := by
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * H * (a * b)
      = b.conjTranspose * (a.conjTranspose * H * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [ha, hb]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem radial_residue_formula : RDResRad := by
  classical
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD J hJ
  have hz := hD.1.2.1
  have hz' := hD.1.2.2.1
  rw [rdb_ffl_om_eq] at hJ
  obtain ⟨hS, -, -, hE⟩ := hJ
  have huh : ∀ a b : Mx P.k P.r, a ∈ UH (Hpk P.k P.r) → b ∈ UH (Hpk P.k P.r) →
      a * b ∈ UH (Hpk P.k P.r) :=
    fun a b ha hb => conjTranspose_mul_H_mul_preserved_of_preserved _ a b ha hb
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c ∈ UH (Hpk P.k P.r) := by
    intro c hc
    refine List.prod_induction _ huh ?_ ?_
    · show (1 : Mx P.k P.r).conjTranspose * Hpk P.k P.r * 1 = Hpk P.k P.r
      simp
    · intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact Qx3.weyl_cell_mem_unitary a (hc a)
  have hcomm : ∀ (c : Fin P.r → ℂ) (h : Mx P.k P.r), h ∈ UWset P.k P.r z →
      Commute (wCell P.k P.r (Fin.last P.r) c) h := by
    intro c h hh
    refine Commute.list_prod_left _ _ ?_
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact Qx3.w1_commute_of_mem_Glev a (c a) ⟨hh.1, fun b _ => hh.2.1 b⟩
  have hin : ∀ x ∈ DomR P.k P.r z z',
      wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Glev P.k P.r 0 ∩ OmPlus P.k P.r z z' :=
    fun x hx => ⟨Rad.glev0 (huh _ _ (hcell _ hx.1) hx.2.1.1),
      Rad.wCell_mem_omPlus hz hz' hx.1 hx.2.1 hx.2.2⟩
  let Φ0 : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR P.k P.r z z' then resG P.k P.r (Fin.last P.r) J c g else 0
  have hmem : Φ0 ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact if_neg hx
    · intro x₀ hx₀
      obtain ⟨U, F, hU, hxU, hF, hag⟩ :=
        Rad.sf_resG hS x₀ ⟨hx₀.1, (hin x₀ hx₀).2⟩ hx₀.2.1
      refine ⟨U ∩ (Prod.fst ⁻¹' OmX P.r ∩ Prod.snd ⁻¹' {g | 0 < GGl P.k P.r z z' g}), F,
        hU.inter (((Qx3.isOpen_OmX _).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((Qx5.GGl_continuous _ _ _ _).comp continuous_snd))),
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hF.mono Set.inter_subset_left, ?_⟩
      intro x hx hg
      have hxD : x ∈ DomR P.k P.r z z' := ⟨hx.2.1, hg, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
      rw [if_pos hxD]
      exact hag x hx.1 hg
    · intro x hx h hh h' hh'
      have hx' := Rad.domR_uw hx hh hh'
      show (if (x.1, h * x.2 * h') ∈ DomR P.k P.r z z' then _ else _) =
        π h ∘SL (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) ∘SL π' h'
      rw [if_pos hx', if_pos hx]
      simp only [resG]
      rw [show wCell P.k P.r (Fin.last P.r) x.1 * (h * x.2 * h') =
          h * (wCell P.k P.r (Fin.last P.r) x.1 * x.2) * h' by
        simp only [← mul_assoc, (hcomm x.1 h hh).eq]]
      rw [hE _ (hin x hx) h hh h' hh']
      simp [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨⟨Φ0, hmem⟩, fun x hx => ?_⟩
  show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
  rw [if_pos hx]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_group_residue : RDGqRes := by
  intro k r Wp Wq _ _ _ _ _ _ D q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hsec := (D.sec.2 q.2 hq2).1
  have hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r :=
    TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec
  have hv := TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2
  refine ⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩
  · refine ⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩
    show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'
    have hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2 := by
      unfold zetaL fvec
      simpa using hv.2.2
    rw [hz]
    linarith
  · refine ⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      split_ifs
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))
      · exact one_ne_zero
    · intro J _
      have hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q := by
        rw [Rad.wCell_last_eq]
        exact ((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm
      unfold resG
      rw [hcell]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntegralJacobianFactor
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section fubini

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def psiH {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : ℂ := G.psi U.betaU (U.subS (lhOf σ v))

theorem volume_empty_blocks_real (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

def regroup (σ : Equiv.Perm (Fin p)) :
    XL k p ρ σ ≃ᵐ PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ) :=
  MeasurableEquiv.prodAssoc.symm

theorem regroup_apply (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : regroup σ x = ((x.1, x.2.1), x.2.2) := rfl

theorem regroup_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (regroup σ) (muL Bj σ)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  exact (measurePreserving_prodAssoc (Bj.μW.prod Bj.μN) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))).symm

def fH (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ)
    (q : PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) : Wq →L[ℂ] Wp :=
  psiH σ q.2.2 • PBQ.pbI Bj B0 rfl H (U.mMap k p ρ (lhOf σ q.2.2 * U.hMat σ d) g) q.1

theorem ellL_eq (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) = fH Bj B0 σ d H g (regroup σ x) := by
  have hP : PBQ.GoodP Bj (x.1, x.2.1) := hx
  have hs : sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g =
      D.castM rfl (PBQ.sP Bj (x.1, x.2.1)) * U.mMap k p ρ (lhOf σ x.2.2.2 * U.hMat σ d) g := by
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, sxL, if_pos hx, PBQ.sP, if_pos hP]
    have e := embedding_map_lower_unipotent k p ρ (lhOf σ x.2.2.2) (U.hMat σ d) 1 g (lh_unit σ x.2.2.2)
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.mul_one] at e
    rw [e]
    have e2 := embedded_group_measure_preserving k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
      ((lhOf σ x.2.2.2)ᴴ⁻¹)
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← Matrix.mul_assoc (U.muP k p ρ _) (U.embG k p ρ _), ← e2, Matrix.mul_assoc]
  rw [hs, regroup_apply]
  unfold fH ellL PBQ.pbI cL PBQ.cP psiH
  simp only [_root_.smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceInt (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g) := by
  obtain ⟨hint, hJ⟩ := core_lf hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hsf : SigmaFinite (PBQ.muXP (p := p) Bj) := by unfold PBQ.muXP; infer_instance
  have hae : (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) =ᵐ[muL Bj σ]
      fun x => fH Bj B0 σ d H g (regroup σ x) := by
    filter_upwards [ae_goodL Bj σ] with x hx
    exact ellL_eq Bj B0 σ d H g x hx
  have mp := regroup_mp Bj σ
  have hint2 : Integrable (fH Bj B0 σ d H g)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) :=
    (mp.integrable_comp_emb (regroup σ).measurableEmbedding).1 ((hint.congr hae))
  have hJ2 : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, fH Bj B0 σ d H g q ∂((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) ×
        (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))) := by
    rw [hJ, integral_congr_ae hae, mp.integral_comp' (fH Bj B0 σ d H g)]
  have hin : ∀ c : ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ),
      ∫ xP, fH Bj B0 σ d H g (xP, c) ∂(PBQ.muXP Bj) =
        psiH σ c.2 • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ c.2 * U.hMat σ d) g) := by
    intro c
    unfold fH PBQ.pbF
    exact integral_smul (psiH σ c.2) _
  have hR1 := hint2.integral_prod_right
  simp only [hin] at hR1
  have hR2 := hR1.integral_prod_right
  simp only [integral_const, volume_empty_blocks_real, one_smul] at hR2
  refine ⟨hR2, ?_⟩
  rw [hJ2, integral_prod_symm _ hint2]
  simp only [hin]
  rw [integral_fun_snd (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)),
    volume_empty_blocks_real, one_smul]

end fubini

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem slice_integral_jacobian_factor {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ,
          G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g) :=
  SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR

end Formalism.FourierDecayAlt.P
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

def ProperLeftVariablesDomain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (PBQ.domP P.k P.r j p.T.base.z p.T.base.z')

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceIntN (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + ρ) ∧ Dmin k (p + ρ) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    ext x
    show _ ∧ _ ↔ _ ∧ _
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p ρ B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := hset ▸ hHc
  have h := (Formalism.FourierDecayAlt.P.slice_integral_jacobian_factor hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR).2
  have hF : D.castF (rfl : p + ρ = p + ρ) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + ρ) + k + 1) → ℂ, D.castV (rfl : p + ρ = p + ρ).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end gen

section pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slice_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (H : B.Mat k r → E) (a : C.LPt) (hle : D.ptSize a ≤ r)
    (h2 : r - D.ptSize a = r - D.ptSize a) (e : D.ptSize a + (r - D.ptSize a) = r) :
    D.castF h2 (D.sliceAt k r z z' H a) =
      U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm z) (D.castV e.symm z')
        (D.castF e H) (fun a => a.elim0) := by
  funext y
  unfold D.castF
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dite_eq_left hle]
  rfl

theorem mMap_castM {k j a b : ℕ} (h : a = b) (Z : Matrix (Fin j) (Fin j) ℂ) (g : B.Mat k a) :
    U.mMap k j b Z (D.castM h g) = D.castM (by omega : j + a = j + b) (U.mMap k j a Z g) := by
  subst h
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem pt_eq {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det) (τ : ℂ) (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (e0 : j + (r - j) = r) (h1 : 1 + (r - (j + 1)) = r - j) :
    D.castM e0 (U.mMap k j (r - j) Z (D.castM h1 (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ))) =
      LevelPointCoordinates.x0 k r j hj Z τ γ := by
  rw [mMap_castM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.zfull
  have hM : D.castM (Formalism.FourierDecayAlt.P.PBH.hs' k j (r - (j + 1)))
      (U.mMap k j (1 + (r - (j + 1))) Z (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ)) =
      U.mMap k (j + 1) (r - (j + 1)) (U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)) γ :=
    Formalism.FourierDecayAlt.P.PBH.M2 (k := k) (ρ := r - (j + 1)) Z hZ τ hτ γ
  rw [← hM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]

end pt

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end
