module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

section Alg
variable {k : Type} [CommRing k] {r : ℕ}

def e1 : Fin r → k := fun i => if (i : ℕ) = 0 then 1 else 0

theorem companionMatrixOfCoeffs_pow_mulVec_firstBasisVector (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  | 0, hj => by
    ext i; simp [e1, Pi.single_apply, Fin.ext_iff]
  | j + 1, hj => by
    rw [pow_succ', ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector p j (by omega), Matrix.mulVec_single_one]
    funext i
    have hj' : j + 1 ≠ r := Nat.ne_of_lt hj
    simp [Matrix.col_apply, companion, Pi.single_apply, Fin.ext_iff, hj']

theorem mom_sec_add (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by
  have h1 : mom (sec a) (n + j) = a.2.1 ⬝ᵥ ((companion a.1 ^ n) *ᵥ ((companion a.1 ^ (j : ℕ)) *ᵥ e1)) := by
    simp only [mom, sec, pow_add, ← mulVec_mulVec]; rfl
  rw [h1, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector a.1 j j.2, dotProduct_mulVec, dotProduct_single_one]

theorem hankel_apply' (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j :=
  mom_sec_add a i j

theorem hankel_isSymm (a : Inv r k) : (hankel a).IsSymm := by
  ext i j; simp [hankel, add_comm]

def hankelShift (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ) + 1)

theorem hankelShift_isSymm (a : Inv r k) : (hankelShift a).IsSymm := by
  ext i j; simp [hankelShift]; ring_nf

theorem hankel_mul_companion (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by
  ext i j
  have h2 : hankelShift a i j = mom (sec a) (((i : ℕ) + 1) + j) := by simp [hankelShift]; ring_nf
  rw [h2, mom_sec_add, Matrix.mul_apply, pow_succ, ← Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul, dotProduct, hankel_apply']

theorem companion_map {k' : Type} [CommRing k'] (φ : k →+* k') (p : Fin r → k) :
    (companion p).map φ = companion (fun i => φ (p i)) := by
  ext i j; simp only [companion, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

end Alg

section Herm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem map_isSelfAdjoint {N : Matrix (Fin r) (Fin r) F} (hN : N.IsSymm) :
    IsSelfAdjoint (N.map (algebraMap F E)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply, Unram.star_fix, hN.apply i j]

theorem conjTranspose_map (N : Matrix (Fin r) (Fin r) F) :
    (N.map (algebraMap F E))ᴴ = Nᵀ.map (algebraMap F E) := by
  ext i j; simp [Matrix.conjTranspose_apply, Unram.star_fix]

def mkX (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : Hn r F E :=
  (⟨star h⁻¹ * (hankelShift a).map (algebraMap F E) * h⁻¹, by
      have h1 := (map_isSelfAdjoint (E := E) (hankelShift_isSymm a)).conjugate (star h⁻¹)
      rw [star_star] at h1
      exact h1⟩, h *ᵥ e1, a.2.2)

theorem mkX_snd_fst (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := rfl

variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}

theorem mkX_fst (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    (mkX a h).1.1 = h * (companion a.1).map (algebraMap F E) * h⁻¹ := by
  have hd' : IsUnit hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  simp only [mkX]
  rw [← hankel_mul_companion, Matrix.map_mul, ← hh, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]

theorem pow_mulVec_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    ((mkX a h).1.1 ^ (j : ℕ)) *ᵥ (h *ᵥ e1) = h *ᵥ Pi.single j 1 := by
  rw [mkX_fst hh hd]
  have key : ∀ n : ℕ, (h * (companion a.1).map (algebraMap F E) * h⁻¹) ^ n =
      h * ((companion a.1).map (algebraMap F E)) ^ n * h⁻¹ := by
    intro n; induction n with
    | zero => simp [Matrix.mul_nonsing_inv _ hd]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [key, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    companion_map, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector _ j j.2]

theorem bm_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by
  ext i j
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.mulVec_single_one]; rfl

theorem mom_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    mom (mkX a h).toGl j = algebraMap F E (a.2.1 j) := by
  have h0 : 0 < r := j.pos
  simp only [mom, Hn.toGl]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh]
  have he : star (e1 : Fin r → E) = Pi.single (⟨0, h0⟩ : Fin r) 1 := by
    ext i; by_cases hi : (i : ℕ) = 0 <;> simp [e1, hi, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one, single_one_dotProduct]
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hankel_apply']
  simp
end Herm

section Top
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}

theorem continuous_companion : Continuous (fun p : Fin r → k => companion p) :=
  continuous_matrix fun i j => by
    simp only [companion, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

theorem continuous_mom_sec (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by
  simp only [mom, sec]
  exact (continuous_fst.comp continuous_snd).dotProduct
    (((continuous_companion.comp continuous_fst).pow n).matrix_mulVec continuous_const)

theorem continuous_hankel : Continuous (fun a : Inv r k => hankel a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_hankelShift : Continuous (fun a : Inv r k => hankelShift a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_delta : Continuous (fun a : Inv r k => Delta a) :=
  continuous_hankel.matrix_det

end Top

section Unit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}


omit [Unram F E] in
theorem continuousStar (F : Type) [NontriviallyNormedField F] [NormedAlgebra F E] [Unram F E] : ContinuousStar E :=
  ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous⟩

theorem bm_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Bm (actU g X).toGl = g.1 * Bm X.toGl := by
  have hg : star g.1 * g.1 = 1 := (Matrix.mem_unitaryGroup_iff').1 g.2
  have key : ∀ n : ℕ, (g.1 * X.1.1 * star g.1) ^ n * g.1 = g.1 * X.1.1 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, Matrix.mul_assoc _ (star g.1), hg, Matrix.mul_one,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  simp only [Bm, Hn.toGl, actU, Matrix.of_apply]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Unit

end GlobalTheory.JR.ImgSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProper
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProper
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbitProper

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem companionMatrixOfCoeffs_pow_mulVec_first_basis (p : Fin r → k) (n : ℕ) (hn : n < r) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = Pi.single (⟨n, hn⟩ : Fin r) 1 := by
  induction n with
  | zero =>
    rw [pow_zero, one_mulVec]
    funext i
    simp [Pi.single_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_single_one]
    funext i
    simp only [companion, transpose_apply, of_apply, Pi.single_apply, Fin.ext_iff]
    have : ¬ (n + 1 = r) := by omega
    simp [this]

theorem conj_pow_GL (g : GL (Fin r) k) (A : Matrix (Fin r) (Fin r) k) (j : ℕ) :
    ((g : Matrix (Fin r) (Fin r) k) * A * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) ^ j =
      (g : Matrix (Fin r) (Fin r) k) * A ^ j * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  exact Units.conj_pow g A j

theorem Bm_sec (a : Inv r k) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, sec, of_apply]
  rw [companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2]
  simp [Pi.single_apply, Matrix.one_apply]

theorem Bm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  ext i j
  simp only [Bm, act, of_apply]
  rw [conj_pow_GL, mulVec_mulVec, mul_assoc _ _ (g : Matrix (Fin r) (Fin r) k), Units.inv_mul, mul_one,
    ← mulVec_mulVec]
  simp [Matrix.mul_apply, mulVec, dotProduct]

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, of_apply]
  rw [conj_pow_GL, vecMul_vecMul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← vecMul_vecMul]
  simp [Matrix.mul_apply, vecMul, dotProduct]

theorem Cm_sec (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, sec, of_apply]
  rw [pow_add, ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, mulVec_single_one, dotProduct_comm]
  simp [vecMul, dotProduct, transpose_apply, mul_comm]

end Alg

section Top
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_companion : Continuous (fun p : Fin r → F => companion p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [companion, of_apply]
  split_ifs
  · exact ((continuous_apply i)).neg
  all_goals exact continuous_const

theorem cont_sec : Continuous (fun a : Inv r F => sec a) := by
  unfold sec
  exact (cont_companion.comp continuous_fst).prodMk
    (continuous_const.prodMk ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

theorem cont_act : Continuous (fun p : GL (Fin r) F × Gl r F => act p.1 p.2) := by
  have h1 : Continuous (fun p : GL (Fin r) F × Gl r F => ((p.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun p : GL (Fin r) F × Gl r F => (((p.1)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
    Units.continuous_coe_inv.comp continuous_fst
  unfold act
  exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
    ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

theorem cont_charpoly_coeff (i : ℕ) :
    Continuous (fun A : Matrix (Fin r) (Fin r) F => A.charpoly.coeff i) := by
  have h : ∀ A : Matrix (Fin r) (Fin r) F, A.charpoly.coeff i =
      MvPolynomial.eval (fun ij : Fin r × Fin r => A ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin r)).coeff i)) := by
    intro A
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  simp_rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem cont_mom (n : ℕ) : Continuous (fun Y : Gl r F => mom Y n) := by
  unfold mom
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).dotProduct
    (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow n).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem cont_inv : Continuous (fun Y : Gl r F => inv Y) := by
  unfold inv
  exact (continuous_pi fun i : Fin r => (cont_charpoly_coeff (r := r) (F := F) (i : ℕ)).comp continuous_fst).prodMk
    ((continuous_pi fun i : Fin r => cont_mom (r := r) (F := F) (i : ℕ)).prodMk
      (show Continuous fun Y : Gl r F => Y.2.2.2 from continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem cont_hankel : Continuous (fun a : Inv r F => hankel a) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Inv r F => mom (sec a) ((i : ℕ) + (j : ℕ))
    exact (cont_mom _).comp cont_sec

theorem cont_Delta : Continuous (fun a : Inv r F => Delta a) := cont_hankel.matrix_det

end Top

section Cpt
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem cont_Bm : Continuous (fun Y : Gl r F => Bm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => ((Y.1 ^ (j : ℕ)) *ᵥ Y.2.1) i
    exact (continuous_apply i).comp
      (((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _).matrix_mulVec
        (continuous_fst.comp continuous_snd))

theorem cont_Cm : Continuous (fun Y : Gl r F => Cm Y) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun Y : Gl r F => (Y.2.2.1 ᵥ* (Y.1 ^ (i : ℕ))) j
    exact (continuous_apply j).comp
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).matrix_vecMul
        ((continuous_fst (X := Matrix (Fin r) (Fin r) F) (Y := (Fin r → F) × (Fin r → F) × F)).pow _))

theorem contAt_hankel_inv (a : Inv r F) (ha : Delta a ≠ 0) :
    ContinuousAt (fun b : Inv r F => (hankel b)⁻¹) a := by
  refine (continuousAt_matrix_inv _ ?_).comp cont_hankel.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ha

theorem coe_eq (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by
  rw [Bm_act, Bm_sec, mul_one]

theorem coe_inv_eq (g : GL (Fin r) F) (a : Inv r F) (ha : Delta a ≠ 0) :
    ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (hankel a)⁻¹ * Cm (act g (sec a)) := by
  have h : IsUnit (hankel a).det := isUnit_iff_ne_zero.mpr ha
  rw [Cm_act, Cm_sec, ← mul_assoc, nonsing_inv_mul _ h, one_mul]

theorem isCompact_set (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  set Φ : Gl r F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    fun q => ((Bm q.1, MulOpposite.op ((hankel q.2)⁻¹ * Cm q.1)), q.2) with hΦdef
  have hΦ : ContinuousOn Φ (C ×ˢ Ω) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have h3 : ContinuousAt (fun q : Gl r F × Inv r F => (hankel q.2)⁻¹) q :=
      (contAt_hankel_inv q.2 (hD q.2 hq.2)).comp continuous_snd.continuousAt
    exact (((cont_Bm.comp continuous_fst).continuousAt).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (h3.mul (cont_Cm.comp continuous_fst).continuousAt))).prodMk
      continuous_snd.continuousAt
  set e : GL (Fin r) F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    Prod.map (Units.embedProduct (Matrix (Fin r) (Fin r) F)) id with hedef
  have he : Topology.IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.prodMap Topology.IsClosedEmbedding.id
  have hK : IsCompact (e ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    he.isCompact_preimage ((hC.prod hΩ).image_of_continuousOn hΦ)
  have hS : IsClosed {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
    have hc : Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) :=
      cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd))
    exact (hΩ.isClosed.preimage continuous_snd).inter (hC.isClosed.preimage hc)
  refine hK.of_isClosed_subset hS ?_
  rintro ⟨g, a⟩ ⟨ha, hY⟩
  refine ⟨(act g (sec a), a), ⟨hY, ha⟩, ?_⟩
  simp only [hΦdef, hedef, Prod.map, id, Units.embedProduct_apply]
  rw [← coe_eq g a, ← coe_inv_eq g a (hD a ha)]

end Cpt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  intro F E _ _ _ _ _ r
  exact ⟨cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd)), cont_inv, cont_Delta,
    fun C Ω hC hΩ hD => isCompact_set C Ω hC hΩ hD⟩

end GlobalTheory.JR.OrbitProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProperStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  first | exact @GlobalTheory.JR.OrbitProper.main | exact GlobalTheory.JR.OrbitProper.main | (intros; apply GlobalTheory.JR.OrbitProper.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormDetMulProdSqLeOfEntryLe
open scoped TensorProduct Matrix
open Module Algebra

namespace GlobalTheory

section Pi

variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

theorem leftMulMatrix_pi_basisFun [DecidableEq ι] (x : ι → E) :
    leftMulMatrix (Pi.basisFun E ι) x = Matrix.diagonal x := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul]
  by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]

theorem algebraTrace_pi_apply (x : ι → E) : Algebra.trace E (ι → E) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E ι), leftMulMatrix_pi_basisFun,
    Matrix.trace_diagonal]

end Pi

section BaseChange

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing E]
  [Algebra R E] [Module.Free R S] [Module.Finite R S]

theorem algebraTrace_one_tmul (x : S) :
    Algebra.trace E (E ⊗[R] S) (1 ⊗ₜ x) = algebraMap R E (Algebra.trace R S x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

end BaseChange

section Split

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]


variable (R S) in
theorem exists_algEquiv_fin_points :
    ∃ (n : ℕ) (P : Fin n ≃ (S →ₐ[R] E)) (e : E ⊗[R] S ≃ₐ[E] (Fin n → E)),
      ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun E (E ⊗[R] S)
  let f : Fin n → (E ⊗[R] S →ₐ[E] E) := fun j ↦
    (Pi.evalAlgHom E (fun _ ↦ E) j).comp e.toAlgHom
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      by_contra h
      have := AlgHom.congr_fun hij (e.symm (Pi.single i 1))
      simp [f, Ne.symm h] at this
    · intro g
      obtain ⟨j, hj⟩ := AlgHom.eq_piEvalAlgHom (g.comp e.symm.toAlgHom)
      refine ⟨j, AlgHom.ext fun x ↦ ?_⟩
      simpa [f] using (AlgHom.congr_fun hj (e x)).symm
  exact ⟨n, (Equiv.ofBijective f hf).trans (AlgHom.liftEquiv R E S E).symm, e, fun x j ↦ rfl⟩

variable (R S) in
theorem finite_algHom_of_isFiniteSplit : Finite (S →ₐ[R] E) := by
  obtain ⟨n, P, -⟩ := exists_algEquiv_fin_points R S E
  exact Finite.of_equiv _ P


variable {E} in
theorem exists_algEquiv_points {ι : Type*} (P : ι ≃ (S →ₐ[R] E)) :
    ∃ e : E ⊗[R] S ≃ₐ[E] (ι → E), ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  obtain ⟨n, Q, e, he⟩ := exists_algEquiv_fin_points R S E
  refine ⟨e.trans (AlgEquiv.piCongrLeft' E (fun _ ↦ E) (Q.trans P.symm)), fun x j ↦ ?_⟩
  simp [he]

variable [Module.Free R S]


variable (R S) in
theorem natCard_algHom_eq_finrank [Nontrivial R] : Nat.card (S →ₐ[R] E) = finrank R S := by
  obtain ⟨n, P, e, -⟩ := exists_algEquiv_fin_points R S E
  rw [← Nat.card_congr P, ← Module.finrank_baseChange (R := E), e.toLinearEquiv.finrank_eq]
  simp

variable {E} {ι : Type*} [Fintype ι]

theorem card_eq_finrank_of_points (P : ι ≃ (S →ₐ[R] E)) : Fintype.card ι = finrank R S := by
  have := (algebraMap R E).domain_nontrivial
  rw [← natCard_algHom_eq_finrank R S E, ← Nat.card_congr P, Nat.card_eq_fintype_card]

variable [Module.Finite R S]

theorem algebraMap_trace_eq_sum_points (P : ι ≃ (S →ₐ[R] E)) (x : S) :
    algebraMap R E (Algebra.trace R S x) = ∑ j, P j x := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  rw [← algebraTrace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, algebraTrace_pi_apply]
  simp [he]

variable [DecidableEq ι]

theorem det_points_sq_eq_discr (P : ι ≃ (S →ₐ[R] E)) (v : ι → S) :
    (Matrix.of fun i j ↦ P j (v i)).det ^ 2 = algebraMap R E (discr R v) := by
  have : (algebraMap R E).mapMatrix (traceMatrix R v) =
      (Matrix.of fun i j ↦ P j (v i)) * (Matrix.of fun i j ↦ P j (v i))ᵀ := by
    ext i j
    simp [Matrix.mul_apply, algebraMap_trace_eq_sum_points P]
  rw [discr_def, RingHom.map_det, this, Matrix.det_mul, Matrix.det_transpose, pow_two]


omit [Module.Free R S] [Module.Finite R S] in
theorem det_points_ne_zero_of_basis (P : ι ≃ (S →ₐ[R] E)) (b : Basis ι R S) :
    (Matrix.of fun i j ↦ P j (b i)).det ≠ 0 := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  have h := (Pi.basisFun E ι).isUnit_det ((Algebra.TensorProduct.basis E b).map e.toLinearEquiv)
  rw [Basis.det_apply, ← Matrix.det_transpose] at h
  convert h.ne_zero using 2
  ext i j
  simp [Basis.toMatrix_apply, Algebra.TensorProduct.basis_apply, he]

end Split

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

end General

section Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Hadamard

section Etale

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_points_ne_zero_iff {E : Type*} [Field E] [Algebra K E] [Module.Finite K A]
    [IsFiniteSplit E (E ⊗[K] A)] (P : ι ≃ (A →ₐ[K] E)) (v : ι → A) :
    (Matrix.of fun i j ↦ P j (v i)).det ≠ 0 ↔ LinearIndependent K v := by
  constructor
  · intro h
    by_contra hli
    have := det_points_sq_eq_discr P v
    rw [discr_zero_of_not_linearIndependent K hli, map_zero] at this
    exact pow_ne_zero 2 h this
  · intro h
    simpa using det_points_ne_zero_of_basis P
      (basisOfLinearIndependentOfCardEqFinrank' v h (card_eq_finrank_of_points P))

theorem discr_ne_zero_iff_of_etale [Algebra.Etale K A] (h : Fintype.card ι = finrank K A)
    (v : ι → A) : discr K v ≠ 0 ↔ LinearIndependent K v := by
  have := FormallyUnramified.finite_of_free K A
  have := finite_algHom_of_isFiniteSplit K A (AlgebraicClosure K)
  obtain ⟨P⟩ : Nonempty (ι ≃ (A →ₐ[K] AlgebraicClosure K)) := by
    rw [← Finite.card_eq, natCard_algHom_eq_finrank, Nat.card_eq_fintype_card, h]
  rw [← det_points_ne_zero_iff P, ← pow_ne_zero_iff (a := Matrix.det _) two_ne_zero,
    det_points_sq_eq_discr]
  simp

end Etale

section DiscrBaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

end DiscrBaseChange

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvr
namespace GlobalTheory.IntegralClosureFG

theorem integralClosure_fg (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  classical
  let b0 := Module.finBasis E A
  have hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i) := by
    intro i
    have h : IsAlgebraic E (b0 i) := Algebra.IsAlgebraic.isAlgebraic _
    have h' : IsAlgebraic O (b0 i) := (IsFractionRing.isAlgebraic_iff O E A).2 h
    obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
    exact ⟨d, hd, hi⟩
  choose d hd0 hdi using hex
  have hu : ∀ i, IsUnit (algebraMap O E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let D : E := (Algebra.traceMatrix E b).det
  have hD : D ≠ 0 := by
    have h1 := (GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A)
      (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent
    rwa [Algebra.discr_def] at h1
  have hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e := by
    intro e he
    exact IsIntegrallyClosed.isIntegral_iff.1 he
  let S : Submodule O A := Submodule.span O (Set.range fun j => D⁻¹ • b j)
  have hS : S.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S := by
    intro x hx
    have hx' : IsIntegral O x := hx
    obtain ⟨v, hv⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x
      (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        ((hb i).mul (hb j))))
      (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        (hx'.mul (hb i))))
    have hx2 : x = ∑ j, v j • (D⁻¹ • b j) := by
      have : x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      rw [this, hv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]
    rw [hx2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS
  exact isNoetherian_submodule.1 this _ hle

end GlobalTheory.IntegralClosureFG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvrStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_finiteEtale_dvr : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntegralClosureFG.integralClosure_fg | exact GlobalTheory.IntegralClosureFG.integralClosure_fg | (intros; apply GlobalTheory.IntegralClosureFG.integralClosure_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LvlPolyDistinguished
noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.Red

def lvlPoly (l : ℕ) (R : Type) [CommRing R] (k : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i

variable {l : ℕ} {R S : Type} [CommRing R] [CommRing S]

theorem lvlPoly_coe (k : ℕ) : ((lvlPoly l R k : Polynomial R) : R⟦X⟧) = lvl l R k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := R))
    (fun i => ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i) (Finset.range l)
  rw [Polynomial.coeToPowerSeries.ringHom_apply] at this
  rw [lvlPoly, this, lvl]
  simp

theorem lvlPoly_map (j : R →+* S) (k : ℕ) : (lvlPoly l R k).map j = lvlPoly l S k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_mul (k : ℕ) :
    lvlPoly l R k * ((1 + Polynomial.X) ^ l ^ k - 1) = (1 + Polynomial.X) ^ l ^ (k + 1) - 1 := by
  rw [lvlPoly, geom_sum_mul, ← pow_mul, pow_succ]

theorem lvlPoly_monic [Nontrivial R] [hl : Fact l.Prime] (k : ℕ) : (lvlPoly l R k).Monic := by
  have h : lvlPoly l R k =
      (Polynomial.cyclotomic (l ^ (k + 1)) R).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl.out, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [h]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_charP {F : Type} [Field F] [hl : Fact l.Prime] [CharP F l] (k : ℕ) :
    lvlPoly l F k = Polynomial.X ^ (l ^ (k + 1) - l ^ k) := by
  have h := lvlPoly_mul (l := l) (R := F) k
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at h
  have hle : l ^ k ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.out.pos (Nat.le_succ k)
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [h, ← pow_add, Nat.sub_add_cancel hle]

theorem lvlPoly_distinguished [hl : Fact l.Prime] [IsLocalRing R] (h : ¬ IsUnit (l : R)) (k : ℕ) :
    (lvlPoly l R k).IsDistinguishedAt (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨fun {n} hn => ?_⟩, lvlPoly_monic k⟩
  have h0 : (l : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact h
  haveI : CharP (IsLocalRing.ResidueField R) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 := lvlPoly_map (l := l) (IsLocalRing.residue R) k
  rw [lvlPoly_charP] at h1
  have h2 : (lvlPoly l R k).natDegree = l ^ (k + 1) - l ^ k := by
    rw [← (lvlPoly_monic (l := l) (R := R) k).natDegree_map (IsLocalRing.residue R), h1,
      Polynomial.natDegree_X_pow]
  have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h1
  rw [h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem lvlPoly_separable {K : Type} [Field K] [CharZero K] [hl : Fact l.Prime] (k : ℕ) :
    (lvlPoly l K k).Separable := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.out.pos _
  have hs : ((1 + Polynomial.X : Polynomial K) ^ l ^ (k + 1) - 1).Separable := by
    obtain ⟨M, hM⟩ : ∃ M, l ^ (k + 1) = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
    rw [hM, Polynomial.separable_def']
    have hc : ((M : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    refine ⟨-1, Polynomial.C ((M : K) + 1)⁻¹ * (1 + Polynomial.X), ?_⟩
    have e : Polynomial.C ((M : K) + 1)⁻¹ * Polynomial.C ((M : K) + 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_pow_succ,
      Polynomial.derivative_add, Polynomial.derivative_X, zero_add, mul_one, sub_zero]
    linear_combination ((1 + Polynomial.X : Polynomial K) ^ (M + 1)) * e
  rw [← lvlPoly_mul] at hs
  exact hs.of_mul_left

theorem lvl_dvd_of_dvd_sq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) (a : O⟦X⟧) (ha : lvl l O k ∣ a ^ 2) : lvl l O k ∣ a := by
  rw [← lvlPoly_coe] at ha ⊢
  have H := lvlPoly_distinguished h k
  obtain ⟨r, -, hr⟩ := GlobalTheory.NB.LT.exists_poly_mod H a
  have h1 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ ((r ^ 2 : Polynomial O) : O⟦X⟧) := by
    rw [Polynomial.coe_pow,
      show (r : O⟦X⟧) ^ 2 = a ^ 2 - (a - r) * (a + r) by ring]
    exact ha.sub (hr.mul_right _)
  have h2 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h1
  let K := FractionRing O
  haveI : CharZero K := algebraRat.charZero K
  have h3 := Polynomial.map_dvd (algebraMap O K) h2
  rw [Polynomial.map_pow, lvlPoly_map] at h3
  have h4 := (lvlPoly_separable (l := l) (K := K) k).squarefree.dvd_pow_iff_dvd two_ne_zero |>.1 h3
  rw [← lvlPoly_map (algebraMap O K),
    Polynomial.map_dvd_map _ (IsFractionRing.injective O K) H.monic] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ (r : O⟦X⟧) :=
    ⟨s, by rw [hs, Polynomial.coe_mul]⟩
  simpa using hr.add h5

end GlobalTheory.CycFr.Red
end
end
