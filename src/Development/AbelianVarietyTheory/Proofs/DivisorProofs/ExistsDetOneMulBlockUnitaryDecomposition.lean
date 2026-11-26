module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DetDecomp

open GlobalTheory.UTrans

theorem hf_single {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    hf σ M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [hf, Pi.single_apply]

theorem isU_mat {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M γ : Matrix (Fin n) (Fin n) R)
    (h : IsU σ M γ) : γᵀ * M * γ.map σ = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_single] at this
  rw [← this]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_aniso {K : Type} [Field K] [CharZero K] {n : ℕ} (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ a b, σ (M a b) = M b a) {i j : Fin n} (hij : M i j ≠ 0) :
    ∃ x : Fin n → K, hf σ M x x ≠ 0 := by
  by_contra hno
  push_neg at hno
  set x : Fin n → K := Pi.single i 1
  set y : Fin n → K := Pi.single j 1
  have hm0 : hf σ M x y ≠ 0 := by rw [hf_single]; exact hij
  have hc := Calc.hf_conj σ M hσ hM x y
  have e : hf σ M (x + hf σ M x y • y) (x + hf σ M x y • y) = hf σ M x x + σ (hf σ M x y) * hf σ M x y
      + hf σ M x y * hf σ M y x + hf σ M x y * σ (hf σ M x y) * hf σ M y y := by
    simp only [Calc.hf_add_left, Calc.hf_add_right, Calc.hf_smul_left, Calc.hf_smul_right]
    ring
  rw [hno, hno x, hno y, ← hc] at e
  have hs : σ (hf σ M x y) ≠ 0 := (map_ne_zero σ).2 hm0
  have : (2 : K) * (σ (hf σ M x y) * hf σ M x y) = 0 := by linear_combination -e
  rcases mul_eq_zero.1 this with h2 | h2
  · exact two_ne_zero h2
  · exact mul_ne_zero hs hm0 h2

theorem refl_isU_det {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ a b, σ (M a b) = M b a) (x : Fin n → R) {Q r z : R}
    (hQ : hf σ M x x = Q) (hrQ : r * Q = 1) (hcr : σ r = r) (hz : z * σ z = 1) :
    IsU σ M (tv σ M x ((z - 1) * r)) ∧ (tv σ M x ((z - 1) * r)).det = z := by
  refine ⟨Calc.isU_tv σ M hσ hM x _ ?_, ?_⟩
  · rw [hQ, map_mul, map_sub, map_one, hcr]
    linear_combination r * hz + (z - 1) * (σ z - 1) * r * hrQ
  · rw [Calc.tv_det, hQ]
    linear_combination (z - 1) * hrQ

variable {D : D7}

theorem hf_incA (V : HSp D) (x0 : Fin V.rank → D.host.E) :
    hf (cA D) (V.gram.map (incA D))ᵀ (fun a => incA D (x0 a)) (fun a => incA D (x0 a)) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA,
    starRingEnd_apply]

theorem exists_aniso_gram (V : HSp D) (hV : 0 < V.rank) :
    ∃ x0 : Fin V.rank → D.host.E, hf (starRingEnd D.host.E) V.gramᵀ x0 x0 ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, V.gramᵀ i j ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply GlobalTheory.LevelSubgroup.gram_det_ne_zero V
    have h0 : V.gram = 0 := Matrix.ext fun a b => hne b a
    rw [h0]
    haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
    exact Matrix.det_zero
  exact exists_aniso _ (fun a => star_star a) _ (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) hij

theorem exists_det_eq (V : HSp D) (hV : 0 < V.rank) (z : Formalism.L2.Theta.AE D) (hz : z * cA D z = 1) :
    ∃ g : GA D V, (mt V g).det = z := by
  obtain ⟨x0, hx0⟩ := exists_aniso_gram V hV
  have hqs : star (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = hf (starRingEnd D.host.E) V.gramᵀ x0 x0 :=
    Calc.hf_conj (starRingEnd D.host.E) V.gramᵀ (fun a => star_star a) (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) x0 x0
  have hrQ : incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ * incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have hcr : cA D (incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, hqs]
  have hMA : ∀ a b, cA D ((V.gram.map (incA D))ᵀ a b) = (V.gram.map (incA D))ᵀ b a := fun a b => by
    simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨hU, hdet⟩ := refl_isU_det (cA D) GlobalTheory.DualPairCheck.cA_cA _ hMA _ (hf_incA V x0) hrQ hcr hz
  generalize tv (cA D) ((HSpace.gram V).map ⇑(incA D))ᵀ (fun a ↦ (incA D) (x0 a))
    ((z - 1) * (incA D) (hf (starRingEnd D.host.E) (HSpace.gram V)ᵀ x0 x0)⁻¹) = γ at hU hdet
  have hzu : IsUnit z := ⟨⟨z, cA D z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hmat := congrArg Matrix.transpose (isU_mat (cA D) _ _ hU)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    ← Matrix.mul_assoc] at hmat
  have hunit := (Matrix.isUnit_iff_isUnit_det γ).2 (by rw [hdet]; exact hzu)
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) hunit.unit.1 * JR (AF D.host.F) V.gram * hunit.unit.1 =
      JR (AF D.host.F) V.gram
    rw [IsUnit.unit_spec]
    exact hmat
  · show (hunit.unit.1).det = z
    rw [IsUnit.unit_spec]
    exact hdet

theorem det_blk {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (P : Matrix (Fin p) (Fin p) R)
    (Q : Matrix (Fin q) (Fin q) R) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).det = P.det * Q.det := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem skewGram_det_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).det ≠ 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, Matrix.det_smul, det_blk, Matrix.det_transpose, Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.LevelSubgroup.gram_det_ne_zero A) (GlobalTheory.LevelSubgroup.gram_det_ne_zero B))

theorem det_mul_conj (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (x : UB J) : (mat x).det * cA D (mat x).det = 1 := by
  have hx : (mat x)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (mat x).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  have hd := congrArg Matrix.det hx
  have hm : ((mat x).map (cA D)).det = cA D (mat x).det := (RingHom.map_det (cA D) (mat x)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm] at hd
  have hJ : IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).det := by
    have hm' : (J.map (incA D)).det = incA D J.det := (RingHom.map_det (incA D) J).symm
    show IsUnit (J.map (incA D)).det
    rw [hm']
    have h0 : J.det ≠ 0 := h ▸ skewGram_det_ne A B e
    refine ⟨⟨incA D J.det, incA D J.det⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    · rw [← map_mul, inv_mul_cancel₀ h0, map_one]
  apply hJ.mul_right_injective
  simp only
  rw [mul_one]
  linear_combination hd

theorem mat_blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A × GA D B) :
    mat (blkU A B e h g) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (mt A g.1) (mt B g.2) := rfl

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem exists_detOne_mul_blkU : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  intro D A B d e J h hd x
  have hz := det_mul_conj A B e h x
  have hzu : IsUnit (mat x).det := ⟨⟨_, _, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hcard : A.rank + B.rank = d := by simpa using Fintype.card_congr e
  obtain ⟨g, hg⟩ : ∃ g : GA D A × GA D B, (mat (blkU A B e h g)).det = (mat x).det := by
    rcases Nat.eq_zero_or_pos A.rank with hA | hA
    · obtain ⟨g, hg⟩ := exists_det_eq B (by omega) _ hz
      exact ⟨(1, g), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, one_mul, hg]⟩
    · obtain ⟨g, hg⟩ := exists_det_eq A hA _ hz
      exact ⟨(g, 1), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, mul_one, hg]⟩
  refine ⟨x * (blkU A B e h g)⁻¹, g, ?_, (inv_mul_cancel_right x _).symm⟩
  have hm : mat x = mat (x * (blkU A B e h g)⁻¹) * mat (blkU A B e h g) := by
    conv_lhs => rw [← inv_mul_cancel_right x (blkU A B e h g)]
    rfl
  have hd2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, hg] at hd2
  apply hzu.mul_left_injective
  simp only [one_mul]
  exact hd2.symm

end GlobalTheory.DetDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detOne_mul_blockUnitary_decomposition : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  first | exact @GlobalTheory.DetDecomp.exists_detOne_mul_blkU | exact GlobalTheory.DetDecomp.exists_detOne_mul_blkU | (intros; apply GlobalTheory.DetDecomp.exists_detOne_mul_blkU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

theorem mul_one_by_one {R : Type} [CommRing R] (C : Matrix (Fin n) (Fin 1) R) (B : Matrix (Fin 1) (Fin 1) R) :
    C * B = B.det • C := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem absE_of_scales {x : Matrix (Fin n) (Fin 1) E} {L : Matrix (Fin 1) (Fin n) E} (hL : L * x = 1) {γ : GAd σ J}
    (hγ : γ ∈ ratPts σ J) {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x γ l) : absE F E l = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F x = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : E := (L * γ0.1.1 * x) 0 0 with hc
  have hl : l.1 = inclR (F := F) (AF F) c := by
    have := congrArg (adMat F L * ·) e
    simp only [Matrix.mul_smul] at this
    rw [hL', hmat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul] at this
    have := congrFun (congrFun this 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this.symm
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := l.mul_inv
      rw [hl, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim l 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = l from
      Units.ext (by simp [hl])] at this

theorem levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y →
    (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (ResLine.col X), m * u * m⁻¹ ∈ unipRad σ J (ResLine.col X)) ∧
    (∀ g ∈ unipRad σ J (ResLine.col X), g ∈ levi σ J X Y {0} → g = 1) ∧
    (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧
    (∀ u ∈ unipRad σ J (ResLine.col X), Scales σ J (ResLine.col X) u 1) ∧
    (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (ResLine.col X) m l ∧ absE F E l = 1) ∧
    ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (ResLine.col X) γ l → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hc : ResLine.col X = initCols X 0 := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hlev : ∀ m ∈ levi σ J X Y {0}, m ∈ frameStab σ J (initCols X 0) ⊤ ∧ m ∈ frameStab σ J (initCols Y 0) ⊤ :=
    fun m hm => by
      simp only [levi, Subgroup.mem_iInf] at hm
      exact hm 0 (Finset.mem_singleton_self _)
  have hT' : cT (σ : E →+* E) (initCols Y 0) * J * initCols X 0 = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE (0 : Fin (r + 1)).2)) (j.castLE (0 : Fin (r + 1)).2)).trans
      (by simp only [Matrix.one_apply, Fin.castLE_inj])
  have h6 : ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (initCols X 0) γ l → absE F E l = 1 := fun γ hγ l e =>
    absE_of_scales hT' hγ e
  rw [hc]
  refine ⟨fun m hm u hu => conj_mem hW 0 (hlev m hm).1 hu, fun g hg hm => eq_one h hJ hW 0 hg (hlev g hm).2,
    fun γ hγ hm => ⟨hm, ?_⟩, fun u hu => ?_, fun m hm => ?_, h6⟩
  · show γ ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker
    simp only [Subgroup.mem_iInf]
    intro k hk
    obtain rfl := Finset.mem_singleton.1 hk
    obtain ⟨B, -, e⟩ := (hlev γ hm).1
    exact ⟨B, h6 γ hγ (Matrix.GeneralLinearGroup.det B) (e.trans (mul_one_by_one _ _)), e⟩
  · exact (unipRad_fix hu).trans (one_smul _ _).symm
  · have h2 : m ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
    simp only [Subgroup.mem_iInf] at h2
    obtain ⟨B, hB, e⟩ := h2 0 (Finset.mem_singleton_self _)
    exact ⟨Matrix.GeneralLinearGroup.det B, e.trans (mul_one_by_one _ _), hB⟩

end GlobalTheory.ResLine.LeviFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBisStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_radical_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (col X), m * u * m⁻¹ ∈ unipRad σ J (col X)) ∧ (∀ g ∈ unipRad σ J (col X), g ∈ levi σ J X Y {0} → g = 1) ∧ (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧ (∀ u ∈ unipRad σ J (col X), Scales σ J (col X) u 1) ∧ (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (col X) m l ∧ absE F E l = 1) ∧ ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (col X) γ l → absE F E l = 1 := by
  first | exact @GlobalTheory.ResLine.LeviFacts.levi_facts | exact GlobalTheory.ResLine.LeviFacts.levi_facts | (intros; apply GlobalTheory.ResLine.LeviFacts.levi_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
noncomputable section

namespace GlobalTheory.GaussDiv

section Finite

theorem exists_int_of_pow_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : 0 < n)
    (hz : z ^ n = 1) (h : z ∈ Set.range σ) : ∃ g : NumberField.RingOfIntegers K, σ g = z := by
  obtain ⟨x, rfl⟩ := h
  have hx : x ^ n = 1 := σ.injective (by rw [map_pow, hz, map_one])
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)
  exact ⟨⟨x, hi⟩, rfl⟩

theorem exists_int_gauss {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] [Fintype Rˣ] (m : Ideal R) (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (χ : Rˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) (t₀ : Rˣ)
    (ht₀ : ∀ x ∈ m, ((t₀ : R) - 1) * x = 0) (hχt₀ : χ t₀ ≠ 1) (hr : ∀ u, χ u ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ Fintype.card R = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = ∑ u : Rˣ, (χ u)⁻¹ * ψ u ∧
      g * g' = (Fintype.card R : NumberField.RingOfIntegers K) := by
  have hN := GlobalTheory.gauss_units_norm_sq m hm ψ hψ χ (map_mul χ) hχ t₀ ht₀ hχt₀
  have h1 : ∀ u, ∃ g : NumberField.RingOfIntegers K, σ g = χ u := fun u =>
    exists_int_of_pow_eq_one σ (Fintype.card_pos (α := Rˣ)) (by rw [← map_pow, pow_card_eq_one, map_one]) (hr u)
  have h2 : ∀ y, ∃ g : NumberField.RingOfIntegers K, σ g = ψ y := fun y => by
    have : ψ y ^ Fintype.card R = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    exact exists_int_of_pow_eq_one σ (Fintype.card_pos (α := R)) this (hζ _ this)
  choose a ha using h1
  choose b hb using h2
  have hinv : ∀ u, χ u⁻¹ = (χ u)⁻¹ := fun u =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hg : σ ((∑ u : Rˣ, a u⁻¹ * b u : NumberField.RingOfIntegers K) : K) = ∑ u : Rˣ, (χ u)⁻¹ * ψ u := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, ha, hb, hinv]
  have hg' : σ ((∑ u : Rˣ, a u * b (-u) : NumberField.RingOfIntegers K) : K) =
      starRingEnd ℂ (∑ u : Rˣ, (χ u)⁻¹ * ψ u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, ha, hb]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.inv_eq_conj (hχ z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  refine ⟨_, ∑ u : Rˣ, a u * b (-u), hg, ?_⟩
  apply NumberField.RingOfIntegers.ext
  apply σ.injective
  have e : ∀ x y : NumberField.RingOfIntegers K, σ ((x * y : NumberField.RingOfIntegers K) : K) = σ x * σ y :=
    fun x y => by simp only [map_mul]
  rw [e, hg, hg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  simp

end Finite

section Local

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_res (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem val_rep_sub {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (y : Res k c) (a : 𝒪[k])
    (h : y = Ideal.Quotient.mk _ a) : valuation k (rep y - a) ≤ valuation k (ϖ : k) ^ c :=
  (mk_eq_mk_iff hϖ c (Quotient.out y) a).1 (by rw [Ideal.Quotient.mk_out, h])


open Classical in
theorem exists_int_gS {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ψl : k → ℂ}
    (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
    (hcond : ∀ x : k, (∀ y : k, valuation k y ≤ 1 → ψl (x * y) = 1) → valuation k x ≤ 1)
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
    (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) (hun : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (hr : ∀ x : kˣ, valuation k (x : k) = 1 → (ν x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (resCard k ^ c) = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = gS ψl ν hϖ hc1 1 ∧
      g * g' = (resCard k : NumberField.RingOfIntegers K) ^ c := by
  have hdiv : ∀ a b : k, valuation k (a - b) ≤ valuation k (ϖ : k) ^ c →
      ψl (a / (ϖ : k) ^ c) = ψl (b / (ϖ : k) ^ c) := fun a b h => by
    apply psi_congr hadd hO
    rw [← sub_div, map_div₀, map_pow]
    exact div_le_one_of_le₀ h zero_le'
  have hmul : ∀ x y : Res k c, valuation k (rep (x * y) - rep x * rep y) ≤ valuation k (ϖ : k) ^ c := fun x y =>
    val_rep_sub hϖ (x * y) (Quotient.out x * Quotient.out y)
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])
  let Ψ : AddChar (Res k c) ℂ :=
    { toFun := fun y => ψl (rep y / (ϖ : k) ^ c)
      map_zero_eq_one' := by
        rw [hdiv _ 0 (val_rep_sub hϖ (0 : Res k c) 0 (map_zero _).symm), zero_div]
        exact hO 0 (by simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd, ← add_div]
        exact hdiv _ _ (val_rep_sub hϖ (x + y) (Quotient.out x + Quotient.out y)
          (by rw [map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])) }
  let χ : (Res k c)ˣ →* ℂ :=
    { toFun := fun u => ν (uRep hϖ hc1 u)
      map_one' := by
        rw [nu_congr hϖ hc1 hc (b := 1) (by simp) (val_rep_sub hϖ (1 : Res k c) 1 (map_one _).symm)]
        simp
      map_mul' := fun u w => by
        rw [nu_congr hϖ hc1 hc (b := uRep hϖ hc1 u * uRep hϖ hc1 w)
          (by simp [map_mul, uRep, val_rep_unit hϖ hc1]) (hmul u w)]
        simp }
  have hΨ : ∀ d : Res k c, (∀ x, Ψ (d * x) = 1) → d = 0 := fun d hd => by
    have h3 := hcond (rep d / (ϖ : k) ^ c) fun a ha => by
      rw [← hd (Ideal.Quotient.mk _ ⟨a, ha⟩), div_mul_eq_mul_div]
      exact (hdiv _ _ (val_rep_sub hϖ _ (Quotient.out d * ⟨a, ha⟩) (by rw [map_mul, Ideal.Quotient.mk_out]))).symm
    rw [← Ideal.Quotient.mk_out d, ← map_zero (Ideal.Quotient.mk _)]
    apply (mk_eq_mk_iff hϖ c _ _).2
    have e2 : rep d = rep d / (ϖ : k) ^ c * (ϖ : k) ^ c := by field_simp
    change valuation k (rep d - 0) ≤ _
    rw [sub_zero, e2, map_mul, map_pow]
    exact mul_le_of_le_one_left' h3
  haveI : Nontrivial (Res k c) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (by omega))))
  haveI : IsLocalRing (Res k c) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨u, ⟨hu1, hu2⟩, hν⟩ := hmin
  have hu' : IsUnit (⟨u, hu1.le⟩ : 𝒪[k]) :=
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hu1
  set ub : (Res k c)ˣ := (hu'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).unit with hub_def
  have hub : (ub : Res k c) = Ideal.Quotient.mk _ ⟨u, hu1.le⟩ := rfl
  have ht₀ : ∀ x ∈ IsLocalRing.maximalIdeal (Res k c), ((ub : Res k c) - 1) * x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 fun h => hx
      (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h).map _)
    have hx' : valuation k (a : k) ≤ valuation k (ϖ : k) := by rw [hϖ]; exact le_uniformizer_iff.2 ha
    have hu2' : valuation k ((u : k) - 1) ≤ valuation k (ϖ : k) ^ (c - 1) := by
      simpa [Units.val_pow_eq_pow_val] using hu2
    rw [hub, ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)), ← map_sub, ← map_mul,
      ← map_zero (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))]
    apply (mk_eq_mk_iff hϖ c _ _).2
    change valuation k (((u : k) - 1) * a - 0) ≤ _
    rw [sub_zero, map_mul]
    calc valuation k ((u : k) - 1) * valuation k (a : k) ≤ valuation k (ϖ : k) ^ (c - 1) * valuation k (ϖ : k) :=
          mul_le_mul' hu2' hx'
      _ = valuation k (ϖ : k) ^ c := by rw [← pow_succ]; congr 1; omega
  have hχt₀ : χ ub ≠ 1 := by
    change ((ν (uRep hϖ hc1 ub) : ℂˣ) : ℂ) ≠ 1
    rw [nu_congr hϖ hc1 hc (b := u) hu1 (val_rep_sub hϖ _ _ hub)]
    exact fun h => hν (Units.ext h)
  obtain ⟨g, g', h1, h2⟩ := exists_int_gauss σ (IsLocalRing.maximalIdeal (Res k c))
    (fun x => by simp [IsLocalRing.mem_maximalIdeal]) Ψ hΨ χ (fun u => hun _) ub ht₀ hχt₀
    (fun u => hr _ (val_rep_unit hϖ hc1 u)) (by rwa [card_res])
  refine ⟨g, g', ?_, by rw [h2, card_res, Nat.cast_pow]⟩
  rw [h1]
  unfold gS
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [one_mul, Units.val_inv_eq_inv_val]
  rfl

end Local

end GlobalTheory.GaussDiv

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)


open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.GaussDiv.gauss_dvd_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  intro F _ _ K _ _ σ ψ v ν hψ hcont hun hc1 hr hζ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hadd : ∀ x y, psiLoc ψ v (x + y) = psiLoc ψ v x * psiLoc ψ v y := fun x y => by
    simp only [psiLoc, map_add (f := _)]
    exact AddChar.map_add_eq_mul ψ _ _
  have hO : ∀ x : Fv F v, valuation (Fv F v) x ≤ 1 → psiLoc ψ v x = 1 := fun x hx => by
    have := ((hψ 1).2 ((val_le_one_iff v 1).1 (by simp))) x ((val_le_one_iff v x).1 hx)
    rwa [one_mul] at this
  have hcond : ∀ x : Fv F v, (∀ y : Fv F v, valuation (Fv F v) y ≤ 1 → psiLoc ψ v (x * y) = 1) →
      valuation (Fv F v) x ≤ 1 := fun x h =>
    (val_le_one_iff v x).2 ((hψ x).1 fun y hy => h y ((val_le_one_iff v y).2 hy))
  have hne : {c | CondLE (unifAt v) c ν}.Nonempty := exists_condLE hϖ ν hcont
  have hmem : CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) ν := Nat.sInf_mem hne
  have hmin : ∃ u ∈ unitCong (unifAt v ^ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1)), ν u ≠ 1 := by
    have hlt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < sInf {c | CondLE (unifAt v) c ν} := by
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν
      omega
    have h : ¬ CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1) ν := Nat.notMem_of_lt_sInf hlt
    simpa [CondLE] using h
  have hq : GlobalTheory.SplitWeil.resCard (Fv F v) = Ideal.absNorm v.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨g, g', h1, h2⟩ := GlobalTheory.GaussDiv.exists_int_gS σ hadd hO hcond hϖ hc1 hmem hmin hun
    (fun x hx => hr x ((val_le_one_iff v _).1 hx.le)
      ((val_le_one_iff v _).1 (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])))
    (by rwa [hq])
  refine ⟨g, g', ?_, by rw [h2, hq]⟩
  rw [h1]
  unfold gauss gS
  refine Finset.sum_congr rfl fun y _ => ?_
  have hr := rep_ne_zero hϖ hc1 y
  unfold rep at hr
  rw [dite_eq_right hr, one_mul]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localGaussSum_integer_dvd_residueCard_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  first | exact @GlobalTheory.GaussDiv.gauss_dvd_pow | exact GlobalTheory.GaussDiv.gauss_dvd_pow | (intros; apply GlobalTheory.GaussDiv.gauss_dvd_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.TriMove

variable {D : D7} {S S' : HSp D}

theorem rdx_conj_diag {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    (rdx (K := ℂ) h)ᴴ * diagonal d * rdx (K := ℂ) h = diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp [rdx, Matrix.one_apply, Matrix.diagonal_apply]

theorem diag_rdx {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    diagonal d * rdx (K := ℂ) h = rdx (K := ℂ) h * diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp only [rdx, finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.mul_one, Matrix.one_mul,
    Function.comp_id]

theorem rdi_mulVec {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (v : Fin m → K) (i : Fin n) :
    (rdi (K := K) h *ᵥ v) i = v ((finCongr h).symm i) := by
  subst h
  simp [rdi, Matrix.one_apply]

theorem cT_sig_eq (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := by
  ext i j
  rfl

theorem mem_latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (y : Fin S'.rank → D.host.E) :
    y ∈ latMove I Λ ↔ I.Q *ᵥ y ∈ Λ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show I.Q *ᵥ (I.P *ᵥ u) ∈ Λ
    rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  · intro hy
    refine ⟨I.Q *ᵥ y, hy, ?_⟩
    show I.P *ᵥ (I.Q *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]

theorem sumForm_eq (G : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_move (I : IsoMat S S') (x y : Fin S.rank → D.host.E) :
    star (I.P *ᵥ x) ⬝ᵥ (S'.gram *ᵥ (I.P *ᵥ y)) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  have hg : I.Pᴴ * S'.gram * I.P = S.gram := by rw [← cT_sig_eq]; exact I.gram
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem latS_mulVec_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (T : Subring (TensorProduct F E R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ Formalism.UG.latS (F := F) R T Λ', (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x ∈ Formalism.UG.latS (F := F) R T Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

theorem mem_hatL_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : Fin S'.rank → Lev.EAf D) :
    x ∈ Formalism.L2.Herm.hatL (latMove I Λ) ↔ fQ I *ᵥ x ∈ Formalism.L2.Herm.hatL Λ := by
  constructor
  · intro hx
    exact latS_mulVec_mem _ _ I.Q (latMove I Λ) Λ (fun y hy => (mem_latMove I Λ y).1 hy) x hx
  · intro hx
    have h := latS_mulVec_mem _ _ I.P Λ (latMove I Λ)
      (fun y hy => (mem_latMove I Λ _).2 (by rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec])) _ hx
    have e : I.P.map (Formalism.UG.inclE _) *ᵥ (fQ I *ᵥ x) = x := by
      show fP I *ᵥ (fQ I *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, fP_fQ, Matrix.one_mulVec]
    rwa [e] at h

theorem frame_inv (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) :
    ((betaMove I β)⁻¹ : GL (Fin S'.rank) (Lev.EAf D)).val =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) I.rank_eq) (β⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) (fQ I) := rfl

theorem frame_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    Formalism.L2.DIV.IsFrame (F := D.host.F) (E := D.host.E) (n := S'.rank) (betaMove I β) (latMove I Λ) := by
  intro x
  rw [mem_hatL_move, hβ, frame_inv]
  simp only [← Matrix.mulVec_mulVec, rdi_mulVec]
  exact ⟨fun H i => H _, fun H j => by simpa using H (finCongr I.rank_eq j)⟩

theorem selfDual_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (h : IsSelfDualC S Λ) :
    IsSelfDualC S' (latMove I Λ) := by
  have hPQ : ∀ y, I.P *ᵥ (I.Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]
  have hQP : ∀ y, I.Q *ᵥ (I.P *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  obtain ⟨hl, hd⟩ := h
  refine ⟨Submodule.IsLattice.of_fg D.host.E (hl.fg.map _), ?_⟩
  · intro y
    rw [mem_latMove, hd (I.Q *ᵥ y)]
    simp only [sumForm_eq]
    constructor
    · intro H x hx
      rw [mem_latMove] at hx
      obtain ⟨b, hb⟩ := H _ hx
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ, hPQ]
    · intro H x hx
      have hx' : I.P *ᵥ x ∈ latMove I Λ := by rw [mem_latMove, hQP]; exact hx
      obtain ⟨b, hb⟩ := H _ hx'
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ]

theorem cartan_conj {m n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hab : a * b = 1) (hba : b * a = 1) (hb : bᴴ * G * b = G') (ha : aᴴ * G' * a = G)
    {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCartanInv G' (a * s * b) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · calc a * s * b * (a * s * b) = a * (s * (b * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hba, Matrix.mul_one, h1, Matrix.mul_one, hab]
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (sᴴ * aᴴ) * G' * (a * s * b) = bᴴ * (sᴴ * (aᴴ * G' * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [ha, h2, hb]
  · have e : G' * (a * s * b) = bᴴ * (G * s) * b := by
      rw [← hb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
    rw [e]
    refine h3.conjTranspose_mul_mul_same fun u v huv => ?_
    have := congrArg (a *ᵥ ·) huv
    simpa [Matrix.mulVec_mulVec, hab] using this

theorem onb_conj {m n : ℕ} (h : n = m) {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ}
    {a : Matrix (Fin m) (Fin n) ℂ} {b : Matrix (Fin n) (Fin m) ℂ} (hba : b * a = 1) (ha : aᴴ * G' * a = G)
    {s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (hs : IsONBasis G s B p) :
    IsONBasis G' (a * s * b) (a * B * rdx (K := ℂ) h) p := by
  obtain ⟨ε, hε, hd, hsB⟩ := hs
  refine ⟨fun i => ε ((finCongr h).symm i), fun i => ?_, ?_, ?_⟩
  · simpa using hε ((finCongr h).symm i)
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (rdx (K := ℂ) h)ᴴ * (Bᴴ * aᴴ) * G' * (a * B * rdx (K := ℂ) h)
        = (rdx (K := ℂ) h)ᴴ * (Bᴴ * (aᴴ * G' * a) * B) * rdx (K := ℂ) h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hd]; exact rdx_conj_diag h _
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul, ← Matrix.mul_assoc s B, hsB, Matrix.mul_assoc B, diag_rdx h]
    rfl

theorem rigMove_is {S S' : HSp D} (I : IsoMat S S') (r : Rig S) (hr : r.Is) : (rigMove I r).Is := by
  unfold Rig.Is at hr ⊢
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨selfDual_move I r.Λ h1, frame_move I r.Λ r.β h2, fun τ => ?_⟩
  have hG' : (I.qT τ)ᴴ * gramAt D S τ * I.qT τ = gramAt D S' τ := I.qT_gram τ
  have hG : (I.pT τ)ᴴ * gramAt D S' τ * I.pT τ = gramAt D S τ := I.symm.qT_gram τ
  obtain ⟨hc, p, hp⟩ := h3 τ
  exact ⟨cartan_conj (I.pT_qT τ) (I.qT_pT τ) hG' hG hc, p, onb_conj I.rank_eq (I.qT_pT τ) hG hp⟩

end GlobalTheory.TriMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryMovedRigging_is : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig S), r.Is → (GlobalTheory.TriMove.rigMove I r).Is := by
  first | exact @GlobalTheory.TriMove.rigMove_is | exact GlobalTheory.TriMove.rigMove_is | (intros; apply GlobalTheory.TriMove.rigMove_is <;> assumption)
end
end
