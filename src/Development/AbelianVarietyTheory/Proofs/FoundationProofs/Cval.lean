module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

def cval (g : GL3Theta.G1 p) (s : ℂ) : ℂ_[p] := lamC g.lam (U1 g.abelian₂ s (sgStar g.abelian₂) 0)

def tau (g : GL3Theta.G1 p) (s : ℂ) : PowerSeries ℂ_[p] :=
  (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ s (sgStar g.abelian₂))

def logc (g : GL3Theta.G1 p) (s : ℂ) : ℝ := if s ∈ g.abelian₂ then 0 else Real.log ‖cval g s‖

end GlobalTheory.ThetaTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLevels

theorem bc_nsmul_left (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T (n • x) y = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_left, ih, pow_succ]

theorem bc_nsmul_right (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    bc D T x (n • y) = bc D T x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, bc_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, bc_add_right, ih, pow_succ]

theorem wd_entire (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem levels_closed : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N'
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  refine ⟨fun L L' hL hL' F hF => ?_, fun z F hF => ?_, fun F hF G hG => ?_, fun a F hF => ?_⟩
  · have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
    have n1 := GlobalTheory.ThetaTriple.nice_of_klat hc k1
    obtain ⟨hd, hF⟩ := (n1.mem_ThSp F).1 hF
    refine ⟨hd, _, Nat.pos_of_ne_zero (GlobalTheory.ThetaTriple.index_ne_zero hc k1 k), fun x hx => hF _ ?_⟩
    exact AddSubgroup.nsmul_index_mem
      ((La D (tor0 D cc δ) L L').addSubgroupOf (La0 D (tor0 D cc δ) N N')) ⟨x, hx⟩
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨n, hn, hz⟩ := GlobalTheory.ThetaInter.klat_mul_mem (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 k z
    change n • pt D (tor0 D cc δ) δ z ∈ _ at hz
    refine ⟨wd_entire D _ _ hd, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have hmx := AddSubgroup.nsmul_mem _ hx m
    have h1 : bc D (tor0 D cc δ) ((m * n) • x) (pt D (tor0 D cc δ) δ z) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_left, ← bc_nsmul_right]
      exact n0.2.1 _ hmx _ hz
    have h2 : bc D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) = 1 := by
      rw [mul_comm, mul_smul, bc_nsmul_right, ← bc_nsmul_left]
      exact n0.2.1 _ hz _ hmx
    have h3 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h4 := Wd_Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) ((m * n) • x) F
    rw [h3, h2, add_comm] at h4
    rw [Wd_Wd, h1, h4]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    obtain ⟨hd', n, hn, hG⟩ := hG
    refine ⟨hd.add hd', m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    have h1 : Wd D (tor0 D cc δ) ((m * n) • x) F = F := by
      rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hx n)
    have h2 : Wd D (tor0 D cc δ) ((m * n) • x) G = G := by
      rw [mul_comm, mul_smul]; exact hG _ (AddSubgroup.nsmul_mem _ hx m)
    rw [Wd_add, h1, h2]
  · obtain ⟨hd, m, hm, hF⟩ := hF
    exact ⟨hd.const_smul a, m, hm, fun x hx => by rw [Wd_smul, hF x hx]⟩

end GlobalTheory.ThetaLevels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosureStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_all_levels_closure : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.ThetaLevels.levels_closed | exact GlobalTheory.ThetaLevels.levels_closed | (intros; apply GlobalTheory.ThetaLevels.levels_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
noncomputable section
namespace GlobalTheory.CartanInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

variable {p q : ℕ}

def l1 {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

def Kc (p q : ℕ) : Set (UpqT p q) := {k | IsKC (UpqT.mat k)}

def eP (B : Fin p → Fin q → ℂ) : UpqT p q :=
  GlobalTheory.CompactDualExists.expU ⟨pY B, (pY_mem B).1⟩

theorem mat_eP (B : Fin p → Fin q → ℂ) : UpqT.mat (eP B) = NormedSpace.exp (pY B) := rfl

theorem continuous_eP : Continuous (eP : (Fin p → Fin q → ℂ) → UpqT p q) :=
  GlobalTheory.CompactDualExists.continuous_expU.comp (continuous_pY.subtype_mk _)

theorem mat_mul (x y : UpqT p q) : UpqT.mat (x * y) = UpqT.mat x * UpqT.mat y := rfl

theorem mat_one : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem isKC_fromBlocks (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    IsKC (Matrix.fromBlocks U 0 0 V : Mat p q) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

theorem mem_Kc_iff (k : UpqT p q) : k ∈ Kc p q ↔
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      UpqT.mat k = Matrix.fromBlocks U 0 0 V := by
  constructor
  · intro hk
    have hk' : IsKC (UpqT.mat k) := hk
    have h : UpqT.mat k = Matrix.fromBlocks (UpqT.mat k).toBlocks₁₁ 0 0 (UpqT.mat k).toBlocks₂₂ := by
      ext a b
      rcases a with i | i <;> rcases b with j | j
      · rfl
      · exact hk' _ _ (by simp [sameBlock])
      · exact hk' _ _ (by simp [sameBlock])
      · rfl
    have hJ := GlobalTheory.UpqTopology.mat_unitary k
    rw [h] at hJ
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at hJ
    refine ⟨_, ?_, _, ?_, h⟩
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.1
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.2.2.2
  · rintro ⟨U, -, V, -, h⟩
    show IsKC (UpqT.mat k)
    rw [h]; exact isKC_fromBlocks U V

theorem star_mul_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : (UpqT.mat k)ᴴ * UpqT.mat k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at hU hV
  rw [h]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU, hV]

theorem mat_inv_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : UpqT.mat k⁻¹ = (UpqT.mat k)ᴴ := by
  have h1 : UpqT.mat k * UpqT.mat k⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc UpqT.mat k⁻¹ = ((UpqT.mat k)ᴴ * UpqT.mat k) * UpqT.mat k⁻¹ := by
        rw [star_mul_of_mem_Kc hk, one_mul]
    _ = (UpqT.mat k)ᴴ := by rw [mul_assoc, h1, mul_one]

def Ksg (p q : ℕ) : Subgroup (UpqT p q) where
  carrier := Kc p q
  one_mem' := (mem_Kc_iff 1).2 ⟨1, one_mem _, 1, one_mem _, by rw [mat_one, Matrix.fromBlocks_one]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := (mem_Kc_iff x).1 hx
    obtain ⟨U', -, V', -, h'⟩ := (mem_Kc_iff y).1 hy
    show IsKC (UpqT.mat (x * y))
    rw [mat_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (UpqT.mat x⁻¹)
    rw [mat_inv_of_mem_Kc hx]
    have hx' : IsKC (UpqT.mat x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

theorem exists_cartan (g : UpqT p q) : ∃ k ∈ Kc p q, ∃ B, g = k * eP B := by
  obtain ⟨U, hU, V, hV, h⟩ := isCartan_cartanB g
  refine ⟨g * (eP fun i j => cartanB g i j)⁻¹, (mem_Kc_iff _).2 ⟨U, hU, V, hV, ?_⟩, _,
    (inv_mul_cancel_right _ _).symm⟩
  have h1 : UpqT.mat (eP fun i j => cartanB g i j) * UpqT.mat (eP fun i j => cartanB g i j)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, h, Matrix.mul_assoc]
  exact (congrArg _ h1).trans (Matrix.mul_one _)

theorem cartanB_mul_eP {k : UpqT p q} (hk : k ∈ Kc p q) (B : Fin p → Fin q → ℂ) :
    cartanB (k * eP B) = Matrix.of B := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  exact cartanB_eq ⟨U, hU, V, hV, by rw [mat_mul, h]; rfl⟩

theorem polJ_aOf (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (sinhcAd_mulVec_of_sq_eigen p q _ _ _ (adMat_sq_mulVec_eigP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (det_eigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem polJ_pOf (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) =
    (∏ i ∈ Finset.range (min p q), shc (2 * singVal B i) * shc (singVal B i) ^ (2 * (max p q - min p q))) *
    ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q),
      if i < j then (shc (singVal B i - singVal B j) * shc (singVal B i + singVal B j)) ^ 2 else 1 := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have e : pOf B = Matrix.fromBlocks U 0 0 V * aOf p q (singVal B) * Matrix.fromBlocks Uᴴ 0 0 Vᴴ := by
    conv_lhs => rw [hB]
    simp [aOf, pOf, singVal, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [e, Conj.polJ_conj p q _ _ _ (by simp [Matrix.fromBlocks_multiply, h1, h2]) (isKC_fromBlocks _ _)
    (isKC_fromBlocks _ _), polJ_aOf, RootProd.prod_shc_rootP]

theorem one_le_shc (x : ℝ) : 1 ≤ shc x := by
  unfold shc
  split_ifs with hx
  · exact le_rfl
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [le_div_iff_of_neg h, one_mul]; exact Real.sinh_le_self_iff.2 h.le
    · rw [le_div_iff₀ h, one_mul]; exact Real.self_le_sinh_iff.2 h.le

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl h

theorem one_le_polJ (B : Matrix (Fin p) (Fin q) ℂ) : 1 ≤ polJ (pOf B) := by
  rw [polJ_pOf]
  refine one_le_mul_of_one_le_of_one_le (one_le_prod_real fun i _ => ?_)
    (one_le_prod_real fun i _ => one_le_prod_real fun j _ => ?_)
  · exact one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_pow₀ (one_le_shc _))
  · split_ifs
    · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_shc _))
    · exact le_rfl

theorem shc_le_exp (x : ℝ) : shc x ≤ Real.exp |x| := by
  have key : ∀ y : ℝ, 0 < y → Real.sinh y / y ≤ Real.exp y := by
    intro y hy
    rw [div_le_iff₀ hy, Real.sinh_eq, div_le_iff₀ two_pos]
    have h1 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(2 * y))
    have h3 := Real.exp_pos y
    rw [h1]; nlinarith
  unfold shc
  split_ifs with hx
  · exact Real.one_le_exp (abs_nonneg x)
  · rcases lt_or_gt_of_ne hx with h | h
    · have := key (-x) (neg_pos.2 h)
      rwa [Real.sinh_neg, neg_div_neg_eq, ← abs_of_neg h] at this
    · rw [abs_of_pos h]; exact key x h

theorem singVal_nonneg (B : Matrix (Fin p) (Fin q) ℂ) (i : ℕ) : 0 ≤ singVal B i :=
  LinearMap.singularValues_nonneg _ _

theorem sum_sum_ite_lt (m : ℕ) (s : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then s i + s j else 0) =
      ((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (s := Finset.range (m + 1))
      (fun j hj => if_neg (by have := Finset.mem_range.1 hj; omega)), add_zero]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem polJ_le_exp (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) ≤
    Real.exp (2 * (((p + q : ℕ) : ℝ) - 1) * ∑ i ∈ Finset.range (min p q), singVal B i) := by
  have h0 := singVal_nonneg B
  have hs : ∀ x, 0 ≤ shc x := fun x => zero_le_one.trans (one_le_shc x)
  rw [polJ_pOf]
  set s := singVal B
  set m := min p q with hm
  set D := max p q - min p q with hD
  have hA : ∏ i ∈ Finset.range m, shc (2 * s i) * shc (s i) ^ (2 * D) ≤
      Real.exp ((2 + 2 * (D : ℝ)) * ∑ i ∈ Finset.range m, s i) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hs _) (pow_nonneg (hs _) _)) fun i _ => ?_
    have a1 := shc_le_exp (2 * s i)
    have a2 := shc_le_exp (s i)
    rw [abs_of_nonneg (by linarith [h0 i])] at a1 a2
    calc _ ≤ Real.exp (2 * s i) * Real.exp (s i) ^ (2 * D) :=
          mul_le_mul a1 (pow_le_pow_left₀ (hs _) a2 _) (pow_nonneg (hs _) _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hB : (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
      if i < j then (shc (s i - s j) * shc (s i + s j)) ^ 2 else 1) ≤
      Real.exp (4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i)) := by
    rw [← sum_sum_ite_lt, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
      fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
    split_ifs
    · have a1 := (shc_le_exp (s i - s j)).trans (Real.exp_le_exp.2
        (show |s i - s j| ≤ s i + s j from abs_le.2 ⟨by linarith [h0 i], by linarith [h0 j]⟩))
      have a2 := shc_le_exp (s i + s j)
      rw [abs_of_nonneg (by linarith [h0 i, h0 j])] at a2
      calc _ ≤ (Real.exp (s i + s j) * Real.exp (s i + s j)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (hs _) (hs _)) (mul_le_mul a1 a2 (hs _) (Real.exp_pos _).le) 2
        _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    · simp
  refine (mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity) (Real.exp_pos _).le).trans (le_of_eq ?_)
  have e : ((p + q : ℕ) : ℝ) = D + 2 * m := by
    have : p + q = D + 2 * m := by omega
    exact_mod_cast this
  rw [← Real.exp_add, e]; ring_nf

end GlobalTheory.CartanInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaLatticePoints

def ptHom (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    Matrix (Fin d) (Fin a) D.host.E →+ VC D a d :=
  AddMonoidHom.mk' (pt D (tor0 D cc δ) δ) fun y y' => by
    funext τ i j
    simp [pt, embV, tor0, mul_add]

theorem ptHom_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ)
    (z : Matrix (Fin d) (Fin a) D.host.E) : ptHom D cc δ a d z = pt D (tor0 D cc δ) δ z := rfl

theorem ptHom_injective (D : D7) (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) (a d : ℕ) :
    Function.Injective (ptHom D cc δ a d) := by
  intro y y' h
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D (D.eTau.symm 1) (y i j) = δ * embT D (D.eTau.symm 1) (y' i j) :=
    congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem ptHom_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (c : 𝓞 D.host.K)
    (y : Matrix (Fin d) (Fin a) D.host.E) :
    ptHom D cc δ a d (((c : D.host.K) : D.host.E) • y) =
      (δ * D.host.φ₀ ((c : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) y := by
  funext τ i j
  simp only [ptHom_apply, pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    GlobalTheory.InducedType.restrict_K D τ, mul_assoc]

theorem single_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (i : Fin d) (j : Fin a)
    {t : D.host.E} (ht : t ∈ coefLat D cc) (r : 𝓞 D.host.E) :
    ptHom D cc δ a d (Matrix.single i j (r • t)) ∈ La0 D (tor0 D cc δ) a d := by
  induction ht using Submodule.span_induction generalizing r with
  | mem t ht =>
    obtain ⟨c, hc, m, hm, rfl⟩ := ht
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Matrix.single i j (r • m), ?_, ?_⟩
    · refine (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_
      rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hm
      · exact D.host.AA0.zero_mem
    · rw [← ptHom_smul, Matrix.smul_single, smul_eq_mul, mul_smul_comm]
  | zero => rw [smul_zero, Matrix.single_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add, Matrix.single_add, map_add (f := _)]; exact add_mem (hx r) (hy r)
  | smul s x _ hx => rw [smul_smul]; exact hx _

theorem La0_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    La0 D (tor0 D cc δ) a d = (lat0 D cc a d).map (ptHom D cc δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D cc δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D cc δ a d c A⟩
    exact Submodule.subset_span ⟨c, hc, A i j, (GlobalTheory.OddGenus.mem_iff_entries D a d A).1 hA i j, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single z, map_sum]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun j _ => ?_
    simpa using single_mem D cc δ a d i j (hz i j) 1

end GlobalTheory.ThetaLatticePoints
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockOrdFinSumFinEquiv
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem blockOrd_finSumFinEquiv (p q : ℕ) :
    GlobalTheory.RealPar.BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have : a < b := hab
    exact (Fin.strictMono_castAdd q) this
  · exact hab.elim
  · exact hab.elim
  · have : a < b := hab
    exact (Fin.strictMono_natAdd p) this

end GlobalTheory.HolDS
end

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem eq_one_of_smul_haar_eq {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [LocallyCompactSpace H] (ν : Measure H) [ν.IsHaarMeasure] {c : NNReal} (h : c • ν = ν) :
    c = 1 := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have h1 : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (c : ENNReal) * ν K = 1 * ν K := by
    conv_rhs => rw [← h]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_left_inj h0 h1] at h2
  exact_mod_cast h2

theorem haar_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant := by
  intro p q T
  have h := blockOrd_finSumFinEquiv p q
  haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T
  set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
  set f := GlobalTheory.RealPar.SqInt.covU h T
  have hf : Measurable f := (GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable
  obtain ⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hR : T.haar.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have hg := Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g
    have h1 : (T.haar.map (· * g)).map f = T.haar.map f := by
      have h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g) := by
        rw [Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]
        congr 1
        ext x
        simp
      rw [h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]
      exact (measurable_mul_const _).aemeasurable
    rw [hg, Measure.map_smul] at h1
    · rw [hg, eq_one_of_smul_haar_eq _ h1, one_smul]
    · exact hf.aemeasurable
  refine ⟨hR, ⟨?_⟩⟩
  haveI : T.haar.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have h1 : T.haar.inv.map f = T.haar.map f := by
    have h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹) := by
      rw [Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]
      congr 1
      ext x
      simp
    rw [h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]
    exact measurable_inv.aemeasurable
  rw [hd, Measure.map_smul] at h1
  · rw [hd, eq_one_of_smul_haar_eq _ h1, one_smul]
  · exact hf.aemeasurable

end GlobalTheory.HolDS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBound
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.CoordConj

theorem cj_coe (ρ : Qbar →ₐ[ℚ] ℂ) (w : Qbar) : cj Qbar ρ (w : ℂ) = ρ w := by
  simp [cj, TaylorLogMetric.liftM]

theorem differentiable_U {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N')) {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U _ hG).const_mul _).const_mul _

theorem applyAt0_comb {D : D7} {a d : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (G : ι → VC D a d → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i)) (p : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D p (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * GL3Theta.applyAt0 D p (G i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) 0 (differentiable_const 0)).2.2.1 0 p
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ ((hG i).const_smul (c i))).2.2.2 _ p
        (Differentiable.sum fun j _ => (hG j).const_smul (c j)), ih,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ (hG i)).2.2.1]

theorem comb_bound {ι : Type} [Fintype ι] (ρ : Qbar →ₐ[ℚ] ℂ) (r : ι → Qbar) (t : ι → ℂ) (S M : ℝ) (hM : 0 ≤ M)
    (hr : (∑ i, ‖ρ (r i)‖) ^ 2 ≤ S) (ht : ∀ i, t i ∈ Qbar ∧ ‖cj Qbar ρ (t i)‖ ^ 2 ≤ M) :
    ∑ i, (r i : ℂ) * t i ∈ Qbar ∧ ‖cj Qbar ρ (∑ i, (r i : ℂ) * t i)‖ ^ 2 ≤ S * M := by
  have e : ∑ i, (r i : ℂ) * t i = ((∑ i, r i * ⟨t i, (ht i).1⟩ : Qbar) : ℂ) := by
    push_cast
    rfl
  refine ⟨e ▸ SetLike.coe_mem _, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, cj_coe, map_sum]
  have h1 : ∀ i, ‖ρ ⟨t i, (ht i).1⟩‖ ≤ Real.sqrt M := fun i => by
    rw [← cj_coe]
    exact Real.le_sqrt_of_sq_le (ht i).2
  have h2 : ‖∑ i, ρ (r i * ⟨t i, (ht i).1⟩)‖ ≤ (∑ i, ‖ρ (r i)‖) * Real.sqrt M := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg _)
  calc _ ≤ ((∑ i, ‖ρ (r i)‖) * Real.sqrt M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = (∑ i, ‖ρ (r i)‖) ^ 2 * M := by rw [mul_pow, Real.sq_sqrt hM]
    _ ≤ S * M := mul_le_mul_of_nonneg_right hr hM

theorem coord_conj_le : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D hI cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact GlobalTheory.T.vacuumTranslate_conjugate_jet_bound D hI cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := GlobalTheory.T.definiteThetaPair_testVector_expansion D hI cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := GlobalTheory.T.intertwiner_selfDual_vacuum_isVacuum D hI cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, applyAt0_comb _ _ _ fun i => differentiable_U _ hGd]
    refine comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.NormSum.CoordConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBoundStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPair_coordinates_conjugate_bound : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.NormSum.CoordConj.coord_conj_le | exact GlobalTheory.NormSum.CoordConj.coord_conj_le | (intros; apply GlobalTheory.NormSum.CoordConj.coord_conj_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerEqNormalisedAdelicSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerEqNormalisedAdelicSum
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.IopSum

theorem act_inv_act {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u⁻¹ (actA D N N' u ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_act_inv {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u (actA D N N' u⁻¹ ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem mem_map_act {D : D7} {N N' : ℕ} (A : Submodule (𝓞 D.host.E) (XA D N N')) (u : GA D N × GA D N') (ζ : XA D N N') :
    ζ ∈ A.map (actA D N N' u) ↔ actA D N N' u⁻¹ ζ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv u ζ⟩

theorem mem_moved {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    ζ ∈ (latA D cc N N').map (actA D N N' (g, g')) ↔
      ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  rw [mem_map_act, Prod.inv_mk, actA_apply, mem_latA, Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem pt_sub {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - z') = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ z' := by
  funext τ i j
  simp [pt, embV, tor0, mul_sub]

theorem sd_of_moves {D : D7} {N : ℕ} (g : GA D N) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := Submodule.ext fun x => (h x).trans ((hLt g).1 x).symm
  rw [this]
  exact (hLt g).2

end GlobalTheory.FinWeil.IopSum

namespace GlobalTheory.FinWeil

open IopSum

theorem iop_eq_sumOp : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  intro D hG cc δ hC N N' w γ WA hM g g' L₁ L₁' hL hL' hSD F hF
  obtain ⟨hlat1, -, hlat3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  have hidx := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g g').1
  have hidx' := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g⁻¹ g'⁻¹).1
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hW := (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨L₁, L₁', sd_of_moves g hL, sd_of_moves g' hL', rfl⟩)).2.1
  simp only [← mem_moved] at hA hB
  set A := latA D cc N N' with hAdef
  set B := A.map (actA D N N' (g, g')) with hBdef
  set La₂ := La D (tor0 D cc δ) L₁ L₁' with hLa₂
  set La₁ := La0 D (tor0 D cc δ) N N' with hLa₁

  have hm : ∀ a ∈ A, idx A (A.map (actA D N N' (g⁻¹, g'⁻¹))) • a ∈ B := by
    intro a ha
    rw [hBdef, mem_map_act, map_nsmul, Prod.inv_mk]
    exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (A.map (actA D N N' (g⁻¹, g'⁻¹))).toAddSubgroup) ⟨a, ha, rfl⟩
  choose z hz hzB using fun q : La₂ ⧸ La₁.addSubgroupOf La₂ => hA _ (Quotient.out q).2
  have hsub : ∀ x y : Matrix (Fin N') (Fin N) D.host.E, x.map (inc D) - y.map (inc D) ∈ A ↔
      pt D (tor0 D cc δ) δ x - pt D (tor0 D cc δ) δ y ∈ La₁ := by
    intro x y
    rw [← Matrix.map_sub _ (map_sub (inc D)), hlat1, pt_sub]
  have huniq : ∀ q q', (z q).map (inc D) - (z q').map (inc D) ∈ A → q = q' := by
    intro q q' h
    rw [hsub, ← hz, ← hz] at h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  have htr : ∀ b ∈ B, ∃! q, b - (z q).map (inc D) ∈ A := by
    intro b hb
    obtain ⟨y, a, ha, hy⟩ := hlat3 b _ (Nat.pos_of_ne_zero hidx')
    have hyB : y.map (inc D) ∈ B := hy ▸ B.add_mem hb (hm a ha)
    have hex : b - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
      have h1 : y.map (inc D) - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
        rw [hsub, ← hz]
        have h2 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨_, hB y hyB⟩ : La₂ ⧸ La₁.addSubgroupOf La₂)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
        simpa [neg_add_eq_sub] using h2
      have h3 := A.sub_mem h1 (nsmul_mem ha (idx A (A.map (actA D N N' (g⁻¹, g'⁻¹)))))
      rw [hy] at h3
      convert h3 using 1
      abel
    refine ⟨QuotientAddGroup.mk ⟨_, hB y hyB⟩, ?_, ?_⟩
    · exact hex
    · intro q hq
      refine huniq _ _ ?_
      have := A.sub_mem hex hq
      rwa [sub_sub_sub_cancel_left] at this
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hidx
  haveI : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine Finite.of_injective (fun q => (QuotientAddGroup.mk ⟨_, hzB q⟩ :
      B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)) fun q q' h => ?_
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (huniq q' q ?_).symm
    simpa [neg_add_eq_sub] using h
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinWeil.sumOp_transversal hM.1 A B hSD).1 F hF _ (fun q => (z q).map (inc D)) hzB htr
  rw [h1, h2]
  funext v
  rw [Iop, finsum_eq_sum_of_fintype, AddSubgroup.index, Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.2.2.2.1, ← hz, hW _ (Quotient.out q).2]

end GlobalTheory.FinWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerEqNormalisedAdelicSumStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  first | exact @GlobalTheory.FinWeil.iop_eq_sumOp | exact GlobalTheory.FinWeil.iop_eq_sumOp | (intros; apply GlobalTheory.FinWeil.iop_eq_sumOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanA
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanA
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem U_pullB_eq_prod (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (g : ℂ → ℂ) (t z : VC D N N') :
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b g) z =
      ∏ j, U1 (lamOf D cc δ) (coordB D (tor0 D cc δ) b j t) g (coordB D (tor0 D cc δ) b j z) := by
  obtain ⟨-, -, hP, -, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by rw [coordB_add]
  · congr 1
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tor0]
    ring

theorem normalisedThetaPullback_mem_torsionTranslatesSpan (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (N N' r : ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) :
    pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hgood := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  obtain ⟨-, -, -, hL, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  set t : VC D N N' := ∑ j, (fun _ : Fin r => t0) j • embV D (tor0 D cc δ) (b j) with htdef
  have hco : ∀ j, coordB D (tor0 D cc δ) b j t = t0 := fun j => hgood.coordB_sum hb.1 _ j
  have h2 : (2 : ℕ) • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [two_nsmul, coordB_add, hco, ← two_mul]
    exact ht.1
  have hq : U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0 ∈ Qbar := by
    have := (GlobalTheory.T.forall_use1 D cc δ hc).1 t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ 0
    simpa [coef1] using this
  have hmem : U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∈
      Tr D (tor0 D cc δ) b := Submodule.subset_span ⟨t, ⟨2, two_pos, h2⟩, rfl⟩
  have := Submodule.smul_mem _
    (⟨(U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r, pow_mem (inv_mem hq) r⟩ : Qbar) hmem
  convert this using 1
  funext z
  change _ = (U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹ ^ r *
    U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
  rw [U_pullB_eq_prod D hG cc δ b hb]
  simp only [hco, pullB, GL3Theta.th0, div_eq_inv_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end GlobalTheory.ThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalisedThetaPullbackMemTorsionTranslatesSpanAStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullB_th0_mem_tr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | exact GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan | (intros; apply GlobalTheory.ThetaConj.normalisedThetaPullback_mem_torsionTranslatesSpan <;> assumption)
end
end
