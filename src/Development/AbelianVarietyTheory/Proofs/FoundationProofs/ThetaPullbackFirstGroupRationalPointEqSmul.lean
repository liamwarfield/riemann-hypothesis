module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatRow

variable {D : D7} {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h : ∀ y, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply _ y
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, conj_conj]

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L₁ L₁'}
    (h : Moves D (g : GL (Fin N) (AE D)) L₁) (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    KLat D T (La D T L₁ L₁') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem isRat_one (D : D7) (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem hf_unitary (T : Tor D) {M' : Matrix (Fin N') (Fin N') D.host.E} {M : Matrix (Fin N) (Fin N) D.host.E}
    (h' : adj D M' * M' = 1) (h : M * adj D M = 1) (z w : VC D N N') :
    Hf D T (mulV D M' M z) (mulV D M' M w) = Hf D T z w := by
  rw [Hf_mulV, mulV_mulV, h', h, mulV_one]

theorem mulV_comm (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') :
    mulV D M' 1 (mulV D 1 M z) = mulV D 1 M (mulV D M' 1 z) := by
  simp only [mulV_mulV, Matrix.mul_one, Matrix.one_mul]

theorem mulV_scalar (a : D.host.E) (z : VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    mulV D (Matrix.diagonal fun _ => a) 1 z τ i j = embT D τ a * z τ i j := by
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  rfl

def revM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E := Matrix.of fun i j => if j = i.rev then 1 else 0

def halfM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E :=
  Matrix.diagonal fun i => if i < i.rev then 1 else 0

theorem revM_mul_self (n : ℕ) : revM D n * revM D n = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun k _ hk => by simp [revM, hk]) (by simp)]
  simp [revM, Matrix.one_apply, eq_comm]

theorem adj_revM (n : ℕ) : adj D (revM D n) = revM D n := by
  refine Matrix.ext fun i j => ?_
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> rintro rfl <;> simp
  simp only [adj, revM, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, this]
  split_ifs <;> simp

theorem halfM_mul_self (n : ℕ) : halfM D n * halfM D n = halfM D n := by
  rw [halfM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem adj_halfM (n : ℕ) : adj D (halfM D n) = halfM D n := by
  rw [adj, halfM, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  funext i
  split_ifs <;> simp

theorem revM_mul_halfM {n : ℕ} (hn : Even n) : revM D n * halfM D n = revM D n - halfM D n * revM D n := by
  refine Matrix.ext fun i j => ?_
  obtain ⟨k, rfl⟩ := hn
  simp only [halfM, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, revM, Matrix.of_apply]
  by_cases h : j = i.rev
  · subst h
    have hi := i.2
    by_cases h1 : i < i.rev
    · have h2 : ¬ i.rev < i := not_lt.2 h1.le
      simp [h1, h2]
    · have h2 : i.rev < i := by
        rw [Fin.lt_def, Fin.val_rev] at *
        omega
      simp [h1, h2]
  · simp [h]

theorem integral_diagonal {n : ℕ} {d : Fin n → D.host.E} (hd : ∀ i, IsIntegral ℤ (d i)) (i j : Fin n) :
    IsIntegral ℤ (Matrix.diagonal d i j) := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact isIntegral_zero

theorem integral_one {n : ℕ} (i j : Fin n) : IsIntegral ℤ ((1 : Matrix (Fin n) (Fin n) D.host.E) i j) :=
  integral_diagonal (fun _ => isIntegral_one) i j

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  rw [adj, Matrix.det_transpose]
  exact ((D.host.conj : D.host.E →+* D.host.E).map_det M).symm

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, Matrix.one_apply, eq_comm]

theorem det_mul_conj (hN : Even N) {γ : Matrix (Fin N) (Fin N) D.host.E} (h : γ * adj D γ = 1) :
    γ.det * D.host.conj (1 - γ).det = (1 - γ).det := by
  rw [← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, h, Matrix.mul_one, ← neg_sub, Matrix.det_neg,
    Fintype.card_fin, hN.neg_one_pow, one_mul]

theorem phase {g w : ℂ} (hw : w ≠ 0) (h : g * (starRingEnd ℂ) w = w) (k : ℕ) :
    ((‖w ^ (k + k)‖ : ℝ) : ℂ) / w ^ (k + k) = g ^ (-(k : ℤ)) := by
  have hg : g ≠ 0 := by rintro rfl; exact hw (by simpa using h.symm)
  have h1 : ((‖w ^ (k + k)‖ : ℝ) : ℂ) = (w * (starRingEnd ℂ) w) ^ k := by
    rw [Complex.mul_conj', norm_pow, ← two_mul, pow_mul]; push_cast; rfl
  rw [h1, zpow_neg, zpow_natCast, div_eq_iff (pow_ne_zero _ hw), eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hg), ← mul_pow,
    mul_left_comm, h, mul_pow, pow_add]

theorem pull_eq_smul_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hr hdet hm
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D N).2.2.2.1 γA γ hr
  have hu' : adj D γ * γ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨hint, hden, hmov⟩ := GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ)
    (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one])
    (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])
  have ua : ∀ z, u z = mulV D 1 (adj D γ) z := fun _ => rfl
  have us : ∀ z, u.symm z = mulV D 1 γ z := fun _ => rfl
  have hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ) :=
    LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl
  have hd : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - γ).det ^ N' := by
    rw [hid, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]; simp
  have hw : ∀ τ, embT D τ (1 - γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hdet
  have key := GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N'))
    (klat _ (moves_one D N) (moves_one D N')) (klat _ hm (moves_one D N')) u
    (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu']))
    (hmov γA 1 γ 1 L₁ _ hr (isRat_one D N') hm (moves_one D N'))
    (by rw [hd]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ)) ?_
    (mulV D (halfM D N') 1) (mulV D (revM D N') 1) ?_
    (fun x => by rw [mulV_mulV, halfM_mul_self, Matrix.one_mul])
    (fun x y => by rw [Hf_mulV, adj_halfM, adj_one])
    (fun x => by rw [mulV_mulV, revM_mul_self, Matrix.one_mul, mulV_one])
    (hf_unitary _ (by rw [adj_revM, revM_mul_self]) (by rw [adj_one, Matrix.one_mul]))
    (fun x => by rw [mulV_mulV, mulV_mulV, revM_mul_halfM hN', Matrix.one_mul, mulV_sub_left])
    (fun x => mulV_comm _ _ x) (fun x => mulV_comm _ _ x) ?_ th hth
  · rw [pull_eq, adj_one]
    refine key.trans ?_
    congr 1
    obtain ⟨k, rfl⟩ := hN'
    rw [hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, show (k + k) / 2 = k by omega]
    refine Finset.prod_congr rfl fun τ _ => phase (hw τ) ?_ k
    rw [← embT_conj, ← map_mul, det_mul_conj hN hu]
  · obtain ⟨m₁, h₁, g₁⟩ := hden 1 (1 - γ)⁻¹
    obtain ⟨m₂, h₂, g₂⟩ := hden 1 ((1 - γ)⁻¹ * γ)
    have e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) = (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x := by
      intro x
      rw [map_nsmul, us, mulV_mulV, Matrix.one_mul]
    refine ⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]; exact nsmul_mem (g₁ x hx) _
    · rw [e, mul_smul]; exact nsmul_mem (g₂ x hx) _
    · have h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1 := by
        have := Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)
        rwa [Matrix.mul_sub, Matrix.mul_one] at this
      rw [e, ← smul_sub, ← mulV_sub_right, h1, mulV_one]
  · refine fun x hx => ⟨hint _ _ (integral_diagonal fun i => ?_) integral_one x hx,
      hint _ _ (fun i j => ?_) integral_one x hx⟩
    · split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · rw [revM, Matrix.of_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  · intro M hM
    obtain ⟨l, b, hlb⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
    have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have hb : D.host.conj (b : D.host.E) = b := by
      have := congrArg D.host.conj hlb
      rw [map_mul, conj_conj, mul_comm, hlb, map_add (f := _), map_neg, map_one, map_mul, map_natCast] at this
      exact (mul_left_cancel₀ hM' (add_left_cancel this)).symm
    refine ⟨mulV D (Matrix.diagonal fun _ => (l : D.host.E)) 1, mulV D (Matrix.diagonal fun _ => (b : D.host.E)) 1,
      fun x hx => ⟨hint _ _ (integral_diagonal fun _ => l.2) integral_one x hx,
        hint _ _ (integral_diagonal fun _ => b.2) integral_one x hx⟩,
      fun x => mulV_comm _ _ x, fun x => mulV_comm _ _ x, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [mulV_mulV, mulV_mulV, halfM, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      simp only [mul_comm]
    · rw [Hf_mulV, adj_one, adj, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
      simp only [hb]
    · have h : ∀ τ, embT D τ l * (starRingEnd ℂ) (embT D τ l) = -1 + M * embT D τ b := by
        intro τ
        rw [← embT_conj, ← map_mul, hlb]; simp
      simp only [Hf, mulV_scalar, ← neg_div, ← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, map_mul]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      linear_combination (x τ i j * (starRingEnd ℂ) (y τ i j)) * h τ

end GlobalTheory.RatRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmulStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  first | exact @GlobalTheory.RatRow.pull_eq_smul_iop | exact GlobalTheory.RatRow.pull_eq_smul_iop | (intros; apply GlobalTheory.RatRow.pull_eq_smul_iop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockIntertwinerCommutesUnitaryAndExtends
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockIntertwinerCommutesUnitaryAndExtends
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockExtGroup

theorem pi_comm {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (g, 1) (F.π (1, h) x) = F.π (1, h) (F.π (g, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem comm_and_extend : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  intro p q n T0 T1 T2 F hn D τ M j I v₀ hτ hM hv₀ hI hJ
  obtain ⟨hfin, -, -, hirr⟩ := GlobalTheory.CompactCoverIrr.hcMod_finite_irr n hn T2 τ M j hτ hM ⟨v₀, 0, hv₀⟩
  obtain ⟨hF, -, hder⟩ := GlobalTheory.FockEmbExp.fock_derived p q n 0 T0 T1 T2 F
  let σ : URep T2 :=
    { H := F.H
      π := F.π.comp (MonoidHom.inr _ _)
      isom := fun _ x => F.isom _ x
      cont := fun x => (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id)) }
  have h1 : ∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
      F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v')) := by
    intro h x v v' hv
    have hK : h ∈ T2.Kset := by
      rintro (a | a) (b | b) hab
      · exact (hab trivial).elim
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
    let j₂ : M.V →ₗ[ℂ] σ.H := F.ι ∘ₗ I ∘ₗ TensorProduct.mk ℂ D.HK.V M.V x
    obtain ⟨w, hw1, hw2⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie n 0 T2
      (GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T2) τ σ M.V (fun Y => M.act Y) j j₂
      (fun Y hY _ w => ⟨hM.2.2 Y hY w, by
        have h2 := hder Y hY (I (x ⊗ₜ w))
        have h3 : fockAct2 p q n 0 Y (I (x ⊗ₜ w)) = I (x ⊗ₜ M.act Y w) := hI.2 Y x w
        rw [h3] at h2
        exact h2⟩) h hK v
    obtain rfl : v' = w := hM.1 (hv.trans hw1)
    exact hw2
  refine ⟨h1, ?_⟩
  let N : Submodule ℂ M.V :=
    { carrier := {v | ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
        ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)}
      add_mem' := by
        rintro a b ⟨J, hJ1, hJ2⟩ ⟨J', hJ1', hJ2'⟩
        exact ⟨J + J', fun x => by simp [hJ1, hJ1', TensorProduct.tmul_add],
          fun g y => by simp [hJ2, hJ2']⟩
      zero_mem' := ⟨0, fun x => by simp, fun g y => by simp⟩
      smul_mem' := by
        rintro c a ⟨J, hJ1, hJ2⟩
        exact ⟨c • J, fun x => by simp [hJ1, TensorProduct.tmul_smul],
          fun g y => by simp [hJ2]⟩ }
  rcases hirr N (by
    rintro h v ⟨J, hJ1, hJ2⟩ v' hv
    refine ⟨F.π (1, h) ∘L J, fun x => ?_, fun g y => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, hJ1, h1 h x v v' hv]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pi_comm, hJ2]) with h | h
  · have : v₀ ∈ N := hJ
    rw [h] at this
    exact (hv₀ this).elim
  · intro v
    have : v ∈ N := h ▸ Submodule.mem_top
    exact this

end GlobalTheory.FockExtGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockIntertwinerCommutesUnitaryAndExtendsStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  first | exact @GlobalTheory.FockExtGroup.comm_and_extend | exact GlobalTheory.FockExtGroup.comm_and_extend | (intros; apply GlobalTheory.FockExtGroup.comm_and_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGK
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfIsometryEigenOfDenseISup
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory

theorem mem_of_isometry_eigen_of_dense_iSup :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (m : ℕ) (y : H), U y = lam m • y → y ∈ E m := by
  intro H _ _ _ U hU E lam hlam hfin hE hd m y hy
  let V : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  have hin : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => V.inner_map_map a b
  haveI := hfin m
  obtain ⟨p, hp, q, hq, rfl⟩ := (E m).exists_add_mem_mem_orthogonal y
  have hUq : U q = lam m • q := by
    rw [map_add (f := _), hE m p hp, smul_add] at hy
    exact add_left_cancel hy
  have horth : ∀ m', ∀ e ∈ E m', ⟪e, q⟫_ℂ = 0 := by
    intro m' e he
    by_cases hm : m' = m
    · subst hm
      exact (Submodule.mem_orthogonal _ _).1 hq e he
    by_cases he0 : e = 0
    · simp [he0]
    have h1 := hin e q
    have h2 := hin e e
    rw [hE m' e he, hUq, inner_smul_left, inner_smul_right] at h1
    rw [hE m' e he, inner_smul_left, inner_smul_right] at h2
    have hee : ⟪e, e⟫_ℂ ≠ 0 := by simpa using he0
    have h3 : (starRingEnd ℂ) (lam m') * lam m' = 1 := by
      apply mul_right_cancel₀ hee
      rw [one_mul, mul_assoc, h2]
    by_contra hne
    have h4 : (starRingEnd ℂ) (lam m') * lam m = 1 := by
      apply mul_right_cancel₀ hne
      rw [one_mul, mul_assoc, h1]
    have h5 : (starRingEnd ℂ) (lam m') ≠ 0 := left_ne_zero_of_mul_eq_one h3
    exact hm (hlam (mul_left_cancel₀ h5 (h3.trans h4.symm)))
  have hle : (⨆ m, E m : Submodule ℂ H) ≤ (ℂ ∙ q)ᗮ := by
    refine iSup_le fun m' e he => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact horth m' e he
  have hq0 : q = 0 := by
    have hcl : closure ((⨆ m, E m : Submodule ℂ H) : Set H) ⊆ ((ℂ ∙ q)ᗮ : Submodule ℂ H) :=
      closure_minimal hle (Submodule.isClosed_orthogonal _)
    have := hcl (hd q)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    simpa using this
  simpa [hq0] using hp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGK
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem irrU_of_dense_graded_irrGK :
    ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  intro p q T σ M j hinj hd hder hirr N k lam hfin hN _ hlam heig
  haveI := hirr.1
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hreal : ∀ Y ∈ upq p q, ∀ y, j y ∈ S → j (M.act Y y) ∈ S := by
    intro Y hY y hy
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder Y hY y)
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (inner ℂ w (j (M.act Y y))) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
      exact (Submodule.inner_left_of_mem_orthogonal (hinv _ _ hy) hw).symm
    exact h2.unique (hasDerivAt_const _ _)
  have hstab : ∀ Z, ∀ y ∈ S.comap j, M.act Z y ∈ S.comap j := by
    intro Z y hy
    obtain ⟨X, hX, Y, hY, rfl⟩ := GlobalTheory.FockTensor.exists_upq_add Z
    rw [Submodule.mem_comap] at hy ⊢
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact S.add_mem (hreal X hX y hy) (S.smul_mem _ (hreal Y hY y hy))
  rcases hirr.2 _ hstab with h | h
  · left
    have hperp : ∀ b ∈ Sᗮ, σ.π k b ∈ Sᗮ := by
      intro b hb
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [GlobalTheory.FockTensor.inner_pi_left]
      exact Submodule.inner_left_of_mem_orthogonal (hinv _ _ hu) hb
    have hdense : Dense ((⨆ m, (N m).map j : Submodule ℂ σ.H) : Set σ.H) := by
      rw [← Submodule.map_iSup, hN, Submodule.map_top]
      exact hd
    have hle : (⨆ m, (N m).map j : Submodule ℂ σ.H) ≤ Sᗮ := by
      refine iSup_le fun m => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := S.exists_add_mem_mem_orthogonal (j x)
      have he := heig m x hx
      rw [hab, map_add (f := _), smul_add] at he
      have hdiff : σ.π k a - lam m • a = lam m • b - σ.π k b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have h1 : σ.π k a - lam m • a ∈ S := S.sub_mem (hinv _ _ ha) (S.smul_mem _ ha)
      have h2 : σ.π k a - lam m • a ∈ Sᗮ := by
        rw [hdiff]
        exact Sᗮ.sub_mem (Sᗮ.smul_mem _ hb) (hperp b hb)
      have h3 : σ.π k a = lam m • a :=
        sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2))
      have h4 := GlobalTheory.mem_of_isometry_eigen_of_dense_iSup σ.H (σ.π k) (σ.isom k)
        (fun m => (N m).map j) lam hlam (fun m => by haveI := hfin m; infer_instance)
        (by rintro m _ ⟨x, hx, rfl⟩; exact heig m x hx) hdense m a h3
      obtain ⟨x', -, hx'⟩ := h4
      have h5 : x' ∈ S.comap j := by rw [Submodule.mem_comap, hx']; exact ha
      rw [h, Submodule.mem_bot] at h5
      rw [h5, map_zero] at hx'
      rw [hab, ← hx', zero_add]
      exact hb
    rw [← Submodule.orthogonal_eq_top_iff, eq_top_iff]
    intro v _
    exact closure_minimal hle S.isClosed_orthogonal (hdense v)
  · right
    rw [eq_top_iff]
    intro v _
    refine closure_minimal ?_ hS (hd v)
    rintro _ ⟨x, rfl⟩
    have : x ∈ S.comap j := by rw [h]; trivial
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGKStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_completion_of_graded_irreducible_gK : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  first | exact @GlobalTheory.irrU_of_dense_graded_irrGK | exact GlobalTheory.irrU_of_dense_graded_irrGK | (intros; apply GlobalTheory.irrU_of_dense_graded_irrGK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalStableLeISupEigen
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem form_aeval_of_left_eigen {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (φ : V →ₗ[ℂ] ℂ) (c : ℂ) (h : ∀ v, φ (T v) = c * φ v) (f : Polynomial ℂ) (v : V) :
    φ (Polynomial.aeval T f v) = f.eval c * φ v := by
  have hpow : ∀ (n : ℕ) (v : V), φ ((T ^ n) v) = c ^ n * φ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, h]; ring
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_smul, hpow, smul_eq_mul, mul_assoc]

theorem finiteDimensional_stable_le_iSup_eigen :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → (∀ w ∈ W, U w ∈ W) → W ≤ ⨆ m, E m := by
  intro H _ _ _ U hU E lam hinj hfin heig hdense W hW hst
  classical
  have hinner : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    (⟨(U : H →ₗ[ℂ] H), hU⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hleft : ∀ m, ∀ e ∈ E m, ∀ y, ⟪e, U y⟫_ℂ = lam m * ⟪e, y⟫_ℂ := by
    intro m e he y
    by_cases h0 : e = 0
    · simp [h0]
    have h1 : ‖lam m‖ = 1 := by
      have := hU e
      rw [heig m e he, norm_smul] at this
      have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      exact mul_right_cancel₀ hne (by rw [this, one_mul])
    have h2 : lam m * (starRingEnd ℂ) (lam m) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have h3 := hinner e y
    rw [heig m e he, inner_smul_left] at h3
    rw [← h3, ← mul_assoc, h2, one_mul]
  let T : Module.End ℂ W := (U : H →ₗ[ℂ] H).restrict hst
  let f : Polynomial ℂ := LinearMap.charpoly T
  have hf0 : f ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hfT : Polynomial.aeval T f = 0 := LinearMap.aeval_self_charpoly T
  have hsfin : (lam ⁻¹' {z | f.IsRoot z}).Finite :=
    (Polynomial.finite_setOf_isRoot hf0).preimage hinj.injOn
  let s : Finset ℕ := hsfin.toFinset
  have hout : ∀ m, m ∉ s → ∀ e ∈ E m, ∀ y ∈ W, ⟪e, y⟫_ℂ = 0 := by
    intro m hm e he y hy
    have hne : f.eval (lam m) ≠ 0 := by
      intro h
      exact hm (hsfin.mem_toFinset.mpr h)
    have := form_aeval_of_left_eigen T (((innerₛₗ ℂ e : H →ₗ[ℂ] ℂ)).comp W.subtype) (lam m)
      (fun v => hleft m e he v) f ⟨y, hy⟩
    rw [hfT] at this
    simp only [LinearMap.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  let F : Submodule ℂ H := ⨆ m ∈ s, E m
  haveI hF : FiniteDimensional ℂ F := by
    have : F = s.sup E := by simp [F, Finset.sup_eq_iSup]
    rw [this]; infer_instance
  have hFle : F ≤ ⨆ m, E m := iSup₂_le fun m _ => le_iSup E m
  have hForth : ∀ m, m ∉ s → F ≤ (E m)ᗮ := by
    intro m hm
    refine iSup₂_le fun k hk x hx => ?_
    rw [Submodule.mem_orthogonal]
    intro e he
    have h1 := hleft m e he x
    rw [heig k x hx, inner_smul_right] at h1
    have hne : lam k - lam m ≠ 0 := by
      intro h
      have := hinj (sub_eq_zero.mp h)
      exact hm (this ▸ hk)
    have : (lam k - lam m) * ⟪e, x⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  intro y hy
  have hz : y - F.starProjection y ∈ (⨆ m, E m)ᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    by_cases hm : m ∈ s
    · have hle : E m ≤ F := le_iSup₂_of_le (f := fun m (_ : m ∈ s) => E m) m hm le_rfl
      exact Submodule.orthogonal_le hle (Submodule.sub_starProjection_mem_orthogonal y)
    · refine Submodule.sub_mem _ ?_ (hForth m hm (F.starProjection_apply_mem y))
      rw [Submodule.mem_orthogonal]
      intro e he
      exact hout m hm e he y hy
  have hz0 : y - F.starProjection y = 0 := by
    have htop : (⨆ m, E m : Submodule ℂ H).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rw [Submodule.topologicalClosure_eq_top_iff] at htop
    rw [htop] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  rw [sub_eq_zero.mp hz0]
  exact hFle (F.starProjection_apply_mem y)

end GlobalTheory.HolDS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedKFin

variable {p q : ℕ}

theorem kset_one (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    cases a <;> simp [sameBlock] at hab
  simp [Matrix.one_apply, this]

theorem kset_mul (T : GrpData p q) {g h : T.G} (hg : g ∈ T.Kset) (hh : h ∈ T.Kset) :
    g * h ∈ T.Kset := by
  intro a b hab
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := by
      cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
    rw [hh c b hcb, mul_zero]
  · rw [hg a c hac, zero_mul]

theorem map_stable (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q)
    (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    {g : T.G} (hg : g ∈ T.Kset) : ∀ x ∈ W.map j, σ.π g x ∈ W.map j := by
  have hcl := GlobalTheory.CoverKGen.kset_gen p q hpq T g hg
  suffices h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1
  clear hg
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨Y, ⟨hY, hKC⟩, rfl⟩ := hg
    have hf := GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)
    have hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY 1 (-1)
      rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at this
      exact (eq_inv_of_mul_eq_one_right this.symm).symm
    refine ⟨?_, ?_⟩
    · have := hf 1
      simpa only [one_smul] using this
    · rw [hinv]; exact hf (-1)
  | one => simp
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul]; exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 x hx)
  | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isHCMod_of_graded : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  intro p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig
  refine ⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨W, hWf, hv, hW⟩ := M.kfin v
    have hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · have hsup : (⨆ m, (N m).map j) = LinearMap.range j := by
      rw [← Submodule.map_iSup, htop, Submodule.map_top]
    have hle := GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k)
      (fun m => (N m).map j) lam hlam (fun m => inferInstance)
      (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy)
      (by rw [hsup]; exact hd)
      (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨g, rfl⟩ := hw
          refine Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩
          simp only [map_mul]
          rfl
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
    rw [hsup] at hle
    exact hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)

end GlobalTheory.GradedKFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGKStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHCModule_of_graded_dense_gK : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  first | exact @GlobalTheory.GradedKFin.isHCMod_of_graded | exact GlobalTheory.GradedKFin.isHCMod_of_graded | (intros; apply GlobalTheory.GradedKFin.isHCMod_of_graded <;> assumption)
end
end
