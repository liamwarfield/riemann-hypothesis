module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCusps
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SwdTendstoZeroAtCusps
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHigh
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCuspsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBounded
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace InvBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem exists_int_sum_type (hΨ : IsType Ψ) {t : E} (ht : IsIntegral ℤ t) (hc : cc t = t) :
    ∃ k : ℤ, ∑ τ : Ψ, τ.1 (2 * t) = k := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E t) := Algebra.isIntegral_trace ht
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨k, ?_⟩
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := t)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ σ : E →+* ℂ, σ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom _ _) _ _ fun _ => rfl).symm
  have h4 : ∑ σ ∈ Ψᶜ, σ t = ∑ σ ∈ Ψ, σ t := by
    refine Finset.sum_bij' (fun σ _ => ComplexEmbedding.conjugate σ)
      (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      by_contra h
      exact (Finset.mem_compl.1 hσ) ((hΨ σ).2 h)
    · intro σ hσ
      exact Finset.mem_compl.2 ((hΨ σ).1 hσ)
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _
      have := Base.map_cc σ t
      rw [hc] at this
      simpa using this
  rw [h3, ← Finset.sum_add_sum_compl Ψ, h4, ← hk] at h2
  rw [Finset.sum_coe_sort Ψ (fun τ => τ (2 * t))]
  simp only [map_mul, map_ofNat, ← Finset.mul_sum]
  rw [two_mul, ← h2]
  simp

theorem chiH_eq_one (hΨ : IsType Ψ) (R : ℕ) {y : Matrix (Fin N) (Fin N) E} (hy : IntM y)
    (hc : ccT y = y) {x : Matrix (Fin n) (Fin N) E} (hx : IntM ((R : E) • x)) :
    chiH Ψ (((2 * R ^ 2 : ℕ) : E) • y) x = 1 := by
  set u := (R : E) • x with hu
  have e : (x * (((2 * R ^ 2 : ℕ) : E) • y) * ccT x).trace = 2 * (u * y * ccT u).trace := by
    have : ccT u = (R : E) • ccT x := by
      ext i j; simp [hu, ccT, cc]
    rw [this, hu]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    push_cast; ring
  have hi : IsIntegral ℤ (u * y * ccT u).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun b _ =>
      (IsIntegral.sum _ fun a _ => (hx k a).mul (hy a b)).mul (Base.isIntegral_cc (hx k b))
  have hr : cc (u * y * ccT u).trace = (u * y * ccT u).trace := by
    have h1 : ccT (u * y * ccT u) = u * y * ccT u := by
      rw [Base.ccT_mul, Base.ccT_mul, Base.ccT_ccT, hc, Matrix.mul_assoc]
    have h2 : ∀ w : Matrix (Fin n) (Fin n) E, cc w.trace = (ccT w).trace := fun w => by
      simp [Matrix.trace, ccT, cc]
    rw [h2, h1]
  obtain ⟨k, hk⟩ := exists_int_sum_type hΨ hi hr
  rw [chiH, e, hk, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem exists_common_level {M R : ℕ} (hM : 0 < M) (hR : 0 < R) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ φ : Fam E n N, admitted M R φ → ∀ c : Cls E n M,
      HasLevel R₀ (φ (Quot.out c).1) := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  choose s hs _ h1 h2 using fun c : Cls E n M => (Quot.out c).2.2.2
  refine ⟨(∏ c, s c) * R, Nat.mul_pos (Finset.prod_pos fun c _ => hs c) hR, fun φ hφ c => ?_⟩
  obtain ⟨m, hm⟩ : s c ∣ ∏ c, s c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  rw [hm]
  constructor
  · intro x hx k a
    have := Base.nat_smul_mem _ m (h1 c _ (hφ.supp _ (Quot.out c).2 x hx a))
    have := (Base.mem_stdL _).1 this k
    convert this using 1
    simp; ring
  · intro x y hy
    have := hφ.per _ (Quot.out c).2 x (((s c * m : ℕ) : E) • y) fun a => by
      have := Base.nat_smul_mem _ m (h2 c (yᵀ a) ((Base.mem_stdL _).2 fun k => hy k a))
      convert this using 1
      ext k; simp; ring
    rw [← this, smul_smul]
    congr 3
    push_cast; ring


omit [IsCMField E] in
theorem differentiableOn_of_isHeat {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) :
    DifferentiableOn ℂ (fun Z : CF Ψ N N => D Z 0 0) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} := by
  have g : Differentiable ℂ (fun Z : CF Ψ N N => ((Z, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N)) :=
    differentiable_id.prodMk (differentiable_const _)
  have := DifferentiableOn.comp (s := {Z : CF Ψ N N | (Z : CM Ψ N N) ∈ Hn Ψ N}) hD.1
    g.differentiableOn fun Z hZ => hZ
  exact this

theorem bound_high (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * (N + 1) < n) (hS : SWAt Ψ n N)
    (M R : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ (N + 1) δ,
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  obtain ⟨R₀, hR₀, hL⟩ := exists_common_level (E := E) (n := n) (N := N + 1) hM hR
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded E Ψ hΨ n (N + 1) hn hN R₀ (δ / 4) hR₀ (by positivity)
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.decay_of_vanishing_at_cusps' E Ψ hΨ (N + 1) (2 * R₀ ^ 2) δ ((n : ℝ) / 2) (Nat.succ_pos N)
    (by positivity) hδ (by positivity)
  obtain ⟨R', C', -, hsb⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn 1 R one_pos hR
  refine ⟨C₂ * ((∑ c : Cls E n M, ‖(wt M (Quot.out c).1 : ℂ)‖) * (2 * C₁)),
    fun φ hφ B hB Z hZ => ?_⟩
  have hSB : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := fun Λ hΛ =>
    (hsb M Λ hΛ 1 Base.one_mem_UU (fun i j => by
      by_cases h : i = j <;> simp [h, isIntegral_one, isIntegral_zero])
      (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1
  rw [mul_assoc]
  refine hC₂ (fun Z => swd Ψ M φ Z 0 0) _ ?_ ?_ ?_ ?_ Z hZ
  · exact differentiableOn_of_isHeat (GlobalTheory.T.isHeat_swd_of_adm E Ψ hΨ n (N + 1) hn hN M R φ hφ)
  · intro y hy hc W hW
    have h := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM hSB W hW).2.1
      (((2 * R₀ ^ 2 : ℕ) : E) • y) (by
        conv_rhs => rw [← hc]
        ext i j; simp [ccT, cc])
    change swd Ψ M φ _ 0 0 = swd Ψ M φ W 0 0
    rw [← h]
    unfold swd classSum
    refine finsum_congr fun c => ?_
    have : (fun x => chiH Ψ (((2 * R₀ ^ 2 : ℕ) : E) • y) x * φ (Quot.out c).1 x) =
        φ (Quot.out c).1 := by
      funext x
      by_cases hx : φ (Quot.out c).1 x = 0
      · rw [hx, mul_zero]
      · rw [chiH_eq_one hΨ R₀ hy hc ((hL φ hφ c).1 x hx), one_mul]
    simp only [this]
  · intro W hW
    unfold swd classSum
    rw [finsum_eq_sum_of_fintype, mul_assoc, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨-, h1, h2⟩ := hC₁ _ (hL φ hφ c) B (hB _ (Quot.out c).2) W hW
    refine (norm_sub_le _ _).trans ?_
    linarith
  · exact GlobalTheory.T.tendsto_swd_pushZ_atTop_zero E Ψ hΨ n N hn hN hS M R φ hφ

theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.le_def.1 (hZ τ).det_pos.le).1

end InvBound

theorem swd_invariant_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N →
    ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1),
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn hN hS M R
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  obtain ⟨c, δ, hc, hδ, hred⟩ := GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high E Ψ hΨ (N + 1)
  obtain ⟨R', hadm⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  obtain ⟨R'', C₁, -, hlev⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn c R hc hR
  obtain ⟨C₂, hC₂⟩ := InvBound.bound_high hΨ hn hN hS M R' hδ
  refine ⟨C₂ * C₁, fun φ hφ B hB Z hZ => ?_⟩
  obtain ⟨γ, hγ, hd, hW⟩ := hred Z hZ
  have hl := fun Λ hΛ => hlev M Λ hΛ γ hγ hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩
  have h := hC₂ _ (hadm M φ hφ γ hγ hd) (C₁ * B) (fun Λ hΛ => (hl Λ hΛ).2.2 B (hB Λ hΛ)) _ hW
  rw [(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM (fun Λ hΛ => (hl Λ hΛ).1) Z hZ).1 γ hγ] at h
  obtain ⟨-, hH, hdet, -⟩ := (unitary_act_halfSpace E Ψ (N + 1) γ hγ).2 Z hZ
  have hf : ‖hFac Ψ γ Z (0 : CM Ψ n (N + 1)) 0‖ =
      (∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2) ^ ((n : ℝ) / 2) := by
    have h0 : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n (N + 1)) τ k = 0 := fun _ _ => rfl
    rw [← Real.finsetProd_rpow _ _ fun _ _ => by positivity]
    simp only [hFac, h0, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, norm_prod, norm_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast; ring
  rw [← hdet, Real.mul_rpow (InvBound.detIm_nonneg hH) (Finset.prod_nonneg fun _ _ => by positivity),
    ← hf, mul_assoc C₂]
  rw [norm_mul] at h
  refine le_of_eq_of_le ?_ h
  ring

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBoundedStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ, (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1), ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  first | exact @GlobalTheory.SW.swd_invariant_bound | exact GlobalTheory.SW.swd_invariant_bound | (intros; apply GlobalTheory.SW.swd_invariant_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevel
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistAdm

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

def imL (b : Matrix (Fin N) (Fin N) E) : AddSubgroup (Fin N → E) :=
  (stdL E N).toAddSubgroup.map (Matrix.toLin' b).toAddMonoidHom

theorem mem_imL {b : Matrix (Fin N) (Fin N) E} {x : Fin N → E} :
    x ∈ imL b ↔ ∃ v ∈ stdL E N, b *ᵥ v = x := by
  simp [imL]

theorem std_eq_closure : (stdL E N).toAddSubgroup =
    AddSubgroup.closure (Set.range (Pi.basis fun _ : Fin N => integralBasis E)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Base.mem_stdL,
    Module.Basis.mem_span_iff_repr_mem, Sigma.forall]
  refine forall_congr' fun a => ?_
  simp only [Pi.basis_repr]
  rw [← Module.Basis.mem_span_iff_repr_mem, mem_span_integralBasis]
  exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩

theorem relIndex_imL {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by
  let B := Pi.basis fun _ : Fin N => integralBasis E
  have key : ∀ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 → ∃ B' : Module.Basis _ ℚ (Fin N → E),
      imL b = AddSubgroup.closure (Set.range B') ∧ B.det B' = Algebra.norm ℚ b.det := by
    intro b hb
    have hd : LinearMap.det (Matrix.toLin' b) ≠ 0 := by rwa [LinearMap.det_toLin']
    refine ⟨B.map (((Matrix.toLin' b).equivOfDetNeZero hd).restrictScalars ℚ), ?_, ?_⟩
    · rw [imL, std_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp]
      rfl
    · rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
      have := B.det_comp ((Matrix.toLin' b).restrictScalars ℚ) B
      rw [B.det_self, mul_one] at this
      exact this
  obtain ⟨B₁, e₁, d₁⟩ := key b₁ h₁
  obtain ⟨B₂, e₂, d₂⟩ := key b₂ h₂
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B₁ B₂ e₁ e₂, ← d₁, ← d₂, ← abs_mul, mul_comm,
    Module.Basis.det_mul_det]

theorem gidx_mul_le {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by
  have hs : ((t : E) • (1 : Matrix (Fin N) (Fin N) E)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 ht.ne')
  set s := (t : E) • (1 : Matrix (Fin N) (Fin N) E) with hsd
  have h1 : imL (1 : Matrix (Fin N) (Fin N) E) = (stdL E N).toAddSubgroup := by
    ext x; simp [mem_imL]
  have hKX : imL s ≤ 𝔛.toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using h v hv
  have hKL : imL s ≤ (stdL E N).toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using nat_smul_mem _ t hv
  have e1 := relIndex_imL hs hb (hKX.trans hX)
  have e2 := relIndex_imL hs (b₂ := 1) (by simp) (h1 ▸ hKL)
  rw [h1, Matrix.det_one, map_one, abs_one, mul_one] at e2
  have hn : 0 < |Algebra.norm ℚ s.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hs)
  have n1 : (imL s).relIndex (imL b) ≠ 0 := fun h0 => by
    rw [h0] at e1; simp at e1; exact hn.ne' (by simpa using e1.symm)
  have l1 := AddSubgroup.relIndex_le_of_le_right (H := imL s) hX n1
  have m1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_right : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  have m2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_left : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  rw [AddSubgroup.inf_relIndex_right] at m1
  rw [AddSubgroup.inf_relIndex_left] at m2
  rw [← m1] at l1
  rw [← m2] at e2
  unfold gidx
  generalize (imL s).relIndex ((stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup) = k at *
  generalize (stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup = p at *
  generalize 𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup = q at *
  have hkq : (0 : ℚ) < (k * q : ℕ) := e2 ▸ hn
  have hk : 0 < k := Nat.pos_of_mul_pos_right (by exact_mod_cast hkq)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (by exact_mod_cast hkq)
  have l2 : ((k * p : ℕ) : ℚ) * |Algebra.norm ℚ b.det| ≤ (k * q : ℕ) := by
    rw [e2, ← e1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast l1) (abs_nonneg _)
  have l3 : (p : ℚ) * |Algebra.norm ℚ b.det| ≤ q := by
    push_cast at l2
    rw [mul_assoc] at l2
    exact le_of_mul_le_mul_left l2 (by exact_mod_cast hk)
  rw [div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast l3

theorem exists_frame (E : Type) [Field E] [NumberField E] (N : ℕ) : ∃ c : ℕ, 0 < c ∧
    ∀ (𝔛 : Lt E N) (t : ℕ), 0 < t → (∀ v ∈ 𝔛, (t : E) • v ∈ stdL E N) →
      (∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛) → ∃ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 ∧
        (∀ v ∈ stdL E N, b *ᵥ v ∈ 𝔛) ∧ ∀ u, b *ᵥ u ∈ 𝔛 → (c : E) • u ∈ stdL E N := by
  obtain ⟨C, hC⟩ := NearPrim.exists_reduce E
  obtain ⟨M, hM⟩ := NearPrim.exists_approx E
  refine ⟨M.factorial ^ N, pow_pos M.factorial_pos _, fun 𝔛 t ht h1 h2 => ?_⟩
  have ht0 : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  let L : AddSubgroup (Fin N → E) :=
    { carrier := {s | (t : E) • s ∈ 𝔛}
      add_mem' := fun {s t} hs ht => by
        rw [Set.mem_setOf_eq, smul_add]; exact add_mem hs ht
      zero_mem' := by simp
      neg_mem' := fun {s} hs => by rw [Set.mem_setOf_eq, smul_neg]; exact neg_mem hs }
  have hO : ∀ s : Fin N → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs =>
    h2 s ((Base.mem_stdL s).2 hs)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs => by
    change (t : E) • y • s ∈ 𝔛
    rw [smul_comm]
    exact 𝔛.smul_mem (⟨y, hy⟩ : 𝓞 E) hs
  have hden : ∀ s ∈ L, ∀ i, IsIntegral ℤ (((t * t : ℤ) : E) * s i) := fun s hs i => by
    have := (Base.mem_stdL _).1 (h1 _ hs) i
    simpa [mul_assoc] using this
  choose a haL ha0 hai haC hmin using NearPrim.exists_rows L hO (t * t)
    (by positivity) hden C hC
  refine ⟨(t : E) • (Matrix.of a)ᵀ, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_transpose,
      Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact mul_ne_zero (pow_ne_zero _ ht0) (Finset.prod_ne_zero_iff.2 fun i _ => hai i)
  · exact colsIn_mulVec (fun j => haL j) hv
  · rw [Matrix.smul_mulVec, Matrix.mulVec_transpose] at hu
    exact (Base.mem_stdL _).2 (NearPrim.integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin N
      le_rfl u (fun j hj => absurd j.2 (not_lt.2 hj)) hu)

variable [IsCMField E]

theorem admissibleLatticeFamily_moved_by_rational_matrix {M R : ℕ} {φ : Fam E n N} {𝔛 : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) 𝔛 (stdL E N)) (a : Matrix (Fin N) (Fin N) E) {c : ℕ} (hc0 : 0 < c)
    (h1 : ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ stdL E N) :
    admitted M (R * c) (fun Λ (x : Matrix (Fin n) (Fin N) E) => twist R 𝔛 φ Λ
      (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  have hex := exists_mult hφ.pos.2 hA
  refine ⟨⟨hφ.pos.1, Nat.mul_pos hφ.pos.2 hc0⟩, ?_,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).1,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).2, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨R', hR'⟩ := twist_adm hφ hA
    have := hR'.equiv h hh Λ hΛ Λ' hΛ' hm (x * a)
    rwa [← Matrix.mul_assoc] at this
  · intro Λ hΛ Λ' hΛ' ⟨u, hu, hc, h3, h4⟩ x hx hx'
    have hct : u.Coprime (c * c) := by
      have : u.Coprime c := hc.coprime_dvd_right ⟨R * M, by ring⟩
      exact this.mul_right this
    have key : ∀ A B : Lt E n, (∀ v ∈ A, (u : E) • v ∈ B) → ColsIn B (((R * c : ℕ) : E) • x) →
        (∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ A) → ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ B := by
      intro A B hAB hB h ξ hξ
      refine mem_of_coprime B hct (hAB _ (h ξ hξ)) ?_
      have := colsIn_mulVec hB (h2 ξ hξ)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec] at this
      rw [smul_smul]
      convert this using 2
      push_cast; ring
    simp only [twist_eq φ hex]
    by_cases h : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · have h' := key Λ Λ' h3 hx' h
      rw [if_pos h, if_pos h']
      exact hφ.loc Λ hΛ Λ' hΛ' ⟨u, hu, hc.coprime_dvd_right ⟨c, by ring⟩, h3, h4⟩ _
        (cols_of_cond hex.choose_spec.2 h) (cols_of_cond hex.choose_spec.2 h')
    · rw [if_neg h, if_neg (fun h' => h (key Λ' Λ h4 hx h'))]

end GlobalTheory.SW.TwistMove


open GlobalTheory.SW.TwistMove in
theorem GlobalTheory.SW.twist_move_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ N
  obtain ⟨c, hc, H⟩ := exists_frame E N
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨c, |(Algebra.norm ℚ ((c : E) ^ N) : ℝ)|, hc, fun n M R φ 𝔛 hφ _ hA => ?_⟩
  obtain ⟨t, ht, -, h1, h2⟩ := id hA
  obtain ⟨b, hb, hb1, hb2⟩ := H 𝔛 t ht h1 h2
  have hu : IsUnit b.det := hb.isUnit
  have ha : b⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det b hu).ne_zero
  have k2 : ∀ ξ ∈ 𝔛, (c : E) • (b⁻¹ *ᵥ ξ) ∈ stdL E N := fun ξ hξ => hb2 _ (by
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec])
  refine ⟨b⁻¹, ha, ?_, admissibleLatticeFamily_moved_by_rational_matrix hφ hA b⁻¹ hc (fun v hv => ⟨b *ᵥ ((c : E) • v),
    hb1 _ (TwistAdm.nat_smul_mem _ c hv), by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]⟩) k2⟩
  have hd : ((c : E)⁻¹ • b).det * ((c : E) ^ N * b⁻¹.det) = 1 := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, inv_pow]
    field_simp
  have hle := gidx_mul_le ht h2 (left_ne_zero_of_mul_eq_one hd) (fun ξ hξ => mem_imL.2
    ⟨_, k2 ξ hξ, by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩)
  have hn := congrArg (fun z : E => |((Algebra.norm ℚ z : ℚ) : ℝ)|) hd
  simp only [map_mul, Rat.cast_mul, abs_mul, map_one, Rat.cast_one, abs_one] at hn
  have := mul_le_mul_of_nonneg_right hle (mul_nonneg
    (abs_nonneg (Algebra.norm ℚ ((c : E) ^ N) : ℝ)) (abs_nonneg (Algebra.norm ℚ b⁻¹.det : ℝ)))
  rwa [mul_assoc, hn, mul_one, one_mul] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  first | exact @GlobalTheory.SW.twist_move_adm | exact GlobalTheory.SW.twist_move_adm | (intros; apply GlobalTheory.SW.twist_move_adm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistedSiegelWeilDifferenceBounded
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}


omit [IsCMField E] in
theorem abs_norm_eq (h : IsType Ψ) (t : E) :
    |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ τ : Ψ, ‖τ.1 t‖ ^ 2 := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
  have h3 : ∏ σ : E →+* ℂ, σ t = ∏ σ : E →ₐ[ℚ] ℂ, σ t :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
  have h1 : |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ t‖ := by
    rw [← norm_prod, h3, ← h2, eq_ratCast, Complex.norm_ratCast]
  rw [h1, Finset.prod_coe_sort Ψ fun τ => ‖τ t‖ ^ 2, ← Finset.prod_mul_prod_compl Ψ,
    Finset.prod_pow, sq]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem isSB_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.per Λ hΛ x _ fun a => h2 _ ((Base.mem_stdL _).2 fun k => hy k a)

theorem bounded_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M h.pos.1).1
  have h1 : ∀ c : Cls E n M, ∃ B : ℝ, ∀ x, ‖φ (Quot.out c).1 x‖ ≤ B := fun c => by
    obtain ⟨S, hS, hl⟩ := isSB_of_adm h (Quot.out c).2
    exact (ip_self_nonneg_and_bounds E _ _ S _ hS hl).2.2.2.2.1
  choose b hb using h1
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun Λ hΛ x => ?_⟩
  set c : Cls E n M := Quot.mk _ ⟨Λ, hΛ⟩ with hc
  obtain ⟨g, hg, hm⟩ := (Base.cls_eq_iff ⟨Λ, hΛ⟩ (Quot.out c)).1 (Quot.out_eq c).symm
  rw [← h.equiv g hg Λ hΛ _ (Quot.out c).2 hm x]
  exact ((hb c _).trans (hB ⟨c, rfl⟩)).trans (le_max_left _ _)

theorem det_ccT (a : Matrix (Fin N) (Fin N) E) : (ccT a).det = cc a.det := by
  rw [ccT, Matrix.det_transpose]
  exact ((IsCMField.complexConj E).toRingEquiv.toRingHom.map_det a).symm

theorem diag_mem_UU {a d : Matrix (Fin N) (Fin N) E} (h : ccT a * d = 1) :
    Matrix.fromBlocks a 0 0 d ∈ UU E N := by
  have h' : ccT d * a = 1 := by
    have := congrArg ccT h
    rwa [Base.ccT_mul, Base.ccT_ccT, Base.ccT_one] at this
  have e : ccT (Matrix.fromBlocks a 0 0 d : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 (ccT d) := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h, h']

theorem exists_moved (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {φ : Fam E n N} (hφ : ∀ Λ ∈ Vset E n M, IsSB (φ Λ)) {a : Matrix (Fin N) (Fin N) E}
    (ha : a.det ≠ 0) (hψ : ∀ Λ ∈ Vset E n M, IsSB fun x => φ Λ (x * a))
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : ∃ Z' ∈ Hn Ψ N,
      swd Ψ M (fun Λ x => φ Λ (x * a)) Z' 0 0 = swd Ψ M φ Z 0 0 ∧
        detIm Z' = |((Algebra.norm ℚ a.det : ℚ) : ℝ)| * detIm Z := by
  have ha' : (ccT a).det ≠ 0 := by
    rw [det_ccT]; simpa [cc] using ha
  set d := (ccT a)⁻¹ with hd
  have had : ccT a * d = 1 := Matrix.mul_nonsing_inv _ ha'.isUnit
  have hdet : cc a.det * d.det = 1 := by rw [← det_ccT, ← Matrix.det_mul, had, Matrix.det_one]
  have hd0 : d.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  set γ : M2 E N := Matrix.fromBlocks a 0 0 d with hγ
  have hU : γ ∈ UU E N := diag_mem_UU had
  obtain ⟨-, hZ', hIm, -⟩ := (unitary_act_halfSpace E Ψ N γ hU).2 Z hZ
  have hden : ∀ τ, (hDen Ψ γ Z τ).det = τ.1 d.det := fun τ => by
    simp only [hDen, hγ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.map_zero _ (map_zero τ.1), Matrix.zero_mul, zero_add]
    exact (τ.1.map_det d).symm
  set k : ℂ := ∏ τ : Ψ, τ.1 d.det ^ n with hk
  have hk0 : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by simpa using hd0)
  have hfac : hFac Ψ γ Z (0 : CM Ψ n N) 0 = k := by
    have h : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
    simp only [hFac, hden, h, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, hk]
  refine ⟨_, hZ', ?_, ?_⟩
  · have h1 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M φ hM hφ Z hZ).1 γ hU
    have h2 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (fun Λ x => φ Λ (x * a)) hM hψ _ hZ').2.2.2.1 k
    apply mul_left_cancel₀ hk0
    rw [← h2, ← hfac, ← h1, hfac]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have : weil Ψ γ (φ Λ) = (k • fun Λ x => φ Λ (x * a) : Fam E n N) Λ := by
      funext x
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn (φ Λ) (hφ Λ hΛ)).1 γ hU rfl x]
      simp [hγ, chiH, hk]
    simp only [this]
  · rw [← hIm, abs_norm_eq hΨ, mul_left_comm, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one, mul_one]
    intro τ _
    rw [hden, ← mul_pow, ← Complex.norm_conj (τ.1 a.det), ← Base.map_cc, ← norm_mul, ← map_mul,
      hdet]
    simp


omit [NumberField E] [IsCMField E] in
theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1.le

end GlobalTheory.SW.TwistBound

namespace GlobalTheory.SW


open TwistBound in
theorem twist_swd_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ hφ
  obtain ⟨B, hB0, hB⟩ := bounded_of_adm hφ
  obtain ⟨c, C₁, -, h1⟩ := GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level E (N + 1)
  obtain ⟨C₂, h2⟩ := GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded E Ψ hΨ n N hn hN hSW M (R * c)
  refine ⟨max C₁ 0 ^ ((n : ℝ) / 2) * (C₂ * B), fun 𝔛 hfg hag Z hZ => ?_⟩
  obtain ⟨a, ha, hidx, hadm⟩ := h1 n M R φ 𝔛 hφ hfg hag
  obtain ⟨-, -, -, hpos, ⟨R', hR'⟩, -⟩ := twist_admissible E n (N + 1) M R φ 𝔛 hφ hfg hag
  obtain ⟨Z', hZ', e1, e2⟩ := exists_moved hΨ hn hN hφ.pos.1 (fun Λ hΛ => isSB_of_adm hR' hΛ) ha
    (fun Λ hΛ => isSB_of_adm hadm hΛ) hZ
  have h3 := h2 _ hadm B (fun Λ hΛ x => by
    unfold twist
    split_ifs
    · exact hB Λ hΛ _
    · simpa using hB0) Z' hZ'
  have hD := detIm_nonneg hZ
  replace h3 : ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z' ^ ((n : ℝ) / 2) ≤ C₂ * B := by
    rw [← e1]; exact h3
  rw [e2, Real.mul_rpow (abs_nonneg _) hD] at h3
  have h4 : gidx 𝔛 ^ ((n : ℝ) / 2) ≤
      max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (le_max_right _ _) (abs_nonneg _)]
    exact Real.rpow_le_rpow hpos.le
      (hidx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
  have h5 : 0 ≤ max C₁ 0 ^ ((n : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  calc _ ≤ (max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2)) *
        ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) := by gcongr
    _ = max C₁ 0 ^ ((n : ℝ) / 2) * (‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ *
        (|((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) * detIm Z ^ ((n : ℝ) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 h5

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistedSiegelWeilDifferenceBoundedStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_siegelWeil_difference_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  first | exact @GlobalTheory.SW.twist_swd_bounded | exact GlobalTheory.SW.twist_swd_bounded | (intros; apply GlobalTheory.SW.twist_swd_bounded <;> assumption)
end
