module

public import ReciprocityTheory.DualLattices.SubMemOfCompat

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.ThetaQSurj
section -- merged from ReciprocityTheory.DualLattices.MulVecMemPP
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section F3b

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def sumX (D : Lifts H U X) : (Ix g → R) →ₗ[R] augIdeal H.AA.carrier where
  toFun c := ⟨∑ k, c k • xL D k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (D.x_mem k)⟩
  map_add' c c' := by apply Subtype.ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by apply Subtype.ext; simp [Finset.smul_sum, smul_smul]

omit [Fact p.Prime] in
lemma mem_pP {n : ℕ} (w : Fin n → R) :
    w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R)) ↔ ∃ w', w = (p : R) • w' := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w', _, hw'⟩
    exact ⟨w', hw'.symm⟩
  · rintro ⟨w', hw'⟩
    exact ⟨w', Submodule.mem_top, hw'.symm⟩

omit [Fact p.Prime] in
lemma mulVec_mem_pP {n n' : ℕ} (M : Matrix (Fin n') (Fin n) R) {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) :
    M *ᵥ w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n' → R)) := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  exact (mem_pP _).2 ⟨M *ᵥ w', Matrix.mulVec_smul M (p : R) w'⟩

lemma εL_eq_zero_of_r (U : UnramData p g v R O σ cp H) {τ : Fin U.m} (h : U.r τ = 0) :
    U.εL τ = 0 := by
  obtain ⟨e⟩ := U.rank τ
  haveI : Subsingleton (Fin (U.r τ) → R) := by rw [h]; infer_instance
  haveI : Subsingleton (LinearMap.range (Matrix.mulVecLin (U.εL τ))) := e.toEquiv.subsingleton
  ext i j
  have h1 : (⟨U.εL τ *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩ :
      LinearMap.range (Matrix.mulVecLin (U.εL τ))) = 0 := Subsingleton.elim _ _
  have h2 := congrArg (fun x : LinearMap.range (Matrix.mulVecLin (U.εL τ)) => (x : Fin g → R) i) h1
  simpa [Matrix.mulVec_single_one] using h2

lemma phi_x_grade (hS : HodgeTateSetting p v R O σ cp) (D : Lifts H U X) (k : Ix g) (τ : Fin U.m)
    (hτ : τ ≠ D.κ k) (l : Fin g → R)
    (hl : H.φ ⟨xL D k, D.x_mem k⟩ = Submodule.Quotient.mk l) :
    (U.εL τ)ᵀ *ᵥ l ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R)) := by
  by_cases hτκ : ∃ j, D.κ j = τ
  · obtain ⟨j', rfl⟩ := hτκ
    obtain ⟨k', hk'⟩ := D.sep j' k hτ
    have hf' : ∀ t, ((U.sg (D.κ k) (D.b k') • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) :
        augIdeal H.AA.carrier) : Nb p g → C) (red p g t) =
        ((⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) : Nb p g → C) (red p g (H.ρ (D.b k') *ᵥ t)) := by
      intro t
      simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, xL]
      rw [D.eig k k' t]
      ring
    have h1 := H.cotangent_linear (D.b k') _ _ l hf' hl
    rw [map_smul, hl, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    have h2 := mulVec_mem_pP (U.εL (D.κ j'))ᵀ h1
    have e : (U.εL (D.κ j'))ᵀ *ᵥ (U.sg (D.κ k) (D.b k') • l - (H.ρL (D.b k'))ᵀ *ᵥ l) =
        (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) • ((U.εL (D.κ j'))ᵀ *ᵥ l) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, U.εL_eig,
        Matrix.transpose_smul, Matrix.smul_mulVec, sub_smul]
    rw [e] at h2
    have hv : v (algebraMap R C (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k'))) = 1 := by
      rw [← neg_sub, map_neg, Valuation.map_neg]
      exact hk'
    have hunit : IsUnit (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) := by
      refine hS.integers.isUnit_of_one ?_ hv
      exact Ne.isUnit fun h0 => by rw [h0, Valuation.map_zero] at hv; exact zero_ne_one hv
    obtain ⟨u, hu⟩ := hunit
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h3
  · push_neg at hτκ
    rw [εL_eq_zero_of_r U (D.r_zero τ hτκ), Matrix.transpose_zero, Matrix.zero_mulVec]
    exact Submodule.zero_mem _

end F3b

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section F3c

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}

def bvec (U : UnramData p g v R O σ cp H) (τ : Fin U.m) (s : Fin (U.r τ)) : Fin g → R :=
  ((U.rank τ).some.symm (Pi.single s 1)).1

def thetaL (U : UnramData p g v R O σ cp H) (τ : Fin U.m) : (Fin g → R) →ₗ[R] (Fin (U.r τ) → R) where
  toFun l s := l ⬝ᵥ bvec U τ s
  map_add' l l' := by funext s; simp [add_dotProduct]
  map_smul' r l := by funext s; simp [smul_dotProduct]

lemma theta_kill (U : UnramData p g v R O σ cp H) {τ σ' : Fin U.m} (h : σ' ≠ τ) (μ : Fin g → R) :
    thetaL U τ ((U.εL σ')ᵀ *ᵥ μ) = 0 := by
  funext s
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  show ((U.εL σ')ᵀ *ᵥ μ) ⬝ᵥ bvec U τ s = 0
  rw [hb, mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, U.εL_orth, if_neg h,
    vecMul_zero, zero_dotProduct]

lemma theta_surj (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaL U τ) := by
  intro y
  classical
  have key : ∀ (φ : (Fin g → R) →ₗ[R] R) (z : Fin g → R),
      (fun i => φ (fun j => if i = j then 1 else 0)) ⬝ᵥ z = φ z := by
    intro φ z
    rw [LinearMap.pi_apply_eq_sum_univ φ z, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; exact mul_comm _ _
  refine ⟨fun i => ((∑ s, y s • LinearMap.proj s : (Fin (U.r τ) → R) →ₗ[R] R) ∘ₗ
      (U.rank τ).some.toLinearMap ∘ₗ (Matrix.mulVecLin (U.εL τ)).rangeRestrict)
      (fun j => if i = j then 1 else 0), ?_⟩
  funext s
  show _ ⬝ᵥ bvec U τ s = y s
  refine (key _ _).trans ?_
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  have hfix : (Matrix.mulVecLin (U.εL τ)).rangeRestrict (bvec U τ s) =
      (U.rank τ).some.symm (Pi.single s 1) := by
    apply Subtype.ext
    show U.εL τ *ᵥ bvec U τ s = bvec U τ s
    rw [hb, mulVec_mulVec, U.εL_orth, if_pos rfl]
  simp only [LinearMap.comp_apply, hfix, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

def redP (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R)}) :=
  LinearMap.pi fun s => (Ideal.span {(p : R)}).mkQ ∘ₗ LinearMap.proj s

lemma redP_pP {n : ℕ} {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) : redP (p := p) n w = 0 := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  funext s
  show (Ideal.span {(p : R)}).mkQ (((p : R) • w') s) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def thetaQ (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    LieDualModP p R g →ₗ[R] (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
  (Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R))).liftQ (redP (U.r τ) ∘ₗ thetaL U τ)
    (fun w hw => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
      rw [map_smul]
      exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩))

lemma thetaQ_surj (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaQ U τ) := by
  intro y
  choose y' hy' using fun s => Submodule.mkQ_surjective (Ideal.span {(p : R)}) (y s)
  obtain ⟨l, hl⟩ := theta_surj U τ y'
  refine ⟨Submodule.Quotient.mk l, ?_⟩
  show redP (p := p) (U.r τ) (thetaL U τ l) = y
  rw [hl]
  funext s
  exact hy' s

end F3c

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem u7F3 : FrobeniusLengthBoundStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hdet hbasis τ N z hN hNsq hz
  have hv : v.Integers R := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj

  have hsqle : sqIdeal (augIdeal H.AA.carrier) ≤ augIdeal H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf, f', hf', rfl⟩
    rw [SetLike.mem_coe]
    obtain ⟨hfA, hf0⟩ := Submodule.mem_inf.1 hf
    obtain ⟨hfA', -⟩ := Submodule.mem_inf.1 hf'
    refine Submodule.mem_inf.2 ⟨H.AA.mul_mem f f' hfA hfA', ?_⟩
    rw [LinearMap.mem_ker] at hf0 ⊢
    simp only [LinearMap.proj_apply, Pi.mul_apply] at hf0 ⊢
    rw [hf0, zero_mul]

  have hkill : ∀ k, D.κ k ≠ τ → thetaQ U τ (H.φ ⟨xL D k, D.x_mem k⟩) = 0 := by
    intro k hk
    obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (H.φ ⟨xL D k, D.x_mem k⟩)
    have hg := phi_x_grade hS D k τ (Ne.symm hk) l hl.symm
    obtain ⟨w', hw'⟩ := (mem_pP _).1 hg
    rw [← hl]
    change redP (U.r τ) (thetaL U τ l) = 0
    have hl_sum : ∑ i, (U.εL i)ᵀ *ᵥ l = l := by
      funext j
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      have h1 : ∀ k', ∑ i, U.εL i k' j = (1 : Matrix (Fin g) (Fin g) R) k' j := fun k' => by
        rw [← U.εL_sum, Matrix.sum_apply]
      simp [h1, Matrix.one_apply]
    have hθ : thetaL U τ l = (p : R) • thetaL U τ w' := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hl_sum, map_sum,
        Finset.sum_eq_single τ (fun i _ hi => theta_kill U hi l) (by simp), hw', map_smul]
    rw [hθ]
    exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩)
  have hsx : ∀ d : Ix g → R,
      sumX D d = ∑ k, d k • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) := by
    intro d
    apply Subtype.ext
    simp [sumX]
  let π : (blockL D τ ⧸ N.comap (blockL D τ).subtype) →ₗ[R]
      (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
    (N.comap (blockL D τ).subtype).liftQ
      (thetaQ U τ ∘ₗ H.φ ∘ₗ sumX D ∘ₗ (blockL D τ).subtype) (by
        intro c hc
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hc
        obtain ⟨f, hf, hfc⟩ := hNsq _ hc
        obtain ⟨c', hc', hsub⟩ := sub_lin_mem_sq hv D hdet hbasis (hsqle hf)
        have hcc : c' = (c : Ix g → R) := funext fun k => hinj ((hc' k).trans (hfc k).symm)
        rw [hcc] at hsub
        have hmem : sumX D (c : Ix g → R) ∈ LinearMap.ker H.φ := by
          rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
          have h2 := Submodule.sub_mem _ hf hsub
          rw [sub_sub_cancel] at h2
          simpa [sumX] using h2
        rw [LinearMap.mem_ker] at hmem ⊢
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, hmem, map_zero])
  have hsurj : Function.Surjective π := by
    intro w
    obtain ⟨y, rfl⟩ := thetaQ_surj U τ w
    obtain ⟨f, rfl⟩ := H.cotangent_surjective y
    obtain ⟨c0, -, hsub0⟩ := sub_lin_mem_sq hv D hdet hbasis f.2
    let c : blockL D τ :=
      ⟨fun k => if D.κ k = τ then c0 k else 0, fun k hk => by simp [hk]⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    change thetaQ U τ (H.φ (sumX D (c : Ix g → R))) = thetaQ U τ (H.φ f)
    have hf0 : H.φ f = H.φ (sumX D c0) := by
      rw [← sub_eq_zero, ← map_sub]
      apply LinearMap.mem_ker.1
      rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
      simpa [sumX] using hsub0
    rw [hf0]
    have hzero : thetaQ U τ (H.φ (sumX D (c0 - (c : Ix g → R)))) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsx, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_smul, map_smul]
      by_cases hk : D.κ k = τ
      · have hck : (c0 - (c : Ix g → R)) k = 0 := by simp [c, hk]
        rw [hck, zero_smul]
      · rw [hkill k hk, smul_zero]
    rw [map_sub, map_sub, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  exact hasLen_le_of_surj hv hz (p : R) (U.r τ) π hsurj

end ReciprocityTheory.PGsh.Up
