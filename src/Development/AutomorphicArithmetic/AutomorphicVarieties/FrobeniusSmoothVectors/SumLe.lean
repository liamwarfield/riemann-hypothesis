module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGbox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZeroOfNeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LieTMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpHasobs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpMazur

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CwZero
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cw_skew {K : Type} [CommRing K] (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) :
    (X * x.mat * Jmat (R := K) 3)ᵀ = -(X * x.mat * Jmat (R := K) 3) := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr, sgnAct_neg_one] using this
  have hX' : x.mat * thetaLie X * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X := by
    simpa [GG.adFun, hr] using hX
  have h2 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left h1
  have hg : x.mat = Jmat (R := K) 3 * x.matᵀ * Jmat (R := K) 3 := by
    show ((x.left : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    conv_lhs => rw [← h2]
    rw [theta_inv_val]
    rfl
  have hgJ : x.mat * Jmat (R := K) 3 = Jmat (R := K) 3 * x.matᵀ := by
    conv_lhs => rw [hg]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hXg : X * x.mat = x.mat * thetaLie X := by
    conv_lhs => rw [← hX']
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    have : ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x.mat = 1 := by
      show ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x.left : Matrix (Fin 3) (Fin 3) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  calc (X * x.mat * Jmat (R := K) 3)ᵀ = Jmat (R := K) 3 * x.matᵀ * Xᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, Matrix.mul_assoc]
    _ = x.mat * Jmat (R := K) 3 * Xᵀ := by rw [hgJ]
    _ = -(X * x.mat * Jmat (R := K) 3) := by
        rw [hXg, thetaLie]
        simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

private theorem cw_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : GG (m := 3) (R := K)) (hx : x * x = 1) (hr : x.right = -1)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : x.adFun X = X) (a : (X * x.mat) 0 0 = 0) (b : (X * x.mat) 0 1 = 0)
    (c : (X * x.mat) 1 0 = 0) : X = 0 := by
  have hs := cw_skew x hx hr X hX
  have e : ∀ i j, (X * x.mat * Jmat (R := K) 3) i j = (X * x.mat) i (Fin.rev j) := by
    intro i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat]
  have sk : ∀ i j, (X * x.mat * Jmat (R := K) 3) j i = -(X * x.mat * Jmat (R := K) 3) i j := by
    intro i j
    have := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using this
  have dg : ∀ i, (X * x.mat * Jmat (R := K) 3) i i = 0 := by
    intro i
    have h := sk i i
    have h' : (2 : K) * (X * x.mat * Jmat (R := K) 3) i i = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
    exact (mul_eq_zero.mp h').resolve_left h2
  have m01 : (X * x.mat * Jmat (R := K) 3) 0 1 = 0 := by rw [e]; exact b
  have m02 : (X * x.mat * Jmat (R := K) 3) 0 2 = 0 := by rw [e]; exact a
  have m12 : (X * x.mat * Jmat (R := K) 3) 1 2 = 0 := by rw [e]; exact c
  have m10 : (X * x.mat * Jmat (R := K) 3) 1 0 = 0 := by rw [sk, m01, neg_zero]
  have m20 : (X * x.mat * Jmat (R := K) 3) 2 0 = 0 := by rw [sk, m02, neg_zero]
  have m21 : (X * x.mat * Jmat (R := K) 3) 2 1 = 0 := by rw [sk, m12, neg_zero]
  have hM : X * x.mat * Jmat (R := K) 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.zero_apply]
    all_goals first
      | exact dg _
      | exact m01
      | exact m02
      | exact m12
      | exact m10
      | exact m20
      | exact m21
  have hY : X * x.mat = 0 := by
    have : X * x.mat = X * x.mat * Jmat (R := K) 3 * Jmat (R := K) 3 := by
      rw [Matrix.mul_assoc (X * x.mat), Jmat_mul_Jmat, Matrix.mul_one]
    rw [this, hM, Matrix.zero_mul]
  have hinv : x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    show (x.left : Matrix (Fin 3) (Fin 3) K) * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc X = X * x.mat * ((x.left⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = 0 := by rw [hY, Matrix.zero_mul]

theorem UpperTheory.V.Fr.ep_cw :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ c : F.Γ, c * c = 1 → F.del c = -1 → Module.finrank K (LinearMap.ker (h.ad 0 c - 1)) ≤ 1 ∧ Module.finrank K (LinearMap.ker (h.ad 1 c - 1)) ≤ 2 := by
  intro l _ k _ F K _ h2 B π h c hc hd
  have hx : B.r c * B.r c = 1 := by rw [← map_mul, hc, map_one]
  have hr : (B.r c).right = -1 := by rw [B.nu, hd]
  have hg : ∀ a b, pw a b ≠ 0 → (B.r c).mat a b = 0 := fun a b hab => h.r c a b hab
  have key : ∀ j (v : LinearMap.ker (h.ad j c - 1)),
      (B.r c).adFun ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) = ((v : adp K j) : Matrix (Fin 3) (Fin 3) K) := by
    intro j v
    have hv := v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
    have := congrArg Subtype.val hv
    simpa [Box.Ev.ad, Box.ad, adRep, GG.ad_apply] using this
  constructor
  · let f : LinearMap.ker (h.ad 0 c - 1) →ₗ[K] K :=
      { toFun := fun v => (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 0 → ((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 0).2 a b hab
      have e01 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hg 0 1 (by decide), hX 0 1 (by decide), hg 2 1 (by decide)]
        ring
      have e10 : (((v : adp K 0) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 1 0 (by decide), hg 1 0 (by decide), hX 1 2 (by decide)]
        ring
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 0 v) hv e01 e10
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  · let f : LinearMap.ker (h.ad 1 c - 1) →ₗ[K] K × K :=
      { toFun := fun v => ((((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 1,
          (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 1 0)
        map_add' := by intro v w; simp [Matrix.add_mul]
        map_smul' := by intro a v; simp [Matrix.smul_mul] }
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hX : ∀ a b, pw a b ≠ 1 → ((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) a b = 0 :=
        fun a b hab => (v : adp K 1).2 a b hab
      have e00 : (((v : adp K 1) : Matrix (Fin 3) (Fin 3) K) * (B.r c).mat) 0 0 = 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_three, hX 0 0 (by decide), hg 1 0 (by decide), hX 0 2 (by decide)]
        ring
      have hv' := Prod.mk.inj hv
      have h0 := cw_zero h2 (B.r c) hx hr _ (key 1 v) e00 hv'.1 hv'.2
      exact Subtype.ext (Subtype.ext h0)
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NegOneZpowSg
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem neg_one_zpow_sg (K : Type) [CommRing K] (j : ℤ) :
    (((-1 : Kˣ) ^ j : Kˣ) : K) = sg K (j : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · rw [Even.neg_one_zpow (even_two_mul k)]
    push_cast
    rw [h2, zero_mul]
    simp [sg]
  · rw [Odd.neg_one_zpow (odd_two_mul_add_one k)]
    push_cast
    rw [h2, zero_mul, zero_add]
    show _ = (-1 : K) ^ 1
    simp

private theorem map_sg {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (j : ZMod 2) :
    f (sg K j) = sg K' j := by simp [sg]

private theorem sg_sq (K : Type) [CommRing K] (j : ZMod 2) : sg K j * sg K j = 1 := by
  rw [sg, ← mul_pow]; simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
  (S : Space O F 3)

private theorem ex_tau : ∃ τ : S.R →ₐ[O] S.R,
    (∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j) ∧
      ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g := by
  obtain ⟨ρ', h1, h2⟩ := alg_twist (-1 : S.Rˣ) S.ρ
  obtain ⟨⟨c1, c2⟩, ⟨b1, b2⟩, d⟩ := S.lift
  have hl : IsLift O ρ' := by
    refine ⟨⟨fun i j N => ?_, by rw [h2]; exact c2⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
    · simp only [h1, map_mul]
      exact (c1 i j N).comp (fun y => Ideal.Quotient.mk _ _ * y)
    · rw [NRep.map_r, h1, sub_self, zpow_zero, Units.val_one, one_mul]
      exact b1 g i
    · rw [NRep.map_ψ, h2]
      exact b2 v i g
    · rw [NRep.map_r, h1, map_mul]
      have := d g i j hij
      rw [NRep.map_r] at this
      rw [this, mul_zero]
  obtain ⟨τ, hτ, -⟩ := S.univ S.R ρ' hl
  refine ⟨τ, fun g i j => ?_, fun v i g => ?_⟩
  · rw [← h1, ← hτ]; rfl
  · conv_rhs => rw [← h2, ← hτ]
    rfl

private theorem tau_B (τ : S.R →ₐ[O] S.R)
    (h1 : ∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j)
    (h2 : ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g) : ∀ y ∈ S.B, τ y = y := by
  have hm : ∀ M : List (F.G0 × Fin 3 × Fin 3), τ (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod =
      (((-1 : S.Rˣ) ^ (M.map fun s => w 3 s.2.1 - w 3 s.2.2).sum : S.Rˣ) : S.R) *
        (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
    intro M
    induction M with
    | nil => simp
    | cons a M ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, h1, ih, _root_.zpow_add, Units.val_mul]
      ring
  have ha : ∀ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}), τ y = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨M, e, rfl⟩ | ⟨v, i, g, rfl⟩
      · rw [hm, e]; simp
      · exact h2 v i g
    | algebraMap r => exact τ.commutes r
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  have hloc : (maximalIdeal S.R).map τ ≤ maximalIdeal S.R := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  intro y hy
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal S.R) inferInstance _ fun N => ?_
  obtain ⟨z, hz, hyz⟩ := hy N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e : τ y - y = τ (y - z) - (y - z) := by rw [map_sub, ha z hz]; ring
  rw [e]
  refine sub_mem ?_ hyz
  have := Ideal.mem_map_of_mem τ hyz
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hloc N this

private theorem ex_tauA : ∃ τ : S.A →ₐ[O] S.A,
    (∀ g i j, τ (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j) ∧ (∀ y : S.B, τ (S.inc y) = S.inc y) ∧
      (∀ a, τ (τ a) = a) ∧ ∀ a, τ a - a ∈ S.u.ee := by
  obtain ⟨τ, h1, h2⟩ := ex_tau S
  have hB := tau_B S τ h1 h2
  have h1' : ∀ g i j, τ (S.ρ.r g i j) = sg S.R (pw i j) * S.ρ.r g i j := fun g i j => by
    rw [h1, neg_one_zpow_sg]; rfl
  have hA : ∀ y ∈ S.A, τ y ∈ S.A := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · rw [hB y hy]; exact S.B_le_A hy
      · rw [h1']
        exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (S.r_mem g i j)
    | algebraMap r => rw [τ.commutes r]; exact S.A.algebraMap_mem r
    | add a b _ _ ha hb => rw [map_add (f := τ)]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let τA : S.A →ₐ[O] S.A := (τ.comp S.A.val).codRestrict S.A fun a => hA a a.2
  have e1 : ∀ g i j, τA (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j := fun g i j =>
    Subtype.ext ((h1' g i j).trans (by
      rw [← map_sg (S.A.val : S.A →+* S.R)]; rfl))
  have e2 : ∀ y : S.B, τA (S.inc y) = S.inc y := fun y => Subtype.ext (hB y y.2)
  have ind : ∀ P : S.A → Prop, (∀ y : S.B, P (S.inc y)) → (∀ g i j, P (S.u.r g i j)) →
      (∀ a b, P a → P b → P (a + b)) → (∀ a b, P a → P b → P (a * b)) → ∀ a, P a := by
    intro P p1 p2 p3 p4 ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact p1 ⟨y, hy⟩
      · exact p2 g i j
    | algebraMap r => exact p1 (algebraMap O S.B r)
    | add a b ha hb qa qb => exact p3 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
    | mul a b ha hb qa qb => exact p4 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
  refine ⟨τA, e1, e2, ind _ (fun y => by rw [e2, e2]) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_,
    ind _ (fun y => by rw [e2, sub_self]; exact zero_mem _) (fun g i j => ?_) (fun a b qa qb => ?_)
      fun a b qa qb => ?_⟩
  · rw [e1, map_mul, e1, ← mul_assoc]
    have := map_sg (τA : S.A →+* S.A) (pw i j)
    rw [RingHom.coe_coe] at this
    rw [this, sg_sq, one_mul]
  · rw [map_add (f := _), map_add (f := _), qa, qb]
  · rw [map_mul, map_mul, qa, qb]
  · rw [e1, pw, ← neg_one_zpow_sg]
    rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
    · rw [h.neg_one_zpow]; simp
    · exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
        (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  · rw [map_add (f := _), add_sub_add_comm]; exact add_mem qa qb
  · have : τA (a * b) - a * b = (τA a - a) * τA b + a * (τA b - b) := by rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ qa) (Ideal.mul_mem_left _ _ qb)

end

theorem UpperTheory.V.Fr.ep_inv :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∃ σ, L.IsInv σ := by
  intro l _ O _ _ _ _ F C₀ _ S x L hx
  obtain ⟨τ, h1, h2, h3, h4⟩ := ex_tauA S
  obtain ⟨σ, hσ, -⟩ := L.univ L.R (L.ι.comp τ) fun a => by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff, AlgHom.comp_apply, ← map_sub]
    have := hx (h4 a)
    rw [← L.lies] at this
    exact this
  obtain ⟨g₀, -, hu⟩ := L.univ L.R L.ι fun _ => rfl
  have hsq : σ.comp σ = AlgHom.id _ _ :=
    (hu (σ.comp σ) fun a => by
      rw [AlgHom.comp_apply, hσ, AlgHom.comp_apply, hσ, AlgHom.comp_apply, h3]).trans
      (hu (AlgHom.id _ _) fun _ => rfl).symm
  refine ⟨σ, fun y => DFunLike.congr_fun hsq y, fun g a b => ?_, fun y => ?_⟩
  · show σ (L.ι (S.u.r g a b)) = sg _ _ * L.ι (S.u.r g a b)
    rw [hσ, AlgHom.comp_apply, h1, map_mul, ← map_sg (L.ι : S.A →+* L.R)]
    rfl
  · show σ (L.ι (S.inc y)) = sg _ _ * L.ι (S.inc y)
    rw [hσ, AlgHom.comp_apply, h2]
    simp [sg]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpRels
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_rels :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2) (J : Ideal (MvPowerSeries ι O)), IsHomog O wt J → ∃ (κ : Type) (_ : Fintype κ) (f : κ → MvPowerSeries ι O) (wf : κ → ZMod 2), (∀ u, f u ∈ wtPart O wt (wf u)) ∧ J = Ideal.span (Set.range f) ∧ ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries ι O) * J → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 ι _ wt J hJ
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  obtain ⟨τ, hττ, hev, hw⟩ := ep_ps O h2 ι wt
  have hτJ : ∀ y ∈ J, τ y ∈ J := by
    intro y hy
    have e := hw 1 y
    have hs : sg (MvPowerSeries ι O) 1 = -1 := by
      simp only [sg]
      rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    rw [hs] at e
    have : τ y = y - 2 * wcomp O wt 1 y := by linear_combination e
    rw [this]
    exact J.sub_mem hy (J.mul_mem_left 2 (hJ y hy 1))
  have hτm : ∀ y ∈ maximalIdeal (MvPowerSeries ι O), τ y ∈ maximalIdeal (MvPowerSeries ι O) := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    rw [← hττ y]
    exact hu.map τ
  have hτN : ∀ y ∈ maximalIdeal (MvPowerSeries ι O) * J,
      τ y ∈ maximalIdeal (MvPowerSeries ι O) * J := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm j hj
      rw [map_mul]
      exact Ideal.mul_mem_mul (hτm m hm) (hτJ j hj)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb
  obtain ⟨a, g, z, hz, hle, hmin⟩ :=
    ep_basis O h2 (MvPowerSeries ι O) τ hττ J (maximalIdeal (MvPowerSeries ι O) * J) hτJ hτN le_rfl
  refine ⟨Fin a ⊕ Fin g, inferInstance, z, Space.Loc.par a g, ?_, ?_, hmin⟩
  · intro s
    rw [← hev]
    exact (hz s).2
  · apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J)
        (maximalIdeal_le_jacobson _)
      exact hle
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact (hz s).1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpVars
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

open MvPowerSeries in
private theorem ev_decomp {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O) :
    ∃ h : σ → MvPowerSeries σ O, f = C (constantCoeff f) + ∑ i, MvPowerSeries.X i * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) f :=
  _root_.UpperTheory.Reformulated.B.Qf39.ev_decomp f

private theorem ev_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem ev_sg_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (f : A →ₐ[O] B) (j : ZMod 2) : f (sg A j) = sg B j := by
  simp [sg]

private theorem ev_sg_sq (A : Type) [CommRing A] (j : ZMod 2) : sg A j * sg A j = 1 := by
  rw [sg, ← mul_pow]; simp

theorem UpperTheory.V.Fr.ep_vars :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∃ (a g : ℕ) (p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R), Function.Surjective p ∧ (∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R) ∧ (∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j) ∧ IsHomog O (Space.Loc.par a g) (RingHom.ker p) ∧ ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨a, g, z, hz, hspan, hind⟩ := ep_basis O h2 R σ hσ (maximalIdeal R)
    ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2) (fun y hy => (ev_max σ).2 hy)
    (by
      have : (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ≤
          ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2).comap σ := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
        · refine le_trans ?_ (Ideal.comap_mono le_sup_right)
          refine le_trans (Ideal.pow_right_mono ?_ 2) (Ideal.le_comap_pow σ 2)
          exact fun y hy => (ev_max σ).2 hy
      exact fun y hy => this hy)
    (by rw [← pow_two]; exact le_sup_right)
  obtain ⟨τ, -, hτe, hτw⟩ := ep_ps O h2 (Fin a ⊕ Fin g) (Space.Loc.par a g)
  haveI := co_mvps O O (Fin a ⊕ Fin g)
  obtain ⟨p, ⟨-, hpX⟩, -⟩ := co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) z fun s => (hz s).1
  have hC : ∀ (H : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (x : O),
      H (MvPowerSeries.C x) = Algebra.ofId O R x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hsurj : Function.Surjective p := by
    refine co_surj O _ R p (hspan.trans (sup_le (le_sup_of_le_left ?_) (sup_le_sup_right ?_ _)))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hpX]
      refine Ideal.mem_map_of_mem p ((ev_max p).1 ?_)
      rw [hpX]
      exact (hz s).1
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← p.commutes]
      refine Ideal.mem_map_of_mem p ?_
      exact (ev_max (Algebra.ofId O _)).2 hc
  have heq : p.comp τ = σ.comp p := by
    refine (co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) (fun s => σ (z s))
      fun s => (ev_max σ).2 (hz s).1).unique ⟨hC _, fun s => ?_⟩ ⟨hC _, fun s => ?_⟩
    · have h1 : (MvPowerSeries.X s : MvPowerSeries (Fin a ⊕ Fin g) O) ∈ evp τ (Space.Loc.par a g s) := by
        rw [hτe]; exact X_mem_wtPart O _ s
      have h3 : τ (MvPowerSeries.X s) = _ := h1
      have h4 : σ (z s) = _ := (hz s).2
      rw [AlgHom.comp_apply, h3, h4, map_mul, ev_sg_map, hpX]
    · rw [AlgHom.comp_apply, hpX]
  have heq' : ∀ y, p (τ y) = σ (p y) := fun y => DFunLike.congr_fun heq y
  have hw : ∀ j y, 2 * p (wcomp O (Space.Loc.par a g) j y) = p y + sg R j * σ (p y) := fun j y => by
    have := congrArg p (hτw j y)
    rwa [map_mul, map_ofNat, map_add, map_mul, ev_sg_map, heq'] at this
  refine ⟨a, g, p, hsurj, fun s => by rw [hpX]; exact (hz s).1, fun j => le_antisymm ?_ fun x hx => ?_,
    fun f hf j => ?_, fun h hh => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ evp τ j := by rw [hτe]; exact hf
    have h3 : τ f = _ := h1
    show σ (p f) = sg R j * p f
    rw [← heq', h3, map_mul, ev_sg_map]
  · obtain ⟨y, rfl⟩ := hsurj x
    have h1 : σ (p y) = _ := hx
    refine ⟨_, wcomp_mem O _ j y, ?_⟩
    show p _ = p y
    refine h2R.mul_left_cancel ?_
    rw [hw, h1, ← mul_assoc, ev_sg_sq, one_mul, two_mul]
  · have h1 : p f = 0 := hf
    show p _ = 0
    refine h2R.mul_left_cancel ?_
    rw [hw, h1]
    simp
  · obtain ⟨u, hu, hu0⟩ := ev_decomp h
    have h0 : p h = 0 := hh
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ i, z i * p (u i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hu, map_add (f := _), map_sum, hC] at h0
      simp only [map_mul, hpX] at h0
      exact h0
    have h3 : MvPowerSeries.constantCoeff h ∈ maximalIdeal O := by
      rw [← ev_max (Algebra.ofId O R)]
      show algebraMap O R _ ∈ _
      rw [eq_neg_of_add_eq_zero_left h1]
      exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hz i).1)
    refine hind (fun s => MvPowerSeries.coeff (Finsupp.single s 1) h) ?_
    have h4 : ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) h • z s =
        -algebraMap O R (MvPowerSeries.constantCoeff h) +
          ∑ s, z s * p (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single s 1) h) - u s) := by
      rw [eq_neg_of_add_eq_zero_left h1, neg_neg, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_sub, hC, Algebra.smul_def, Algebra.ofId_apply]
      ring
    rw [h4]
    refine Submodule.add_mem_sup (neg_mem (Ideal.mem_map_of_mem _ h3)) (Ideal.sum_mem _ fun s _ => ?_)
    rw [pow_two]
    refine Ideal.mul_mem_mul (hz s).1 ((ev_max p).2 fun hU => ?_)
    have h5 := MvPowerSeries.isUnit_constantCoeff _ hU
    rw [map_sub, hu0, MvPowerSeries.constantCoeff_C, sub_self] at h5
    exact not_isUnit_zero h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemSpanX
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
open MvPowerSeries
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf
end

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {σ : R →ₐ[O] R} (P : GPres O σ) (D : R →ₗ[O] ResidueField O) (hD : D ∈ PtDer (res O R) (ResidueField O))
    (h : ∀ s, D (P.p (MvPowerSeries.X s)) = 0) : D = 0 := by
  have hm : ∀ f g, D (f * g) = res O R f • D g + res O R g • D f := hD
  have h1 : D 1 = 0 := by
    have := hm 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  have hs : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : _ → MvPowerSeries (Fin P.a ⊕ Fin P.g) O)),
      res O R (P.p g) = 0 ∧ D (P.p g) = 0 := fun g hg => by
    refine Submodule.span_induction (p := fun g _ => res O R (P.p g) = 0 ∧ D (P.p g) = 0) ?_ (by simp) ?_ ?_ hg
    · rintro _ ⟨s, rfl⟩
      exact ⟨(res_eq_zero_iff O R _).2 (P.var s), h s⟩
    · rintro x y - - ⟨a, b⟩ ⟨c, d⟩
      simp [a, b, c, d]
    · rintro x y - ⟨a, b⟩
      rw [smul_eq_mul, map_mul, map_mul, hm, a, b]
      simp
  ext x
  obtain ⟨f, rfl⟩ := P.surj x
  have e : f = (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) + (MvPowerSeries.constantCoeff f) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  have h2 := (hs _ (mem_span_X (f - algebraMap O _ (MvPowerSeries.constantCoeff f))
    (by simp [MvPowerSeries.algebraMap_apply]))).2
  rw [e, map_add (f := _), map_add (f := _), h2, map_smul, map_smul, map_one, h1]
  simp

private theorem der_off {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] {σ : R →ₐ[O] R} (P : GPres O σ) (j : ZMod 2) (D : R →ₗ[O] ResidueField O)
    (hD : D ∈ derp O σ j) (s : Fin P.a ⊕ Fin P.g) (hs : Space.Loc.par P.a P.g s ≠ j) :
    D (P.p (MvPowerSeries.X s)) = 0 := by
  have h1 : P.p (MvPowerSeries.X s) ∈ evp σ (Space.Loc.par P.a P.g s) := by
    rw [← P.part]
    exact ⟨_, X_mem_wtPart O _ s, rfl⟩
  have h3 : σ (P.p (MvPowerSeries.X s)) = sg R (Space.Loc.par P.a P.g s) * P.p (MvPowerSeries.X s) := h1
  have h4 : D (σ (P.p (MvPowerSeries.X s))) = sg (ResidueField O) j * D (P.p (MvPowerSeries.X s)) := hD.2 _
  have h5 : (2 : ResidueField O) ≠ 0 := by
    have := (h2.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  rw [h3] at h4
  generalize Space.Loc.par P.a P.g s = i at hs h4
  generalize P.p (MvPowerSeries.X s) = y at h4
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have hc : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  apply (mul_eq_zero.1 (show 2 * D y = 0 from ?_)).resolve_left h5
  rcases hc i with rfl | rfl <;> rcases hc j with rfl | rfl
  · exact absurd rfl hs
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul] at h4
    linear_combination h4
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul, map_neg] at h4
    linear_combination -h4
  · exact absurd rfl hs

private theorem der_bound {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R]
    [Algebra O R] (N : Submodule (ResidueField O) (R →ₗ[O] ResidueField O)) {ι : Type} [Fintype ι] (y : ι → R)
    (h : ∀ D ∈ N, (∀ i, D (y i) = 0) → D = 0) :
    Module.Finite (ResidueField O) N ∧ Module.finrank (ResidueField O) N ≤ Fintype.card ι := by
  let φ : N →ₗ[ResidueField O] (ι → ResidueField O) :=
    { toFun := fun D i => D.1 (y i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun D hD =>
    Subtype.ext (h D.1 D.2 fun i => congrFun hD i)
  exact ⟨Module.Finite.of_injective φ hφ, by
    simpa using LinearMap.finrank_le_finrank_of_injective hφ⟩

theorem UpperTheory.V.Fr.ep_der :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), (∀ j, Module.Finite (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (derp O σ 0) ≤ P.a ∧ Module.finrank (ResidueField O) (derp O σ 1) ≤ P.g := by
  intro O _ _ _ _ h2 R _ _ _ σ P
  refine ⟨fun j => (der_bound (derp O σ j) (fun s => P.p (MvPowerSeries.X s))
    fun D hD h => der_zero P D hD.1 h).1, ?_, ?_⟩
  · have := (der_bound (derp O σ 0) (fun i : Fin P.a => P.p (MvPowerSeries.X (.inl i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact h i
        · exact der_off h2 P 0 D hD _ (show (1 : ZMod 2) ≠ 0 by decide)).2
    simpa using this
  · have := (der_bound (derp O σ 1) (fun i : Fin P.g => P.p (MvPowerSeries.X (.inr i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact der_off h2 P 1 D hD _ (show (0 : ZMod 2) ≠ 1 by decide)
        · exact h i).2
    simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsPaddedFamily
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_padded_family {κ M : Type} [Finite κ] [Zero M] (q : κ → Prop) (f : κ → M) (n : ℕ)
    (h : Nat.card {u // q u} ≤ n) :
    ∃ G : Fin n → M, (∀ i, G i = 0 ∨ ∃ u, q u ∧ G i = f u) ∧ ∀ u, q u → ∃ i, G i = f u := by
  classical
  haveI := Fintype.ofFinite κ
  have hc : Fintype.card {u // q u} ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨Function.extend e (fun u => f u.1) 0, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ u, e u = i
    · obtain ⟨u, rfl⟩ := hi
      right
      exact ⟨u.1, u.2, by rw [e.injective.extend_apply]⟩
    · left
      rw [Function.extend_apply' _ _ _ hi]
      rfl
  · intro u hu
    exact ⟨e ⟨u, hu⟩, by rw [e.injective.extend_apply]⟩

theorem UpperTheory.V.Fr.ep_pad :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (S : Space O F 3) (x : Ideal S.A) (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R), L.IsInv σ → ∀ P : GPres L.O' σ, Nat.card {u // P.wf u = 0} + (3 * F.d + 1) ≤ P.a → Nat.card {u // P.wf u = 1} ≤ P.g → L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) → Nonempty L.EPres := by
  intro l _ O _ _ F S x L σ hσ P h0 h1 hee
  obtain ⟨Fe, hF, hF'⟩ := exists_padded_family (fun u => P.wf u = 0) P.f (P.a - (3 * F.d + 1)) (by omega)
  obtain ⟨Go, hG, hG'⟩ := exists_padded_family (fun u => P.wf u = 1) P.f P.g h1
  have two : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  refine ⟨{ a := P.a, b := P.a - (3 * F.d + 1), g := P.g, p := P.p, Fe := Fe, Go := Go,
            num := by omega, surj := P.surj, ker := ?_, even := ?_, odd := ?_, min := P.min,
            ent := ?_, base := ?_, ee := hee }⟩
  · rw [P.ker]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro _ ⟨u, rfl⟩
      rcases two (P.wf u) with h | h
      · exact Or.inl (hF' u h)
      · exact Or.inr (hG' u h)
    · rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rcases hF i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
      · rcases hG i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
  · intro i
    rcases hF i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro i
    rcases hG i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro s i j
    rw [P.part]
    exact hσ.ent s i j
  · intro y
    rw [P.part]
    exact hσ.base y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpOddSpanX
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ep_odd_span_X {O σ ι : Type} [CommRing O] (e : ι → σ) (s : Finset ι) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) →
      f ∈ Ideal.span (Set.range fun i => (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X e s

theorem UpperTheory.V.Fr.ep_odd :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), Ideal.span (evp σ 1 : Set R) = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) := by
  intro O _ _ R _ _ _ σ P
  classical
  rw [← P.part 1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ Ideal.span (Set.range fun i : Fin P.g =>
        (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin P.a ⊕ Fin P.g) O)) := by
      refine ep_odd_span_X Sum.inr Finset.univ f fun n hn => hf n ?_
      have : Finsupp.weight (Space.Loc.par P.a P.g) n = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        refine Finset.sum_eq_zero fun s _ => ?_
        rcases s with s | s
        · simp [Space.Loc.par]
        · simp [hn s (Finset.mem_univ _)]
      rw [this]
      decide
    have h2 := Ideal.mem_map_of_mem P.p h1
    rw [Ideal.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨MvPowerSeries.X (.inr i), fun n hn => ?_, rfl⟩
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply hn
    simp [Finsupp.weight_single, Space.Loc.par]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgZero
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_zero (R : Type) [CommRing R] : sg R 0 = 1 := by simp [sg]

private theorem sg_one (R : Type) [CommRing R] : sg R 1 = -1 := by
  show (-1 : R) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem UpperTheory.V.Fr.ep_ee :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∀ σ, L.IsInv σ → L.ρ.ee = Ideal.span (evp σ 1 : Set L.R) := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx σ hσ
  have hl : l ≠ 2 := hF.l_odd
  have h2O : IsUnit (2 : L.O') := by
    by_contra h
    have hm : (2 : L.O') ∈ maximalIdeal L.O' := (mem_maximalIdeal _).mpr h
    have hr : residue L.O' 2 = 0 := (residue_eq_zero_iff _).mpr hm
    rw [map_ofNat] at hr
    have hd : l ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)
    have hp : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hl h1
  have h2 : IsUnit (2 : L.R) := by
    have := h2O.map (algebraMap L.O' L.R)
    rw [map_ofNat] at this
    exact this
  have hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  have hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0
    rw [hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  apply le_antisymm
  · unfold NRep.ee
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, i, j, hodd, rfl⟩
    apply Ideal.subset_span
    have he := hσ.ent g i j
    rw [hpw i j hodd] at he
    exact he
  · refine Ideal.span_le.mpr ?_
    intro y hy
    have hy' : σ y = sg L.R 1 * y := hy
    rw [sg_one] at hy'
    have hIm : L.ρ.ee ≤ maximalIdeal L.R := by
      unfold NRep.ee
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, i, j, hodd, rfl⟩
      have hmem : S.u.r g i j ∈ S.u.ee := Ideal.subset_span ⟨g, i, j, hodd, rfl⟩
      have hxm := hx hmem
      rw [← L.lies] at hxm
      exact Ideal.mem_comap.mp hxm
    haveI : Nontrivial (L.R ⧸ L.ρ.ee) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)
    haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) :=
      co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)
    have key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})),
        Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rcases hz with hB | ⟨g, i, j, rfl⟩
        · have hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩ := hσ.base ⟨z, hB⟩
          rw [sg_zero, one_mul] at hb'
          show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)
          rw [hb']
        · have he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j := hσ.ent g i j
          show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)
          rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
          · rw [hpw0 i j h, sg_zero, one_mul] at he'
            rw [he']
          · rw [hpw i j h, sg_one] at he'
            have hm : L.ρ.r g i j ∈ L.ρ.ee := Ideal.subset_span ⟨g, i, j, h, rfl⟩
            rw [he', Ideal.Quotient.eq]
            have hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j := by ring
            rw [hc]
            exact Ideal.mul_mem_left _ _ hm
      | algebraMap r =>
        show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))
        rw [L.ι.commutes]
        have hc := (σ.restrictScalars O).commutes r
        rw [AlgHom.restrictScalars_apply] at hc
        rw [hc]
      | add a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add (f := _), iha, ihb]
      | mul a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))
        simp only [map_mul, iha, ihb]
    have huniq := L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by
      show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _
      exact res_map _ _)
    have h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := by
      rintro ⟨z, hz⟩
      exact key' z hz
    have h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := fun a => rfl
    have heq := huniq.unique h1 h2'
    have hyq := AlgHom.congr_fun heq y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq
    have hd := Ideal.Quotient.eq.mp hyq
    have h2y : 2 * y ∈ L.ρ.ee := by
      have hc : 2 * y = -((-1 * y) - y) := by ring
      rw [hc]
      exact neg_mem hd
    obtain ⟨u, hu⟩ := h2
    have hc : y = (↑u⁻¹ : L.R) * (2 * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show y ∈ L.ρ.ee
    rw [hc]
    exact Ideal.mul_mem_left _ _ h2y
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sum_ge {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (m : ℕ) (e : F.V → ℕ)
    (h : ∀ v, m ≤ e v) : m * F.d ≤ ∑ v, F.dv v * e v := by
  unfold Frame.d
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (h v)

private theorem sum_le {I : Type} [Fintype I] (m : ℕ) (e : I → ℕ) (h : ∀ v, e v ≤ m) :
    ∑ v, e v ≤ m * Fintype.card I := by
  have := Finset.sum_le_card_nsmul Finset.univ e m (fun v _ => h v)
  simpa [mul_comm] using this

theorem UpperTheory.V.Fr.epres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → Nonempty L.EPres := by
  intro l _ O _ _ _ _ F C₀ hok S x L hx
  obtain ⟨σ, hσ⟩ := ep_inv hok S x L hx
  have hbarL := pr_res hok (Or.inr rfl) S x L
  obtain ⟨φ, hφ⟩ := hbarL.1
  have hgood := pr_good hok (Or.inr rfl) (ResidueField L.O') φ _ hφ
  have h2K : (2 : ResidueField L.O') ≠ 0 := hgood.1.two
  have h2 : IsUnit (2 : L.O') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_ofNat]
    exact h2K
  have hloc := loc_rho hok (Or.inr rfl) S x L
  have hU : NRep.Univ L.O' L.ρ := ⟨hloc.1, fun C _ _ _ ρ' hc hb => def_iso hok (Or.inr rfl) S x L C ρ' hc hb⟩
  obtain ⟨B₀, hB₀, hB₀c⟩ := pr_box hok L.R (maximalIdeal L.R) L.ρ hloc.1
    (fun v => flag hok (Or.inr rfl) S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨B, π, hBo, hBr, hG⟩ := ep_gbox L.O' h2 hok.del_c L.R σ hσ.sq L.ρ B₀ hB₀ hgood.1 hσ.ent
    (fun v i s => hσ.base (S.ψB v i s))
  have hBc : Box.Cont (maximalIdeal L.R) B := by
    unfold Box.Cont
    rw [hBr]
    exact hB₀c
  have hEv := ep_ev L.O' h2 L.R σ B π hG
  have htan := ep_tan hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv hgood.2.1 hgood.2.2
  obtain ⟨a, g, p, hsurj, hvar, hpart, hhom, hmin⟩ := ep_vars L.O' h2 L.R σ hσ.sq
  obtain ⟨κ, _, f, wf, hf, hker, hind⟩ := ep_rels L.O' h2 (Fin a ⊕ Fin g) (Space.Loc.par a g) (RingHom.ker p) hhom
  let P : GPres L.O' σ := ⟨a, g, p, κ, f, wf, hsurj, hvar, hpart, hhom, hmin, hf, hker, hind⟩
  have hee : L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (Sum.inr i))) := by
    rw [ep_ee hok S x L hx σ hσ, ep_odd L.O' L.R σ P]
  have hBbOf : (Box.bar L.O' B).Of (NRep.bar L.O' L.ρ) := hBo.map _
  have hdual := pr_dual hok (Or.inr rfl) (ResidueField L.O') φ (NRep.bar L.O' L.ρ) (Box.bar L.O' B) hBbOf hφ hbarL.2
  have hprp := ep_prp h2K (Box.bar L.O' B) π hEv
  have hopen := (pr_open hok L.O' L.R B hBc).2.1
  have hopenj : ∀ j, IsOpen ((hEv.ad j).ker : Set F.Γ) := by
    intro j
    apply Subgroup.isOpen_mono _ hopen
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp [Box.Ev.ad_apply, hs]
  have hstab : ∀ j (v : F.V) (s : F.Gv v), ∀ X ∈ (Box.bar L.O' B).bp j v, (hEv.ad j (F.loc v s)) X ∈ (Box.bar L.O' B).bp j v := by
    intro j v s X hX
    simp only [Box.bp, Submodule.mem_comap, Submodule.subtype_apply] at hX ⊢
    rw [Box.Ev.ad_apply]
    exact pr_bstab _ _ v s _ hX
  have EC := fun j => hok.ec (ResidueField L.O') (adp (ResidueField L.O') j) (hEv.ad j) ((Box.bar L.O' B).bp j) (hopenj j) (hstab j) (hprp.2 j _ hdual)
  have hder := ep_der L.O' h2 L.R σ P
  have hdimb := ep_dimb h2K (Box.bar L.O' B) π hEv
  have hcw := fun w => ep_cw h2K (Box.bar L.O' B) π hEv (F.cw w) (hok.cw_sq w) (hok.del_cw w)
  refine ep_pad S x L σ hσ P ?_ ?_ hee
  · haveI := (EC 0).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 0 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 0)
    have hs1 : 4 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 0 v) :=
      sum_ge F 4 _ (fun v => (hdimb v).1)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 0 (F.cw w)) - 1).ker ≤ 1 * Fintype.card F.Inf :=
      sum_le 1 _ (fun w => (hcw w).1)
    rw [hok.card_inf] at hs2
    have e := (EC 0).2
    have t := htan.2
    have d0 := hder.2.1
    omega
  · haveI := (EC 1).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 1 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 1)
    have hs1 : 2 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 1 v) :=
      sum_ge F 2 _ (fun v => (hdimb v).2)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 1 (F.cw w)) - 1).ker ≤ 2 * Fintype.card F.Inf :=
      sum_le 2 _ (fun w => (hcw w).2)
    rw [hok.card_inf] at hs2
    have e := (EC 1).2
    have t := htan.1 1
    have d1 := hder.2.2
    omega
