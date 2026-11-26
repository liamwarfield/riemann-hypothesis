module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem tri_zero {K G ι : Type} [Field K] [Fintype ι] [LinearOrder ι] (M : G → Matrix ι ι K) (ω : G → K)
    (Φ : Matrix ι ι K) (hM : ∀ g i j, j < i → M g i j = 0)
    (h : ∀ g i j, ∑ p, M g i p * Φ p j = ω g * ∑ q, Φ i q * M g q j)
    (key : ∀ i j, (∀ g, M g i i * Φ i j = ω g * (Φ i j * M g j j)) → Φ i j = 0) : ∀ i j, Φ i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih' =>
  refine key i j fun g => ?_
  have := h g i j
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at this
  · exact this
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with h1 | h1
    · rw [ih' q h1, zero_mul]
    · rw [hM g q j h1, mul_zero]
  · simp
  · intro p _ hp
    rcases lt_or_gt_of_ne hp with h1 | h1
    · rw [hM g i p h1, zero_mul]
    · rw [ih p h1 j, mul_zero]
  · simp

private theorem om_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Frame l k) {K : Type} [Field K]
    [CharP K l] (φ : k →+* K) (g : F.Γ) : φ (F.om k g : k) = (F.om K g : K) := by
  have : φ.comp (ZMod.castHom (dvd_refl l) k) = ZMod.castHom (dvd_refl l) K := Subsingleton.elim _ _
  exact RingHom.congr_fun this _

private theorem w_cases {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) :
    w n j - w n i = 0 ∨ (w n j - w n i = 1 ∨ w n j - w n i = -1) ∨
      ((w n j - w n i = 2 ∨ w n j - w n i = -2) ∧ j = i.rev) := by
  rcases hn with rfl | rfl
  · revert i j; decide
  · revert i j; decide

private theorem thetaLie_single {K : Type} [Field K] {n : ℕ} (i : Fin n) :
    thetaLie (Matrix.single i i.rev (1 : K)) = -Matrix.single i i.rev (1 : K) := by
  unfold thetaLie
  congr 1
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev, Matrix.mul_apply, Finset.sum_eq_single a.rev]
  · simp only [Jmat, Matrix.transpose_apply, Matrix.single_apply, Fin.rev_rev, if_true, one_mul, mul_one,
      Fin.rev_inj]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  · intro p _ hp
    simp [Jmat, hp]
  · simp
  · intro p _ hp
    have : b ≠ p.rev := fun h => hp (by simp [h])
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_dual :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] [CharP K l] (φ : k →+* K) (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.IsBar φ → ((∀ g, UpT (ρ.r g)) ∨ ∀ g, UpT (ρ.r g)ᵀ) → ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K, (∀ g X, f (B.ad g X) = F.om K g * f X) → f = 0 := by
  intro l _ k _ _ F C₀ n ok hn K _ _ φ ρ B hB hbar htri f hf
  set Φ : Matrix (Fin n) (Fin n) K := fun i j => f (Matrix.single i j 1) with hΦ
  have hsum : ∀ X : Matrix (Fin n) (Fin n) K, f X = ∑ i, ∑ j, X i j * Φ i j := fun X => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : ∀ (g : F.G0) X, f (ρ.r g * X) = F.om K g * f (X * ρ.r g) := fun g X => by
    rw [← hf]
    congr 1
    have hr : (B.r g).right = 1 := (B.nu g).trans g.2
    show _ = (B.r g).adFun _
    rw [GG.adFun, if_pos hr, ← hB.res g, GG.mat]
    simp [Matrix.mul_assoc]
  have h1 : ∀ (g : F.G0) i j, ∑ p, ρ.r g p i * Φ p j = F.om K g * ∑ q, Φ i q * ρ.r g j q := fun g i j => by
    have := h0 g (Matrix.single i j 1)
    rw [hsum, hsum] at this
    rw [Finset.sum_eq_single i (s := Finset.univ) (f := fun a => ∑ b, (Matrix.single i j (1 : K) * ρ.r g) a b * Φ a b)]
      at this
    · convert this using 2 with p
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
        · simp
      · simp [mul_comm]
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, zero_mul]
    · simp
  have hc : ∀ i, -Φ i i.rev = F.om K F.c * Φ i i.rev := fun i => by
    rw [hΦ]
    dsimp only
    rw [← hf, ← map_neg, ← thetaLie_single]
    congr 1
    have hr : (B.r F.c).right ≠ 1 := by rw [B.nu, ok.del_c]; decide
    have hl : (B.r F.c).left = 1 := Units.ext hB.atc
    show _ = (B.r F.c).adFun _
    rw [GG.adFun, if_neg hr, GG.mat, hl]
    simp
  have key : ∀ i j, (∀ g : F.G0, ρ.r g i i * Φ i j = F.om K g * (Φ i j * ρ.r g j j)) → Φ i j = 0 := by
    intro i j h
    by_contra hne
    have h2 : ∀ g : F.G0, F.om k g * F.Ψ g ^ (w n j - w n i) = 1 := fun g => by
      have e := h g
      rw [hbar.1, hbar.1, ← om_map F φ, mul_comm (Φ i j), ← mul_assoc, ← map_mul] at e
      have e2 := φ.injective (mul_right_cancel₀ hne e)
      rw [← Units.val_mul, Units.val_inj] at e2
      rw [_root_.zpow_sub, ← mul_assoc, ← e2, mul_inv_cancel]
    rcases w_cases hn i j with h3 | h3 | ⟨h3, rfl⟩
    · obtain ⟨g, hg⟩ := ok.f2a
      exact hg (by simpa [h3] using h2 g)
    · obtain ⟨g, hg⟩ := ok.f2b _ h3
      exact hg (h2 g)
    · obtain ⟨g, hg⟩ := ok.f2c _ h3
      apply hg
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · rw [h2 ⟨g, hd⟩, one_mul]
        simp [Frame.delK, hd]
      · have hm : g * F.c ∈ F.del.ker := by rw [MonoidHom.mem_ker, map_mul, hd, ok.del_c]; rfl
        have e := h2 ⟨_, hm⟩
        have ec : F.om k F.c = -1 := by
          apply Units.ext
          apply φ.injective
          rw [om_map]
          have := hc i
          rw [← neg_one_mul] at this
          rw [← mul_right_cancel₀ hne this]
          simp
        have ed : F.delK k g = -1 := by
          apply Units.ext
          simp [Frame.delK, hd]
        simp only [map_mul, ec, ok.Ψ_c, mul_one] at e
        rw [ed, mul_right_comm, e]
  have hz : ∀ i j, Φ i j = 0 := by
    rcases htri with ht | ht
    · exact tri_zero (ι := (Fin n)ᵒᵈ) (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ
        (fun g i j hij => ht g j i hij) h1 key
    · exact tri_zero (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ ht h1 key
  ext1 X
  simp [hsum, hz]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgClosed
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_closed :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ c : ℕ → C, (∀ N, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1)) → ∃ x : C, ∀ N, algebraMap C D (x - c N) ∈ 𝔪 ^ (N + 1) := by
  intro C _ _ _ _ D _ _ 𝔪 h c hc
  let J : ℕ → Ideal C := fun n => (𝔪 ^ n).comap (algebraMap C D)
  have hJ : Antitone J := fun _ _ hab => Ideal.comap_mono (Ideal.pow_le_pow_right hab)
  have h0 : ⨅ n, J n = ⊥ := by
    simp only [J]
    rw [← Ideal.comap_iInf, h.sep, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
    exact h.inj
  choose s hs using GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot J hJ h0
  have hd : ∀ N d, c (N + d) - c N ∈ J (N + 1) := fun N d => by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : c (N + d + 1) - c (N + d) ∈ J (N + 1) := hJ (show N + 1 ≤ N + d + 1 by omega) (hc (N + d))
      have := (J (N + 1)).add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  have hle : ∀ {a b}, a ≤ b → c b - c a ∈ J (a + 1) := fun {a b} hab => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact hd a d
  let t : ℕ → ℕ := fun k => k + ∑ i ∈ Finset.range (k + 1), s i
  have ht : ∀ k, s k ≤ t k := fun k => by
    simp only [t, Finset.sum_range_succ]
    omega
  have ht' : ∀ k, k ≤ t k := fun k => Nat.le_add_right _ _
  have htm : Monotone t := fun a b hab =>
    Nat.add_le_add hab (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal C) (fun k => c (t k)) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact hs m (hJ (by have := ht m; omega) (hle (htm hmn)))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun N => ?_⟩
  have h1 : c (t (N + 1)) - L ∈ J (N + 1) := by
    have := hL (N + 1)
    rw [← h.comap] at this
    exact Ideal.le_comap_pow _ (N + 1) this
  have h2 : c (t (N + 1)) - c N ∈ J (N + 1) := hle (by have := ht' (N + 1); omega)
  have h3 := (J (N + 1)).sub_mem h2 h1
  rwa [sub_sub_sub_cancel_left] at h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDualb
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_dualb :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Ideal C) (κ : Type) [Fintype κ] (ε : κ → C), maximalIdeal C * K = ⊥ → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) → ∃ co : κ → K →ₗ[O] ResidueField O, ∀ y : K, ∃ a : κ → O, (∀ u, residue O (a u) = co u y) ∧ (y : C) = ∑ u, a u • ε u := by
  intro O _ _ C _ _ _ K κ _ ε hK hspan hind
  have hε : ∀ u, ε u ∈ K := fun u => by
    rw [hspan]; exact Ideal.subset_span ⟨u, rfl⟩
  have hex : ∀ y : K, ∃ a : κ → O, (y : C) = ∑ u, a u • ε u := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span (Set.range ε) := hspan ▸ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
    choose a ha using fun u => IsCO.res_surj (O := O) (c u)
    refine ⟨a, ?_⟩
    show y = _
    rw [← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h0 : (c u - algebraMap O C (a u)) * ε u ∈ maximalIdeal C * K :=
      Ideal.mul_mem_mul (ha u) (hε u)
    rw [hK, Ideal.mem_bot, sub_mul, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def]
  have huniq : ∀ a b : κ → O, ∑ u, a u • ε u = ∑ u, b u • ε u →
      ∀ u, residue O (a u) = residue O (b u) := by
    intro a b hab u
    have h := hind (fun u => a u - b u) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hab, sub_self]) u
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h
  choose a ha using hex
  refine ⟨fun u =>
    { toFun := fun y => residue O (a y u)
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }, fun y => ⟨a y, fun u => rfl, ha y⟩⟩
  · rw [← map_add (f := _)]
    refine huniq (a (x + y)) (fun u => a x u + a y u) ?_ u
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, ← ha, ← ha]
    rfl
  · have h := huniq (a (c • x)) (fun u => c * a x u) (by
      simp only [mul_smul, ← Finset.smul_sum]
      rw [← ha, ← ha]
      rfl) u
    rw [h, RingHom.id_apply, map_mul, Algebra.smul_def]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hA i c hc, zero_mul]
  · rw [hB c j (lt_of_lt_of_le h hc), mul_zero]

private theorem upT_of_comm {K : Type} [Field K] {n : ℕ} {T Z : Matrix (Fin n) (Fin n) K} (hT : UpT T)
    (hd : ∀ i j, i ≠ j → T i i ≠ T j j) (h : UpT (T * Z - Z * T)) : UpT Z := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, n - i.val + j.val = m → j < i → Z i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h0 := h i j hji
      have hji' : j.val < i.val := hji
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
      · have h1 : (T i i - T j j) * Z i j = 0 := by linear_combination h0
        exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hd i j hji.ne'))
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · have hc' : c.val < j.val := hc
          rw [ih (n - i.val + c.val) (by omega) i c rfl (hc.trans hji), zero_mul]
        · rw [hT c j hc, mul_zero]
      · simp
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [hT i c hc, zero_mul]
        · have hc' : i.val < c.val := hc
          have := c.isLt
          rw [ih (n - c.val + j.val) (by omega) c j rfl (hji.trans hc), mul_zero]
      · simp
  exact fun i j hij => key _ i j rfl hij

theorem UpperTheory.V.Fr.pr_brig :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (K : Type) [Field K] (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.Good → ∀ (v : F.V) (Y : Matrix (Fin n) (Fin n) K), (∀ s, B.ad (F.loc v s) Y - Y ∈ B.b v) → Y ∈ B.b v := by
  intro l _ k _ F n K _ ρ B hOf hG v Y hY
  obtain ⟨s, hs⟩ := hG.ψd v
  have hT := B.tri v s
  have hr : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have hres : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hOf.res (F.loc0 v s)
  have h1 : UpT ((B.g v : Matrix (Fin n) (Fin n) K) * ((B.r (F.loc v s)).adFun Y - Y) *
      (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hY s
  show UpT ((B.g v : Matrix (Fin n) (Fin n) K) * Y * (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  refine upT_of_comm hT (fun i j hij => ?_) ?_
  · rw [hres, hOf.psi, hOf.psi]
    exact fun e => hs i j hij (Units.ext e)
  · convert upT_mul h1 hT using 1
    simp only [GG.adFun, hr, if_true, GG.mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointFiberNonempty
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_fiber_nonempty :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 2 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strS Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hup : ∀ g : F.G0, ρ.r g 0 1 = 0 := by
    intro g
    have h : ρ.r g 0 1 ∈ ρ.triM := by
      apply Ideal.subset_span (s := {x | ∃ g i j, i < j ∧ x = ρ.r g i j})
      exact ⟨g, 0, 1, by decide, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]
    rw [hd0, hd1]
    ring
  · intro g
    show ρ.r (F.star g) 1 0 = ρ.r g 1 0
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]
    rfl
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hd : d ≠ 0 := by
      intro h
      apply ht
      rw [hdd, sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    refine ⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![s, t]) 1) 0
    simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : Fin 2) ≠ 0), if_false, if_true, smul_zero,
      sub_zero, smul_eq_mul, mul_one] at h10
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    rw [hd0, hd1, hψ0, hψ1, hl, hl] at h10
    simp only [mul_zero, sub_zero] at h10
    have hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹)
        * algebraMap k Q d⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]
    simp only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]
    linear_combination algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResDual
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrExt
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ},
      F.Ok C₀ → ∀ (C : Type) [CommRing C] (r r' : F.Γ →* GG (m := n) (R := C)),
        (∀ s, (r s).right = F.del s) → (∀ s, (r' s).right = F.del s) →
        (r F.c).mat = (r' F.c).mat → (∀ s : F.G0, (r s).mat = (r' s).mat) → r = r' := by
  intro l _ k _ _ F C₀ n hF C _ r r' h h' hc h0
  have key : ∀ s, (r s).mat = (r' s).mat → r s = r' s := fun s hs =>
    SemidirectProduct.ext (Units.ext hs) ((h s).trans (h' s).symm)
  refine MonoidHom.ext fun s => ?_
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact key s (h0 ⟨s, hs⟩)
  · have hm : s * F.c ∈ F.del.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, hF.del_c]
      simp
    have e := key _ (h0 ⟨s * F.c, hm⟩)
    rw [map_mul, map_mul, key _ hc] at e
    exact mul_right_cancel e
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O _ x = x.fst := by
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective x.fst
  have ha : (algebraMap O (DualNumber (ResidueField O)) o).fst = x.fst := by
    rw [← ho]
    first
      | rfl
      | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, IsLocalRing.ResidueField.algebraMap_eq]
  have hfst : (x - algebraMap O _ o).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, ha, sub_self]
  have hsq : (x - algebraMap O _ o) * (x - algebraMap O _ o) = 0 := by
    ext
    · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, hfst, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]
  have hmem : x - algebraMap O _ o ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h2 := hu.mul hu
    rw [hsq] at h2
    exact not_isUnit_zero h2
  have h0 := (res_eq_zero_iff O _ _).2 hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  rw [h0, ← ha]
  first
    | rfl
    | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

theorem UpperTheory.V.Fr.pr_dof :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (DualNumber (ResidueField O))] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → ∀ (ρ' : NRep F n (DualNumber (ResidueField O))) (r' : F.Γ →* GG (m := n) (R := DualNumber (ResidueField O))), ρ'.Cont (maximalIdeal _) → ρ'.bar O = ρ.bar O → (∀ s, (r' s).right = F.del s) → (r' F.c).mat = 1 → (∀ s : F.G0, (r' s).mat = ρ'.r s) → ∃ D ∈ Tan O R, ∀ s, (r' s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ R _ _ _ ρ B hU hOf ρ' r' hc' hbar hnu hatc hres
  obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hc' hbar
  have hfst : ∀ x, (g x).fst = res O R x := fun x => by
    rw [← res_dual O (g x), res_map]
  let Dd : R →ₗ[O] ResidueField O :=
    { toFun := fun x => (g x).snd
      map_add' := fun x y => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun a x => by
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
  have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = r' := by
    refine pr_ext hF _ _ _ (Box.nu _) hnu ?_ ?_
    · change (B.r F.c).mat.map g = (r' F.c).mat
      rw [hOf.atc, hatc]
      exact Matrix.map_one _ (map_zero g) (map_one g)
    · intro s
      change (B.r s).mat.map g = (r' s).mat
      rw [hOf.res]
      change (ρ.map (g : R →+* DualNumber (ResidueField O))).r s = (r' s).mat
      rw [hg, hres]
  refine ⟨Dd, ?_, fun s => ?_⟩
  · intro f h
    rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
  · rw [← hr]
    show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
    rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_count :
    ∀ {K G W V T : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W] [Module.Finite K W] [AddCommGroup T] [Module K T] [Module.Finite K T] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation K G W) (b : V → Submodule K W) (φ : T →ₗ[K] (G → W)), (∀ v Y, (∀ s, ρ (loc v s) Y - Y ∈ b v) → Y ∈ b v) → (∀ x ∈ Z1C loc ρ b, ∃ D X, ∀ s, φ D s = x.1 s + (ρ s X - X)) → Module.finrank K (H1C loc ρ b) ≤ Module.finrank K T ∧ ∀ (X₀ : W) (D₀ : T), X₀ ≠ 0 → (∀ s, φ D₀ s = ρ s X₀ - X₀) → Module.finrank K (H1C loc ρ b) + 1 ≤ Module.finrank K T + Module.finrank K (coneH0 ρ b) := by
  intro K G W V T _ _ _ _ _ _ _ _ _ Gv _ loc ρ b φ hA hB
  let cob : W →ₗ[K] (G → W) := LinearMap.pi (fun s => ρ s - LinearMap.id)
  have hcob : ∀ X s, cob X s = ρ s X - X := fun X s => rfl
  let C := LinearMap.range cob
  let f : T →ₗ[K] (G → W) ⧸ C := C.mkQ ∘ₗ φ
  let Ψ : Z1C loc ρ b →ₗ[K] (G → W) ⧸ C :=
    C.mkQ ∘ₗ (LinearMap.fst K (G → W) (V → W)) ∘ₗ (Z1C loc ρ b).subtype
  have hle : Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hx⟩ hxB
    rw [Submodule.mem_comap] at hxB
    obtain ⟨X, hX, -⟩ := hxB
    rw [LinearMap.mem_ker]
    show C.mkQ x.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X, funext fun s => ((hX s).trans (hcob X s).symm).symm⟩
  have hker : LinearMap.ker Ψ ≤ Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) := by
    rintro ⟨x, hx⟩ hk
    rw [LinearMap.mem_ker] at hk
    change C.mkQ x.1 = 0 at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
    obtain ⟨X, hX⟩ := hk
    obtain ⟨-, -, hloc⟩ := hx
    rw [Submodule.mem_comap]
    refine ⟨X, fun s => (congrFun hX s).symm, fun v => ?_⟩
    have hmem : X - x.2 v ∈ b v := by
      refine hA v _ (fun s => ?_)
      have h1 := hloc v s
      convert h1 using 1
      rw [← hX, hcob, map_sub]
      abel
    have h2 := (b v).neg_mem hmem
    rwa [neg_sub] at h2
  let L := (Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b)).liftQ Ψ hle
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : ∀ y, L y ∈ LinearMap.range f := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨D, X, hD⟩ := hB z.1 z.2
    refine ⟨D, ?_⟩
    show C.mkQ (φ D) = C.mkQ z.1.1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨X, funext fun s => ?_⟩
    show cob X s = φ D s - z.1.1 s
    rw [hcob, hD]
    abel
  let L' : H1C loc ρ b →ₗ[K] LinearMap.range f := L.codRestrict _ hrange
  have hinj' : Function.Injective L' := fun a c h => hinj (congrArg Subtype.val h)
  have h1 : Module.finrank K (H1C loc ρ b) ≤ Module.finrank K (LinearMap.range f) :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := LinearMap.finrank_range_le f
  refine ⟨h1.trans h3, ?_⟩
  intro X₀ D₀ hX₀ hD₀
  by_cases hinv : ∀ s, ρ s X₀ = X₀
  · have hH0 : X₀ ∈ coneH0 ρ b := by
      show (∀ g, ρ g X₀ = X₀) ∧ ∀ v, X₀ ∈ b v
      exact ⟨hinv, fun v => hA v X₀ (fun s => by rw [hinv, sub_self]; exact (b v).zero_mem)⟩
    have h4 : Module.finrank K (coneH0 ρ b) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hH0
      exact hX₀ ((Submodule.mem_bot K).1 hH0)
    omega
  · push_neg at hinv
    obtain ⟨s, hs⟩ := hinv
    have hD0 : D₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      show C.mkQ (φ D₀) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨X₀, funext fun t => (hcob X₀ t).trans (hD₀ t).symm⟩
    have hne : D₀ ≠ 0 := by
      rintro rfl
      apply hs
      have h5 := hD₀ s
      rw [map_zero, Pi.zero_apply] at h5
      exact (sub_eq_zero.1 h5.symm)
    have h4 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hD0
      exact hne ((Submodule.mem_bot K).1 hD0)
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem hom_eq_res (g : R →ₐ[O] ResidueField O) (x : R) : g x = res O R x := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : g (x - algebraMap O R a) = 0 := by
    have hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O) := by
      rw [hker]
      exact ha
    exact (RingHom.mem_ker).1 hm
  have h2 : res O R (x - algebraMap O R a) = 0 := (res_eq_zero_iff O R _).2 ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem tan_mul (D : Tan O R) (f g : R) :
    D.1 (f * g) = res O R f * D.1 g + res O R g * D.1 f := D.2 f g

private theorem tan_one (D : Tan O R) : D.1 1 = 0 := by
  simpa using tan_mul D 1 1

private theorem tan_alg (D : Tan O R) (a : O) : D.1 (algebraMap O R a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]

private theorem tan_finite : Module.Finite (ResidueField O) (Tan O R) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  let φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O) :=
    { toFun := fun D i => D.1 (i : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)
  have h0 : ∀ i ∈ s, D.1 i = 0 := fun i hi => congrFun hD ⟨i, hi⟩
  have hm : ∀ y ∈ maximalIdeal R, D.1 y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h0 z hz
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
    | smul c z hz ih =>
      have hz' : z ∈ maximalIdeal R := by
        rw [← hs]
        exact hz
      rw [smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h := hm _ ha
  rw [map_sub, tan_alg, sub_zero] at h
  exact h

private noncomputable def tanEquiv : (R →ₐ[O] DualNumber (ResidueField O)) ≃ Tan O R where
  toFun f := ⟨{ toFun := fun x => (f x).snd
                map_add' := fun x y => by simp
                map_smul' := fun a x => by simp }, fun x y => by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    show (f (x * y)).snd = res O R x • (f y).snd + res O R y • (f x).snd
    rw [map_mul, DualNumber.snd_mul, h, h, smul_eq_mul, smul_eq_mul, mul_comm (f x).snd]⟩
  invFun D :=
    { toFun := fun x => TrivSqZeroExt.inl (res O R x) + TrivSqZeroExt.inr (D.1 x)
      map_one' := by ext <;> simp [tan_one]
      map_mul' := fun x y => by ext <;> simp [tan_mul, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [tan_alg, TrivSqZeroExt.algebraMap_eq_inl'] }
  left_inv f := by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    refine AlgHom.ext fun x => ?_
    ext <;> simp [h]
  right_inv D := Subtype.ext (LinearMap.ext fun x => by simp)

end

theorem UpperTheory.V.Fr.pr_tan :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Module.Finite (ResidueField O) (Tan O R) ∧ Nat.card (R →ₐ[O] (DualNumber (ResidueField O))) = Nat.card (Tan O R) := by
  intro O _ _ R _ _ _
  exact ⟨tan_finite, Nat.card_congr tanEquiv⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  revert j; decide

private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  show (-1 : K) ^ ((1 : ZMod 2).val) = -1
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · simp [sg0]
  · simp [sg0]
  · simp [sg0]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]
    ring

private theorem sg_nsmul (K : Type) [CommRing K] (m : ℕ) (i : ZMod 2) : sg K (m • i) = sg K i ^ m := by
  induction m with
  | zero => simp [sg0]
  | succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]

private theorem sg_weight (K : Type) [CommRing K] {ι : Type} (wt : ι → ZMod 2) (n : ι →₀ ℕ) :
    (n.prod fun s m => sg K (wt s) ^ m) = sg K (Finsupp.weight wt n) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]
  generalize n.support = t
  refine Finset.induction_on t ?_ ?_
  · simp [sg0]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]

private theorem coeff_sg (O : Type) [CommRing O] {ι : Type} (j : ZMod 2) (y : MvPowerSeries ι O) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (sg _ j * y) = sg O j * MvPowerSeries.coeff n y := by
  rcases zcases j with rfl | rfl <;> simp [sg0, sg1]

theorem UpperTheory.V.Fr.ep_ps :
    ∀ (O : Type) [CommRing O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2), ∃ τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O, (∀ y, τ (τ y) = y) ∧ (∀ j, evp τ j = wtPart O wt j) ∧ ∀ j y, (2 : MvPowerSeries ι O) * wcomp O wt j y = y + sg _ j * τ y := by
  classical
  intro O _ h2 ι _ wt
  have hsq : ∀ i : ZMod 2, sg O i * sg O i = 1 := by
    intro i
    rw [← sg_add]
    rcases zcases i with rfl | rfl
    · exact sg0 O
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
      exact sg0 O
  have hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j := by
    intro i j hij
    rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
    · exact absurd rfl hij
    · simp [sg0, sg1]
    · simp [sg0, sg1]
    · exact absurd rfl hij
  let a : ι → O := fun s => sg O (wt s)
  have hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := by
    intro y n
    rw [MvPowerSeries.coeff_rescale, sg_weight]
  let τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O :=
    AlgHom.mk (MvPowerSeries.rescale a) (fun r => by
      ext n
      show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _
      rw [hcoef]
      by_cases hn : n = 0
      · subst hn
        simp [sg0]
      · classical
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.coeff_C, if_neg hn, mul_zero])
  have hτ : ∀ y n, MvPowerSeries.coeff n (τ y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := hcoef
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro y
    ext n
    rw [hτ, hτ, ← mul_assoc, hsq, one_mul]
  · intro j
    ext y
    show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0
    constructor
    · intro h n hn
      have := congrArg (MvPowerSeries.coeff n) h
      rw [hτ, coeff_sg, hne _ _ hn] at this
      have h' : 2 * MvPowerSeries.coeff n y = 0 := by
        linear_combination (-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j
      exact (h2.mul_right_eq_zero).mp h'
    · intro h
      ext n
      rw [hτ, coeff_sg]
      by_cases hn : Finsupp.weight wt n = j
      · rw [hn]
      · rw [h n hn, mul_zero, mul_zero]
  · intro j y
    ext n
    rw [two_mul, map_add (f := _), coeff_wcomp, map_add (f := _), coeff_sg, hτ]
    split_ifs with hn
    · rw [hn]
      linear_combination (-MvPowerSeries.coeff n y) * hsq j
    · rw [hne _ _ hn]
      linear_combination MvPowerSeries.coeff n y * hsq j
end
