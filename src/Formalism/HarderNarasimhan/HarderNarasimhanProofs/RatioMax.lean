module

public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt

@[expose] public section

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
open Module Submodule

noncomputable section

namespace Formalism.HN

theorem le_of_imageLattice_le {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (L N₁ N₂ : Submodule R V)
    (hinj : Set.InjOn ρ (L : Set V)) (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h : zl ρ N₁ ≤ zl ρ N₂) :
    N₁ ≤ N₂ := by
  intro x hx
  have hx' : ρ x ∈ zl ρ N₂ :=
    h ((satR_mem_zl ρ N₁ (ρ x)).2 ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := (satR_mem_zl ρ N₂ (ρ x)).1 hx'
  have hxy : y = x := hinj (h₂ hy) (h₁ hx) hyx
  rw [← hxy]
  exact hy

universe u v w in
theorem ratioMax_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) : RatioMax.{u, v, w} := by
  unfold RatioMax
  intro R V E _ _ _ _ _ _ ρ L S hL hS hSL
  obtain ⟨hsub, hmono, hsat, -, -, -, hLsat, -⟩ := h2 R V E ρ L hL
  have hinj : Set.InjOn ρ (L : Set V) := hL.1
  have hdL : DiscreteTopology (zl ρ L) := hL.2
  have hSle : S ≤ L := hS.1
  have hSL' : S < L := lt_of_le_of_ne hSle hSL
  have hgap : ∀ N : Submodule R V, S < N → N ≤ L → (rk ρ S : ℝ) < rk ρ N := by
    intro N hSN hNL
    have hle := (hmono S N hSN.le hNL).1
    have hne : rk ρ N ≠ rk ρ S := fun he => hSN.ne (hsat S N hS hSN.le hNL he).symm
    exact_mod_cast lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨f, hf⟩ : ∃ f : Submodule R V → ℝ, ∀ N, f N =
      (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) := ⟨_, fun _ => rfl⟩
  have hdeg : ∀ N : Submodule R V, S < N → N ≤ L → f L ≤ f N →
      deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ N := by
    intro N hSN hNL hc
    have hpos : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNL)
    have hrN : (rk ρ N : ℝ) - rk ρ S ≤ rk ρ L := by
      have h3 : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (hmono N L hNL le_rfl).1
      have h4 : (0 : ℝ) ≤ rk ρ S := Nat.cast_nonneg _
      linarith
    rw [hf N, le_div_iff₀ hpos] at hc
    have h3 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ N : ℝ) - rk ρ S) := by
      calc -|f L| * (rk ρ L : ℝ) ≤ -|f L| * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonpos_left hrN (neg_nonpos.2 (abs_nonneg _))
        _ ≤ f L * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonneg_right (neg_abs_le _) hpos.le
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Submodule R V),
      T = {N | IsSat ρ L N ∧ S < N ∧ f L ≤ f N} := ⟨_, rfl⟩
  have hmemT : ∀ N, N ∈ T ↔ IsSat ρ L N ∧ S < N ∧ f L ≤ f N := by
    intro N
    subst hTdef
    exact Iff.rfl
  have hfinE := Formalism.F.finiteSaturated E (zl ρ L) hdL
      (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_
    · rintro _ ⟨N, hN, rfl⟩
      obtain ⟨hNs, hSN, hc⟩ := (hmemT N).1 hN
      show _ ∧ _
      refine ⟨hNs.2, ?_⟩
      have hlat := hsub N hNs.1
      have : DiscreteTopology (zl ρ N) := hlat.2
      have hcpos : 0 < Formalism.F.covol (zl ρ N) :=
        Formalism.F.covol_pos _
      have hd := hdeg N hSN hNs.1 hc
      have hdN : deg ρ N = -Real.log (Formalism.F.covol (zl ρ N)) := rfl
      rw [← Real.log_le_iff_le_exp hcpos]
      linarith
    · intro A hA B hB hAB
      have hA' := ((hmemT A).1 hA).1.1
      have hB' := ((hmemT B).1 hB).1.1
      exact le_antisymm
        (le_of_imageLattice_le ρ L A B hinj hA' hB' hAB.le)
        (le_of_imageLattice_le ρ L B A hinj hB' hA' hAB.ge)
  have hLT : L ∈ T := (hmemT L).2 ⟨hLsat, hSL', le_rfl⟩
  obtain ⟨N, hNT, hNmax⟩ := Set.exists_max_image T f hT ⟨L, hLT⟩
  obtain ⟨hNsat, hSN, -⟩ := (hmemT N).1 hNT
  refine ⟨N, hSN, hNsat, ?_⟩
  intro N' hSN' hN'L
  have hpos' : 0 < (rk ρ N' : ℝ) - rk ρ S := sub_pos.2 (hgap N' hSN' hN'L)
  have hposN : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNsat.1)
  have key : f N' ≤ f N := by
    by_cases hc : f L ≤ f N'
    · obtain ⟨N'', hle, hN''L, himg⟩ := h1 R V E ρ L N' hL hN'L
      have hmon : zl ρ N' ≤ zl ρ L := satBasic_zl_mono ρ hN'L
      have hsp := Formalism.F.saturProps E (zl ρ L) (zl ρ N')
        hdL hmon
      have hsat'' : IsSat ρ L N'' := by
        refine And.intro hN''L ?_
        rw [himg]
        exact hsp.1
      have hrk : rk ρ N'' = rk ρ N' := by
        show Formalism.F.rk (zl ρ N'') = Formalism.F.rk (zl ρ N')
        rw [himg]
        exact hsp.2.2
      have hdg : deg ρ N' ≤ deg ρ N'' := (hmono N' N'' hle hN''L).2 hrk.symm
      have hff : f N' ≤ f N'' := by
        rw [hf N', hf N'', hrk, div_le_div_iff₀ hpos' hpos']
        exact mul_le_mul_of_nonneg_right (by linarith) hpos'.le
      have hN''T : N'' ∈ T := (hmemT N'').2 ⟨hsat'', lt_of_lt_of_le hSN' hle, hc.trans hff⟩
      exact hff.trans (hNmax N'' hN''T)
    · have hlt : f N' < f L := not_le.1 hc
      exact hlt.le.trans ((hmemT N).1 hNT).2.2
  rw [hf N', hf N, div_le_div_iff₀ hpos' hposN] at key
  exact key

theorem maximal_slope_ratio : RatioMax :=
  ratioMax_of real_saturation_property saturation_basic_properties

end Formalism.HN
end
end

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
open Module Submodule

noncomputable section

namespace Formalism.HN

universe u v w w₂

theorem shiftInv_zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) {A B : Submodule R V}
    (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  exact satBasic_zl_mono ρ h

theorem shiftInv_isSat_iff {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {L : Submodule R V} (hL : IsLat ρ L) (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by
  have hB := saturation_basic_properties R V E ρ L hL
  constructor
  · intro hN
    exact ⟨hN.1, fun N' h₁ h₂ h₃ => hB.2.2.1 N N' hN h₁ h₂ h₃⟩
  · rintro ⟨hNL, hmax⟩
    obtain ⟨N', hNN', hN'L, himg⟩ := real_saturation_property R V E ρ L N hL hNL
    have hsat := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hL.2
      (shiftInv_zl_mono ρ hNL)
    have hrk : rk ρ N' = rk ρ N := by
      show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
      rw [himg]
      exact hsat.2.2
    have heq : N' = N := hmax N' hNN' hN'L hrk
    refine ⟨hNL, ?_⟩
    rw [← heq, himg]
    exact hsat.1

theorem shiftInv_mu {R : Type u} {V : Type v} {E : Type w} {E₂ : Type w₂} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (ρ : V →+ E) (ρ₂ : V →+ E₂) (L : Submodule R V) (c : ℝ) (hL : IsLat ρ L)
    (hL₂ : IsLat ρ₂ L)
    (hsh : ∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N)
    (hL0 : L ≠ ⊥) : muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c := by
  obtain ⟨hmax, hmin, -, -, -⟩ := h1 R V E ρ L hL hL0
  obtain ⟨hmax₂, hmin₂, -, -, -⟩ := h1' R V E₂ ρ₂ L hL₂ hL0
  have hrL := (hsh L le_rfl).1
  have hdL := (hsh L le_rfl).2
  constructor
  · apply le_antisymm
    · rw [hmax₂]
      intro N hN
      rw [(hsh N hN).1, (hsh N hN).2]
      have := (hmax (muMax ρ L)).1 le_rfl N hN
      linarith
    · have key : muMax ρ L ≤ muMax ρ₂ L - c := by
        rw [hmax]
        intro N hN
        have := (hmax₂ (muMax ρ₂ L)).1 le_rfl N hN
        rw [(hsh N hN).1, (hsh N hN).2] at this
        linarith
      linarith
  · apply le_antisymm
    · have key : muMin ρ₂ L - c ≤ muMin ρ L := by
        rw [hmin]
        intro N hN
        have := (hmin₂ (muMin ρ₂ L)).1 le_rfl N hN
        rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2] at this
        linarith
      linarith
    · rw [hmin₂]
      intro N hN
      rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2]
      have := (hmin (muMin ρ L)).1 le_rfl N hN
      linarith

theorem shiftInv_count (c : ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, if i < k then c else 0) = c * ((min k m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m < k
    · rw [if_pos h, min_eq_right h.le, min_eq_right (show m + 1 ≤ k by omega)]
      push_cast
      ring
    · rw [if_neg h]
      replace h := not_lt.mp h
      rw [min_eq_left h, min_eq_left (show k ≤ m + 1 by omega)]
      ring

private theorem sum_fin_ite_lt_const_eq_mul_min (c : ℝ) (k n : ℕ) :
    (∑ j : Fin n, if (j : ℕ) < k then c else 0) = c * ((min k n : ℕ) : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun i => if i < k then c else 0) n).trans (shiftInv_count c k n)

theorem shiftInv_sum {n m : ℕ} (h : m = n) (f : Fin n → ℝ) (g : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hfg : ∀ (j : ℕ) (h1 : j < m) (h2 : j < n), g ⟨j, h1⟩ = f ⟨j, h2⟩ + c) :
    (∑ j : Fin m, if (j : ℕ) < k then g j else 0) =
      (∑ j : Fin n, if (j : ℕ) < k then f j else 0) + c * ((min k n : ℕ) : ℝ) := by
  subst h
  rw [← sum_fin_ite_lt_const_eq_mul_min c k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact hfg j.1 j.2 j.2
  · simp

private theorem lt_card_filter_le_iff_of_antitone {n : ℕ} {s : Fin n → ℝ} (hs : Antitone s) (j : Fin n) (θ : ℝ) :
    (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ s i)).card ↔ θ ≤ s j := by
  constructor
  · intro h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h2 : Finset.univ.filter (fun i => θ ≤ s i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hji
      replace hji := not_lt.mp hji
      have := hs hji
      linarith
    have c2 := Finset.card_le_card h2
    rw [Fin.card_Iio] at c2
    omega
  · intro h
    have h1 : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ s i) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hs hi)
    have c1 := Finset.card_le_card h1
    rw [Fin.card_Iic] at c1
    omega

theorem shiftInvariance_of (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (h4 : HNSlopes.{u, v, w}) : ShiftInvariance.{u, v, w, w₂} := by
  intro R V E E₂ _ _ _ _ _ _ _ _ _ ρ ρ₂ L c hL hL₂ hsh
  have hBL := saturation_basic_properties R V E ρ L hL
  have hBL₂ := saturation_basic_properties R V E₂ ρ₂ L hL₂
  have hfilt : ∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ := by
    intro θ
    unfold hnStep
    congr 1
    ext N
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
    · rintro ⟨hNL, hN0, hθ⟩
      have hm := (shiftInv_mu h1 h1' ρ ρ₂ N c (hBL.1 N hNL) (hBL₂.1 N hNL)
        (fun N' hN' => hsh N' (hN'.trans hNL)) hN0).2
      exact ⟨hNL, hN0, by linarith⟩
  have hfiltle : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => sSup_le fun N hN => hN.1
  have hS := h4 R V E ρ L hL
  have hslope : ∀ (j : ℕ) (hj₂ : j < rk ρ₂ L) (hj : j < rk ρ L),
      slopeList ρ₂ L ⟨j, hj₂⟩ = slopeList ρ L ⟨j, hj⟩ + c := by
    intro j hj₂ hj
    have hset : {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = Set.Iic (slopeList ρ L ⟨j, hj⟩ + c) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      have hf : hnStep ρ₂ L θ = hnStep ρ L (θ - c) := by
        have := hfilt (θ - c)
        rwa [sub_add_cancel] at this
      rw [hf, (hsh _ (hfiltle (θ - c))).1, ← hS.2.1 (θ - c)]
      refine (lt_card_filter_le_iff_of_antitone hS.1 ⟨j, hj⟩ (θ - c)).trans ?_
      constructor <;> intro h <;> linarith
    show sSup {θ : ℝ | j < rk ρ₂ (hnStep ρ₂ L θ)} = slopeList ρ L ⟨j, hj⟩ + c
    rw [hset, csSup_Iic]
  refine ⟨fun N => ?_, fun hL0 => shiftInv_mu h1 h1' ρ ρ₂ L c hL hL₂ hsh hL0,
    hfilt, fun k => ?_⟩
  · rw [shiftInv_isSat_iff ρ₂ hL₂, shiftInv_isSat_iff ρ hL]
    constructor
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1]
    · rintro ⟨hNL, hm⟩
      refine ⟨hNL, fun N' hNN' hN'L hr => hm N' hNN' hN'L ?_⟩
      rwa [(hsh N' hN'L).1, (hsh N hNL).1] at hr
  · exact shiftInv_sum (hsh L le_rfl).1 (slopeList ρ L) (slopeList ρ₂ L) c k hslope

end Formalism.HN
end
end

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
open Module

noncomputable section

namespace Formalism.HN

theorem gramBlock_norm_sum_sq {P F : Type*} [Fintype P] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (y : P → F) (h : ∀ v w, v ≠ w → inner ℝ (y v) (y w) = 0) :
    ‖∑ v, y v‖ ^ 2 = ∑ v, ‖y v‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single v (fun w _ hw => h v w (Ne.symm hw)) (by simp),
    real_inner_self_eq_norm_sq]

theorem gramBlock_gram_comb {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : E →ₗ[ℝ] F) (f : ι → E) (M : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => g (∑ i, M i j • f i)) = M.transpose * Matrix.gram ℝ (fun i => g (f i)) * M := by
  ext j l
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem det_gram_le_one_of_norm_sum_sq_le {κ F : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (w : κ → F)
    (hw : ∀ x : κ → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2) :
    (Matrix.gram ℝ w).det ≤ 1 := by
  have hP := Matrix.posSemidef_gram ℝ w
  rw [hP.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_le_one₀
  · intro i _
    simpa using hP.eigenvalues_nonneg i
  · intro i _
    have hv : ∑ a, (hP.isHermitian.eigenvectorBasis i).ofLp a ^ 2 = 1 := by
      have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : κ => ℝ) (hP.isHermitian.eigenvectorBasis i)
      rw [hP.isHermitian.eigenvectorBasis.orthonormal.1 i] at h1
      simpa [Real.norm_eq_abs, sq_abs] using h1.symm
    have h2 := hP.isHermitian.eigenvalues_eq i
    rw [Matrix.star_dotProduct_gram_mulVec, RCLike.re_to_real, real_inner_self_eq_norm_sq] at h2
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [h2, ← hv]
    exact hw _

theorem gram_block_determinant : GramBlock := by
  intro P E E' ι _ _ _ _ _ _ _ _ _ _ Ev Ev' T c W u hEv hEv' hc hT hW hu hspan
  classical
  let k : P → ℕ := fun v => Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)
  let B : ∀ v, OrthonormalBasis (Fin (k v)) ℝ (W ⊓ Ev v : Submodule ℝ E) :=
    fun v => stdOrthonormalBasis ℝ _
  let f : (Σ v, Fin (k v)) → E := fun a => (B a.1 a.2 : E)
  have hfW : ∀ a, f a ∈ W ⊓ Ev a.1 := fun a => (B a.1 a.2).2
  have hfon : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, i⟩ ⟨w, j⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 := orthonormal_iff_ite.1 (B v).orthonormal i j
      rw [Submodule.coe_inner] at h1
      simp only [f]
      rw [h1]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    · rw [if_neg (fun h => hvw (congrArg Sigma.fst h))]
      exact hEv v w hvw _ (hfW ⟨v, i⟩).2 _ (hfW ⟨w, j⟩).2
  have hspanf : Submodule.span ℝ (Set.range f) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact (hfW a).1
    · conv_lhs => rw [hW]
      refine iSup_le fun v => ?_
      intro x hx
      have key : ((∑ i, inner ℝ (B v i) (⟨x, hx⟩ : (W ⊓ Ev v : Submodule ℝ E)) • B v i :
          (W ⊓ Ev v : Submodule ℝ E)) : E) = x := by
        rw [(B v).sum_repr']
      rw [← key, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, i⟩, rfl⟩)
  have hcard : Fintype.card (Σ v, Fin (k v)) = Fintype.card ι := by
    have h1 := finrank_span_eq_card hfon.linearIndependent
    have h2 := finrank_span_eq_card hu
    rw [hspanf] at h1
    rw [hspan] at h2
    omega
  let e := Fintype.equivOfCardEq hcard
  let f' : ι → E := f ∘ e.symm
  have hf'on : Orthonormal ℝ f' := hfon.comp _ e.symm.injective
  have hspan' : Submodule.span ℝ (Set.range f') = W := by
    rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    exact hspanf
  have hex : ∀ j, ∃ a : ι → ℝ, ∑ i, a i • f' i = u j := by
    intro j
    have : u j ∈ Submodule.span ℝ (Set.range f') := by
      rw [hspan', ← hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 this
  choose a ha using hex
  let M : Matrix ι ι ℝ := fun i j => a j i
  have huM : u = fun j => ∑ i, M i j • f' i := funext fun j => (ha j).symm
  have hG1 : Matrix.gram ℝ f' = 1 := by
    ext i j
    rw [Matrix.gram_apply, orthonormal_iff_ite.1 hf'on, Matrix.one_apply]
  have hGu : (Matrix.gram ℝ u).det = M.det ^ 2 := by
    have h1 := gramBlock_gram_comb (LinearMap.id : E →ₗ[ℝ] E) f' M
    simp only [LinearMap.id_apply] at h1
    simp only [huM]
    rw [h1, hG1, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hGT : (Matrix.gram ℝ (fun i => T (u i))).det =
      M.det ^ 2 * (Matrix.gram ℝ (fun i => T (f' i))).det := by
    simp only [huM]
    rw [gramBlock_gram_comb T f' M, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hreidx : (Matrix.gram ℝ (fun i => T (f' i))).det =
      (Matrix.gram ℝ (fun a => T (f a))).det := by
    have h1 : Matrix.gram ℝ (fun i => T (f' i)) =
        (Matrix.gram ℝ (fun a => T (f a))).submatrix e.symm e.symm := by
      ext i j
      rfl
    rw [h1, Matrix.det_submatrix_equiv_self]
  have hTf : ∀ a, T (f a) ∈ Ev' a.1 ∧ ‖T (f a)‖ ≤ c a.1 := by
    intro a
    have h1 := hT a.1 (f a) (hfW a).2
    rw [hfon.1 a, mul_one] at h1
    exact h1
  have hprod : ∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)) =
      ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Finset.prod_const, ← pow_mul, k]
  have hA : (Matrix.gram ℝ (fun a => T (f a))).det ≤ ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    by_cases h0 : ∃ a : (Σ v, Fin (k v)), c a.1 = 0
    · obtain ⟨a, ha0⟩ := h0
      have hz : T (f a) = 0 := by
        have h1 := (hTf a).2
        rw [ha0] at h1
        exact norm_le_zero_iff.1 h1
      rw [Matrix.det_eq_zero_of_row_eq_zero a (fun j => by rw [Matrix.gram_apply, hz, inner_zero_left])]
      exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    · push_neg at h0
      have hpos : ∀ a : (Σ v, Fin (k v)), 0 < c a.1 := fun a => lt_of_le_of_ne (hc a.1) (h0 a).symm
      let w : (Σ v, Fin (k v)) → E' := fun a => (c a.1)⁻¹ • T (f a)
      have hgram : Matrix.gram ℝ (fun a => T (f a)) =
          Matrix.diagonal (fun a => c a.1) * Matrix.gram ℝ w * Matrix.diagonal (fun a => c a.1) := by
        ext a b
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply, w,
          real_inner_smul_left, real_inner_smul_right]
        field_simp [(hpos a).ne', (hpos b).ne']
      have hnorm : ∀ x : (Σ v, Fin (k v)) → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2 := by
        intro x
        let z : P → E := fun v => ∑ i, x ⟨v, i⟩ • f ⟨v, i⟩
        let y : P → E' := fun v => (c v)⁻¹ • T (z v)
        have hsum : ∑ a, x a • w a = ∑ v, y v := by
          rw [Fintype.sum_sigma]
          refine Finset.sum_congr rfl fun v _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [y, z, w, map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
        have hzE : ∀ v, z v ∈ Ev v := fun v =>
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfW ⟨v, i⟩).2
        have hyE : ∀ v, y v ∈ Ev' v := fun v => Submodule.smul_mem _ _ (hT v _ (hzE v)).1
        have hyz : ∀ v, ‖y v‖ ≤ ‖z v‖ := by
          intro v
          rcases (hc v).eq_or_lt with h | h
          · simp [y, ← h]
          · have hv := (hT v _ (hzE v)).2
            simp only [y]
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
            calc (c v)⁻¹ * ‖T (z v)‖ ≤ (c v)⁻¹ * (c v * ‖z v‖) := by gcongr
              _ = ‖z v‖ := by field_simp
        have hzsum : ∑ v, z v = ∑ a, x a • f a := by
          rw [Fintype.sum_sigma]
        rw [hsum, gramBlock_norm_sum_sq y (fun v w hvw => hEv' v w hvw _ (hyE v) _ (hyE w))]
        calc ∑ v, ‖y v‖ ^ 2 ≤ ∑ v, ‖z v‖ ^ 2 :=
              Finset.sum_le_sum fun v _ => pow_le_pow_left₀ (norm_nonneg _) (hyz v) 2
          _ = ‖∑ v, z v‖ ^ 2 :=
              (gramBlock_norm_sum_sq z (fun v w hvw => hEv v w hvw _ (hzE v) _ (hzE w))).symm
          _ = ∑ a, x a ^ 2 := by
              rw [hzsum, ← real_inner_self_eq_norm_sq, hfon.inner_sum x x Finset.univ]
              simp [sq]
      have hle : (Matrix.gram ℝ w).det ≤ 1 := det_gram_le_one_of_norm_sum_sq_le w hnorm
      have hP0 : 0 ≤ ∏ a : (Σ v, Fin (k v)), c a.1 := Finset.prod_nonneg fun a _ => (hpos a).le
      rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      calc (∏ a : (Σ v, Fin (k v)), c a.1) * (Matrix.gram ℝ w).det * ∏ a : (Σ v, Fin (k v)), c a.1
          ≤ (∏ a : (Σ v, Fin (k v)), c a.1) * 1 * ∏ a : (Σ v, Fin (k v)), c a.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hP0) hP0
        _ = ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
            rw [mul_one, ← Finset.prod_mul_distrib]
            simp [sq]
  refine ⟨?_, fun hiso => ?_⟩
  · rw [hGT, hGu, hreidx, hprod, mul_comm]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  · have hdiag : Matrix.gram ℝ (fun a => T (f a)) = Matrix.diagonal (fun a => c a.1 ^ 2) := by
      ext a b
      rw [Matrix.gram_apply, Matrix.diagonal_apply]
      by_cases hab : a.1 = b.1
      · obtain ⟨v, i⟩ := a
        obtain ⟨w, j⟩ := b
        simp only at hab
        subst hab
        rw [hiso v _ (hfW ⟨v, i⟩).2 _ (hfW ⟨v, j⟩).2, orthonormal_iff_ite.1 hfon]
        split_ifs <;> simp
      · rw [if_neg (fun h => hab (congrArg Sigma.fst h))]
        exact hEv' _ _ hab _ (hTf a).1 _ (hTf b).1
    rw [hGT, hGu, hreidx, hdiag, Matrix.det_diagonal, hprod]
    ring

end Formalism.HN
end
end

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
noncomputable section

namespace Formalism.HN

namespace PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace

lemma final_real1 (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by
  have hsw : √w ^ 2 = w := Real.sq_sqrt hw0
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX0
  have hse0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hse : √e ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRt : R ≤ 2 * t := by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 / D := le_trans hX0 hX
    have h2 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg h1 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    by_contra hneg
    push_neg at hneg
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]
  push_neg at hε4
  set q := √(ε * e) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ √e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * √X with hy
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [hy, mul_pow, div_pow, hsX]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]
  have hyt : y * t = D * √X := by rw [hy]; field_simp
  have hDt : D * (t / D) = t := by field_simp
  have hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t / D * w - √w * √X ≤ R * (ε + q) := by linarith
    have h2 : t * w - D * (√w * √X) ≤ D * (R * (ε + q)) := by
      have := mul_le_mul_of_nonneg_left h1 hD.le
      have e1 : D * (t / D * w - √w * √X) = t * w - D * (√w * √X) := by
        linear_combination w * hDt
      linarith
    have h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      nlinarith
    have e2 : t * (√w * y) = D * (√w * √X) := by linear_combination √w * hyt
    nlinarith
  have hmain : w - √w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : √w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (√w - y)]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]

end PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace

private lemma hs2_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg (fun m _ => sq_nonneg _)

theorem frame_linear_algebra_first : FrameLA1 := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW
  have hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : finrank ℂ H = 0
  · have h0 : finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (finrank ℂ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hnk i))
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    have : ε * ∑ i, (finrank ℂ (V i) : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
    linarith

  have hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    have := (abs_le.mp h).1
    linarith
  have hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
    calc _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => Nat.cast_nonneg _) (fun i => hs2_nonneg _)
      _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
      _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
          rw [Real.sqrt_mul he0]
          have := Real.mul_self_sqrt hR.le
          linear_combination √e * this
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfull i)
    rw [Finset.sum_sub_distrib] at h2
    nlinarith [hCS1]

  set b := stdOrthonormalBasis ℂ W with hb
  set g : Fin (finrank ℂ W) → H := fun l => (b l : H) with hgdef
  have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re with htWdef
  have htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [htWdef]
    simp only [re_inner_Q, Finset.mul_sum]
    exact Finset.sum_comm
  have hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤
      ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) +
        √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
      intro l n hn
      have hmem : B i n ∈ ⨆ j, (Nτ j).map (B j) :=
        Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)
      exact (Submodule.mem_orthogonal _ _).mp (b l).2 _ hmem
    have h1 := W_upper (B i) (Nτ i) hg hperp
    have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) hf
    simp only [Fintype.card_fin] at h2
    have hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))
    rw [hk] at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hWi i)
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))
        ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc _ ≤ √(∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) *
              √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
            Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => sub_nonneg.mpr (hnk i))
              (fun i => hs2_nonneg _)
        _ ≤ √(ε * ∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ))
                = ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith

  set s : ℝ := (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) with hs
  set A : H →ₗ[ℂ] H := frQ c B - (s : ℂ) • LinearMap.id with hA
  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ)
      - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW := by
    have h := sum_re_inner_bound A hg
    simp only [Fintype.card_fin] at h
    have h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1 := fun l => by
      rw [inner_self_eq_norm_sq_to_K, hg.1 l]; simp
    have hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re
        = tW - s * (finrank ℂ W : ℝ) := by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, htWdef]
      ring
    rw [hsum] at h
    have := (abs_le.mp h).1
    linarith
  have hX : hs2 A
      ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    set u := stdOrthonormalBasis ℂ H with hu
    have hterm : ∀ n, ‖A (u n)‖ ^ 2
        = ‖frQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, frQ c B (u n)⟫_ℂ).re + s ^ 2 := by
      intro n
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hsym : (⟪frQ c B (u n), u n⟫_ℂ).re = (⟪u n, frQ c B (u n)⟫_ℂ).re :=
        inner_re_symm (𝕜 := ℂ) _ _
      rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_one, sq_abs, hsym]
      ring
    have htr : (LinearMap.trace ℂ H (frQ c B)).re = ∑ n, (⟪u n, frQ c B (u n)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (frQ c B) u, Complex.re_sum]
    have hT2 : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (u n)‖ ^ 2 := trace_frame_sq_eq_sum c B
    rw [hilbert_schmidt_eq_basis_sum _ u]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htr, ← hT2]
    have hsD : s * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hst : (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hQ' : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := hQ
    rw [show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
          + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring] at hQ'
    have hDs2 : (finrank ℂ H : ℝ) * s ^ 2 = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [← hsD]; ring
    linarith
  exact final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (hs2_nonneg _) hX hlow hup

end Formalism.HN
end
end
