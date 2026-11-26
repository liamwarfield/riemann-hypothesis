module

public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
public import Lemmata.GeneralBFactLeftForm.Imports

@[expose] public section

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
open Module NumberField

noncomputable section

namespace Formalism.HN

namespace PlaceOperatorNorms

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem realize_apply0 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 0) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).re := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem realize_apply1 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 1) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).im := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem norm_sq_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, realize_apply0, realize_apply1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cnorm_eq (u : κ → ℂ) : Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ := by
  simp [Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]

theorem fcoord_map (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (φ : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b' X' v (φ x) =
      ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b' v (φ x) =
      ((LinearMap.toMatrix b b' φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b' φ x]
    first
      | simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]
      | simp [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v),
    Matrix.mul_one]

theorem normAt_map_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (φ : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ opNormAt b X b' X' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.normAt, fcoord_map b X b' X' hX v φ x, cnorm_eq, cnorm_eq, opNormAt]
  have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))).le_opNorm
      (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))
  convert this using 1
  all_goals first
    | rfl
    | simp [Matrix.toEuclideanLin_apply]
    | (congr 1; simp [Matrix.toEuclideanLin_apply])

theorem opNormAt_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX' : ∀ v, IsUnit (X' v).det) (c : InfinitePlace K → ℝ)
    (hc : ∀ v, 0 < c v) (v : InfinitePlace K) (φ : V →ₗ[K] W) :
    opNormAt b X b' (fun w => ((c w : ℂ)) • X' w) v φ = (c v)⁻¹ * opNormAt b X b' X' v φ := by
  have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
  have hi : ((c v : ℂ) • X' v)⁻¹ = ((c v : ℂ))⁻¹ • (X' v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (hX' v)]
  simp only [opNormAt, hi, Matrix.smul_mul, map_smul, norm_smul]
  first
    | rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hc v).le]
    | simp [norm_inv, abs_of_pos (hc v)]

theorem opNormAt_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (hX' : ∀ v, IsUnit (X' v).det) (v : InfinitePlace K) (φ : V →ₗ[K] W) (hφ : φ ≠ 0) :
    0 < opNormAt b X b' X' v φ := by
  rw [opNormAt, norm_pos_iff]
  intro h0
  apply hφ
  have hA := (Matrix.toEuclideanLin.map_eq_zero_iff).mp
    ((LinearMap.toContinuousLinearMap.map_eq_zero_iff).mp h0)
  have hΦ : (LinearMap.toMatrix b b' φ).map v.embedding = 0 := by
    have e : (LinearMap.toMatrix b b' φ).map v.embedding =
        X' v * ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) * (X v)⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul]
    rw [e, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hM : LinearMap.toMatrix b b' φ = 0 := by
    ext i j
    have := congrFun (congrFun hΦ i) j
    simpa using this
  exact (LinearMap.toMatrix b b').map_eq_zero_iff.mp hM

end PlaceOperatorNorms

open PlaceOperatorNorms in
theorem slopeIneqMean_of (h1 : Twist) (h2 : PlLat) (h3 : SlopeIneq.{0, 0, 0, 0, 0}) :
    SlopeIneqMean := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA hφA
  have hφ : φ ≠ 0 := by
    rintro rfl
    apply hφA
    rw [LinearMap.restrictScalars_zero, Submodule.map_zero]
  have hpos : ∀ v, 0 < opNormAt b X b' X' v φ := fun v => opNormAt_pos b X b' X' hX hX' v φ hφ
  have hf : (nPl K : ℝ) ≠ 0 := by
    unfold nPl
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = htMap b X b' X' φ / 2 := ⟨_, rfl⟩
  have hs' : s = (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ) := by
    rw [hs, htMap, Finset.sum_congr rfl (fun v _ => Real.log_pow (opNormAt b X b' X' v φ) 2),
      ← Finset.mul_sum]
    push_cast
    ring
  obtain ⟨c, hc_def⟩ : ∃ c : InfinitePlace K → ℝ,
      c = fun v => opNormAt b X b' X' v φ * Real.exp (-s) := ⟨_, rfl⟩
  have hc : ∀ v, 0 < c v := fun v => by
    rw [hc_def]
    exact mul_pos (hpos v) (Real.exp_pos _)
  have ht0 : (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) = 0 := by
    have hl : ∀ v, Real.log (c v) = Real.log (opNormAt b X b' X' v φ) - s := fun v => by
      rw [hc_def]
      dsimp only
      rw [Real.log_mul (hpos v).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_sub, ← hs']
    have hfs : (1 / (nPl K : ℝ)) * ((Fintype.card (InfinitePlace K) : ℝ) * s) = s := by
      unfold nPl at hf ⊢
      field_simp
    rw [hfs, sub_self]
  obtain ⟨X'', hX''⟩ : ∃ X'' : InfinitePlace K → Matrix κ κ ℂ,
      X'' = fun v => ((c v : ℂ)) • X' v := ⟨_, rfl⟩
  have hdet'' : ∀ v, IsUnit (X'' v).det := fun v => by
    rw [hX'']
    dsimp only
    rw [Matrix.det_smul]
    exact ((Complex.ofReal_ne_zero.mpr (hc v).ne').isUnit.pow _).mul (hX' v)
  have htw : ∀ N : Submodule (𝓞 K) W, N.FG → N ≠ ⊥ →
      muMax (Formalism.HermitianLatticesTheory.realize b' X'') N = muMax (Formalism.HermitianLatticesTheory.realize b' X') N ∧
      muMin (Formalism.HermitianLatticesTheory.realize b' X'') N = muMin (Formalism.HermitianLatticesTheory.realize b' X') N := by
    intro N hN hN0
    have := (h1 K W κ b' X' c hX' hc N hN).2.1 hN0
    rw [ht0, add_zero, add_zero] at this
    rw [hX'']
    exact this
  have hC : 0 < Real.exp s := Real.exp_pos s
  have hbound : ∀ x : V,
      ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ≤ Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have hpl : ∀ v, Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x) ≤ Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by
      intro v
      have hop : opNormAt b X b' X'' v φ = Real.exp s := by
        rw [hX'', opNormAt_smul b X b' X' hX' c hc v φ, hc_def]
        dsimp only
        rw [mul_inv, Real.exp_neg, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hpos v).ne',
          one_mul]
      calc Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x)
          ≤ opNormAt b X b' X'' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := normAt_map_le b X b' X'' hX v φ x
        _ = Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by rw [hop]
    have hsq : ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ^ 2 ≤
        (Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2 := by
      rw [mul_pow, norm_sq_realize, norm_sq_realize, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpl v) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hAlat := (h2 K V ι b X hX A hA).1
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    apply hφA
    exact Submodule.map_bot _
  have key : ∀ M : Submodule (𝓞 K) W, M.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ M →
      (muMin (Formalism.HermitianLatticesTheory.realize b X) A - s ≤
          muMin (Formalism.HermitianLatticesTheory.realize b' X'') (A.map (φ.restrictScalars (𝓞 K))) ∧
        muMin (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) ∧
      (Set.InjOn φ (A : Set V) →
        muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) := by
    intro M hM hAM
    have hMlat := (h2 K W κ b' X'' hdet'' M hM).1
    have hmem : ∀ x : A, (φ.restrictScalars (𝓞 K)).domRestrict A x ∈ M := fun x =>
      hAM (Submodule.mem_map_of_mem x.2)
    let ψ : A →ₗ[𝓞 K] M := LinearMap.codRestrict M ((φ.restrictScalars (𝓞 K)).domRestrict A) hmem
    have hψ : ∀ x : A, ((ψ x : M) : W) = φ x := fun x => rfl
    have hS := h3 (𝓞 K) V W _ _ (Formalism.HermitianLatticesTheory.realize b X) (Formalism.HermitianLatticesTheory.realize b' X'') A M hAlat hMlat
      ψ (Real.exp s) hC (fun x => by rw [hψ]; exact hbound x)
    rw [Real.log_exp] at hS
    have hrange : (LinearMap.range ψ).map M.subtype = A.map (φ.restrictScalars (𝓞 K)) := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hψ0 : ψ ≠ 0 := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hφA
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      intro h
      apply hy0
      have := congrArg (fun g : A →ₗ[𝓞 K] M => ((g ⟨x, hx⟩ : M) : W)) h
      simpa [hψ] using this
    refine ⟨?_, fun hinj => hS.2 ?_ hA0⟩
    · have := (hS.1 hψ0).1
      rw [hrange] at this
      exact ⟨this, (hS.1 hψ0).2⟩
    · intro x y hxy
      apply Subtype.ext
      apply hinj x.2 y.2
      have := congrArg (fun z : M => (z : W)) hxy
      simpa [hψ] using this
  have hφA_fg : (A.map (φ.restrictScalars (𝓞 K))).FG := hA.map _
  obtain ⟨⟨k1, -⟩, -⟩ := key _ hφA_fg le_rfl
  have htφA := htw _ hφA_fg hφA
  rw [htφA.2] at k1
  refine ⟨?_, fun B hB hAB => ?_⟩
  · unfold muMinDef
    linarith
  · have hB0 : B ≠ ⊥ := fun h => hφA (le_bot_iff.mp (h ▸ hAB))
    obtain ⟨⟨-, k2⟩, k3⟩ := key B hB hAB
    have htB := htw B hB hB0
    rw [htB.1] at k2 k3
    refine ⟨?_, fun hinj => ?_⟩
    · unfold muMinDef muMaxDef
      linarith
    · have := k3 hinj
      unfold muMaxDef
      linarith

theorem slope_inequality_mean : SlopeIneqMean := by
  exact slopeIneqMean_of (twist_of rescale_covolume_formula place_lattice_structure
    (shiftInvariance_of slope_characterization slope_characterization polygon_slopes_characterization)) place_lattice_structure slope_inequality_general

end Formalism.HN
end
end

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
open Module Submodule

noncomputable section

namespace Formalism.HN

universe u v w

theorem hnExtreme_mem_iff {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  first | exact Bl.general_b_fact_left_form.goal1 .. | (apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_form.goal1 <;> first | assumption | infer_instance)

theorem hnExtreme_of (h1 : HNSlopes.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : HNStep.{u, v, w})
    (h4 : SatBasic.{u, v, w}) : HNExtreme.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL hL0
  obtain ⟨hanti, hcard, -⟩ := h1 R V E ρ L hL
  obtain ⟨B1, B2, B3, B4, B5, -, -, -⟩ := h4 R V E ρ L hL
  obtain ⟨M1, -, M3, -⟩ := h2 R V E ρ L hL hL0
  have key : ∀ (θ : ℝ) (j : Fin (rk ρ L)),
      θ ≤ slopeList ρ L j ↔ (j : ℕ) < rk ρ (hnStep ρ L θ) := by
    intro θ j
    rw [← hcard θ]
    exact hnExtreme_mem_iff _ hanti θ j
  have hSL : ∀ θ : ℝ, hnStep ρ L θ ≤ L := fun θ => (h3 R V E ρ L hL θ).1.1
  have hbot : rk ρ (⊥ : Submodule R V) = 0 := (B4 ⊥ bot_le).2 rfl
  have hrkpos : 0 < rk ρ L := by
    rcases Nat.eq_zero_or_pos (rk ρ L) with h | h
    · exact absurd ((B4 L le_rfl).1 h) hL0
    · exact h

  have hstepMin : hnStep ρ L (muMin ρ L) = L := by
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMin ρ L)
    exact le_antisymm (hSL _) (S3 L le_rfl hL0 le_rfl)
  have lowB : ∀ j, muMin ρ L ≤ slopeList ρ L j := by
    intro j
    rw [key, hstepMin]
    exact j.2

  have stepMax : ∀ θ : ℝ, hnStep ρ L θ ≠ ⊥ → θ ≤ muMax ρ L := by
    intro θ hne
    obtain ⟨-, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hHL : IsLat ρ (hnStep ρ L θ) := B1 _ (hSL θ)
    obtain ⟨-, N2, -⟩ := h2 R V E ρ _ hHL hne
    have hθ := (N2 θ).1 (S2 hne) ⊥ bot_le
    simp only [hbot, B5, Nat.cast_zero, sub_zero] at hθ
    have hdeg := ((M1 (muMax ρ L)).1 le_rfl) _ (hSL θ)
    have hpos : (0 : ℝ) < rk ρ (hnStep ρ L θ) := by
      have : rk ρ (hnStep ρ L θ) ≠ 0 := fun h => hne ((B4 _ (hSL θ)).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    exact le_of_mul_le_mul_right (le_trans hθ hdeg) hpos
  have upB : ∀ j, slopeList ρ L j ≤ muMax ρ L := by
    intro j
    apply stepMax
    intro h
    have := (key _ j).1 le_rfl
    rw [h, hbot] at this
    exact Nat.not_lt_zero _ this

  have hstepMaxNe : hnStep ρ L (muMax ρ L) ≠ ⊥ := by
    obtain ⟨N, hNs, hN0, hNsl⟩ := M3
    have hNL : N ≤ L := hNs.1
    have hNlat : IsLat ρ N := B1 N hNL
    obtain ⟨-, N2, -⟩ := h2 R V E ρ N hNlat hN0
    have hmin : muMax ρ L ≤ muMin ρ N := by
      rw [N2]
      intro Q hQ
      have hQd := ((M1 (muMax ρ L)).1 le_rfl) Q (le_trans hQ hNL)
      have hrkN : (rk ρ N : ℝ) ≠ 0 := by
        have : rk ρ N ≠ 0 := fun h => hN0 ((B4 N hNL).1 h)
        exact_mod_cast this
      have hsl : slope ρ N = deg ρ N / rk ρ N := rfl
      have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
        rw [← hNsl, hsl, div_mul_cancel₀ _ hrkN]
      rw [mul_sub]
      linarith
    obtain ⟨-, -, S3, -⟩ := h3 R V E ρ L hL (muMax ρ L)
    have hle := S3 N hNL hN0 hmin
    intro h
    rw [h] at hle
    exact hN0 (le_bot_iff.1 hle)
  refine ⟨fun j => ⟨lowB j, upB j⟩, ⟨⟨0, hrkpos⟩, le_antisymm (upB _) ?_⟩,
    ⟨⟨rk ρ L - 1, by omega⟩, le_antisymm ?_ (lowB _)⟩⟩
  · rw [key]
    show 0 < rk ρ (hnStep ρ L (muMax ρ L))
    rcases Nat.eq_zero_or_pos (rk ρ (hnStep ρ L (muMax ρ L))) with h | h
    · exact absurd ((B4 _ (hSL _)).1 h) hstepMaxNe
    · exact h
  · by_contra hlt
    rw [not_le] at hlt
    set θ := slopeList ρ L ⟨rk ρ L - 1, by omega⟩ with hθdef
    have hj := (key θ ⟨rk ρ L - 1, by omega⟩).1 le_rfl
    simp only at hj
    obtain ⟨S1, S2, -, -⟩ := h3 R V E ρ L hL θ
    have hle := (B2 _ L (hSL θ) le_rfl).1
    have hrk : rk ρ L = rk ρ (hnStep ρ L θ) := by omega
    have heq : L = hnStep ρ L θ := B3 _ L S1 (hSL θ) le_rfl hrk
    have hne : hnStep ρ L θ ≠ ⊥ := by rw [← heq]; exact hL0
    have := S2 hne
    rw [← heq] at this
    linarith

theorem polygon_extreme_slopes : HNExtreme :=
  hnExtreme_of polygon_slopes_characterization slope_characterization (hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties) saturation_basic_properties

end Formalism.HN
end
end
