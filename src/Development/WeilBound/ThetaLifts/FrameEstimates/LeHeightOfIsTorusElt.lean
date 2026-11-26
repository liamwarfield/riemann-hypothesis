module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem realAd_snd (t : ℝ) : (realAd F t).2 = 0 := rfl

theorem realAd_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((realAd F t).1 w) = t := by
  have hw := IsTotallyReal.isReal w
  have e := congrArg (fun z => z.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t))
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact congrArg _ e

theorem rId_snd (t : ℝ) : (rId F t).2 = 1 := add_zero _

theorem rId_inf [IsTotallyReal F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = Real.exp t := by
  change InfinitePlace.Completion.extensionEmbedding w (1 + (realAd F (Real.exp t - 1)).1 w) = _
  rw [map_add (f := _), map_one, realAd_inf]
  push_cast
  ring

theorem rId_add [IsTotallyReal F] (s t : ℝ) : rId F (s + t) = rId F s * rId F t := by
  refine Prod.ext (funext fun w => (InfinitePlace.Completion.extensionEmbedding w).injective ?_) ?_
  · change _ = InfinitePlace.Completion.extensionEmbedding w ((rId F s).1 w * (rId F t).1 w)
    rw [map_mul, rId_inf, rId_inf, rId_inf, Real.exp_add, Complex.ofReal_mul]
  · change _ = (rId F s).2 * (rId F t).2
    rw [rId_snd, rId_snd, rId_snd, mul_one]

theorem rId_zero' : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

theorem continuous_rId [IsTotallyReal F] : Continuous (rId F) := by
  refine Continuous.prodMk (f := fun t => (rId F t).1) (g := fun t => (rId F t).2) (continuous_pi fun w => ?_) ?_
  · refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.continuous_iff.2 ?_
    have : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (rId F t).1 w) = fun t => (Real.exp t : ℂ) :=
      funext fun t => rId_inf w t
    rw [this]
    fun_prop
  · simp only [rId_snd]
    exact continuous_const

variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

omit [NumberField F] [NumberField E] in
theorem yx_eq_one (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  have cc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => hs _
  have cJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

omit [NumberField F] [NumberField E] in
theorem two_mul_le_of_wittFrame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : 2 * r ≤ n := by
  have e : Matrix.fromRows (cT (σ : E →+* E) Y * J) (cT (σ : E →+* E) X * J) * Matrix.fromCols X Y = 1 := by
    rw [Matrix.fromRows_mul_fromCols, yx_eq_one hs hJ hW, hW.xx, hW.yy, hW.xy, Matrix.fromBlocks_one]
  have e2 := congrArg Matrix.rank e
  rw [Matrix.rank_one, Fintype.card_sum, Fintype.card_fin] at e2
  have := (Matrix.rank_mul_le_right _ _).trans' e2.symm.le |>.trans (Matrix.rank_le_card_height _)
  rw [Fintype.card_fin] at this
  omega


omit [NumberField F] [NumberField E] in
theorem ext_of_frame (hs : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {A : Type} [CommRing A]
    (φ : E →+* A) {m m' : Matrix (Fin n) (Fin n) A} (h1 : m * X.map φ = m' * X.map φ) (h2 : m * Y.map φ = m' * Y.map φ)
    (h3 : ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      m *ᵥ (fun i => φ (z i)) = m' *ᵥ fun i => φ (z i)) : m = m' := by
  set P : Matrix (Fin n) (Fin n) E := 1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J) with hP
  have p1 : cT (σ : E →+* E) X * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
    simp
  have p2 : cT (σ : E →+* E) Y * J * P = 0 := by
    simp only [hP, Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx_eq_one hs hJ hW]
    simp
  have h4 : m * P.map φ = m' * P.map φ := Matrix.ext fun i j =>
    congrFun (h3 (fun k => P k j) (funext fun k => congrFun (congrFun p1 k) j)
      (funext fun k => congrFun (congrFun p2 k) j)) i
  have e : (1 : Matrix (Fin n) (Fin n) A) =
      P.map φ + X.map φ * (cT (σ : E →+* E) Y * J).map φ + Y.map φ * (cT (σ : E →+* E) X * J).map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add φ), ← Matrix.map_add _ (map_add φ), hP,
      ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    congr 1
    abel
  rw [← Matrix.mul_one m, ← Matrix.mul_one m', e]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, h1, h2, h4]

theorem isTorusElt_unique (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ}
    {a a' : GAd σ J} (ha : IsTorusElt σ J X Y t a) (ha' : IsTorusElt σ J X Y t a') : a = a' := by
  refine GAd_ext σ J (fun w => ?_) fun v => by
    rw [mem_infPts_iff_forall.1 ha.1 v, mem_infPts_iff_forall.1 ha'.1 v]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  refine Subtype.ext (Units.ext ?_)
  rw [← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h]
  exact ext_of_frame (sigma_sigma h) hJ hW τ.1 ((ha.2 w τ).1.trans (ha'.2 w τ).1.symm)
    ((ha.2 w τ).2.1.trans (ha'.2 w τ).2.1.symm) fun z h1 h2 =>
      ((ha.2 w τ).2.2 z h1 h2).trans ((ha'.2 w τ).2.2 z h1 h2).symm

theorem le_height_of_isTorusElt (hW : IsWittFrame σ J X Y) {t : Fin r → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) (i : Fin r) : t i ≤ height σ J a := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set M := archMat σ J τ (projArch σ J w a) with hM
  have h1 : opNorm M ≤ height σ J a :=
    ((normInf_le_iff F w).1 (le_htOf (normInf F w) (matHom _ σ J (projArch σ J w a))) τ).trans (htInf_le_height σ J w a)
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun k => τ.1 (X k i)
  have hv : v ≠ 0 := fun e => by
    have hx : ∀ k, X k i = 0 := fun k => τ.1.injective ((congrArg (fun z : EuclideanSpace ℂ (Fin n) => z k) e).trans
      (map_zero _).symm)
    have := congrFun (congrFun hW.xy i) i
    simp [Matrix.mul_apply, cT, hx] at this
  have h2 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M v = (t i : ℂ) • v := by
    ext k
    have := congrFun (congrFun (ha.2 w τ).1 k) i
    rw [mul_diagonal, mul_comm] at this
    exact this
  have h3 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M).le_opNorm v
  rw [h2, norm_smul, Complex.norm_real] at h3
  have h4 := le_of_mul_le_mul_right h3 (norm_pos_iff.2 hv)
  exact (le_abs_self _).trans (h4.trans (show ((opNorm M : ℝ≥0) : ℝ) ≤ _ from h1))

theorem exists_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a : (Fin r → ℝ) → GAd σ J, (∀ s t, a (s + t) = a s * a t) ∧ Continuous a ∧
      (∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)) ∧ ∀ t,
      (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))) ∧
      (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))) ∧
      ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z := by
  have := h.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let ι := algebraMap (AF F) (AE F E)
  let d : ℝ → (AE F E)ˣ := fun x => ⟨ι (rId F x), ι (rId F (-x)),
    by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one],
    by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]⟩
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, JR, Matrix.map_mul]
  have key := fun t : Fin r → ℝ => exists_unit_torus (s := sigR (AF F) σ) (J := JR (F := F) (AF F) J) (X := adMat F X)
    (Y := adMat F Y)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x))
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    ((c2 X X).trans (hW.xx ▸ Matrix.map_zero _ (map_zero _))) ((c2 Y Y).trans (hW.yy ▸ Matrix.map_zero _ (map_zero _)))
    ((c2 X Y).trans (hW.xy ▸ Matrix.map_one _ (map_zero _) (map_one _))) (fun i => d (t i))
    (fun i => congrArg (rId F (t i) ⊗ₜ[F] ·) (map_one σ))
  choose m hm hX hY he using key
  have hZ : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (m t).1 *ᵥ incV F z = incV F z := fun t z hz hz' => by
    have h4 : ∀ Z : Matrix (Fin n) (Fin r) E, (cT (σ : E →+* E) Z * J) *ᵥ z = 0 →
        (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *ᵥ incV F z = 0 :=
      fun Z hZ => funext fun i => by
        have e : (cT (sigR (AF F) σ) (adMat F Z) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) =
          (cT (σ : E →+* E) Z * J).map (inclR (F := F) (AF F)) := by
          rw [c1, Matrix.map_mul]; rfl
        rw [e]
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ z i).symm.trans (by rw [hZ]; exact map_zero _)
    rw [he, add_mulVec, add_mulVec, ← mulVec_mulVec, h4 Y hz', mulVec_zero, ← mulVec_mulVec, h4 X hz]
    simp
  have hadd : ∀ s t, m (s + t) = m s * m t := fun s t => by
    refine Units.ext (ext_of_frame (sigma_sigma h) hJ hW (inclR (F := F) (AF F)) ?_ ?_ fun z h1 h2 => ?_)
    · rw [Units.val_mul, Matrix.mul_assoc, hX, hX, ← Matrix.mul_assoc, hX, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι (rId_add _ _)).trans (map_mul ι _ _))
    · rw [Units.val_mul, Matrix.mul_assoc, hY, hY, ← Matrix.mul_assoc, hY, Matrix.mul_assoc, diagonal_mul_diagonal]
      exact congrArg (_ * diagonal ·) (funext fun i => (congrArg ι ((congrArg (rId F) (neg_add _ _)).trans
        (rId_add _ _))).trans (map_mul ι _ _))
    · exact (hZ _ z h1 h2).trans (by
        rw [Units.val_mul, ← mulVec_mulVec]
        exact ((congrArg _ (hZ t z h1 h2)).trans (hZ s z h1 h2)).symm)
  have h0 : m 0 = 1 := by simpa using hadd 0 0
  have hinv : ∀ t, (m t)⁻¹ = m (-t) := fun t => inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hι : Continuous ι := continuous_algebraMap _ _
  have hc : Continuous fun t => (m t).1 := by
    simp only [he]
    refine Continuous.add (Continuous.add continuous_const (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const))
      (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
      (Continuous.matrix_diagonal (continuous_pi fun i => ?_))) continuous_const)
    · exact (hι.comp (continuous_rId.comp (continuous_apply i))).sub continuous_const
    · exact (hι.comp (continuous_rId.comp (continuous_apply i).neg)).sub continuous_const
  have hc' : Continuous m := Units.continuous_iff.2 ⟨hc, by simp only [hinv]; exact hc.comp continuous_neg⟩
  refine ⟨fun t => ⟨m t, hm t⟩, fun s t => Subtype.ext (hadd s t), hc'.subtype_mk _, fun t => ⟨?_, fun w τ => ?_⟩,
    fun t => ⟨hX t, hY t, hZ t⟩⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    let ψ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    have h1 : ∀ x, ψ (d x).1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) x)
    have h2 : ∀ x, ψ (d x)⁻¹.1 = 1 := fun x => congrArg (· ⊗ₜ[F] (1 : E)) (rId_snd (F := F) (-x))
    change ψ ((m t).1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.add_apply, Matrix.mul_apply (N := cT _ _ * _), mul_diagonal, map_add (f := _), map_sum, map_mul, map_sub, h1,
      h2, map_one, sub_self, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, apply_ite ψ, map_zero]
  · let φ := (infEmb τ).comp (compInf F E w)
    have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have h1 : ∀ x : ℝ, φ (ι (rId F x)) = Real.exp x := fun x => by
      change infEmb τ ((rId F x).1 w ⊗ₜ[F] 1) = _
      rw [infEmb_tmul, map_one, mul_one, rId_inf]
    have h2 : ∀ Z : Matrix (Fin n) (Fin r) E, (adMat F Z).map φ = Z.map τ.1 := fun Z => Matrix.ext fun i j => h0 _
    have h3 : archMat σ J τ (projArch σ J w ⟨m t, hm t⟩) = (m t).1.map φ := rfl
    rw [h3]
    refine ⟨?_, ?_, fun z hz hz' => ?_⟩
    · rw [← h2, ← Matrix.map_mul, hX, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => h1 _)
    · rw [← h2, ← Matrix.map_mul, hY, Matrix.map_mul, diagonal_map (map_zero _)]
      exact congrArg (_ * diagonal ·) (funext fun i => (h1 (-t i)).trans (by rw [Real.exp_neg, Complex.ofReal_inv]))
    · funext i
      rw [show (fun i => τ.1 (z i)) = φ ∘ incV F z from funext fun i => (h0 _).symm,
        ← RingHom.map_mulVec, hZ t z hz hz']
      exact h0 _

end PositivityTheory.ThKEst.Sieg

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LintegralLeOfCover
noncomputable section

namespace PositivityTheory.ThKEst.Sieg

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def shf (r : ℕ) (c : ℝ) : Fin r → ℝ := fun i => ((r : ℝ) - i.val) * |Real.log c|

theorem exp_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ Cone r) :
    (fun i => Real.exp ((t + shf r c) i)) ∈ GlobalTheory.SiegelSet.cone r c := by
  have h1 := le_abs_self (Real.log c)
  refine ⟨fun i => Real.exp_pos _, fun i j e => ?_, fun i e => ?_⟩
  · rw [← Real.exp_log hc, ← Real.exp_add, Real.exp_log hc]
    refine Real.exp_le_exp.2 ?_
    have h2 : t j ≤ t i := ht.1 (by rw [Fin.le_def]; omega)
    simp only [Pi.add_apply, shf, e]
    push_cast
    nlinarith
  · refine (Real.log_le_iff_le_exp hc).1 ?_
    have h2 : (r : ℝ) = i.val + 1 := by exact_mod_cast e.symm
    have h3 := ht.2 i
    simp only [Pi.add_apply, shf, h2]
    nlinarith

theorem log_mem_Cone {r : ℕ} {c : ℝ} (hc : 0 < c) {u : Fin r → ℝ} (hu : u ∈ GlobalTheory.SiegelSet.cone r c) :
    ((fun i => Real.log (u i)) + shf r c) ∈ Cone r := by
  have h1 := neg_abs_le (Real.log c)
  obtain _ | r := r
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have ha : Antitone ((fun i => Real.log (u i)) + shf (r + 1) c) := by
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h2 := Real.log_le_log (mul_pos hc (hu.1 _)) (hu.2.1 i.castSucc i.succ (by simp))
    rw [Real.log_mul hc.ne' (hu.1 _).ne'] at h2
    simp only [Pi.add_apply, shf, Fin.val_succ, Fin.val_castSucc]
    push_cast
    nlinarith
  refine ⟨ha, fun i => le_trans ?_ (ha (Fin.le_last i))⟩
  have h2 := Real.log_le_log hc (hu.2.2 (Fin.last r) (by simp))
  simp only [Pi.add_apply, shf, Fin.val_last]
  push_cast
  nlinarith

theorem isClosed_Cone (r : ℕ) : IsClosed (Cone r) := by
  have : Cone r = (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {t : Fin r → ℝ | t j ≤ t i}) ∩ ⋂ i, {t | 0 ≤ t i} := by
    ext t; simp [Cone, Antitone]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply j) (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))

theorem modulus_exp (F : Type) [Field F] [NumberField F] (n : ℕ) {r : ℕ} (v : Fin r → ℝ) :
    GlobalTheory.SiegelSet.modulus F n (fun i => Real.exp (v i)) = Real.exp (2 * Module.finrank ℚ F * rho2 n v) := by
  rw [GlobalTheory.SiegelSet.modulus, rho2, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  push_cast
  ring

theorem rho_sub_alt (n : ℕ) {r : ℕ} (s t : Fin r → ℝ) : rho2 n (s - t) = rho2 n s - rho2 n t := by
  simp [rho2, mul_sub, Finset.sum_sub_distrib]

theorem cone_integral_le (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ} (hc : 0 < c)
    (φ : (Fin r → ℝ) → ℝ≥0∞) :
    ∫⁻ u in GlobalTheory.SiegelSet.cone r c, φ ((fun i => Real.log (u i)) + shf r c) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n u * ∏ i, u i)⁻¹) ≤
      ENNReal.ofReal (Real.exp (2 * Module.finrank ℚ F * rho2 n (shf r c))) *
        ∫⁻ t in Cone r, φ t * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * rho2 n t))) := by
  let Φ : (Fin r → ℝ) → Fin r → ℝ := fun t i => Real.exp ((t - shf r c) i)
  let Φ' : (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] Fin r → ℝ := fun t =>
    LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (Φ t)))
  have hd : ∀ t ∈ Cone r, HasFDerivWithinAt Φ (Φ' t) (Cone r) t := fun t _ => by
    refine HasFDerivAt.hasFDerivWithinAt (hasFDerivAt_pi'.2 fun i => ?_)
    have := ((hasFDerivAt_apply (𝕜 := ℝ) i t).sub_const (shf r c i)).exp
    refine this.congr_fderiv ?_
    ext v
    simp [Φ', Φ, Matrix.mulVec_diagonal]
  have hi : Set.InjOn Φ (Cone r) := fun s _ t _ e => funext fun i => by
    have := Real.exp_injective (congrFun e i)
    simpa using this
  have hs : GlobalTheory.SiegelSet.cone r c ⊆ Φ '' Cone r := fun u hu =>
    ⟨_, log_mem_Cone hc hu, funext fun i => by simp [Φ, Real.exp_log (hu.1 i)]⟩
  refine (lintegral_mono_set hs).trans ?_
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (isClosed_Cone r).measurableSet hd hi,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_of_eq (lintegral_congr fun t => ?_)
  have e1 : (fun i => Real.log (Φ t i)) + shf r c = t := funext fun i => by simp [Φ]
  have e2 : (Φ' t).det = ∏ i, Φ t i := by
    simp [Φ', ContinuousLinearMap.det, LinearMap.det_toLin']
  have e3 : 0 < ∏ i, Φ t i := Finset.prod_pos fun i _ => Real.exp_pos _
  rw [e1, e2, abs_of_pos e3, mul_left_comm, mul_left_comm (ENNReal.ofReal _), ← ENNReal.ofReal_mul e3.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, modulus_exp, rho_sub_alt, ← Real.exp_add]
  congr 2
  rw [mul_inv, mul_left_comm, mul_inv_cancel₀ e3.ne', mul_one, ← Real.exp_neg]
  congr 1
  ring

theorem lintegral_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {D S : Set G} (hD : IsFundamentalDomain Γ D μ) (hS : MeasurableSet S)
    (hc : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (hf : Measurable f) (hi : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in D, f g ∂μ ≤ ∫⁻ g in S, f g ∂μ := by
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul γ.1⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ γ.1 s⟩
  rw [← lintegral_indicator hS, hD.lintegral_eq_tsum'', ← lintegral_tsum
    (f := fun (γ : Γ) x => S.indicator f (γ • x)) fun γ =>
    ((hf.indicator hS).comp (measurable_const_smul γ)).aemeasurable]
  refine lintegral_mono fun g => ?_
  obtain ⟨γ, hγ, h⟩ := hc g
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : Γ))
  exact ((Set.indicator_of_mem h f).trans (hi γ hγ g)).symm

theorem le_exp_of_add {G : Type} [Group G] {r : ℕ} (h : G → ℝ≥0) (hm : ∀ x y, h (x * y) ≤ h x * h y)
    (a : (Fin r → ℝ) → G) (ha : ∀ s t, a (s + t) = a s * a t) (hc : Continuous fun t => h (a t)) :
    ∃ (C : ℝ) (k : ℕ), ∀ t : Fin r → ℝ, (∀ i, 0 ≤ t i) → (h (a t) : ℝ) ≤ C * Real.exp (k * ∑ i, t i) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin r → ℝ) 1).bddAbove_image
    (NNReal.continuous_coe.comp hc).continuousOn
  have hB' : ∀ t : Fin r → ℝ, ‖t‖ ≤ 1 → (h (a t) : ℝ) ≤ B := fun t ht => hB ⟨t, by simpa using ht, rfl⟩
  obtain ⟨k, hk⟩ := exists_nat_ge B
  have hk' : B ≤ Real.exp k := hk.trans (by linarith [Real.add_one_le_exp (k : ℝ)])
  have hp : ∀ (m : ℕ) (t : Fin r → ℝ), ‖t‖ ≤ 1 → (h (a (((m : ℝ) + 1) • t)) : ℝ) ≤ Real.exp k ^ (m + 1) := by
    intro m t ht
    induction m with
    | zero => simpa using (hB' t ht).trans hk'
    | succ m ih =>
      rw [Nat.cast_succ, add_smul, one_smul, ha, pow_succ]
      refine le_trans (NNReal.coe_le_coe.2 (hm _ _)) ?_
      rw [NNReal.coe_mul]
      exact mul_le_mul ih ((hB' t ht).trans hk') (by positivity) (by positivity)
  refine ⟨Real.exp k, k, fun t ht => ?_⟩
  have h0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
  have h1 : ‖t‖ ≤ ∑ i, t i := (pi_norm_le_iff_of_nonneg h0).2 fun i => by
    rw [Real.norm_of_nonneg (ht i)]; exact Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ i)
  have h2 := Nat.floor_le h0
  have h3 := Nat.lt_floor_add_one (∑ i, t i)
  set m := ⌊∑ i, t i⌋₊
  have h4 : (0 : ℝ) < m + 1 := by positivity
  have h5 := hp m (((m : ℝ) + 1)⁻¹ • t) (by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h4.le, inv_mul_le_iff₀ h4]; linarith)
  rw [smul_inv_smul₀ h4.ne'] at h5
  refine h5.trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  push_cast
  nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

end PositivityTheory.ThKEst.Sieg

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatCpt
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientCompactness

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topRing : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change infEmb τ (compInf F E w (a ⊗ₜ[F] (1 : E))) = _
    change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
    rw [infEmb_tmul, map_one, mul_one]
    rfl
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

theorem continuous_sz {n d : ℕ} : Continuous (sz τ : Ten F E n d → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_piInf (τ w)).comp ((continuous_apply j).comp (continuous_apply i))).norm

theorem sz_nonneg {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem entry_le_sz {n d : ℕ} (z : Ten F E n d) (w : InfinitePlace F) (i : Fin n) (j : Fin d) :
    ‖piInf (τ w) (z i j)‖ ≤ sz τ z := by
  unfold sz
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖piInf (τ w) (z i j)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖piInf (τ w) (z i j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem sz_mul_mul_le {n d : ℕ} (A : Ten F E n n) (B : Ten F E d d) (z : Ten F E n d) :
    sz τ (A * z * Bᵀ : Ten F E n d) ≤ (n * d * (sz τ A * sz τ B)) * sz τ z := by
  have hA := sz_nonneg τ A
  have hB := sz_nonneg τ B
  have key : ∀ w i j, ‖piInf (τ w) ((A * z * Bᵀ : Ten F E n d) i j)‖ ≤
      (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ := by
    intro w i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := entry_le_sz τ A w i k
    have h2 := entry_le_sz τ B w j l
    calc _ ≤ sz τ A * ‖piInf (τ w) (z k l)‖ * sz τ B := by gcongr
      _ = _ := by ring
  calc sz τ (A * z * Bᵀ : Ten F E n d)
      ≤ ∑ w, ∑ _i : Fin n, ∑ _j : Fin d, (sz τ A * sz τ B) * ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key w i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show sz τ z = ∑ w, ∑ k, ∑ l, ‖piInf (τ w) (z k l)‖ from rfl, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

theorem maj_nonneg {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : 0 ≤ maj τ C N z := by
  have := sz_nonneg τ z
  unfold maj
  split_ifs
  · positivity
  · exact le_rfl

theorem maj_le {n d : ℕ} (C C' : Set (Ten F E n d)) (N : ℕ) (A : Ten F E n n) (B : Ten F E d d) (K : ℝ) (hK : 1 ≤ K)
    (hAB : n * d * (sz τ A * sz τ B) ≤ K) (hC : ∀ c ∈ C, (A * c * Bᵀ : Ten F E n d) ∈ C') (z : Ten F E n d) :
    maj τ C N z ≤ K ^ N * maj τ C' N (A * z * Bᵀ : Ten F E n d) := by
  by_cases h : ∃ c ∈ C, At (evI F) (z - c)
  · have h' : ∃ c ∈ C', At (evI F) ((A * z * Bᵀ : Ten F E n d) - c) := by
      obtain ⟨c, hc, hz⟩ := h
      refine ⟨_, hC c hc, fun u hu => ?_⟩
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu, Matrix.mul_zero,
        Matrix.zero_mul]
    unfold maj
    rw [if_pos h, if_pos h']
    have h0 := sz_nonneg τ z
    have h1 := sz_nonneg τ (A * z * Bᵀ : Ten F E n d)
    have h2 : 1 + sz τ (A * z * Bᵀ : Ten F E n d) ≤ K * (1 + sz τ z) := by
      have := (sz_mul_mul_le τ A B z).trans (mul_le_mul_of_nonneg_right hAB h0)
      linarith
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 N
  · have := maj_nonneg τ C' N (A * z * Bᵀ : Ten F E n d)
    rw [maj, if_neg h]
    positivity

theorem continuous_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g :=
  Units.continuous_val.comp continuous_subtype_val

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g κ : UA σ J) : mat κ * mat (g * κ)⁻¹ = mat g⁻¹ := by
  rw [← mat_mul, mul_inv_rev, mul_inv_cancel_left]

end LatticeQuotientCompactness


open LatticeQuotientCompactness in
theorem latCpt_of : LatCpt := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ Ω Ω' hΩ hΩ' C N hC
  have := topRing (F := F) (E := E)
  obtain ⟨M, hM⟩ := (hΩ.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  obtain ⟨M', hM'⟩ := (hΩ'.image ((continuous_sz τ).comp continuous_mat)).bddAbove
  let K : ℝ := max 1 (n * d * (M * M'))
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K ^ N := by positivity
  let f : UA σ J × Ten F E n d × UA σ J' → Ten F E n d := fun p => mat p.1 * p.2.1 * (mat p.2.2)ᵀ
  have hf : Continuous f :=
    ((continuous_mat.comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_mat.comp (continuous_snd.comp continuous_snd)).matrix_transpose
  refine ⟨f '' (Ω ×ˢ C ×ˢ Ω'), ⟨K ^ N, hK0⟩, (hΩ.prod (hC.prod hΩ')).image hf, fun S g h κ hκ κ' hκ' => ?_⟩
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have a1 : sz τ (mat κ) ≤ M := hM ⟨κ, hκ, rfl⟩
  have a2 : sz τ (mat κ') ≤ M' := hM' ⟨κ', hκ', rfl⟩
  have b1 := sz_nonneg τ (mat κ)
  have b2 := sz_nonneg τ (mat κ')
  have hAB : n * d * (sz τ (mat κ) * sz τ (mat κ')) ≤ K := by
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ M := b1.trans a1
    gcongr
  have key := maj_le τ C (f '' (Ω ×ˢ C ×ˢ Ω')) N (mat κ) (mat κ') K hK hAB
    (fun c hc => ⟨(κ, c, κ'), ⟨hκ, hc, hκ'⟩, rfl⟩) (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ)
  have e : mat κ * (mat (g * κ)⁻¹ * incM F x.1 * (mat (h * κ')⁻¹)ᵀ) * (mat κ')ᵀ =
      mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ := by
    rw [← mat_mul_inv g κ, ← mat_mul_inv h κ', Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at key
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_eq_coe_nnreal hK0]
  rfl

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatArch
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEst.LatArchPf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mul_realAd {u : AF F} (hu : evI F u = 0) (t : ℝ) : u * realAd F t = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem emb_realAd (hF : IsTotallyReal F) (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = t := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) with ha
  have h1 : InfiniteAdeleRing.ringEquiv_mixedSpace F a = algebraMap ℝ _ t := by
    rw [ha, RingEquiv.apply_symm_apply]
  have h2 := congrFun (congrArg Prod.fst h1) ⟨w, hw⟩
  have h3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w) = t := h2
  change InfinitePlace.Completion.extensionEmbedding w (a w) = t
  rw [← h3]
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw (a w)).symm

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]

theorem piInf_rId (hF : IsTotallyReal F) {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  rw [piInf_alg, rId, map_add (f := _), map_add (f := _), map_one, map_one, emb_realAd hF]
  push_cast
  ring

theorem sz_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z := by
  unfold sz
  positivity

theorem sz_mul_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (M : ℝ) (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ M) :
    sz τ (y * Bᵀ) ≤ d * M * sz τ y := by
  unfold sz
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ∀ j, ‖piInf (τ w) ((y * Bᵀ) i j)‖ ≤ M * ∑ k, ‖piInf (τ w) (y i k)‖ := fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [map_mul, norm_mul, Matrix.transpose_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB w j k) (norm_nonneg _)
  refine (Finset.sum_le_sum fun j _ => h j).trans ?_
  simp [mul_assoc]

theorem incM_mul {n : ℕ} (x y : Matrix (Fin n) (Fin n) E) : incM F (x * y) = incM F x * incM F y :=
  Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem torus (hb : FrameBasis) (hc : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ}
    {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J) (fr : Frame σ J) (hg : fr.IsGood) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Cone fr.r, At (evI F) (mat (fr.a t) - 1) ∧
      ∀ w i j, ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤ K * Real.exp (∑ j, t j) := by
  obtain ⟨b, lam, ix, iy, -, h2, h3, -, h5⟩ := hb F E σ hc d J hJ fr hg
  set P := incM F b.1 with hP
  set Q := incM F (b⁻¹).1 with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← incM_mul, Units.mul_inv, incM_one]
  refine ⟨∑ w, ∑ i, ∑ j, ∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖, by positivity, fun t ht => ?_⟩
  set D : Matrix (Fin d) (Fin d) (AE F E) :=
    Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)) with hD
  have hB : mat (fr.a t) = P * D * Q := by
    rw [← h5 t, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hlam : ∀ k, lam k t ≤ ∑ j, t j := fun k => by
    have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
    by_cases hk : ∀ i, ix i ≠ k ∧ iy i ≠ k
    · rw [h3 k hk]
      exact h0
    · obtain ⟨i, hi⟩ := not_forall.1 hk
      rcases not_and_or.1 hi with e | e
      · rw [← not_not.1 e, (h2 i t).1]
        exact Finset.single_le_sum (fun j _ => ht.2 j) (Finset.mem_univ i)
      · rw [← not_not.1 e, (h2 i t).2]
        exact (neg_nonpos.2 (ht.2 i)).trans h0
  refine ⟨fun u hu => ?_, fun w i j => ?_⟩
  · have hu' : u • (D - 1) = 0 := by
      ext k l
      by_cases e : k = l
      · subst e
        simp only [hD, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
          Matrix.zero_apply, rId, map_add, map_one, add_sub_cancel_left]
        rw [Algebra.smul_def, ← map_mul, mul_realAd hu, map_zero]
      · simp [hD, Matrix.diagonal_apply_ne _ e, Matrix.one_apply_ne e]
    have e : mat (fr.a t) - 1 = P * (D - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, hB]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.mul_zero, Matrix.zero_mul]
  · have h1 : ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤
        (∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) * Real.exp (∑ j, t j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hB, Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [hD, Matrix.mul_diagonal, map_mul, map_mul, piInf_rId hc.1, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_right_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hlam k)) (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem maj_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (K s : ℝ) (hK : 0 ≤ K) (hs : 1 ≤ s) (h1 : At (evI F) (B - 1))
    (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ K * s) :
    maj τ C N y ≤ ((1 + d * K) * s) ^ N * maj τ C N (y * Bᵀ) := by
  have hy := sz_nonneg τ y
  have hz := sz_nonneg τ (y * Bᵀ)
  have hs0 : 0 < s := by linarith
  unfold maj
  split_ifs with h2 h3 h3
  · have h4 := sz_mul_le τ y B _ hB
    have h5 : 1 + sz τ (y * Bᵀ) ≤ (1 + d * K) * s * (1 + sz τ y) := by
      have : 0 ≤ d * K * s := by positivity
      have : 0 ≤ s * sz τ y := by positivity
      nlinarith
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h5 N
  · refine absurd ?_ h3
    obtain ⟨c, hc, h⟩ := h2
    refine ⟨c, hc, fun u hu => ?_⟩
    have e : y * Bᵀ - c = (y - c) + y * (B - 1)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.transpose_one, Matrix.mul_one]
      abel
    rw [e, smul_add, h u hu, zero_add, ← Matrix.mul_smul, ← Matrix.transpose_smul, h1 u hu, Matrix.transpose_zero,
      Matrix.mul_zero]
  · positivity
  · simp

end PositivityTheory.ThKEst.LatArchPf

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK LatArchPf

theorem latArch_of (hb : FrameBasis) : LatArch := by
  intro F E _ _ _ _ _ σ hc τ n d J J' _ hJ' fr hg C N hC
  obtain ⟨K, hK, h⟩ := torus hb hc τ hJ' fr hg
  refine ⟨C, Real.toNNReal ((1 + d * K) ^ N), hC, fun S g t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
  have h3 := maj_le τ C N (mat g⁻¹ * incM F x.1 * (mat (fr.a t)⁻¹)ᵀ) (mat (fr.a t)) K _ hK (Real.one_le_exp h0) h1 h2
  have e : mat (fr.a t) * mat (fr.a t)⁻¹ = mat (1 : UA σ J')⁻¹ := by
    rw [inv_one, ← mul_inv_cancel (fr.a t)]
    rfl
  rw [Matrix.mul_assoc _ _ (mat (fr.a t))ᵀ, ← Matrix.transpose_mul, e] at h3
  change _ ≤ ENNReal.ofReal ((1 + d * K) ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h3.trans_eq ?_)
  rw [mul_pow, Real.exp_nat_mul]

end PositivityTheory.ThKEst

end
end
