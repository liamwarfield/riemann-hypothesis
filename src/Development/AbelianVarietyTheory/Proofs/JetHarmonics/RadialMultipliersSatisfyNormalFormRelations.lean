module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelations
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelAlg

theorem exists_real_xC_ne_zero (P : M.Par) : ∃ Y : ℝ, ∀ ρ : M.Ty P, M.xC P ρ (Y : ℂ) ≠ 0 := by
  classical
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset
    (((Finset.univ : Finset (M.Ty P)) ×ˢ Finset.Icc 1 (P.k - 1)).image fun x => -M.rho P x.1 x.2)
  refine ⟨Y, fun ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi h => hY ?_
  refine Finset.mem_image.2 ⟨(ρ, i), Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
  have h' : Y + M.rho P ρ i = 0 := by exact_mod_cast h
  show -M.rho P ρ i = Y
  linarith

theorem up_unique {P : M.Par} {l : ℕ} {σ ρ ρ' : M.Ty P} (h : M.Up P l σ ρ) (h' : M.Up P l σ ρ') : ρ = ρ' := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem not_up_self {P : M.Par} {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) : ¬ M.Up P l ρ ρ := by
  intro h
  rw [Finset.mem_Icc] at hl
  have := h ⟨l - 1, by omega⟩
  rw [if_pos (by show l - 1 + 1 = l; omega)] at this
  omega

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem proj_raising_sum_proj_eq_zero (d : Q.NFData P A) (h : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    d.κ (Pi.single ρ 1) * d.weightedSumBis Y * d.κ (Pi.single ρ 1) = 0 := by
  classical
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  have h4 := h.2.2.2.1 l (fun σ => if M.Up P l σ ρ then 1 else 0) (Pi.single ρ 1) (by
    intro σ σ' hu
    by_cases e : σ' = ρ
    · subst e; simp [hu]
    · have : ¬ M.Up P l σ ρ := fun h2 => e (up_unique hu h2)
      simp [this, e])
  rw [← mul_assoc, h4, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  have : ((fun σ => if M.Up P l σ ρ then (1 : ℂ) else 0) *
      ((fun σ => M.xEx P {l} σ Y) * Pi.single ρ 1) : M.Ty P → ℂ) = 0 := by
    funext σ
    by_cases e : σ = ρ
    · subst e; simp [not_up_self hl]
    · simp [e]
  rw [this, map_zero, mul_zero]

theorem eq_zero_of_blocks (d : Q.NFData P A) (X : A) (hc : ∀ f, Commute (d.κ f) X)
    (h0 : ∀ ρ, d.κ (Pi.single ρ 1) * X * d.κ (Pi.single ρ 1) = 0) : X = 0 := by
  classical
  have h1 : ∀ ρ, d.κ (Pi.single ρ 1) * X = 0 := by
    intro ρ
    have := h0 ρ
    rw [mul_assoc, ← (hc _).eq, ← mul_assoc, ← map_mul, ← Pi.single_mul, mul_one] at this
    exact this
  have h2 : ∑ ρ : M.Ty P, d.κ (Pi.single ρ 1) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_one d.κ]
    congr 1
    exact Finset.univ_sum_single (1 : M.Ty P → ℂ)
  rw [← one_mul X, ← h2, Finset.sum_mul]
  exact Finset.sum_eq_zero fun ρ _ => h1 ρ

theorem star_GGi [StarModule ℂ A] {r : ℕ} (L : LevelData A r) (h : IsStarLevel L) : star L.GGi = L.GGi := by
  have hb : star L.ζb = L.ζ := by rw [← h.1, star_star]
  have hG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h.1, hb, ← algebraMap_star_comm, h.2.2]
  have : star L.GGi * L.GG = 1 := by rw [← hG, ← star_mul, L.GG_GGi, star_one]
  calc star L.GGi = star L.GGi * L.GG * L.GGi := by rw [mul_assoc, L.GG_GGi, mul_one]
    _ = L.GGi := by rw [this, one_mul]

theorem nab_rel (d : Q.NFData P A) (h : d.Rel) (m m' : A) (hf : ∀ f ∈ d.L.fns, Commute f m)
    (hf' : ∀ f ∈ d.L.fns, Commute f m') (hκ : ∀ f, Commute (d.κ f) m) (hκ' : ∀ f, Commute (d.κ f) m')
    (hQ : ∀ Y : ℝ, d.QQ Y 1 0 * m = m * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m' * d.QQ Y 1 1) :
    d.L.nab * m = m * d.L.nab + d.L.ζb * d.L.GGi * m' := by
  classical
  obtain ⟨Y, hY⟩ := exists_real_xC_ne_zero P
  have hQ := hQ Y
  have e10 : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
  rw [e10, e11] at hQ
  have mG : d.L.GG ∈ d.L.fns := by simp [LevelData.fns]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζb ∈ d.L.fns := by simp [LevelData.fns]
  have kG : ∀ f, Commute (d.κ f) d.L.GG := fun f => h.2.1 f _ (Or.inl mG)
  have kGi : ∀ f, Commute (d.κ f) d.L.GGi := fun f => h.2.1 f _ (Or.inl mGi)
  have kz : ∀ f, Commute (d.κ f) d.L.ζb := fun f => h.2.1 f _ (Or.inl mz)
  have kn : ∀ f, Commute (d.κ f) d.L.nab := fun f => h.2.1 f _ (Or.inr (by simp))
  have kk : ∀ f, Commute (d.κ f) (d.x Y) := fun f => by
    unfold Q.NFData.x; exact (Commute.all _ _).map d.κ
  set Z : A := m * d.L.nab + d.L.ζb * d.L.GGi * m' - d.L.nab * m with hZ
  set g : A := d.L.GG * d.x Y with hg
  have kZ : ∀ f, Commute (d.κ f) Z := fun f =>
    (((hκ f).mul_right (kn f)).add_right (((kz f).mul_right (kGi f)).mul_right (hκ' f))).sub_right
      ((kn f).mul_right (hκ f))
  have gm : Commute g m := (hf _ mG).mul_left (hκ _)
  have gw : Commute g (d.L.ζb * d.L.GGi * m') :=
    (Commute.mul_right (Commute.mul_right (d.L.fns_comm _ mG _ mz) (d.L.fns_comm _ mG _ mGi)) (hf' _ mG)).mul_left
      (((kz _).mul_right (kGi _)).mul_right (hκ' _))
  have um : Commute (algebraMap ℂ A ((Y : ℂ) + 1 / 2) * (d.L.ζb * d.L.GGi)) m :=
    Commute.mul_left (Algebra.commutes _ _) ((hf _ mz).mul_left (hf _ mGi))
  have hX : g * Z = m * d.weightedSumBis Y - d.weightedSumBis Y * m := by
    have e1 : m * (g * d.L.l0 Y) = g * (m * d.L.l0 Y) := by rw [← mul_assoc, ← gm.eq, mul_assoc]
    rw [add_mul, mul_add, e1, ← gw.eq] at hQ
    have e2 : Z = d.L.l0 Y * m - m * d.L.l0 Y + d.L.ζb * d.L.GGi * m' := by
      unfold LevelData.l0
      rw [sub_mul, mul_sub, um.eq, hZ]
      noncomm_ring
    rw [e2, mul_add, mul_sub, ← mul_assoc g _ m, eq_sub_of_add_eq hQ]
    abel
  have hX0 : g * Z = 0 := by
    refine eq_zero_of_blocks d _ (fun f => ((kG f).mul_right (kk f)).mul_right (kZ f)) fun ρ => ?_
    have := proj_raising_sum_proj_eq_zero d h Y ρ
    rw [hX, mul_sub, sub_mul, ← mul_assoc, (hκ _).eq, mul_assoc m, mul_assoc m, this, ← mul_assoc _ _ m,
      mul_assoc _ m, ← (hκ _).eq, ← mul_assoc, this]
    simp
  have hinv : d.κ (fun ρ => (M.xC P ρ Y)⁻¹) * d.L.GGi * g = 1 := by
    rw [hg, mul_assoc, ← mul_assoc d.L.GGi, d.L.GGi_GG, one_mul]
    unfold Q.NFData.x
    rw [← map_mul, ← map_one d.κ]
    congr 1
    funext ρ
    exact inv_mul_cancel₀ (hY ρ)
  have : Z = 0 := by rw [← one_mul Z, ← hinv, mul_assoc, hX0, mul_zero]
  exact (sub_eq_zero.1 this).symm

theorem mulRel_of_entries : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  intro P A _ _ _ _ d hd m hm q
  obtain ⟨-, hs, hr, -⟩ := hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm q
  obtain ⟨k1, -, -, k4, k5, -⟩ := hm (q + 1)
  have hn := nab_rel d hr (m q) (m (q + 1)) h1 k1 h4 k4 h6
  refine ⟨h1, h2, h3, hn, ?_⟩
  have hb : star d.L.ζb = d.L.ζ := by rw [← hs.1, star_star]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζ ∈ d.L.fns := by simp [LevelData.fns]
  have hst := congrArg star hn
  rw [star_add, star_mul, star_mul, star_mul, star_mul, hs.2.1, h5, k5, hb, star_GGi d.L hs,
    d.L.fns_comm _ mGi _ mz, ← ((k1 _ mz).mul_left (k1 _ mGi)).eq] at hst
  rw [hst]
  abel

end GlobalTheory.HatNF.MulRelAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelationsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_mulRel_of_entry_relations : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  first | exact @GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | exact GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | (intros; apply GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplier
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ContDiff

theorem mulT_ld_contDiff {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hφ

theorem mulT_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have : (fun w : ℂ => Complex.normSq w) = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; simp [Complex.normSq_apply]
  rw [this]
  fun_prop

theorem mulT_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ))
      {w : ℂ | T < Complex.normSq w} := by
  have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Real.log (a * (Complex.normSq w - T)))
      {w : ℂ | T < Complex.normSq w} := by
    refine ContDiffOn.log (contDiff_const.mul (mulT_normSq_contDiff.sub contDiff_const)).contDiffOn ?_
    intro w hw
    exact (mul_pos ha (sub_pos.2 hw)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((mulT_ld_contDiff hφ q).comp_contDiffOn h1)

theorem mulT_fderiv {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w v =
      ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) * (Complex.normSq w - T)⁻¹ *
        (2 * (w.re * v.re + w.im * v.im)) : ℝ) : ℂ) := by
  have hp : 0 < Complex.normSq w - T := sub_pos.2 hw
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    have : (fun w : ℂ => Complex.normSq w) =
        fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
      funext w; simp [Complex.normSq_apply]
    rw [this]
    have h1 := Complex.reCLM.hasFDerivAt (x := w)
    have h2 := Complex.imCLM.hasFDerivAt (x := w)
    refine ((h1.mul h1).add (h2.mul h2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    ring
  have h1 := ((hn.sub_const T).const_mul a).log (mul_pos ha hp).ne'
  have h2 : HasDerivAt (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))
      (LE.ld (q + 1) φ (a * (Complex.normSq w - T))) (Real.log (a * (Complex.normSq w - T))) := by
    unfold LE.ld
    rw [iteratedDeriv_succ]
    exact (((mulT_ld_contDiff hφ q).differentiable (by simp)) _).hasDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp_hasFDerivAt w h1)
  have h4 : fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w = _ := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  congr 1
  field_simp

theorem mulT_dZ {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) :
    NF.dZ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      star w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) ∧
    NF.dZb (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) := by
  unfold NF.dZ NF.dZb
  rw [mulT_fderiv hφ q ha T hw, mulT_fderiv hφ q ha T hw, ← Complex.ofReal_inv]
  generalize LE.ld (q + 1) φ (a * (Complex.normSq w - T)) = b
  generalize (Complex.normSq w - T)⁻¹ = e
  constructor <;> apply Complex.ext <;> simp <;> ring


open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx4 in
theorem t_mul_mulG (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hφ : LE.SmoothLog φ)
    (hW : IsMulG P Bs φ W) (q : ℕ) (Y : ℂ) :
    X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧
      X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧
      X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')
  have hDU := Dp_maps (k := P.k) (r := P.r) Bs.z Bs.z'
  have hD := Qx5.Dp_open P.k P.r Bs.z Bs.z'
  have ha : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < Complex.normSq (∏ a, x.1 a) := fun x hx =>
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)
  have key := fun (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
      (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    zeta_smooth_level Bs.z Bs.z' hD hU hDU (mulT_contDiffOn hφ q (ha x hx) _) (Qx5.slice_smooth Φ.2 hx.1)
      ⟨hx.2.1, hx.2.2⟩ Y
  have hd := fun (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    mulT_dZ hφ q (ha x hx) _ (hDU x.2 hx.2.2)
  have hWa : ∀ (p : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      (W p Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ((LE.ld p φ (Complex.normSq (∏ a, c a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) -
          Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun p Φ c g => hW p Φ c g
  have ht : ∀ (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r),
      x ∈ Q.DomR P.k P.r Bs.z Bs.z' → (X.t Y a b (W q Φ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (fun y =>
          ((LE.ld q φ (Complex.normSq (∏ a, x.1 a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) y) -
            Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
    intro a b Φ x hx
    rw [X.t_apply Y a b _ x hx]
    congr 1
    funext y
    exact hWa q Φ x.1 y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, ht 1 0 Φ x hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Pi.sub_apply, X.fn_apply 2 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).1, smul_smul, smul_smul, mul_assoc]
    rfl
  · rw [Module.End.mul_apply, ht 1 1 Φ x hx, (key Φ x hx).2.1, Module.End.mul_apply, hWa,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, ht 0 1 Φ x hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, X.fn_apply 0 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).2, smul_smul, smul_smul, mul_assoc]
    rfl

theorem nf_t_mul_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 :=
  fun Wp Wq _ _ _ _ _ _ P Bs X _ _ _ _ _ _ _ φ W hφ hW q Y => t_mul_mulG Wp Wq P Bs X φ W hφ hW q Y

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplierStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_entries_commutator_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  first | exact @GlobalTheory.HatNF.nf_t_mul_mulG | exact GlobalTheory.HatNF.nf_t_mul_mulG | (intros; apply GlobalTheory.HatNF.nf_t_mul_mulG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOps
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOps
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF.MulCoord

noncomputable section

theorem exists_fderiv_log {m : ℕ} (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℝ,
      HasFDerivAt (fun x : Fin m → ℂ => Real.log (Complex.normSq (∏ a, x a) * γ)) D c ∧
      ∀ l w, D (Pi.single l w) = 2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l) := by
  classical
  have hopen : IsOpen (OmX m) := by
    have : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  let pr : Fin m → ((Fin m → ℂ) →L[ℝ] ℂ) := fun a => ContinuousLinearMap.proj a
  let R : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.reCLM.comp (pr a)
  let J : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.imCLM.comp (pr a)
  have h1 : ∀ a, HasFDerivAt (fun x : Fin m → ℂ => Real.log (R a x * R a x + J a x * J a x))
      ((R a c * R a c + J a c * J a c)⁻¹ • ((R a c • R a + R a c • R a) + (J a c • J a + J a c • J a))) c := by
    intro a
    refine HasFDerivAt.log (((R a).hasFDerivAt.mul (R a).hasFDerivAt).add
      ((J a).hasFDerivAt.mul (J a).hasFDerivAt)) ?_
    have : Complex.normSq (c a) ≠ 0 := by simpa using hc a
    simpa [R, J, pr, Complex.normSq_apply] using this
  have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => h1 a).add_const (Real.log γ)
  refine ⟨_, h2.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hopen.mem_nhds hc] with x hx
    have hx' : ∀ a, Complex.normSq (x a) ≠ 0 := fun a => by simpa using hx a
    rw [map_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun a _ => hx' a) hγ.ne',
      Real.log_prod (fun a _ => hx' a)]
    simp [R, J, pr, Complex.normSq_apply]
  · intro l w
    rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single l]
    · simp [R, J, pr, Complex.normSq_apply]
      ring
    · intro b _ hb
      simp [R, J, pr, Pi.single_eq_of_ne hb]
    · simp

theorem euler_mul {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ)
    (q : ℕ) (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) (f : (Fin m → ℂ) → E)
    (hf : DifferentiableAt ℝ f c) (l : Fin m) :
    pOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c ∧
    pbOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pbOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c := by
  obtain ⟨D, hD, hDl⟩ := exists_fderiv_log γ hγ c hc
  have hh : Differentiable ℝ (iteratedDeriv q fun u : ℝ => φ (Real.exp u)) :=
    ContDiff.differentiable_iteratedDeriv q hφ (by exact_mod_cast ENat.coe_lt_top q)
  have h1 : HasDerivAt (iteratedDeriv q fun u : ℝ => φ (Real.exp u))
      (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ)) (Real.log (Complex.normSq (∏ a, c a) * γ)) := by
    rw [LE.ld, iteratedDeriv_succ]
    exact (hh _).hasDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp c (h1.comp_hasFDerivAt c hD)
  have h3 : HasFDerivAt (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) _ c :=
    HasFDerivAt.smul h2 hf.hasFDerivAt
  have key : ∀ w, fderiv ℝ (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c
      (Pi.single l w) = ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • fderiv ℝ f c (Pi.single l w) +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) *
          (2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l)) : ℝ) : ℂ) • f c := by
    intro w
    rw [h3.fderiv, ← hDl]
    simp [LE.ld]
  have hn : ((Complex.normSq (c l) : ℝ) : ℂ) ≠ 0 := by simpa using hc l
  have e1 : c l * (((c l).re : ℂ) - Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have e2 : star (c l) * (((c l).re : ℂ) + Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  constructor
  · simp only [pOp, if_pos hc, wirt, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e1
    · ring
  · simp only [pbOp, if_pos hc, wirtBar, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e2
    · ring

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem end_ext (A B : Module.End ℂ (Q.RadSp k r z z' π π'))
    (h : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = (B Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g) : A = B := by
  refine LinearMap.ext fun Φ => Subtype.ext ?_
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR k r z z'
  · exact h Φ c g hx
  · exact ((A Φ).2.1 (c, g) hx).trans ((B Φ).2.1 (c, g) hx).symm


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem differentiableAt_coord (Φ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) (g : Q.Mx k r)
    (hx : (c, g) ∈ Q.DomR k r z z') :
    DifferentiableAt ℝ (fun c' => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c' g) c := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g) hx
  have h1 : DifferentiableAt ℝ F (c, g) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
    h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
  refine h2.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun c' : Fin r → ℂ => (c', g)) c := (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'
  exact hΦ (c', g) hc' hx.2.1

theorem commute_of_mul (A B : Module.End ℂ (Q.RadSp k r z z' π π')) (a b : (Fin r → ℂ) → Q.Mx k r → ℂ)
    (hA : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = a c g • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
    (hB : P5.multiplicationOperator B b) : Commute A B := by
  refine end_ext _ _ fun Φ c g hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hA _ c g hx, hB, hB, hA _ c g hx, smul_comm]

end radial

theorem mul_coord : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ _ φ W hφ hW q
  refine ⟨fun l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).1
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).2
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · exact commute_of_mul _ _ (fun c _ => c l) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (c l)⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => star (c l)) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (star (c l))⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun _ g => Q.fnVal P.k P.r Bs.z Bs.z' j g) _
      (fun Φ c g hx => X.fn_apply j Φ (c, g) hx) (hW q)

end

end GlobalTheory.HatNF.MulCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOpsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  first | exact @GlobalTheory.HatNF.MulCoord.mul_coord | exact GlobalTheory.HatNF.MulCoord.mul_coord | (intros; apply GlobalTheory.HatNF.MulCoord.mul_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelations
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelActual

section pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b * Q.mkP c d = Q.mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b + Q.mkP c d = Q.mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b - Q.mkP c d = Q.mkP (a - c) (b - d) := rfl
theorem mkPair_congr {a b c d : Module.End ℂ V} (h : a = c) (h' : b = d) : Q.mkP a b = Q.mkP c d := by rw [h, h']

theorem snd_eq_of_mkPair_eq {a b c d : Module.End ℂ V} (h : Q.mkP a b = Q.mkP c d) : b = d :=
  congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h

theorem commute_mkP {a b w : Module.End ℂ V} (ha : Commute a w) (hb : Commute b w) :
    Commute (Q.mkP a b) (Q.mkP w w) := by
  change Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  exact mkPair_congr ha.eq hb.eq.symm

theorem exists_mkP (x : Q.Pr V) : ∃ a b, x = Q.mkP a b := ⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩

end pairs

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_smul (s : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (s • A) = s • B.hsVec A := rfl

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_sub (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := rfl

omit [FiniteDimensional ℂ Wp] in
theorem eq_zero_of_hsVec {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => congrArg (fun v => v i) h
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simpa using h1 i

omit [FiniteDimensional ℂ Wp] in
theorem eq_of_inner {A A' : Wq →L[ℂ] Wp}
    (h : inner ℂ (B.hsVec (A - A')) (B.hsVec A) = inner ℂ (B.hsVec (A - A')) (B.hsVec A')) : A = A' := by
  have h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0 := by
    nth_rewrite 2 [hsVec_sub]
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem radSp_ext {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact h (c, g) hx
  · rw [Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]

theorem commute_of_adj {a b w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m)
    (hab : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      B.hsInner ((a Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
        B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((b Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) :
    Commute a w := by
  refine LinearMap.ext fun Φ => radSp_ext fun x hx => ?_
  apply eq_of_inner
  have h1 := hab (w Φ) (a (w Φ) - w (a Φ)) x hx
  have h2 := hab Φ (a (w Φ) - w (a Φ)) x hx
  unfold B.hsInner at h1 h2
  rw [hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)] at h1
  exact h1

theorem commute_of_ptAdj {x : RA P Bs} (hx : PtAdj P Bs x) {w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m) : Commute x (Q.mkP w w) := by
  obtain ⟨a, b, rfl⟩ := exists_mkP x
  refine commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)
  have h := hx Ψ Φ y hy
  unfold B.hsInner at h ⊢
  rw [← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]
  exact congrArg _ h.symm

end hs

theorem mulRel_actual : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1
  have hK := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  have hC := GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  have hT := GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩ := hN
  have hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q)) := fun q f =>
    commute_of_ptAdj (hK f).1 (hW q)
  have hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q)) := by
    intro q f hf
    obtain ⟨ho, hfn⟩ := hC q
    rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
    · rw [h3]; exact commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1
    · rw [h4]; exact commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2
    · rw [h5]; exact commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1
    · rw [h6]; exact commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h7]; exact commute_mkP (hfn _) (hfn _)
      · rw [h8]; exact commute_mkP (hfn _) (hfn _)
      · rw [h9]; exact commute_mkP (hfn _) (hfn _)
      · rw [h10]; exact commute_mkP (hfn _) (hfn _)
      · rw [h11]; exact commute_mkP (hfn _) (hfn _)
      · rw [h12]; exact commute_mkP (hfn _) (hfn _)
  refine GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩
  · rw [h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).1 ?_
    rw [neg_mul, ((hC q).1 l).2.1, mul_neg]; abel
  · rw [h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).2.1 ?_
    rw [neg_mul, ((hC q).1 l).1, mul_neg]; abel
  · have mζ : d.L.ζb ∈ d.L.fns := Or.inr (by simp)
    have mG : d.L.GG ∈ d.L.fns := Or.inr (by simp)
    have mGi : d.L.GGi ∈ d.L.fns := Or.inr (by simp)
    have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
    have c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g := fun g hg => by
      rw [e11]
      exact Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))
    have c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1))) := by
      rw [e11]
      exact Commute.mul_left (hf _ _ mG) (hκ _ _)
    have cζG : Commute d.L.ζb d.L.GGi := d.L.fns_comm _ mζ _ mGi
    have key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 =
        d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb)) := by
      rw [← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq,
        (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]
    have hY : star (Y : ℂ) = Y := Complex.conj_ofReal Y
    have q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _
      rw [hY]
    have q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _
      rw [hY]
    rw [q11, h9, h12] at key
    rw [q10, q11, h9, h12]
    simp only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢
    refine mkPair_congr (hT q Y).1 ?_
    rw [snd_eq_of_mkPair_eq key, (hT q Y).2.2]
    abel

end GlobalTheory.HatNF.MulRelActual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelationsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  first | exact @GlobalTheory.HatNF.MulRelActual.mulRel_actual | exact GlobalTheory.HatNF.MulRelActual.mulRel_actual | (intros; apply GlobalTheory.HatNF.MulRelActual.mulRel_actual <;> assumption)
end
