module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicChar
open NumberField Matrix GlobalTheory.CuspRep

namespace GlobalTheory.StdCharStd

theorem stdPsi_adelicChar : ∀ (E : Type) [Field E] [NumberField E],
    GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) :=
  fun E _ _ => GlobalTheory.StdCharConductor.stdPsi_psi E

end GlobalTheory.StdCharStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicCharStatement
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  first | exact @GlobalTheory.StdCharStd.stdPsi_adelicChar | exact GlobalTheory.StdCharStd.stdPsi_adelicChar | (intros; apply GlobalTheory.StdCharStd.stdPsi_adelicChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZero
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CuspGeneric

def cuspBlockIndexEquivLastColumnIndex (a r : ℕ) : BlockIx a r ≃ UnipotentBlockColumnIndex a r (a - 1) where
  toFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  invFun q := ⟨q.1, q.2.1, q.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem posM_apply_of_blkIx {R : Type} [CommRing R] {a r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM Subtype.val x i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  classical
  simp only [posM, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp [Matrix.single_apply]
    · intro t _ ht
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    have := t.2
    rw [h1, h2] at this
    exact h this

theorem blkU_eq_unip {R : Type} [CommRing R] {a r : ℕ} (x : UnipotentBlockColumnIndex a r (a - 1) → R) :
    (blkU x : GL (Fin a) R) = unip (fun p => x (cuspBlockIndexEquivLastColumnIndex a r p)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = (1 + nilM _ : Matrix (Fin a) (Fin a) R) i j
  rw [Matrix.add_apply, Matrix.add_apply, posM_apply_of_blkIx]
  simp only [nilM, Matrix.of_apply]
  congr 1
  have hj := j.2
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · rw [dite_eq_left h, dite_eq_left ⟨h.1, h.2, by omega⟩]
    rfl
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem avg_blk_last_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ),
    Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F →
    ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a,
      GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1)))
        (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  intro E _ _ _ a F _ _ hF r hr0 hr g
  have hra : r < a := by omega
  letI : MeasurableSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := ⟨rfl⟩
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  swap
  · rfl
  obtain ⟨hμ, h𝓕, -⟩ := h.choose_spec
  set μ := h.choose.1
  set 𝓕 := h.choose.2
  let e := cuspBlockIndexEquivLastColumnIndex a r
  let β : (UnipotentBlockColumnIndex a r (a - 1) → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => x (e p)
      invFun := fun y q => y (e.symm q)
      left_inv := fun x => funext fun q => congrArg x (e.apply_symm_apply q)
      right_inv := fun y => funext fun p => congrArg y (e.symm_apply_apply p)
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply (e p)
      continuous_invFun := continuous_pi fun q => continuous_apply (e.symm q) }
  let q : ratN E a r ≃ ratV E (UnipotentBlockColumnIndex a r (a - 1)) :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨c, hc⟩ := y.2
        exact ⟨fun t => c (e.symm t), by rw [← hc]; rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨c, hc⟩ := x.2
        exact ⟨fun p => c (e p), by rw [← hc]; rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hF r hr0 hra (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) g
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  rw [blkU_eq_unip]
  rfl

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZeroStatement
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F → ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a, GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1))) (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | exact GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_blk_last_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfolding
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors NNReal

noncomputable section

namespace GlobalTheory.RSUnfoldW

open GlobalTheory.CuspGeneric GlobalTheory.MirTower GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def yInf (ℓ : Fin a) (g : GA E a) : Fin a → Cinf E := fun i => pInf E (g.val ℓ i)

def sInv (ℓ : Fin a) (g : GA E a) : GA E a := (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (yInf ℓ g)))⁻¹

def fW (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ) (G : GA E a → ℂ) (g : GA E a) : ℂ :=
  G (g * sInv ℓ g) * ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ)

def wW (ℓ : Fin a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (g : GA E a) : ℝ≥0 :=
  (latt a J).indicator (1 : (Fin a → Af E) → ℝ≥0) ((fun i => pFin E (g.val ℓ i)) - η) *
    Real.toNNReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)

theorem row_mul {ℓ : Fin a} {h : GA E a} (hh : ∀ k, h.val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k)
    (g : GA E a) : (h * g).val ℓ = g.val ℓ := by
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ℓ]
  · rw [hh, Matrix.one_apply_eq, one_mul]
  · intro b _ hb
    rw [hh, Matrix.one_apply_ne hb.symm, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem yInf_mul {ℓ : Fin a} {h : GA E a} (hh : ∀ k, h.val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k)
    (g : GA E a) : yInf ℓ (h * g) = yInf ℓ g := by
  unfold yInf
  rw [row_mul hh]

theorem sInv_mul {ℓ : Fin a} {h : GA E a} (hh : ∀ k, h.val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k)
    (g : GA E a) : sInv ℓ (h * g) = sInv ℓ g := by
  unfold sInv
  rw [yInf_mul hh]

theorem fW_mul {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} {G : GA E a → ℂ} {h : GA E a}
    (hh : ∀ k, h.val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k) (g : GA E a) :
    fW ℓ Φ G (h * g) = G (h * (g * sInv ℓ g)) * ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ) := by
  unfold fW
  rw [sInv_mul hh, yInf_mul hh, mul_assoc]

theorem blkU_row {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → Ad E) (k : Fin a) :
    (blkU x : GA E a).val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k := by
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) (Ad E)) ℓ k = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  have h2 := t.1.2.isLt
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, -⟩
  have : (t.1.1 : ℕ) = ℓ := congrArg Fin.val e1
  omega

theorem ratGL_row {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {γ : GL (Fin a) E} (hγ : γ ∈ mirU E a (a - 1)) (k : Fin a) :
    (ratGL E a γ).val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k := by
  have h := hγ ℓ k (by omega) (by have := k.isLt; omega)
  change algebraMap E (Ad E) (γ.val ℓ k) = _
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem ratGL_row_of_isMir {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {γ : GL (Fin a) E} (hγ : IsMir (a - 1) γ) (k : Fin a) :
    (ratGL E a γ).val ℓ k = (1 : Matrix (Fin a) (Fin a) (Ad E)) ℓ k := by
  have h := hγ ℓ k (Or.inl (by omega))
  change algebraMap E (Ad E) (γ.val ℓ k) = _
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem whit_transport (ψ : AddChar (Ad E) ℂ) : ∀ (m : ℕ) (F : GA E a → ℂ) (ρ : GA E a → GA E a) (c : GA E a → ℂ),
    (∀ k, 0 < k → k ≤ m → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, ρ (blkU y * g) = ρ g ∧ c (blkU y * g) = c g) →
    ∀ g, GlobalTheory.CuspGeneric.whit ψ m (fun g => F (g * ρ g) * c g) g = GlobalTheory.CuspGeneric.whit ψ m F (g * ρ g) * c g := by
  intro m
  induction m with
  | zero => intro F ρ c _ g; rfl
  | succ m ih =>
    intro F ρ c h g
    rw [whit_succ, whit_succ]
    have e : colT ψ (m + 1) (fun g => F (g * ρ g) * c g) = fun g => colT ψ (m + 1) F (g * ρ g) * c g := by
      funext g
      simp only [colT, coefF]
      rw [mul_comm, ← avg_const_mul]
      congr 1
      funext y
      rw [(h (m + 1) (Nat.succ_pos m) le_rfl y g).1, (h (m + 1) (Nat.succ_pos m) le_rfl y g).2, mul_assoc]
      ring
    rw [e]
    exact ih _ ρ c (fun k hk hkm y g => h k hk (by omega) y g) g

theorem det_blkU {r m : ℕ} (y : UnipotentBlockColumnIndex a r m → Ad E) : GeneralLinearGroup.det (blkU y : GA E a) = 1 := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.val_one]
  change (1 + posM Subtype.val y : Matrix (Fin a) (Fin a) (Ad E)).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero, Matrix.one_apply_eq]
    intro t _
    have := t.2
    rw [Matrix.single_apply_of_ne]
    rintro ⟨e1, e2⟩
    have h1 := congrArg Fin.val e1
    have h2 := congrArg Fin.val e2
    omega
  · intro i j hij
    have h3 : (j : ℕ) < i := hij
    rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero, Matrix.one_apply_ne (show i ≠ j from fun h => by subst h; omega)]
    intro t _
    have := t.2
    rw [Matrix.single_apply_of_ne]
    rintro ⟨e1, e2⟩
    have h1 := congrArg Fin.val e1
    have h2 := congrArg Fin.val e2
    omega

theorem continuous_yInf (ℓ : Fin a) : Continuous (yInf ℓ : GA E a → Fin a → Cinf E) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp
    (Units.continuous_val.matrix_elem ℓ i)

theorem enorm_rsPsi_row (ℓ : Fin a) (G : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (x : ℝ) (g : GA E a) :
    ‖GlobalTheory.RSTheta.rsPsi ℓ G G Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) =
      ‖fW ℓ Φ G g‖ₑ ^ 2 * (wW ℓ J η x g : ℝ≥0∞) := by
  have key : ‖G (g * sInv ℓ g) * conj (G (g * sInv ℓ g)) * Φ (yInf ℓ g)‖ =
      ‖G (g * sInv ℓ g) * ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ)‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _)]
    ring
  have key' : ‖G (g * sInv ℓ g) * conj (G (g * sInv ℓ g)) * Φ (yInf ℓ g)‖₊ =
      ‖G (g * sInv ℓ g) * ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ)‖₊ ^ 2 := NNReal.eq (by simpa using key)
  simp only [GlobalTheory.RSTheta.rsPsi, thetaFn, GlobalTheory.RSTheta.rsInf, fW, wW]
  change ‖G (g * sInv ℓ g) * conj (G (g * sInv ℓ g)) * Φ (yInf ℓ g) * _‖ₑ * _ = _
  by_cases hm : ((fun i => pFin E (g.val ℓ i)) - η) ∈ latt a J
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
    simp only [Pi.one_apply, mul_one, one_mul, enorm_eq_nnnorm, key', ENNReal.coe_pow]
    rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
    simp

theorem good_fW {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) (ψ : AddChar (Ad E) ℂ) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ γ g, F (ratGL E a γ * g) = F g)
    (hv : ∀ r, 0 < r → r ≤ a - 1 → ∀ g : GA E a,
      avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F ((blkU x : GA E a) * g)) = 0)
    {Φ : (Fin a → Cinf E) → ℂ} (hΦc : Continuous Φ) (hΦt : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ) :
    Good ψ (a - 1) (fW ℓ Φ F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hy := continuous_yInf (E := E) ℓ
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hp : yInf ℓ g ∈ tsupport Φ
    · have h1 : ContinuousAt (fun g => g * sInv ℓ g) g :=
        continuousAt_id.mul (((GlobalTheory.RSTheta.continuousOn_inv_rowGL ℓ).continuousAt
          ((GlobalTheory.RSTheta.isOpen_rowSet ℓ).mem_nhds (hΦt hp))).comp hy.continuousAt)
      exact (hc.continuousAt.comp h1).mul (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_norm.comp (hΦc.comp hy)))).continuousAt
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [hy.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
      simp [fW, hq]
  · intro γ hγ g
    rw [fW_mul (ratGL_row_of_isMir hℓ hγ), hl]
    rfl
  · intro k hk y g
    have : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.2; have := t.1.2.isLt; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have e1 : (blkU (0 : UnipotentBlockColumnIndex a k k → Ad E) : GA E a) = 1 := posU_zero _
    rw [e1, one_mul]
    simp [dot]
  · intro r hr hra g
    have e : (fun x : UnipotentBlockColumnIndex a r (a - 1) → Ad E => fW ℓ Φ F ((blkU x : GA E a) * g)) =
        fun x => ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ) * F ((blkU x : GA E a) * (g * sInv ℓ g)) := by
      funext x
      rw [fW_mul (blkU_row hℓ x), mul_comm]
    rw [e, avg_const_mul, hv r hr hra, mul_zero]

theorem ratMirU_zero (E : Type) [Field E] [NumberField E] (a : ℕ) : ratMirU E a 0 = GlobalTheory.CellDec.NE E a := by
  unfold ratMirU GlobalTheory.CellDec.NE
  congr 1
  ext g
  rw [GlobalTheory.MirTower.mem_mirU_zero, GlobalTheory.SmGL.mem_unipB]

theorem measurable_wW (ℓ : Fin a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) :
    Measurable (wW ℓ J η x : GA E a → ℝ≥0) := by
  have hcd : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hr : Continuous fun g : GA E a => (fun i => pFin E (g.val ℓ i)) - η :=
    Continuous.sub (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      (Units.continuous_val.matrix_elem ℓ i : Continuous fun g : GA E a => g.val ℓ i)) continuous_const
  exact ((measurable_const.indicator (GlobalTheory.RSTheta.isClosed_latt J).measurableSet).comp hr.measurable).mul
    (measurable_real_toNNReal.comp (hcd.measurable.pow_const x))

end GlobalTheory.RSUnfoldW


open GlobalTheory.RSUnfoldW GlobalTheory.CuspGeneric GlobalTheory.MirTower in
theorem GlobalTheory.RSUnfold.lintegral_theta_eq_whit : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (π : CuspSub E a), π.IsUnitary → ∀ (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕₀ : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ := by
  intro E _ _ _ a ℓ hℓ π hπ F hF Φ hΦc hΦs hΦt J η μ _ 𝓕 𝓕₀ h𝓕 h𝓕₀ x
  have ha : 0 < a := by omega
  obtain ⟨φ, hφ, hφF⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπ hF
  have hB : IsBCC F := by
    have h := (GlobalTheory.JSW.mem_dSub.1 hφ []).2
    rw [GlobalTheory.JSW.word_nil] at h
    rw [← hφF]
    exact h
  haveI : DiscreteTopology (ratMirU E a (a - 1)) := GlobalTheory.MirTower.discrete_of_le_range (Subgroup.map_le_range _ _)
  have := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
  obtain ⟨𝓕P, h𝓕P⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratMirU E a (a - 1)) μ
  have hℓ' : (⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ : Fin a) = ℓ := Fin.ext (by simp only; omega)
  have hdet : ∀ (γ : GL (Fin a) E) (g : GA E a), (ideleModule E (GeneralLinearGroup.det (ratGL E a γ * g)) : ℝ) =
      ideleModule E (GeneralLinearGroup.det g) := by
    intro γ g
    rw [map_mul, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  have hcd : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hmeas : ∀ v : Fin a → E, Measurable fun g : GA E a =>
      ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)‖ₑ *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    intro v
    have hv : Continuous fun g : GA E a => Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val :=
      continuous_const.matrix_vecMul Units.continuous_val
    exact (((GlobalTheory.RSTheta.continuous_rsPsi hB.cont hB.cont hΦc hΦt J η).comp (continuous_id.prodMk hv)).enorm.measurable).mul
      (ENNReal.measurable_ofReal.comp (hcd.measurable.pow_const x))
  have e1 := GlobalTheory.T.lintegral_theta_series_unfold_mirabolic E a ha μ 𝓕 𝓕P h𝓕 h𝓕P
    (fun g y => ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x))
    hmeas (fun γ g y => by simp only [GlobalTheory.RSTheta.rsPsi_ratGL_mul ℓ hB.left hB.left, hdet])
  simp_rw [← ENNReal.tsum_mul_right]
  rw [e1, hℓ']
  simp_rw [enorm_rsPsi_row]
  set ψC : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E) with hψC
  have h𝓕₀' : IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ := by rw [ratMirU_zero]; exact h𝓕₀
  have hwl : ∀ γ ∈ mirU E a (a - 1), ∀ g, wW ℓ J η x (ratGL E a γ * g) = wW ℓ J η x g := by
    intro γ hγ g
    unfold wW
    rw [row_mul (ratGL_row hℓ hγ), hdet]
  have hwu : ∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), wW ℓ J η x (blkU y * g) = wW ℓ J η x g := by
    intro k y g
    unfold wW
    rw [row_mul (blkU_row hℓ y), map_mul, det_blkU, one_mul]
  have hgood : Good ψC (a - 1) (fW ℓ Φ F) :=
    good_fW hℓ ψC hB.cont hB.left (fun r hr hra g => GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero E a F hB.cont hB.left hB.cusp r hr hra g) hΦc hΦt
  have e2 := (GlobalTheory.T.unfold_mirabolic_alt E a μ ψC (GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar E) 𝓕P 𝓕₀ h𝓕P h𝓕₀' (wW ℓ J η x) (measurable_wW ℓ J η x) hwl
    hwu).1 (fW ℓ Φ F) hgood
  rw [e2]
  refine lintegral_congr fun g => ?_
  have hA : GlobalTheory.CuspGeneric.whit ψC (a - 1) (fW ℓ Φ F) g = fW ℓ Φ (GlobalTheory.JSW.whit F) g := by
    have := whit_transport ψC (a - 1) F (sInv ℓ) (fun g => ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ))
      (fun k _ _ y g => ⟨sInv_mul (blkU_row hℓ y) g, by simp only [yInf_mul (blkU_row hℓ y)]⟩) g
    rw [show fW ℓ Φ F = fun g => F (g * sInv ℓ g) * ((Real.sqrt ‖Φ (yInf ℓ g)‖ : ℝ) : ℂ) from rfl, this,
      GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker E a F ha hB.cont hB.left]
    rfl
  rw [hA]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfoldingStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (π : CuspSub E a), π.IsUnitary → ∀ (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕₀ : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
    ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ := by
  first | (exact @GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (exact GlobalTheory.RSUnfold.lintegral_theta_eq_whit) | (intros; apply GlobalTheory.RSUnfold.lintegral_theta_eq_whit  <;> assumption)
end
