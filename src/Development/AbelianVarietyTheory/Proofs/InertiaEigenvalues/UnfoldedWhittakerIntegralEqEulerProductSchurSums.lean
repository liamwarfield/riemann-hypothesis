module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsShiftedVectorShintaniFormulaRamified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitary
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.BumpData

theorem exists_enum {X : Type} (M : Multiset X) {a : ℕ} (h : M.card = a) :
    ∃ f : Fin a → X, Finset.univ.val.map f = M := by
  subst h
  obtain ⟨l, rfl⟩ := Quotient.exists_rep M
  refine ⟨fun i => l.get ⟨i, by simpa using i.2⟩, ?_⟩
  rw [Fin.univ_val_map]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem bumpData : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  intro E _ _ _ a π hπ T hT
  induction π using Quotient.inductionOn with | _ π₀ => ?_
  obtain ⟨ω, hωu, hω⟩ := hπ
  have hsat : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, (CG.mk π₀).HasSat w.1 (sat (CG.mk π₀) w.1) := by
    intro w
    have hx : ∃ B, (CG.mk π₀).HasSat w.1 B := hT w.1 w.2
    unfold sat
    rw [dite_eq_left hx]
    exact hx.choose_spec
  have hα : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∃ f : Fin a → ℂˣ,
      Finset.univ.val.map f = sat (CG.mk π₀) w.1 := fun w => exists_enum _ (hsat w).card
  choose α hα using hα
  refine ⟨α, π₀, ω, hα, rfl, hωu, hω, ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩, fun w => ?_⟩
  rw [hα w]
  exact hsat w

end GlobalTheory.BumpData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitaryStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  first | (exact @GlobalTheory.BumpData.bumpData) | (exact GlobalTheory.BumpData.bumpData) | (intros; apply GlobalTheory.BumpData.bumpData  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfolding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfolding
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell.CptMod

variable {E : Type} [Field E] [NumberField E]

theorem continuous_finGL_cpt {a : ℕ} : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem exists_pLoc_ite {n : ℕ} (c : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ h : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) h = if w ∈ T then c w else 1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w => by simp⟩
  | insert v T hvT ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨locGL E n v (c v) * h, fun w => ?_⟩
    rw [map_mul, hh w]
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, if_neg hvT, if_pos (Finset.mem_insert_self _ _), mul_one]
    · rw [pLoc_locGL_of_ne hw, one_mul]
      simp [Finset.mem_insert, hw]

theorem isCompact_intGL (n : ℕ) :
    IsCompact {κ : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (n := n)} := by
  convert GlobalTheory.isCompact_KGL E n using 1
  ext κ
  simp only [Set.mem_setOf_eq, GlobalTheory.LFun.KGL, GlobalTheory.CellDec.mem_GLint_iff_entries_cell, ← map_inv]
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · intro h v
    exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩

theorem row_mul_inv {R : Type} [CommRing R] {n : ℕ} {A B : GL (Fin n) R} {i : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) R) i = (B : Matrix (Fin n) (Fin n) R) i) :
    ((A * B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i = (1 : Matrix (Fin n) (Fin n) R) i := by
  funext j
  rw [Units.val_mul, Matrix.mul_apply, h, ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem row_last_unip_mul {R : Type} [CommRing R] {m : ℕ} {u : GL (Fin (m + 1)) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (k : GL (Fin (m + 1)) R) :
    ((u * k : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro i _ hi
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem row_tl_mul {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {i : Fin n} (hl : ∀ w, l w i = 0) (g : GA E n) :
    ((GlobalTheory.CellDec.tl n ϖ l * g : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i = (g : Matrix (Fin n) (Fin n) (Ad E)) i := by
  have h0 : Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l = 0 := by
    ext w
    simp [hl w]
  funext j
  rw [GlobalTheory.CellDec.tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]
  simp only [h0, GlobalTheory.CellDec.adl_zero, map_one, Units.val_one, one_mul]

theorem compV_tl_eq_one {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {w : HeightOneSpectrum (𝓞 E)} (hw : l w = 0) :
    GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hw]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem tl_mul_comm [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (hl : ∀ v ∈ T, l v = 0) {p : GA E n}
    (hp : ∀ w ∉ T, GlobalTheory.CellDec.compV E n w p = 1) :
    GlobalTheory.CellDec.tl n ϖ l * p = p * GlobalTheory.CellDec.tl n ϖ l := by
  apply ga_ext
  · simp [GlobalTheory.CellDec.tl, map_mul]
  · apply GlobalTheory.CellDec.GL_ext_pLoc
    intro w
    change GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l * p) = GlobalTheory.CellDec.compV E n w (p * GlobalTheory.CellDec.tl n ϖ l)
    rw [map_mul, map_mul]
    by_cases hw : w ∈ T
    · rw [compV_tl_eq_one ϖ l (hl w hw), one_mul, mul_one]
    · rw [hp w hw, one_mul, mul_one]

end GlobalTheory.RSCell.CptMod

namespace GlobalTheory.RSCell.CptMod

open scoped Pointwise

theorem exists_isCompact_mod_NA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := (m + 1))) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  intro E _ _ _ m T ϖ hϖ F l₀ U Φ J C hC hl0 hU hKT hN hsupp hΦ hΦs hJ horb
  set K₁ : Set (GA E (m + 1)) :=
    finGL E (m + 1) '' {κ | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (n := (m + 1))} with hK₁d
  set K₂ : Set (GA E (m + 1)) :=
    (fun u => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u)) '' tsupport Φ with hK₂d
  have hK₁ : IsCompact K₁ := (isCompact_intGL (m + 1)).image continuous_finGL_cpt
  have hK₂ : IsCompact K₂ := (show IsCompact (tsupport Φ) from hΦ).image_of_continuousOn
    (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL (Fin.last m)).mono hΦs))
  refine ⟨C * K₁ * K₂ * K₁, ((hC.mul hK₁).mul hK₂).mul hK₁, ?_⟩
  intro x g hg hB
  obtain ⟨u₁, hu₁, k, hk, rfl⟩ := hg
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht
  have hrow : ((t * (u₁ * k) : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    rw [row_tl_mul ϖ l₀.1 hl0, row_last_unip_mul hu₁]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hud
  set yf : Fin (m + 1) → Af E := fun i => pFin E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hyf
  set σ := infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u) with hσ
  have hB1 := left_ne_zero_of_mul hB
  rw [enorm_ne_zero] at hB1
  unfold GlobalTheory.RSTheta.rsPsi GlobalTheory.ThetaPoisson.thetaFn at hB1
  rw [hrow] at hB1
  obtain ⟨hB2, hlat⟩ := mul_ne_zero_iff.1 hB1
  have hlat' : yf - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J := Set.mem_of_indicator_ne_zero hlat
  unfold GlobalTheory.RSTheta.rsInf at hB2
  obtain ⟨hB3, hΦu⟩ := mul_ne_zero_iff.1 hB2
  have hW : GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹) ≠ 0 := left_ne_zero_of_mul hB3
  have hu_supp : u ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hΦu)
  have hunit : IsUnit (u (Fin.last m)) := GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦs hu_supp)
  obtain ⟨κ, hκU, hκK, hκ1, hκrow⟩ := horb yf hlat'
  obtain ⟨hf, hhf⟩ := exists_pLoc_ite (fun w => GlobalTheory.CellDec.compV E (m + 1) w k) T
  set h := infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf with hhd
  set kT := h⁻¹ * k with hkTd
  have hcV_inf : ∀ w (y : GL (Fin (m + 1)) (Cinf E)), GlobalTheory.CellDec.compV E (m + 1) w (infGL E (m + 1) y) = 1 := by
    intro w y
    change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E (m + 1) y)) = 1
    rw [pFin_infGL, map_one]
  have hcV_h : ∀ w, GlobalTheory.CellDec.compV E (m + 1) w h = if w ∈ T then GlobalTheory.CellDec.compV E (m + 1) w k else 1 := by
    intro w
    rw [hhd, map_mul, hcV_inf, GlobalTheory.CellDec.compV_finGL, hhf w, one_mul]
  have hinf_h : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hhd, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hkT_inf : GeneralLinearGroup.map (pInf E) kT = 1 := by
    rw [hkTd, map_mul, map_inv, hinf_h, inv_mul_cancel]
  have hkT_T : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w kT = 1 := by
    intro w hw
    rw [hkTd, map_mul, map_inv, hcV_h, if_pos hw, inv_mul_cancel]
  have hkT_US : kT ∈ GlobalTheory.CellDec.US E (m + 1) T := GlobalTheory.CellDec.mem_US.2 fun w hw => by
    rw [hkTd, map_mul, map_inv, hcV_h, if_neg hw, inv_one, one_mul]
    exact GlobalTheory.CellDec.mem_US.1 hk w hw
  have hkT_fin : kT = finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    conv_lhs => rw [← infGL_mul_finGL kT]
    rw [hkT_inf, map_one, one_mul]
  have hkT_K : ∀ w, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) kT) ∈ GlobalTheory.LFun.KGL w (n := (m + 1)) := by
    intro w
    change GlobalTheory.CellDec.compV E (m + 1) w kT ∈ _
    by_cases hw : w ∈ T
    · rw [hkT_T w hw]
      exact one_mem _
    · exact GlobalTheory.CellDec.mem_US.1 hkT_US w hw
  set B := finGL E (m + 1) κ * σ with hBd
  have hrowB : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    funext j
    apply ad_ext
    · change (GeneralLinearGroup.map (pInf E) h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j =
        (GeneralLinearGroup.map (pInf E) B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
      rw [hinf_h, hBd, map_mul, pInf_finGL, one_mul, hσ, pInf_infGL, GlobalTheory.RSTheta.val_rowGL hunit,
        GlobalTheory.RSTheta.rowMat, Matrix.updateRow_self]
      rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro w
      change (GlobalTheory.CellDec.compV E (m + 1) w h : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
        (GlobalTheory.CellDec.compV E (m + 1) w B : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j
      rw [hcV_h, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hσ, hcV_inf, mul_one]
      split_ifs with hw
      · rw [hκrow w hw j]
        rfl
      · rw [hκ1 w hw]
  set p := h * B⁻¹ with hpd
  have hp_sup : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hpd, map_mul, map_inv, hcV_h, if_neg hw, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hκ1 w hw, hσ, hcV_inf,
      mul_one, inv_one, one_mul]
  have hp_mir : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
    refine ⟨fun w hw => hp_sup w hw, fun j => ?_⟩
    have e := congrFun (row_mul_inv hrowB) j
    rw [← hpd] at e
    rw [e, Matrix.one_apply]
    by_cases hj : j = Fin.last m
    · rw [if_pos hj.symm, if_pos hj]
    · rw [if_neg (Ne.symm hj), if_neg hj]
  have hcomm : kT * σ⁻¹ = σ⁻¹ * kT := by
    rw [hkT_fin, hσ, ← map_inv]
    exact (infGL_comm _ _).symm
  have hnorm : ‖GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹)‖ = ‖GlobalTheory.JSW.whit F (p * t)‖ := by
    have e1 : t * (u₁ * k) * σ⁻¹ = (t * u₁ * t⁻¹) * (t * k * σ⁻¹) := by group
    rw [e1, hN _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu₁)]
    have e2 : t * k * σ⁻¹ = t * h * σ⁻¹ * kT := by
      rw [mul_assoc (t * h), ← hcomm, hkTd]
      group
    rw [e2, hKT kT hkT_US hkT_inf hkT_T]
    have e3 : t * h * σ⁻¹ = t * p * finGL E (m + 1) κ := by
      rw [hpd, hBd]
      group
    rw [e3, hU κ hκU, tl_mul_comm ϖ l₀.1 l₀.2 hp_sup]
  have hWp : GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
    rw [← ht, ← norm_ne_zero_iff, ← hnorm, norm_ne_zero_iff]
    exact hW
  obtain ⟨u₂, hu₂, hu₂C⟩ := hsupp p hp_mir hWp
  refine ⟨u₂ * u₁⁻¹, mul_mem hu₂ (inv_mem hu₁), ?_⟩
  have e : u₂ * u₁⁻¹ * (u₁ * k) = u₂ * p * finGL E (m + 1) κ * σ * finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    rw [← hkT_fin, hpd, hBd, hkTd]
    group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu₂C ⟨κ, hκK, rfl⟩) ⟨u, hu_supp, rfl⟩) ⟨_, hkT_K, rfl⟩

end GlobalTheory.RSCell.CptMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfoldingStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_decomposition_lattice_integral_unfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := (m + 1))) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  first | (exact @GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (exact GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (intros; apply GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarian
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarian
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.JSW.WhitNorm

theorem continuous_whit_and_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  intro E _ _ _ a F hF hl
  refine ⟨?_, fun u hu g => ?_⟩
  · have e : GlobalTheory.JSW.whit F = GroundTheory.Automorphic.FourierWhittaker.partialCoeff F 0 :=
      funext fun g => GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hF g
    rw [e]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hF 0
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := (GlobalTheory.SmGL.mem_unipB _).1 hu
    rw [GlobalTheory.JSW.WhitModel.whit_mul hF hl hu' g, norm_mul, GlobalTheory.JSW.psiN, Circle.norm_coe, one_mul]

end GlobalTheory.JSW.WhitNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarianStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  first | exact @GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | exact GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | (intros; apply GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariant
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.JSW

theorem mspanR_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  intro E _ _ _ a π
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g}
      add_mem' := by
        intro F G hF hG γ g
        simp only [Pi.add_apply, hF γ g, hG γ g]
      zero_mem' := by intro γ g; rfl
      smul_mem' := by
        intro c F hF γ g
        simp only [Pi.smul_apply, hF γ g] }
  have hS : mspanR π ≤ S := by
    refine sInf_le ⟨?_, ?_, ?_⟩
    · intro φ hφ γ g
      exact (π.cusp φ hφ).1.left γ g
    · intro F hF h γ g
      show F (ratGL E a γ * g * h) = F (g * h)
      rw [mul_assoc]; exact hF γ (g * h)
    · intro F hF X _ ν _ k γ' _ γ g
      show (∫ x, k x * F (ratGL E a γ * g * infGL E a (γ' x)) ∂ν) = ∫ x, k x * F (g * infGL E a (γ' x)) ∂ν
      congr 1
      funext x
      rw [mul_assoc, hF γ (g * infGL E a (γ' x))]
  intro F hF
  exact hS hF

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariantStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  first | exact @GlobalTheory.JSW.mspanR_left_invariant | exact GlobalTheory.JSW.mspanR_left_invariant | (intros; apply GlobalTheory.JSW.mspanR_left_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbit
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.BumpOrbit
open GlobalTheory.RSTheta

section Local
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T2Space K]

theorem continuousAt_rowGL {a : ℕ} (ℓ : Fin a) :
    ContinuousAt (rowGL ℓ : (Fin a → K) → GL (Fin a) K) (Pi.single ℓ 1) := by
  have hO : {y : Fin a → K | y ℓ ≠ 0} ∈ nhds (Pi.single ℓ (1:K)) :=
    (isOpen_ne_fun (continuous_apply ℓ) continuous_const).mem_nhds (by simp)
  have hv : (fun y => rowMat ℓ y) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => ((rowGL ℓ y : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    Filter.eventually_of_mem hO fun y hy => (val_rowGL (isUnit_iff_ne_zero.2 hy)).symm
  have hc : Continuous fun y : Fin a → K => rowMat ℓ y := continuous_const.matrix_updateRow ℓ continuous_id
  have hinv : ContinuousAt (fun y : Fin a → K => (rowMat ℓ y)⁻¹) (Pi.single ℓ 1) := by
    refine ContinuousAt.comp (f := fun y => rowMat ℓ y) (g := Inv.inv) ?_ hc.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [det_rowMat, Ring.inverse_eq_inv']
    simpa using continuousAt_inv₀ (one_ne_zero (α := K))
  have hv' : (fun y => MulOpposite.op (rowMat ℓ y)⁻¹) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => MulOpposite.op (((rowGL ℓ y)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    hv.mono fun y hy => by simp only [Matrix.coe_units_inv, ← hy]
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact (hc.continuousAt.congr hv).prodMk ((MulOpposite.continuous_op.continuousAt.comp hinv).congr hv')

end Local

theorem exists_exp_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    ∃ N : ℕ, WithZero.exp (-(N:ℤ)) < c := by
  obtain ⟨k, rfl⟩ : ∃ k, c = WithZero.exp k := ⟨_, (WithZero.exp_log hc).symm⟩
  refine ⟨(-k + 1).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_of_mem_nhds {a : ℕ} (ℓ : Fin a) (w : HeightOneSpectrum (𝓞 E))
    {V : Set (Fin a → w.adicCompletion E)} (hV : V ∈ nhds (Pi.single ℓ 1)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) → y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  have h1 : ∀ j, ∃ N : ℕ, ∀ z : w.adicCompletion E,
      Valued.v (z - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ)) → z ∈ t j := by
    intro j
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (ht j)
    have hc : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by simp
    obtain ⟨N, hN⟩ := exists_exp_lt hc
    refine ⟨N, fun z hz => hγ ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hz hN
  choose N hN using h1
  refine ⟨Finset.univ.sup N, fun y hy => hsub fun j _ => hN j _ ((hy j).trans ?_)⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Finset.le_sup (Finset.mem_univ j)

variable {E : Type} [Field E] [NumberField E]

theorem map_list_prod_locGL {a : ℕ} (g : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin a) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E w) (l.map fun v => locGL E a v (g v)).prod = if w ∈ l then g w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos List.mem_cons_self, mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp [h]

theorem pLoc_single {a : ℕ} (ℓ j : Fin a) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w ((Pi.single ℓ 1 : Fin a → Af E) j) = (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j := by
  by_cases h : j = ℓ
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem exists_nat_rowGL_mem {a : ℕ} (ℓ : Fin a) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) →
      locGL E a w (rowGL ℓ y) ∈ U ∧ rowGL ℓ y ∈ KGL w (n := a) := by
  refine exists_nat_of_mem_nhds ℓ w (V := {y | locGL E a w (rowGL ℓ y) ∈ U ∧
    rowGL ℓ y ∈ KGL w (n := a)}) ?_
  have ho : IsOpen ((locGL E a w) ⁻¹' (U : Set (GL (Fin a) (Af E))) ∩
      (KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E)))) :=
    (hU.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)).inter
      (GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E)))
  exact (continuousAt_rowGL ℓ).preimage_mem_nhds
    (ho.mem_nhds (by simp only [rowGL_single, Set.mem_inter_iff, Set.mem_preimage, map_one, SetLike.mem_coe,
      one_mem, and_self]))

theorem pLoc_apply (w : HeightOneSpectrum (𝓞 E)) (x : Af E) : pLoc E w x = x w := rfl

theorem val_sub_single_le {a : ℕ} (ℓ : Fin a) {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {y : Fin a → Af E}
    (hy : y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J) (w : HeightOneSpectrum (𝓞 E)) (j : Fin a) :
    Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
      WithZero.exp (-FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E)) := by
  have h1 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hy j) w
  rw [← pLoc_apply, Pi.sub_apply, map_sub, pLoc_single] at h1
  exact h1

theorem exists_bump_ideal_rowGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := a)) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  intro E _ _ _ a ℓ T U hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_rowSet (E := E) ℓ) (Pi.single ℓ 1) (by
    intro w; simp)
  let f : ContDiffBump (Pi.single ℓ 1 : Fin a → Cinf E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  choose Nw hNw using fun w => exists_nat_rowGL_mem (E := E) ℓ hU w
  set N : ℕ := T.sup Nw + 1 with hN
  set n : HeightOneSpectrum (𝓞 E) → ℤ := fun w => if w ∈ T then (N : ℤ) else 0 with hn
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
    by_contra h
    simp [hn, h] at hv
  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  have hJ : ∀ w, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = n w :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow n hfin
  refine ⟨fun u => ((f u : ℝ) : ℂ), J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · refine (tsupport_comp_subset Complex.ofReal_zero f).trans ?_
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  · intro u; simp [f.nonneg]
  · simp [f.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; positivity))]
  · intro w hw; rw [hJ, hn]; simp [hw]
  · intro y hy
    have hloc : ∀ w ∈ T, ∀ j, Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
        WithZero.exp (-(N : ℤ)) := by
      intro w hw j
      have h1 := val_sub_single_le ℓ hy w j
      rw [hJ, hn] at h1
      simpa only [hw, if_true] using h1
    have hmem : ∀ w ∈ T, locGL E a w (rowGL ℓ (fun j => pLoc E w (y j))) ∈ U ∧
        rowGL ℓ (fun j => pLoc E w (y j)) ∈ KGL w (n := a) := by
      intro w hw
      refine hNw w _ fun j => (hloc w hw j).trans ?_
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, hN]
      exact (Finset.le_sup hw).trans (Nat.le_succ _)
    have hunit : ∀ w ∈ T, IsUnit (pLoc E w (y ℓ)) := by
      intro w hw
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have h2 := hloc w hw ℓ
      rw [h0, Pi.single_eq_same, zero_sub, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h2
      omega
    have key := map_list_prod_locGL (E := E) (a := a) (fun v => rowGL ℓ (fun j => pLoc E v (y j))) T.toList
      T.nodup_toList
    refine ⟨(T.toList.map fun v => locGL E a v (rowGL ℓ (fun j => pLoc E v (y j)))).prod, ?_, ?_, ?_, ?_⟩
    · refine Subgroup.list_prod_mem U fun x hx => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact (hmem v (Finset.mem_toList.1 hv)).1
    · intro w
      rw [key w]
      split_ifs with h
      · exact (hmem w (Finset.mem_toList.1 h)).2
      · exact one_mem _
    · intro w hw
      rw [key w, if_neg (by simpa using hw)]
    · intro w hw j
      rw [key w, if_pos (Finset.mem_toList.2 hw), val_rowGL (hunit w hw)]
      simp [rowMat]

end GlobalTheory.BumpOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbitStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := a)) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  first | (exact @GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (exact GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (intros; apply GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentity
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

theorem bInt_tl_last_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  intro E _ _ _ m T ϖ F Φ J l₀ hl hW hΦ x
  have h0 : Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1 = 0 := by
    ext w; simp [hl w]
  have hadl : GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1) = 1 := by
    rw [h0]; apply Units.ext; apply FiniteAdeleRing.ext; intro v
    simp [GlobalTheory.CellDec.adl]; rfl
  have hrow : (GlobalTheory.CellDec.tl (m+1) ϖ l₀.1).val (Fin.last m) = Pi.single (Fin.last m) 1 := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, GlobalTheory.SmGL.val_diagT]
    funext j
    simp [Matrix.diagonal_apply, Pi.single_apply, hadl, eq_comm]
  set g := GlobalTheory.CellDec.tl (m+1) ϖ l₀.1 with hg
  have hpi : (fun i => pInf E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hpf : (fun i => pFin E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hlat : (0 : Fin (m+1) → Af E) ∈ GlobalTheory.ThetaPoisson.latt (m+1) J := fun i => zero_mem _
  have hpsi : GlobalTheory.RSTheta.rsPsi (Fin.last m) (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J (Pi.single (Fin.last m) 1) g (g.val (Fin.last m))
      = GlobalTheory.JSW.whit F g * (starRingEnd ℂ) (GlobalTheory.JSW.whit F g) * Φ (Pi.single (Fin.last m) 1) := by
    rw [hrow, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, hpi, hpf, sub_self, Set.indicator_of_mem hlat,
      GlobalTheory.RSTheta.rsInf, GlobalTheory.RSTheta.rowGL_single, map_one, inv_one, mul_one]
    simp
  rw [bInt, hpsi]
  refine mul_ne_zero ?_ ?_
  · rw [enorm_ne_zero]
    exact mul_ne_zero (mul_ne_zero hW (by simpa using hW)) hΦ
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (ideleModule E _).2 x

end GlobalTheory.RSCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentityStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  first | exact @GlobalTheory.RSCell.bInt_tl_last_ne_zero | exact GlobalTheory.RSCell.bInt_tl_last_ne_zero | (intros; apply GlobalTheory.RSCell.bInt_tl_last_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSums
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSCell

theorem exists_isUnifV : ∀ (E : Type) [Field E] [NumberField E], ∃ ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ, ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E) := by
  intro E _ _
  refine ⟨fun w => GroundTheory.Global.uniformizerUnit w, fun w => ?_⟩
  have h := GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  rw [zpow_one] at h
  exact h


set_option maxHeartbeats 4000000 in
theorem lintegral_unfolded_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, π₀, ω, hα, hmk, hωu, hω, hπ₀, hsat⟩ := GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary E (m + 1) π hπ T hT
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E
  obtain ⟨F, hF, l₀, hl₀, ⟨U, hUo, hU⟩, hK, hW0, ⟨C, hC, hCp⟩, hprof⟩ := GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified E m T π₀ hπ₀ α hsat ϖ hϖ
  have hSm : F ∈ Sm E (m + 1) := (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ₀ hF : GlobalTheory.MSpanDecay.Good F).mem_Sm
  let φ : Sm E (m + 1) := ⟨F, hSm⟩
  have hFc : Continuous F := by
    refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E (m + 1) φ
      (GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun k hk => ?_))
    exact Subtype.ext (funext fun g => hU k hk g)
  obtain ⟨hWc, hWN⟩ := GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant E (m + 1) F hFc (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant E (m + 1) π₀ F hF)
  obtain ⟨Φ, J, hΦs, hΦc, hΦr, hΦreal, hΦ1, hJ0, horb⟩ := GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit E (m + 1) (Fin.last m) T U hUo
  have hWU : ∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g := fun u hu g => by
    rw [GlobalTheory.JSW.whit_mul_right]
    exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hU u hu z)
  have hWK : ∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g :=
    fun k hk h1 h2 g => by
      rw [GlobalTheory.JSW.whit_mul_right]
      exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hK k hk h1 h2 z)
  let αc : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ := fun w i => ((α w i : ℂˣ) : ℂ)
  have hpw := GlobalTheory.T.cell_identity_rankinSelberg_torus_translate E m T ϖ hϖ αc F l₀ U Φ J hl₀ hWU hWK hWN hprof hΦr hJ0
    (fun y hy => (horb y hy).imp fun κ hκ => ⟨hκ.1, hκ.2.2⟩)
  obtain ⟨K, hKc, hKp⟩ := GlobalTheory.T.cell_decomposition_lattice_integral_unfolding E m T ϖ hϖ F l₀ U Φ J C hC hl₀ hWU hWK hWN hCp hΦc hΦr hJ0 horb
  obtain ⟨hBc, hBN, hBtop⟩ := GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant E (m + 1) (Fin.last m) (by simp) F Φ J (Pi.single (Fin.last m) 1) hWc hWN
    hΦs.continuous hΦr
  have hΦ1' : Φ (Pi.single (Fin.last m) 1) ≠ 0 := fun h => by rw [h] at hΦ1; simp at hΦ1
  have hone := GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity E m T ϖ F Φ J l₀ hl₀ hW0 hΦ1'
  refine ⟨α, Fin.last m, Φ, J, Pi.single (Fin.last m) 1, π₀, ω, φ, by simp, hα, hmk, hωu, hω, Or.inr hF, ?_, hΦs,
    hΦc, hΦr, hΦreal, fun h => hΦ1' (congrFun h _), ?_⟩
  · intro h
    apply hW0
    have e : F = 0 := congrArg Subtype.val h
    rw [e]
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  intro μ _ 𝓕₀ h𝓕

  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → GA E (m + 1) → ℝ, B = fun x g =>
      (GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g)).toReal :=
    ⟨_, rfl⟩
  have hB1 : Continuous (Function.uncurry B) := by
    have h1 : Continuous fun p : ℝ × GA E (m + 1) => (p.1, GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have h2' := hBc.comp h1
    have h2 : Continuous fun p : ℝ × GA E (m + 1) => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) p.1
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) := h2'
    have h3 := ENNReal.continuousOn_toReal.comp_continuous h2 fun p => hBtop _ _
    subst hBdef
    exact h3
  have hBg : ∀ (x : ℝ) (h : GA E (m + 1) → GA E (m + 1)), Continuous h →
      Continuous fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (h g) := by
    intro x h hh
    have h2 := hBc.comp (continuous_const.prodMk hh : Continuous fun g => (x, h g))
    exact h2
  have hB2 : ∀ x g, 0 ≤ B x g := fun _ _ => by rw [hBdef]; exact ENNReal.toReal_nonneg
  have hB3 : ∀ x, 0 < B x 1 := fun x => by
    rw [hBdef]
    refine ENNReal.toReal_pos ?_ (hBtop _ _)
    rw [mul_one]
    exact hone x
  have hB4 : ∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B x (u * g) = B x g := fun x u hu g => by
    rw [hBdef]
    beta_reduce
    have e : GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * (u * g) =
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * u * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1)⁻¹) * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) := by
      group
    rw [e, hBN x _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu)]
  have hB5 : ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ x g, g ∈ GlobalTheory.CellDec.C0 E (m + 1) T → B x g ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K :=
    ⟨K, hKc, fun x g hg h => hKp x g hg fun h0 => h (by rw [hBdef]; simp only; rw [h0]; rfl)⟩
  obtain ⟨hI, hIc⟩ := GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous E (m + 1) μ T 𝓕₀ h𝓕 B hB1 hB2 hB3 hB4 hB5
  have hd : 0 < GlobalTheory.CellDec.dinv (m + 1) l₀.1 := by
    unfold GlobalTheory.CellDec.dinv
    refine Finset.prod_pos fun w _ => zpow_pos ?_ _
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    unfold Formalism.UG.qV
    exact_mod_cast (zero_lt_one.trans this)

  have key : ∀ x : ℝ, ∫⁻ g in 𝓕₀, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g ∂μ =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) αc x *
        (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ) := by
    intro x
    have hmeas : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, Measurable fun g =>
        GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) := fun l =>
      (hBg x _ (continuous_const.mul continuous_id)).measurable
    have hnm : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T) μ :=
      h𝓕.nullMeasurableSet.inter (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) T).measurableSet.nullMeasurableSet
    have hmx : Measurable fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g :=
      (hBg x (fun g => g) continuous_id).measurable
    rw [GlobalTheory.CellDec.cell_lintegral μ T ϖ hϖ 𝓕₀ h𝓕 _ hmx
      (hBN x), ← GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct E (m + 1) T αc x l₀, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have e1 : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
          GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ENNReal.ofReal (B x g) * GlobalTheory.RSCell.cellProd T αc x (l.1 - l₀.1) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hnm] with g hg
      rw [hpw x g hg.2 l, hBdef, ENNReal.ofReal_toReal (hBtop _ _)]
    have hm2 : Measurable fun g => ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * ENNReal.ofReal (B x g) := by
      rw [hBdef]
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hmeas l₀)))
    rw [e1, lintegral_mul_const _ hm2, mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
    ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal, ?_, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · have e : (fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal) =
        fun x => GlobalTheory.CellDec.dinv (m + 1) l₀.1 * (∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal := by
      funext x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
    rw [e]
    exact (continuous_const.mul hIc).continuousWithinAt
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI 1).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI 1).2.ne)
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI x).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne)
  · rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne), mul_comm]
    exact key x

end GlobalTheory.RSCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSumsStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  first
  | exact @GlobalTheory.RSCell.lintegral_unfolded_eq
  | exact GlobalTheory.RSCell.lintegral_unfolded_eq
  | (intros; apply GlobalTheory.RSCell.lintegral_unfolded_eq <;> assumption)
end
