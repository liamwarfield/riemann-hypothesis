module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_eq (x : ℝ) {a : ℕ} (g : GA E a) :
    detPow E a x g = Real.exp (x * GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g)) := by
  change ‖((GlobalTheory.Mem.Chr.CharModel.absHom E (x : ℂ) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = _
  rw [GlobalTheory.Mem.Chr.CharModel.absHom_val, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem single_last_eq {R : Type} [Zero R] [One R] (j : Fin (m + 1)) :
    (Pi.single (Fin.last m) (1 : R) : Fin (m + 1) → R) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
  by_cases h : j = Fin.last m
  · subst h; simp
  · have : (j : ℕ) ≠ m := fun e => h (Fin.ext e)
    rw [Pi.single_apply, if_neg h, if_neg (by omega)]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_natLat {N : ℕ} (hN : 0 < N) : IsOpen (natLat E N) := by
  have hu : IsUnit (N : Af E) := by
    have e : (N : Af E) = algebraMap E (Af E) (N : E) := (map_natCast _ _).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hN.ne')).map _
  have e : natLat E N = (fun x => ((hu.unit⁻¹ : (Af E)ˣ) : Af E) * x) ⁻¹'
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    simp only [natLat, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← mul_assoc, hu.val_inv_mul, one_mul]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [e]
  exact GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul continuous_id)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_indN {N : ℕ} (hN : 0 < N) : Continuous fun y : Fin (m + 1) → Af E => indN N y := by
  set T : Set (Fin (m + 1) → Af E) :=
    {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} with hT
  have hTc : IsClopen T := by
    have e : T = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [T]
    rw [e]
    exact isClopen_iInter_of_finite fun i =>
      ⟨(GlobalTheory.ZUnfWt.isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const),
        (isOpen_natLat hN).preimage ((continuous_apply i).sub continuous_const)⟩
  have e2 : (fun y : Fin (m + 1) → Af E => indN N y) = T.indicator (fun _ => (1 : ℂ)) := by
    funext y
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem h]; unfold indN; exact if_pos h
    · rw [Set.indicator_of_notMem h]; unfold indN; exact if_neg h
  rw [e2]
  exact continuous_indicator (by simp [hTc.frontier_eq]) continuous_const.continuousOn

theorem continuous_uInt {N : ℕ} (hN : 0 < N) {φ φ' : GA E (m + 1) → ℂ} (hφ : Continuous (GlobalTheory.JSW.whit φ))
    (hφ' : Continuous (GlobalTheory.JSW.whit φ')) {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) (x : ℝ) :
    Continuous (GlobalTheory.ZEul.uInt φ φ' Φ N x) := by
  have hi : Continuous fun g : GA E (m + 1) => indN N (GlobalTheory.ZUnf.yFin g) :=
    (continuous_indN hN).comp GlobalTheory.ZUnfWt.continuous_yFin
  have hw : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) :=
    Complex.continuous_ofReal.comp (GlobalTheory.ZUnfWt.continuous_detPow x)
  have e : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun q => GlobalTheory.JSW.whit φ (q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q))) *
      conj (GlobalTheory.JSW.whit φ' (q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q)))) * Φ (GlobalTheory.ZUnf.yInf q) *
      indN N (GlobalTheory.ZUnf.yFin q) * (detPow E (m + 1) x q : ℂ) := rfl
  rw [e]
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : GlobalTheory.ZUnf.yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (GlobalTheory.ZUnf.yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [GlobalTheory.ZUnf.secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun q : GA E (m + 1) => q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp GlobalTheory.ZUnf.continuous_yInf.continuousAt)
    exact (((hφ.continuousAt.comp h1).mul (Complex.continuous_conj.continuousAt.comp (hφ'.continuousAt.comp h1))).mul
      (hΦ.comp GlobalTheory.ZUnf.continuous_yInf).continuousAt).mul hi.continuousAt |>.mul hw.continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [GlobalTheory.ZUnf.continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [hq]

theorem uInt_self_zero {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ Φ N 0 g = ((GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re : ℂ) ∧ 0 ≤ (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := by
  set w := GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) with hw
  set y : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i) with hy
  set c := indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) with hc
  have hc' : c = (c.re : ℂ) ∧ 0 ≤ c.re := by
    simp only [c, indN]; split_ifs <;> simp
  have hΦy : Φ y = ((Φ y).re : ℂ) := Complex.ext rfl (by simp [(hΦ y).2])
  have hd : detPow E (m + 1) 0 g = 1 := by rw [detPow_eq]; simp
  have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 g = ((Complex.normSq w * (Φ y).re * c.re : ℝ) : ℂ) := by
    change w * conj w * Φ y * c * (detPow E (m + 1) 0 g : ℂ) = _
    conv_lhs => rw [hd, Complex.mul_conj, hΦy, hc'.1]
    push_cast; ring
  rw [e, Complex.ofReal_re]
  exact ⟨rfl, mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ y).1) hc'.2⟩

theorem uInt_unip_mul {φ : GA E (m + 1) → ℂ}
    (hN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) {u : GA E (m + 1)} (hu : u ∈ NA E (m + 1))
    (g : GA E (m + 1)) : GlobalTheory.ZEul.uInt φ φ Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ Φ N x g := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := ⟨h1, h2⟩
  have hr : GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := GlobalTheory.ZUnf.lastRow_mul_of_row fun l => by
    rcases lt_or_eq_of_le (Fin.le_last l) with hl | rfl
    · rw [h1 _ _ hl, Matrix.one_apply_ne (ne_of_gt hl)]
    · rw [h2, Matrix.one_apply_eq]
  have hd : detPow E (m + 1) x (u * g) = detPow E (m + 1) x g := by
    rw [detPow_eq, detPow_eq, map_mul,
      show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu), one_mul]
  have hp : GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [GlobalTheory.JSW.psiN, Circle.norm_coe]
    simp
  unfold GlobalTheory.ZEul.uInt
  rw [hr, hd, mul_assoc u g, hN u hu' _, map_mul]
  set W := GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))
  set r := Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
    (detPow E (m + 1) x g : ℂ)
  linear_combination (W * conj W * r) * hp

end GlobalTheory.CellBump

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem single_vecMul_eq_lastRow (g : GA E (m + 1)) :
    Matrix.vecMul (Pi.single (Fin.last m) (1 : Ad E)) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
      GlobalTheory.ZEul.lastRow g := by
  funext j
  rw [Matrix.single_one_vecMul]
  rfl

theorem exists_compact_support {S : Finset (HeightOneSpectrum (𝓞 E))} {b φ : GA E (m + 1) → ℂ} {N : ℕ}
    {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hJ : ∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))
    (hNJ : ∀ z ∈ natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)))
    (hΦc : HasCompactSupport Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m))
    (hN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g)
    (hK : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g)
    (hb : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C)
    (hW : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p) :
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ g ∈ C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g ≠ 0 →
      ∃ u ∈ NA E (m + 1), u * g ∈ K := by
  obtain ⟨C, hC, hbC⟩ := hb
  refine ⟨(C * (finGL E (m + 1) '' (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set _))) *
      ((fun y => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) y)) '' tsupport Φ),
    (hC.mul ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1)).image
      GlobalTheory.RSLocalPart.continuous_finGL)).mul
      (hΦc.isCompact.image_of_continuousOn
        (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL _).mono hs))), ?_⟩
  intro g hg h0
  have hrow := single_vecMul_eq_lastRow g
  have hdef : GlobalTheory.ZEul.uInt φ φ Φ N 0 g =
      GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
        conj (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
        (detPow E (m + 1) 0 g : ℂ) := rfl
  have hΦ0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 := fun h => h0 (by rw [hdef, h]; ring)
  have hy : (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ∈ tsupport Φ := subset_tsupport _ hΦ0
  have hcond : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) -
      (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N := by
    by_contra hc
    apply h0
    have : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 := by unfold indN; exact if_neg hc
    rw [hdef, this]; ring
  have hi : (fun i => pInf E (Matrix.vecMul (Pi.single (Fin.last m) 1) (g : Matrix _ _ (Ad E)) i)) ∈
      GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs hy
  have hf : ∀ v ∈ S, ∀ j : Fin (m + 1),
      Valued.v ((GlobalTheory.CuspRep.pFin E (Matrix.vecMul (Pi.single (Fin.last m) 1) (g : Matrix _ _ (Ad E)) j) -
        (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
        WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow, single_last_eq]
    exact hNJ _ (hcond j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp (fun i => Fin.le_last i) hJ hg hi hf
  rw [hrow] at e
  set y : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i) with hydef
  have hge : g = u * p * finGL E (m + 1) κ * infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) y) := by
    rw [← e, inv_mul_cancel_right]
  have hpS : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := ⟨fun w hw => hp.2 w hw, hp.1⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  have hW' : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv y)) = GlobalTheory.JSW.psiN u * b p := by
    rw [GlobalTheory.ZUnf.secInv_eq_inv_rowGL (hs hy), map_inv, e, mul_assoc, hN u ⟨h1, h2⟩, hK κ hκ, hW p hpS]
  have hbp : b p ≠ 0 := by
    intro hb0
    apply h0
    rw [hdef]
    change GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv y)) * _ * _ * _ * _ = 0
    rw [hW', hb0, mul_zero]; ring
  obtain ⟨u', hu', hc'⟩ := hbC p hpS hbp
  have hu'N : u' ∈ NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB _).2 hu'
  refine ⟨(u * u')⁻¹, inv_mem (mul_mem hu hu'N), _, ⟨_, hc', _, ⟨κ, GlobalTheory.RSLocalPart.levelAt_subset S J hκ, rfl⟩, rfl⟩,
    _, ⟨y, hy, rfl⟩, ?_⟩
  rw [hge]
  group

end GlobalTheory.CellBump

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ

set_option synthInstance.maxHeartbeats 100000 in
theorem exists_cellPart_unfoldedIntegral_positive_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (φ : GA E (m + 1) → ℂ)
    (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    0 < N → (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ (Pi.single (Fin.last m) 1) ≠ 0 →
    Continuous (GlobalTheory.JSW.whit φ) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    b 1 = 1 → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
  intro E _ _ _ m S b φ N J Φ hN0 hJ hNJ hΦ hΦc hs hΦr hΦ1 hWc hN hK hb1 hb hW μ _ 𝓕₀ h𝓕
  have hO := isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S
  have hre := fun g => uInt_self_zero hΦr φ N g
  have hc : Continuous (GlobalTheory.ZEul.uInt φ φ Φ N 0) := continuous_uInt hN0 hWc hWc hΦ hs 0
  have hBc : Continuous fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := Complex.continuous_re.comp hc
  obtain ⟨K, hKc, hKs⟩ := exists_compact_support hJ hNJ hΦc hs hN hK hb hW

  have hS1 : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = Pi.single (Fin.last m) 1 := by
    funext i
    by_cases h : i = Fin.last m
    · subst h; simp [GlobalTheory.ZEul.lastRow]
    · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
  have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) = GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
    funext i; rw [single_last_eq]; rfl
  have hf1 : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
    unfold indN
    refine if_pos fun i => ?_
    have : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) = if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [← single_last_eq (R := Af E)]
      by_cases h : i = Fin.last m
      · subst h; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    show GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
    rw [this, sub_self]
    exact ⟨0, fun v => zero_mem _, by simp⟩
  have hB1 : 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re := by
    have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
      change GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i))) *
        conj (GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        (detPow E (m + 1) 0 1 : ℂ) = _
      rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul, hW 1 hS1, hb1, detPow_eq, ← hyl]
      simp
    rw [e]
    refine lt_of_le_of_ne (hΦr _).1 fun h => hΦ1 (Complex.ext h.symm (hΦr _).2)

  obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
    (fun _ g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
    (fun _ u hu g => by simp only [uInt_unip_mul hN Φ N 0 hu g])
    ⟨K, hKc, fun _ g hg h0 => hKs g hg fun h => h0 (by rw [h, Complex.zero_re])⟩
  obtain ⟨hlpos, hltop⟩ := hpos 0
  have hIB : IntegrableOn (fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (𝓕₀ ∩ C0 E (m + 1) S) μ :=
    ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩

  set t : GA E (m + 1) → ℝ := fun g => GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) with ht
  have htc : Continuous t := (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
  have htu : ∀ u ∈ NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
    simp only [ht, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu),
      one_mul]
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
  refine ⟨(C0 E (m + 1) S).indicator fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re, t,
    hBc.measurable.indicator hO.measurableSet, htc.measurable,
    fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g, ?_, ?_, ⟨R, fun g hg => ?_⟩,
    fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
  · unfold IntegrableOn
    rw [integrable_indicator_iff hO.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
    exact hIB
  · rw [integral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, Set.inter_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
    exact ENNReal.toReal_pos hlpos.ne' hltop.ne
  · have hgC : g ∈ C0 E (m + 1) S := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hgC] at hg
    obtain ⟨u, hu, hk⟩ := hKs g hgC fun h => hg (by rw [h, Complex.zero_re])
    have := hR _ hk
    rwa [htu u hu, Real.norm_eq_abs] at this
  · rw [Set.indicator_of_mem hg]
    exact (hre g).1
  · rw [detPow_eq, Complex.ofReal_exp]
    push_cast
    rfl

end GlobalTheory.CellBump
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  first | (exact @GlobalTheory.JSW.WhitCont.continuous_whit) | (exact GlobalTheory.JSW.WhitCont.continuous_whit) | (intros; apply GlobalTheory.JSW.WhitCont.continuous_whit  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [_root_.NumberField.IsTotallyComplex E]

theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams


open GlobalTheory.RSParams in
theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCellStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  first | exact @GlobalTheory.RSParams.exists_level_nat_bump | exact GlobalTheory.RSParams.exists_level_nat_bump | (intros; apply GlobalTheory.RSParams.exists_level_nat_bump <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

namespace GlobalTheory.ZEul

set_option synthInstance.maxHeartbeats 100000 in
theorem unfolded_bump_eq :
∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
  (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
  (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
  ∀ b : GA E (m + 1) → ℂ, b 1 = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) →
  (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) →
  ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' →
  ∀ (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
  (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
  (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (α' w))) →
  ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
  (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ (g * finGL E (m + 1) u) = φ g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ g) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
  φ ≠ 0 ∧ φ' ≠ 0 ∧ ∃ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧ (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧
  ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
   ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
    0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
   ∀ x : ℝ, 1 < x →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α' w.1 i : ℂ)) x ≠ ⊤ →
     ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ ∧ ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ' φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α' w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) := by
  intro E _ _ _ m S hsat hψ b hb1 hbN hbC π π' ω ω' hω hω' hπ hπ' α α' hα hα' φ φ' hφ hφ' hU hK hU' hK' hsh hsh'
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {ρ : CuspSub E (m + 1)} {ν : HChar E}, ν.IsUnitary → ρ.HasCentChar ν → ∀ F ∈ GlobalTheory.JSW.mspanR ρ,
      GlobalTheory.JSW.IsBCC F := by
    intro ρ ν hν hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded ⟨ν, hν, CuspSub.hasCentral_iff.2 hρ⟩ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hω hπ φ hφ
  have hc' := hreg hω' hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles E (m + 1) φ hc.cont hc.bdd
  have hWc' := GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles E (m + 1) φ' hc'.cont hc'.bdd
  obtain ⟨U, hUo, hUi⟩ := hU
  obtain ⟨U', hUo', hUi'⟩ := hU'
  let stab : (GA E (m + 1) → ℂ) → Subgroup (GL (Fin (m + 1)) (Af E)) := fun F =>
    { carrier := {k | ∀ g, F (g * finGL E (m + 1) k) = F g}
      mul_mem' := fun {a c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
      one_mem' := fun g => by rw [map_one, mul_one]
      inv_mem' := fun {a} ha g => by
        rw [← ha (g * finGL E (m + 1) a⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) := (U ⊓ U') ⊔ Subgroup.closure
    {k | ∃ w ∉ S, ∃ k' ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k' = k}
  have hVle : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ U ⊓ U', ∀ g, F (g * finGL E (m + 1) u) = F g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) → V ≤ stab F := by
    intro F h1 h2
    refine sup_le (fun k hk => h1 k hk) (Subgroup.closure_le _ |>.2 ?_)
    rintro _ ⟨w, hw, k, hk, rfl⟩
    exact h2 w hw k hk
  have hVφ := hVle φ (fun u hu => hUi u hu.1) hK
  have hVφ' := hVle φ' (fun u hu => hUi' u hu.2) hK'
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) :=
    Subgroup.isOpen_mono (le_sup_left : U ⊓ U' ≤ V) (by rw [Subgroup.coe_inf]; exact hUo.inter hUo')
  have hVK : ∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V := fun w hw k hk =>
    (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
  obtain ⟨N, J, Φ, hN, hΦs, hΦc, hΦt, hΦr, hΦe, hJ, hJV, hn1, hn2, hn3⟩ := GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell E m S hsat V hVo hVK
  have hWJ : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g := by
    intro κ hκ g
    have e : (fun z => φ (z * finGL E (m + 1) κ)) = φ := funext fun z => hVφ (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWJ' : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g := by
    intro κ hκ g
    have e : (fun z => φ' (z * finGL E (m + 1) κ)) = φ' := funext fun z => hVφ' (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hb0 : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh ϖ hϖ 0 (by simp) p hp
  have hb0' : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh' ϖ hϖ 0 (by simp) p hp
  have h1mem : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hne : ∀ F : GA E (m + 1) → ℂ, GlobalTheory.JSW.whit F 1 = 1 → F ≠ 0 := by
    rintro F h rfl
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker] at h
  refine ⟨hne φ (by rw [hb0 1 h1mem, hb1]), hne φ' (by rw [hb0' 1 h1mem, hb1]), N, Φ, hN, hΦs, hΦc, hΦt, hΦr, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) :=
    (GlobalTheory.T.isOpen_C0 E (m + 1) S).measurableSet
  have hcell : ∃ f t : GA E (m + 1) → ℝ,
      Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
    let B : GA E (m + 1) → ℝ := fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re
    have hre := GlobalTheory.CellBump.uInt_self_zero hΦr φ N
    have hBc : Continuous B := Complex.continuous_re.comp
      (GlobalTheory.CellBump.continuous_uInt hN hWc hWc hΦs.continuous hΦt 0)
    obtain ⟨K, hKc, hKs⟩ := GlobalTheory.CellBump.exists_compact_support hJ hn2 hΦc hΦt hW hWJ hbC hb0
    have hBK : ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, B g ≠ 0 →
        ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
      intro g hg hB
      apply hKs g hg
      intro hu
      apply hB
      simp [B, hu]
    have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) =
        Pi.single (Fin.last m) 1 := by
      funext i
      by_cases h : i = Fin.last m
      · subst i; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) =
        GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
      funext i
      rw [GlobalTheory.CellBump.single_last_eq]
      rfl
    have hf1 : GlobalTheory.RSJ.indN N
        (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
      unfold GlobalTheory.RSJ.indN
      refine ite_eq_left fun i => ?_
      have hi : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) =
          if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
        rw [← GlobalTheory.CellBump.single_last_eq (R := Af E)]
        by_cases h : i = Fin.last m
        · subst i; simp [GlobalTheory.ZEul.lastRow]
        · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
      change GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
      rw [hi, sub_self]
      exact ⟨0, fun v => zero_mem _, by simp⟩
    have hB1 : 0 < B 1 := by
      have heq : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
        unfold GlobalTheory.ZEul.uInt
        rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul,
          hb0 1 h1mem, hb1, GlobalTheory.CellBump.detPow_eq, ← hyl]
        simp
      change 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re
      rw [heq]
      exact lt_of_le_of_ne (hΦr _).1 fun h => hΦe (Complex.ext h.symm (hΦr _).2)
    obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
      (fun _ g => B g) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
      (fun _ u hu g => by simp only [B, GlobalTheory.CellBump.uInt_unip_mul hW Φ N 0 hu g])
      ⟨K, hKc, fun _ => hBK⟩
    obtain ⟨hlpos, hltop⟩ := hpos 0
    have hIB : IntegrableOn B (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
      ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩
    let t : GA E (m + 1) → ℝ := fun g =>
      GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g)
    have htc : Continuous t :=
      (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
    have htu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
      simp only [t, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from
        Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu), one_mul]
    obtain ⟨R, hRK⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
    refine ⟨(GlobalTheory.CellDec.C0 E (m + 1) S).indicator B, t,
      hBc.measurable.indicator hC0, htc.measurable, fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g,
      ?_, ?_, ⟨R, fun g hg => ?_⟩, fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
    · unfold IntegrableOn
      rw [integrable_indicator_iff hC0]
      unfold IntegrableOn
      rw [Measure.restrict_restrict hC0, Set.inter_comm]
      exact hIB
    · rw [integral_indicator hC0, Measure.restrict_restrict hC0, Set.inter_comm,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
      exact ENNReal.toReal_pos hlpos.ne' hltop.ne
    · have hgC : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S := by
        by_contra h
        exact hg (Set.indicator_of_notMem h _)
      rw [Set.indicator_of_mem hgC] at hg
      obtain ⟨u, hu, hk⟩ := hBK g hgC hg
      have huR := hRK _ hk
      rwa [htu u hu, Real.norm_eq_abs] at huR
    · rw [Set.indicator_of_mem hg]
      exact (hre g).1
    · rw [GlobalTheory.CellBump.detPow_eq, Complex.ofReal_exp]
      push_cast
      rfl
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet⟩ := hcell
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hd hd'
  have ev := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hn1 hn2 hn3 hΦt hW hW' hWJ hWJ' (hsh ϖ hϖ) (hsh' ϖ hϖ) x
  have ev1 := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α α φ φ N J Φ hJ hn1 hn2 hn3 hΦt hW hW hWJ hWJ (hsh ϖ hϖ) (hsh ϖ hϖ) x
  have ev2 := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α' α' φ' φ' N J Φ hJ hn1 hn2 hn3 hΦt hW' hW' hWJ' hWJ' (hsh' ϖ hϖ)
    (hsh' ϖ hϖ) x
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  obtain ⟨R, hR'⟩ := hR
  have hfe : IntegrableOn (fun g => (f g : ℂ) * Complex.exp (x * t g)) 𝓕₀ μ := by
    refine Integrable.mono' (hfi.mul_const (Real.exp (|x| * R))) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact ((Complex.measurable_ofReal.comp hfm).mul (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp htm)))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 g)]
      by_cases h0 : f g = 0
      · simp [h0]
      · refine mul_le_mul_of_nonneg_left ?_ (hf0 g)
        rw [show (x : ℂ) * (t g : ℂ) = ((x * t g : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR' g h0) (abs_nonneg x)))
  have hA : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ ≠ ⊤ :=
    (hfe.mono_set Set.inter_subset_left).2.ne
  have key : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ),
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g))) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) ∧
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) := by
    intro B P hB
    have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
      h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet
    have hae : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ∀ᵐ g ∂μ.restrict (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S),
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g)) :=
      fun l => (ae_restrict_mem₀ hs).mono fun g hg => hB g hg.2 l
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rw [← integral_const_mul, integral_congr_ae (hae l), integral_const_mul, hIC]
    · have hpos : 0 < GlobalTheory.CellDec.dinv (m + 1) l.1 :=
        Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
      have hd : ‖(GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ)‖ₑ = ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ eNorm_ne_top]
      refine lintegral_congr_ae ((hae l).mono fun g hg => ?_)
      dsimp only
      rw [← hd, ← eNorm_mul, hg, eNorm_mul]
  have k12 := key (GlobalTheory.ZEul.uInt φ φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k11 := key (GlobalTheory.ZEul.uInt φ φ Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α w i : ℂ)) x v) (fun g hg l => by
    rw [(ev1 g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k22 := key (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α' w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev2 g hg).2.2 l, (ev g hg).2.1, hfu g hg, hdet, mul_assoc])
  obtain ⟨hm11, hinv11, -⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ φ Φ N x hWc hWc hW hW hΦs.continuous hΦr
  obtain ⟨hm22, hinv22, -⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ' φ' Φ N x hWc' hWc' hW' hW' hΦs.continuous hΦr
  obtain ⟨hm12, hinv12, hbd⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ φ' Φ N x hWc hWc' hW hW' hΦs.continuous hΦr
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq S (m + 1)
  have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, 2 ≤ Ideal.absNorm w.1.asIdeal := fun w => by
    have h1 : Ideal.absNorm w.1.asIdeal ≠ 1 := fun h => w.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h0 : Ideal.absNorm w.1.asIdeal ≠ 0 := fun h => w.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  have hsum : ∀ a : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
        (fun w i => (a w.1 i : ℂ)) x ≠ ⊤ →
      (∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖ₑ) ≠ ⊤ := by
    intro a ha
    have hs := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
      (fun w => a w.1) (fun w => a w.1) x hx hq ha ha).summable
    have h2 := e.summable_iff.2 hs
    have h3 : (fun l' => (fun l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ) => l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun j => (a w.1 j : ℂ)) (fun j => (a w.1 j : ℂ)) x v) (e l')) =
        fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
          (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v :=
      funext fun l => he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
        (fun i => (a w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l
    rw [Function.comp_def, h3] at h2
    have h4 := summable_norm_iff.2 h2
    have h5 : Summable fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm
        (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖₊ :=
      NNReal.summable_coe.1 (by simpa using h4)
    simpa [eNorm_eq_nnNorm] using ENNReal.tsum_coe_ne_top_iff_summable.2 h5
  have hlin : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) →
      (∑' l, ‖P l‖ₑ) ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖B g‖ₑ ∂μ ≠ ⊤ := by
    intro B P hBm hBi hl hP
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 (fun g => ‖B g‖ₑ) hBm.eNorm
      (fun u hu g => by simp only [hBi u hu g])]
    simp_rw [hl, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hP hA
  have liftZP_unit := hlin _ _ hm11 hinv11 k11.2 (hsum α hd)
  have lix_inf_of_locP_le := hlin _ _ hm22 hinv22 k22.2 (hsum α' hd')
  have i11 : Integrable (GlobalTheory.ZEul.uInt φ φ Φ N x) (μ.restrict 𝓕₀) := ⟨hm11.aestronglyMeasurable, liftZP_unit.lt_top⟩
  have i22 : Integrable (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (μ.restrict 𝓕₀) := ⟨hm22.aestronglyMeasurable, lix_inf_of_locP_le.lt_top⟩
  have i12 : Integrable (GlobalTheory.ZEul.uInt φ φ' Φ N x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((i11.norm.add i22.norm).div_const 2) hm12.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => hbd g)
  have hbo : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      Integrable B (μ.restrict 𝓕₀) → (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) →
      ∫ g in 𝓕₀, B g ∂μ = I * ∑' l, P l := by
    intro B P hBm hBi hBinv hl
    have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 B hBm hBi hBinv).2
    simp_rw [hl] at h
    rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  have hre : ∀ a c : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (c w i : ℂ)) x v) =
      ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (a w.1 i : ℂ)) (fun i => (c w.1 i : ℂ)) x v := by
    intro a c
    rw [← e.tsum_eq]
    exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
      (fun i => (c w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l).symm
  refine ⟨liftZP_unit, lix_inf_of_locP_le, ?_, ?_, ?_⟩
  · rw [hbo _ _ hm12 i12 hinv12 k12.1, hre]
  · rw [hbo _ _ hm11 i11 hinv11 k11.1, hre]
  · rw [hbo _ _ hm22 i22 hinv22 k22.1, hre]

end GlobalTheory.ZEul
