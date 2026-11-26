module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

open Matrix

theorem decomp_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  intro E _ _ _ m S J hJ N hN Φ hs g hg hΦ hind
  have hrow : ∀ h : GA E (m + 1), Pi.single (Fin.last m) 1 ᵥ* h.val = fun j => GlobalTheory.ZEul.lastRow h j := fun h => by
    rw [Matrix.single_one_vecMul]; rfl
  have hℓ : ∀ i : Fin (m + 1), i ≤ Fin.last m := Fin.le_last
  have hi : (fun i => pInf E ((Pi.single (Fin.last m) 1 ᵥ* g.val) i)) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs (subset_tsupport _ hΦ)
  have hind' : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
      GlobalTheory.RSJ.natLat E N := by
    by_contra hc
    exact hind (by rw [GlobalTheory.RSJ.indN, if_neg hc])
  have hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single (Fin.last m) 1 ᵥ* g.val) j) -
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow]
    have e : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [Pi.single_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [e]
    exact hN _ (hind' j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp hℓ hJ hg hi hf
  refine ⟨u, (GlobalTheory.SmGL.mem_unipB _).1 hu, p, ⟨hp.2, hp.1⟩, κ, hκ, ?_⟩
  rw [← e, hrow]
  congr 1
  rw [hrow] at hi
  have hu' := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hi
  rw [← map_inv]
  congr 1
  have hm : GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      GlobalTheory.RSTheta.rowMat (Fin.last m) (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    congr 1
    simp [Fin.ext_iff]
  have hd : IsUnit (GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i))).det := by
    rw [hm, GlobalTheory.RSTheta.det_rowMat]; exact hu'
  rw [GlobalTheory.RSJ.secInv, dite_eq_left hd]
  congr 1
  exact Units.ext (hm.trans (GlobalTheory.RSTheta.val_rowGL hu').symm)

end GlobalTheory.ZEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicCell_decomposition_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  first | (exact @GlobalTheory.ZEul.decomp_lastRow) | (exact GlobalTheory.ZEul.decomp_lastRow) | (intros; apply GlobalTheory.ZEul.decomp_lastRow  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellVanish

theorem eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  intro E _ _ _ m S J w hwS hψ ϖ hϖ W hWN hWK l hl p hp
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l with ht
  set D : GL (Fin (m + 1)) (w.adicCompletion E) := GlobalTheory.CellDec.compV E (m + 1) w t with hD
  have hDv : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [hD, ht, GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
    refine Matrix.ext fun i j => ?_
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin (m + 1)) _ : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  set t' := t * (finGL E (m + 1) (locGL E (m + 1) w D))⁻¹ with ht'
  have ht'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t' = 1 := by
    change GlobalTheory.CellDec.compV E (m + 1) w t' = 1
    rw [ht', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : t' * finGL E (m + 1) (locGL E (m + 1) w D) = t := by rw [ht', inv_mul_cancel_right]
  have hlev : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J := by
    intro k hk
    refine ⟨fun v => ?_, fun v hv i j => ?_⟩
    · by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have hvw : v ≠ w := fun h => hwS (h ▸ hv)
      have h1 := congrArg (fun x : GL (Fin (m + 1)) (v.adicCompletion E) => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (v.adicCompletion E)) i j)
        (pLoc_locGL_of_ne hvw k)
      have h0 : ((locGL E (m + 1) w k).val - 1) i j v = 0 := by
        change pLoc E v (((locGL E (m + 1) w k).val - 1) i j) = 0
        rw [Matrix.sub_apply, map_sub]
        change (Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E (m + 1) w k)).val i j - _ = 0
        rw [h1]
        simp [Matrix.one_apply]
      rw [h0, map_zero]
      exact zero_le'
  let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (p * t' * finGL E (m + 1) (locGL E (m + 1) w g))
  have hfD : f D = W (p * t) := by
    simp only [f]
    rw [mul_assoc, htt]
  have hpt : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (p * t') = 1 := by
    rw [map_mul, hp, ht'w, mul_one]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc (p * t'), GlobalTheory.JSW.commute_finGL_locGL w hpt, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK _ (hlev k hk) _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w (m + 1) (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK (ϖ w) hϖ (l w) hl D hDv
  rwa [hfD] at h

end GlobalTheory.CellVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitoneStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  first | exact @GlobalTheory.CellVanish.eq_zero_of_not_antitone | exact GlobalTheory.CellVanish.eq_zero_of_not_antitone | (intros; apply GlobalTheory.CellVanish.eq_zero_of_not_antitone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

variable {E : Type} [Field E] [NumberField E]

theorem one_lt_v_zpow {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E} (h : IsUnifV E v ϖ) {a : ℤ}
    (ha : a < 0) : 1 < Valued.v (ϖ ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -((n + 1 : ℕ) : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at h
  have h1 : Valued.v ϖ < 1 := by
    rw [h]; exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1)
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow]
  have hp : Valued.v ϖ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' h1 (Nat.succ_ne_zero n)
  have hp0 : Valued.v ϖ ^ (n + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 h0)
  exact (one_lt_inv₀ (zero_lt_iff.2 hp0)).2 hp

end GlobalTheory.CellLastRow

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

theorem indN_lastRow_tl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  intro E _ _ _ m S ϖ hϖ N hlat hloc l g hg
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hk' : ∀ v ∉ S, compV E (m + 1) v k ∈ GlobalTheory.LFun.KGL v (n := (m + 1)) := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  set c : (Af E)ˣ := adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) with hc
  have hev : ∀ (x : Af E) v, x v = pLoc E v x := fun _ _ => rfl
  have hcv : ∀ v, pLoc E v (c : Af E) = ((ϖ v ^ l.1 v (Fin.last m) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    intro v
    change ((ϖ v ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) v :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply]
  have hrow : ∀ i, lastRow (u * k) i = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i := by
    intro i
    have := congrFun (GlobalTheory.RSLocalPart.single_vecMul_unip (ℓ := Fin.last m) (fun j => Fin.le_last j) hu k) i
    simpa [lastRow, Units.val_mul, Matrix.single_one_vecMul] using this
  have hrow' : ∀ i, GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) =
      (c : Af E) * GlobalTheory.RSJ.pFin E (lastRow (u * k) i) := by
    intro i
    simp only [lastRow, tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, map_mul]
    congr 1
    change GlobalTheory.RSJ.pFin E (1 - sFin E 1 + sFin E (c : Af E)) = _
    rw [map_add (f := _), map_sub, map_one]
    change 1 - 1 + (c : Af E) = _
    ring
  have hcomp : ∀ v i, pLoc E v (GlobalTheory.RSJ.pFin E (lastRow (u * k) i)) = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i; rw [hrow]; rfl
  have hint : ∀ v ∉ S, ∀ i j, (compV E (m + 1) v k).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0]
    exact (k0.val i j).2
  have hinv : ∀ v ∉ S, ∀ i j, ((compV E (m + 1) v k)⁻¹).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0, ← map_inv]
    exact ((k0⁻¹).val i j).2
  have hδ : ∀ v (i : Fin (m + 1)), pLoc E v (if (i : ℕ) + 1 = m + 1 then (1 : Af E) else 0) ∈ v.adicCompletionIntegers E := by
    intro v i
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  refine ⟨fun hpos => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have key : ∀ i : Fin (m + 1),
        (GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
          GlobalTheory.RSJ.natLat E N ↔
        GlobalTheory.RSJ.pFin E (lastRow (u * k) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) := by
      intro i
      refine (hloc _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)).symm
      · rw [hev, hev, map_sub, map_sub, hrow', map_mul, hcv, l.2 v hv]
        simp
      · rw [hev, map_sub, hcomp]
        exact sub_mem (hint v hv _ _) (hδ v i)
      · rw [hev, map_sub, hrow', map_mul, hcomp, hcv]
        refine sub_mem (mul_mem ?_ (hint v hv _ _)) (hδ v i)
        rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hpos v), zpow_natCast]
        exact pow_mem (GlobalTheory.LFun.mem_Ov_of_isUnifV (hϖ v)) _
    unfold GlobalTheory.RSJ.indN
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun i => (key i).1 (h1 i)) h2
    · exact absurd (fun i => (key i).2 (h2 i)) h1
    · rfl
  · have hwS : w ∉ S := fun h => by
      have h0 := l.2 w h
      rw [h0] at hw
      exact lt_irrefl _ hw
    have hex : ∃ j, ¬ Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) < 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : ((compV E (m + 1) w k).val * ((compV E (m + 1) w k)⁻¹).val) (Fin.last m) (Fin.last m) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at h1
      have h2 : Valued.v (∑ j, (compV E (m + 1) w k).val (Fin.last m) j * ((compV E (m + 1) w k)⁻¹).val j (Fin.last m)) < 1 := by
        refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcon j) (hinv w hwS j (Fin.last m))
      rw [h1, map_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨j, hj⟩ := hex
    have hj1 : Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) = 1 :=
      le_antisymm (hint w hwS _ _) (not_lt.1 hj)
    unfold GlobalTheory.RSJ.indN
    rw [if_neg]
    intro hall
    have hz := hlat _ (hall j) w
    dsimp only at hz
    rw [hev, map_sub, hrow', map_mul, hcomp, hcv] at hz
    have ha := add_mem hz (hδ w j)
    rw [sub_add_cancel, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hj1, mul_one,
      Units.val_zpow_eq_zpow_val] at ha
    exact not_le.2 (one_lt_v_zpow (hϖ w) hw) ha

end GlobalTheory.CellLastRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMulStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowCongruenceIndicator_diagonalUniformizer_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  first
  | exact @GlobalTheory.CellLastRow.indN_lastRow_tl
  | exact GlobalTheory.CellLastRow.indN_lastRow_tl
  | (intros; apply GlobalTheory.CellLastRow.indN_lastRow_tl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

theorem detPow_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n 0 g = 1 := by
  intro E _ _ _ n g
  simp [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem pInf_lastRow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ))
    (g : GA E (m + 1)),
    (fun i => pInf E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) i)) = fun i => pInf E (GlobalTheory.ZEul.lastRow g i) := by
  intro E _ _ _ m ϖ l g
  funext i
  have h := congrArg (fun M : GL (Fin (m + 1)) (Cinf E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) i)
    (show Matrix.GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) =
      Matrix.GeneralLinearGroup.map (pInf E) g by rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul])
  exact h

theorem uInt_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  intro E _ _ _ m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hint hS hloc hΦ hNφ hNφ' hKφ hKφ' hWφ hWφ' x g hg
  have hWp : ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ p = b p ∧ GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    have h0 : GlobalTheory.JSW.tl ϖ (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) = 1 := by simp [GlobalTheory.JSW.tl]
    have e1 := hWφ 0 (by simp) p hp
    have e2 := hWφ' 0 (by simp) p hp
    rw [h0, mul_one] at e1 e2
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one] at e1 e2
    exact ⟨e1, e2⟩
  have hnorm : ∀ u : GA E (m + 1), ‖GlobalTheory.JSW.psiN u‖ = 1 := fun u => Circle.norm_coe _
  have hcc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z z' : ℂ, c * z * conj (c * z') = z * conj z' := by
    intro c hc z z'
    rw [map_mul]
    have : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    calc c * z * (conj c * conj z') = (c * conj c) * (z * conj z') := by ring
      _ = _ := by rw [this, one_mul]
  have hzero : ∀ F F' : GA E (m + 1) → ℂ, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 → GlobalTheory.ZEul.uInt F F' Φ N 0 g = 0 := by
    intro F F' h
    rcases h with h | h <;> simp only [GlobalTheory.ZEul.uInt, h, mul_zero, zero_mul]
  have hdec : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
        g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ ∧
        GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ φ Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    intro h1 h2
    obtain ⟨u, hu, p, hp, κ, hκ, he⟩ := GlobalTheory.T.mirabolicCell_decomposition_lastRow E m S J hJ N hS Φ hΦ g hg h1 h2
    have k1 : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ κ hκ, hNφ u hu, (hWp p hp).1]
    have k2 : GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ' κ hκ, hNφ' u hu, (hWp p hp).2]
    refine ⟨u, hu, p, hp, κ, hκ, he, ?_, ?_, ?_⟩ <;>
      simp only [GlobalTheory.ZEul.uInt, k1, k2, hcc _ (hnorm u), GlobalTheory.ZEul.detPow_zero, Complex.ofReal_one, mul_one]
  have h12 : GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g := by
    by_cases h0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
    · rw [hzero _ _ h0, hzero _ _ h0, hzero _ _ h0]; exact ⟨rfl, rfl⟩
    push_neg at h0
    obtain ⟨-, -, p, -, -, -, -, e1, e2, e3⟩ := hdec h0.1 h0.2
    rw [e1, e2, e3]; exact ⟨rfl, rfl⟩
  refine ⟨h12.1, h12.2, fun l => ?_⟩

  have hyt := GlobalTheory.ZEul.pInf_lastRow_tl_mul E m ϖ l.1 g
  obtain ⟨hind1, hind2⟩ := GlobalTheory.T.lastRowCongruenceIndicator_diagonalUniformizer_mul E m S ϖ hϖ N hint hloc l g hg
  have hdt := GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul E (m + 1) ϖ hϖ l.1 x g
  have hL : GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
      GlobalTheory.JSW.whit φ (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) : ℂ) := by
    simp only [GlobalTheory.ZEul.uInt]; rw [hyt]
  rw [hL]
  have hprod0 : ∀ w ∈ l.1.support, GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
      (fun i => (α' w i : ℂ)) x (l.1 w) = 0 →
      (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v) = 0 :=
    fun w hw h => Finset.prod_eq_zero hw h
  by_cases hz : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
  · have hIt : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0 := by
      rcases hz with h | h
      · exact Or.inl h
      · right
        by_cases hl : ∀ w, 0 ≤ l.1 w (Fin.last m)
        · rw [hind1 hl, h]
        · push_neg at hl; exact hind2 hl
    rw [hzero φ φ hz]
    rcases hIt with h | h <;> simp [h]
  push_neg at hz
  by_cases hlast : ∀ w, 0 ≤ l.1 w (Fin.last m)
  swap
  · push_neg at hlast
    obtain ⟨w, hw⟩ := hlast
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; simp at hw
    rw [hind2 ⟨w, hw⟩, hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨h1, -⟩; exact absurd (h1 (Fin.last m)) (not_le.2 hw)
  rw [hind1 hlast]
  obtain ⟨u, hu, p, hp, κ, hκ, he, -, e0, -⟩ := hdec hz.1 hz.2
  rw [e0]
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l.1 with ht
  have hcomm : p * t = t * p := GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off E (m + 1) S ϖ l p hp.1
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) :=
    (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 ((GlobalTheory.SmGL.mem_unipB (Ad E)).2 hu))
  have hσ : t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      (t * u * t⁻¹) * (p * t) * finGL E (m + 1) κ := by
    rw [mul_assoc t g, he, hcomm]; group
  have hW : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
      (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, F (g * finGL E (m + 1) κ) = F g) →
      F (t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN (t * u * t⁻¹) * F (p * t) := by
    intro F hN hK; rw [hσ, hK κ hκ, hN _ hu']
  rw [hW _ hNφ hKφ, hW _ hNφ' hKφ', hcc _ (hnorm _)]
  by_cases hanti : ∀ w, Antitone (l.1 w)
  swap
  · push_neg at hanti
    obtain ⟨w, hw⟩ := hanti
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    have hws : w ∈ l.1.support := Finsupp.mem_support_iff.2 hw0
    rw [GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone E m S J w hwS (hψ w hwS) ϖ (hϖ w) (GlobalTheory.JSW.whit φ) hNφ hKφ l.1 hw p (hp.1 w hwS), hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨-, h2⟩; exact hw h2
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w i => le_trans (hlast w) (hanti w (Fin.le_last i))
  obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
    ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
  have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
    rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
  have hsupp : l'.support = l.1.support := by
    ext w
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro h h0; apply h; rw [hl'app, h0]; rfl
    · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
  have htl : t = GlobalTheory.JSW.tl ϖ l' := GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal E (m + 1) ϖ l.1 l' hl'
  have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
    rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
  rw [hdt, htl, hWφ l' hsS p hp, hWφ' l' hsS p hp, hsupp]
  have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
      ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l' w)) *
        conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l' w))) *
      (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-x * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
      l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v := by
    rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hq : 0 < qV E w := Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hl'app]
    exact GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product (qV E w) hq (m + 1) _ _ x (l.1 w) (hnn w) (hanti w)
  rw [← key]
  simp only [map_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.ZEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCellStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.uInt_cell_eval
  | exact GlobalTheory.ZEul.uInt_cell_eval
  | (intros; apply GlobalTheory.ZEul.uInt_cell_eval <;> assumption)
end
