module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartSchurComplementExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem fst_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : (idemS S : Ad E).1 = 1 := rfl

open Classical in
theorem pLoc_pFin_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w (pFin E (idemS S)) = if w ∈ S then 1 else 0 := rfl

theorem prS_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        idemS S * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem prO_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prO S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        (1 - idemS S) * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem pLoc_pFin_idemS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (pFin E (idemS S)) = 0 := by
  classical
  rw [pLoc_pFin_idemS]; simp [hw]

theorem pLoc_pFin_one_sub_idemS_of_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    pLoc E w (pFin E (1 - idemS S)) = 0 := by
  classical
  rw [map_sub, map_sub, map_one, map_one, pLoc_pFin_idemS]; simp [hw]

theorem one_sub_idemS_mul_eq_zero {S : Finset (HeightOneSpectrum (𝓞 E))} {x : Ad E}
    (h : ∀ w ∉ S, pLoc E w (pFin E x) = 0) : (1 - idemS S) * x = 0 := by
  refine Prod.ext ?_ (Subtype.ext (funext fun w => ?_))
  · change (1 - (idemS S : Ad E).1) * x.1 = 0
    rw [fst_idemS, sub_self, zero_mul]
  · change pLoc E w (pFin E ((1 - idemS S) * x)) = pLoc E w (pFin E 0)
    rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hw : w ∈ S
    · rw [pLoc_pFin_one_sub_idemS_of_mem hw, zero_mul]
    · rw [h w hw, mul_zero]

theorem pLoc_pFin_one_apply (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (i j : Fin a) :
    pLoc E w (pFin E ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem pLoc_pFin_apply_of_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) (i j : Fin a) :
    pLoc E w (pFin E ((g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  have h := congrArg (fun x : GL (Fin a) (w.adicCompletion E) => (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (hg w hw)
  exact h

theorem one_sub_idemS_mul_sub_eq_zero {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (i j : Fin a) :
    (1 - idemS S) * ((g : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0 :=
  one_sub_idemS_mul_eq_zero fun w hw => by
    rw [map_sub, map_sub, pLoc_pFin_apply_of_mem_supS hg hw, pLoc_pFin_one_apply, sub_self]

theorem prS_prO_supS (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun g w hw => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prS_apply]
    linear_combination (-1 : Ad E) * one_sub_idemS_mul_sub_eq_zero hg i j
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prO_apply]
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
    linear_combination (one_sub_idemS_mul_sub_eq_zero hg i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (pFin E ((prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
    rw [prS_apply, map_add (f := _), map_sub, map_mul, map_mul, map_add (f := _), map_sub, map_mul, map_mul,
      pLoc_pFin_idemS_of_not_mem hw, pLoc_pFin_one_apply]
    ring

end GlobalTheory.SchurExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlacesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_supS) | (exact GlobalTheory.SchurExt.prS_prO_supS) | (intros; apply GlobalTheory.SchurExt.prS_prO_supS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGLStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_mul_infGL) | (exact GlobalTheory.SchurExt.prS_prO_mul_infGL) | (intros; apply GlobalTheory.SchurExt.prS_prO_mul_infGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := by
  first | (exact @GlobalTheory.SchurExt.schurF_blockGL) | (exact GlobalTheory.SchurExt.schurF_blockGL) | (intros; apply GlobalTheory.SchurExt.schurF_blockGL  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem blockGL_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  intro E _ _ m r S h hh w hw
  have hmap : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
      (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
        (Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) h) :=
    Units.ext (GroundTheory.Automorphic.FourierWhittaker.map_blockMat _ _ (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))
  rw [hmap, hh w hw, map_one]

end GlobalTheory.SchurExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlacesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.blockGL_mem_supS) | (exact GlobalTheory.SchurExt.blockGL_mem_supS) | (intros; apply GlobalTheory.SchurExt.blockGL_mem_supS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section
namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem prS_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prS S a (finGL E a k) = finGL E a (prSf S a k) := by
  have hI : ∀ y, idemS S * sFin E y = sFin E (idemSf S * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - idemSf S * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + idemSf S * k i j)
  generalize idemS S = I at hI ⊢
  generalize idemSf S = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem prO_finGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (k : GL (Fin a) (Af E)) :
    prO S a (finGL E a k) = finGL E a (prOf S a k) := by
  have hI : ∀ y, (1 - idemS S) * sFin E y = sFin E ((1 - idemSf S) * y) := fun y => Prod.ext (mul_zero _) rfl
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
        + sFin E (k i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
      - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)
      + sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - (1 - idemSf S) * (1 : Matrix (Fin a) (Fin a) (Af E)) i j
        + (1 - idemSf S) * k i j)
  generalize (1 - idemS S) = I at hI ⊢
  generalize (1 - idemSf S) = J at hI ⊢
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_sub, map_add (f := _), mul_add, mul_sub, hI, sub_zero,
    zero_sub, zero_add] <;> ring

theorem continuous_cornerGL_idemHom (a : ℕ) (e : Af E) (he : IsIdempotentElem e) :
    Continuous (cornerGL a (idemHom e he)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (idemHom e he) 1 + matN a (idemHom e he) x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_const.mul continuous_id : Continuous fun x : Af E => e * x).comp
      ((continuous_apply j).comp (continuous_apply i))

theorem continuous_prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prSf S a) :=
  continuous_cornerGL_idemHom a _ _

theorem continuous_prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : Continuous (prOf S a) :=
  continuous_cornerGL_idemHom a _ _

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.eventually_prS_prO_finGL :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  intro E _ _ a S V V' hV hV'
  have h1 := (continuous_prSf S a).tendsto 1
  have h2 := (continuous_prOf S a).tendsto 1
  rw [map_one] at h1 h2
  filter_upwards [h1 hV, h2 hV'] with k hk hk'
  exact ⟨⟨_, hk, prS_finGL S a k⟩, _, hk', prO_finGL S a k⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_adelicGLProjections_finite_near_one : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  first | (exact @GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (exact GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (intros; apply GlobalTheory.SchurExt.eventually_prS_prO_finGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem coe_cornerGL_idemHom_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (1 : Matrix (Fin a) (Fin a) R) i j - e * (1 : Matrix (Fin a) (Fin a) R) i j + e * (g : Matrix (Fin a) (Fin a) R) i j :=
  rfl

theorem cornerGL_idemHom_mem_NA {a : ℕ} (e : Ad E) (he : IsIdempotentElem e) {u : GA E a}
    (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := a)) : cornerGL a (idemHom e he) u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_cornerGL_idemHom_apply, hu.1 i j hij, Matrix.one_apply_ne (ne_of_lt hij).symm]
    ring
  · rw [coe_cornerGL_idemHom_apply, hu.2 i, Matrix.one_apply_eq]
    ring

theorem cornerGL_idemHom_add_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) {i j : Fin a} (hij : i ≠ j) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j +
      ((cornerGL a (idemHom (1 - e) he.one_sub) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (g : Matrix (Fin a) (Fin a) R) i j := by
  rw [coe_cornerGL_idemHom_apply, coe_cornerGL_idemHom_apply, Matrix.one_apply_ne hij]
  ring

theorem superDiag_cornerGL_idemHom_add {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) :
    GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom e he) g) +
      GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom (1 - e) he.one_sub) g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val = i.val + 1 := (Finset.mem_filter.1 hj).2
  have hij : i ≠ j := fun h => by rw [h] at hj'; omega
  exact cornerGL_idemHom_add_apply e he g hij

theorem prS_prO_NA_psiN :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
      ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧
        GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  intro E _ _ _ a S u hu
  refine ⟨cornerGL_idemHom_mem_NA _ _ hu, cornerGL_idemHom_mem_NA _ _ hu, ?_⟩
  unfold GlobalTheory.JSW.psiN
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  exact congrArg (fun x => ((GroundTheory.Global.adelicChar E x : Circle) : ℂ))
    (superDiag_cornerGL_idemHom_add (idemS S) (isIdempotentElem_idemS S) u)

end GlobalTheory.SchurExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericCharStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_NA_psiN) | (exact GlobalTheory.SchurExt.prS_prO_NA_psiN) | (intros; apply GlobalTheory.SchurExt.prS_prO_NA_psiN  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExtCpt

open Matrix

section Mat

variable {R : Type} [CommRing R] {m r : ℕ}

theorem eqv_symm_inl_val (a : Fin (m + 1)) : (((eqv m r).symm (Sum.inl a)) : ℕ) = a := by simp [eqv]

theorem eqv_symm_inr_val (b : Fin (r + 1)) : (((eqv m r).symm (Sum.inr b)) : ℕ) = m + 1 + b := by simp [eqv]

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := by
  unfold unblk; exact Matrix.submatrix_mul_equiv P Q _ _ _

theorem unblk_one : (unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R)) = 1 := by
  unfold unblk; exact Matrix.submatrix_one_equiv _

theorem fromBlocks_decomp {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (C : Matrix (Fin b) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (uA cA : Matrix (Fin a) (Fin a) R)
    (uD cD : Matrix (Fin b) (Fin b) R) (hD : IsUnit D.det) (hA : uA * cA = A - B * D⁻¹ * C) (hD' : uD * cD = D) :
    fromBlocks uA (B * D⁻¹ * uD) 0 uD * fromBlocks cA 0 (cD * (D⁻¹ * C)) cD = fromBlocks A B C D := by
  rw [fromBlocks_multiply]
  have h1 : B * D⁻¹ * uD * (cD * (D⁻¹ * C)) = B * D⁻¹ * C := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, ← Matrix.mul_assoc uD, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  have h2 : B * D⁻¹ * uD * cD = B := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, hD', Matrix.nonsing_inv_mul_cancel_right _ _ hD]
  have h3 : uD * (cD * (D⁻¹ * C)) = C := by
    rw [← Matrix.mul_assoc, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, h3, hD', hA, sub_add_cancel]

end Mat

variable {E : Type} [Field E] [NumberField E] {m r : ℕ}

def gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : GA E (m + r + 1 + 1) where
  val := unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d)
  inv := unblk (fromBlocks ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0
    (-(Y * ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))) ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))
  val_inv := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.mul_inv, Matrix.mul_neg, Matrix.mul_assoc,
      add_neg_cancel, neg_zero]
  inv_val := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.inv_mul, Matrix.neg_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) (d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)),
      Matrix.mul_one, Matrix.one_mul, neg_add_cancel]

theorem coe_gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) :
    ((gEl a d Y : GA E (m + r + 1 + 1)) : Matrix _ _ (Ad E)) =
      unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d) := rfl

theorem continuous_gEl :
    Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2 := by
  rw [Units.continuous_iff]
  have ha : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_val.comp continuous_fst
  have ha' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_coe_inv.comp continuous_fst
  have hd : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1 : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  have hd' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  have hY : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have h0 : Continuous fun _ : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      (0 : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) := continuous_const
  constructor
  · exact (Continuous.matrix_fromBlocks ha h0 (hd.matrix_mul hY) hd).matrix_submatrix _ _
  · exact (Continuous.matrix_fromBlocks ha' h0 (hY.matrix_mul ha').neg hd').matrix_submatrix _ _

theorem mem_NA_of_blocks (uA : GA E (m + 1)) (uD : GA E (r + 1)) (huA : uA ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)))
    (huD : uD ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1))) (X : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) (u : GA E (m + r + 1 + 1))
    (hu : (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
      unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) X 0 (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))) :
    u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> rw [hu]
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    obtain ⟨y, rfl⟩ := (eqv m r).symm.surjective j
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rw [Fin.lt_iff_val_lt_val] at hij
    rcases x with a | a <;> rcases y with b | b
    · simp only [eqv_symm_inl_val] at hij
      rw [fromBlocks_apply₁₁]; exact huA.1 a b (Fin.lt_iff_val_lt_val.2 hij)
    · simp only [eqv_symm_inl_val, eqv_symm_inr_val] at hij
      exact absurd hij (by have := a.isLt; omega)
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    · simp only [eqv_symm_inr_val] at hij
      rw [fromBlocks_apply₂₂]; exact huD.1 a b (Fin.lt_iff_val_lt_val.2 (by omega))
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rcases x with a | a
    · rw [fromBlocks_apply₁₁]; exact huA.2 a
    · rw [fromBlocks_apply₂₂]; exact huD.2 a

variable [_root_.NumberField.IsTotallyComplex E]

def adOf (z : (Fin (r + 1) → Fin (m + 1) → Cinf E) × (Fin (r + 1) → Fin (m + 1) → Af E)) :
    Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) :=
  fun i j => ((infEq E (z.1 i j), z.2 i j) : InfiniteAdeleRing E × Af E)

theorem continuous_adOf : Continuous (adOf (E := E) (m := m) (r := r)) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_infEq E).comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

end GlobalTheory.SchurExtCpt


open Matrix GlobalTheory.SchurExtCpt in
theorem GlobalTheory.SchurExtCpt.exists_compact_support : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := by
  intro E _ _ _ m r S β b₁ χ ⟨Cβ, hCβ, hβ⟩ ⟨C₁, hC₁, hb⟩ hχ
  let K : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) := adOf ''
    (tsupport χ ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
  have hK : IsCompact K := (hχ.isCompact.prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles E)).image continuous_adOf
  refine ⟨(fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2) ''
    (Cβ ×ˢ C₁ ×ˢ K), (hCβ.prod (hC₁.prod hK)).image continuous_gEl, ?_⟩
  intro p hp hF
  by_cases hD : IsUnit (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  swap
  · exact absurd (by unfold schurF; rw [if_neg hD]) hF
  unfold schurF at hF
  rw [if_pos hD] at hF
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := (mul_ne_zero_iff.1 hF) |>.imp (mul_ne_zero_iff.1) id |>.imp (fun h => h.imp mul_ne_zero_iff.1 id) id

  have hdet : IsUnit (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
    haveI : Invertible (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).toBlocks₂₂ :=
      Matrix.invertibleOfIsUnitDet _ hD
    have he : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det =
        (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det *
          (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      change (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det = _
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))),
        Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
      rfl
    have hu := Matrix.isUnits_det_units p
    rw [he] at hu
    exact isUnit_of_mul_isUnit_right hu

  have hsup : mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    intro w hw
    have hpw := congrArg Units.val (hp.1 w hw)
    apply Units.ext
    change (mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1
    change (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1 at hpw
    rw [coe_mkGL hdet]
    have hbl : (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        blk ((p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E))) from rfl, hpw]
      exact Matrix.submatrix_one_equiv _
    have hA : (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₁ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
    have hB : (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 0 := by
      rw [show (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₂ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
    unfold Scof
    rw [Matrix.map_sub _ (map_sub ((pLoc E w).comp (pFin E))), Matrix.map_mul, Matrix.map_mul, hA, hB]
    simp
  obtain ⟨uA, huA, hcA⟩ := hβ _ hsup h2
  obtain ⟨uD, huD, hcD⟩ := hb _ h3

  have hY : Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) ∈ K := by
    unfold chiF at h4
    obtain ⟨h41, h42⟩ := mul_ne_zero_iff.1 h4
    have hint : ∀ i j, pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hc
      rw [if_neg hc] at h42
      exact h42 rfl
    refine ⟨(fun i j => pInf E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j),
      fun i j => pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)), ⟨subset_tsupport _ ?_, ?_⟩, ?_⟩
    · intro h
      apply h41
      rw [h]
      simp
    · simp only [Set.mem_univ_pi]
      exact fun i j => hint i j
    · funext i j
      refine ad_ext ?_ rfl
      show (infEq E).symm (infEq E _) = _
      exact RingEquiv.symm_apply_apply _ _
  refine ⟨p * (gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))⁻¹, ?_, ⟨(_, _, _), ⟨hcA, hcD, hY⟩, ?_⟩⟩
  · refine mem_NA_of_blocks uA uD huA huD (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
      (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) _ ?_
    have hpU : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
        unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
          (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) 0
          (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) *
        ((gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) : GA E (m + r + 1 + 1)) :
            Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := by
      rw [coe_gEl, unblk_mul]
      conv_lhs => rw [← unblk_blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      congr 1
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))]
      refine (fromBlocks_decomp _ _ _ _ _ _ _ _ hD ?_ ?_).symm
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hdet]; try rfl
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hD]; try rfl
    rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul]
    exact hpU
  · rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_whittaker_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  first | (exact @GlobalTheory.SchurEquiv.schurF_equivariant) | (exact GlobalTheory.SchurEquiv.schurF_equivariant) | (intros; apply GlobalTheory.SchurEquiv.schurF_equivariant <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := by
  first
  | exact @GlobalTheory.SchurExtCpt.exists_compact_support
  | exact GlobalTheory.SchurExtCpt.exists_compact_support
  | (intros; apply GlobalTheory.SchurExtCpt.exists_compact_support <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_smooth_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  first | (exact @GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (exact GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (intros; apply GlobalTheory.SchurExt.schurF_mul_finGL_eq <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.SchurExt
open scoped Topology

namespace GlobalTheory.SchurExt.Parts

theorem L_glob : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := GlobalTheory.T.exists_smooth_whittakerBump_adelicGL

theorem L_equiv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := GlobalTheory.Tx.schur_function_whittaker_equivariant

theorem L_cpt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent

theorem L_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := GlobalTheory.Tx.schur_function_smooth_right_invariant

theorem L_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := GlobalTheory.T.contDiffOn_chart_schurComplementExtension

theorem L_block : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply

theorem L_projNA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar

theorem L_projSupS : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces

theorem L_projInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL

theorem L_projFin : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := GlobalTheory.T.eventually_adelicGLProjections_finite_near_one

theorem L_blockSupS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.Parts
open GlobalTheory.SchurExt.Parts

theorem GlobalTheory.SchurExt.exists_ext : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  intro E _ _ _ m r S β hβN hβC hβU hβS
  obtain ⟨b₁, h1one, h1N, h1C, h1U, h1S⟩ := L_glob E r
  obtain ⟨Φ, hΦ1, hΦN, -, ⟨UΦ, hUΦo, hUΦ⟩, -⟩ := GlobalTheory.WhitBump.exists_bump E (m + r + 1) S
  let f : ContDiffBump (0 : Fin (r + 1) → Fin (m + 1) → Cinf E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC, hCp⟩ := L_cpt E m r S β b₁ f hβC h1C f.hasCompactSupport
  obtain ⟨W, hW, hWk⟩ := L_inv E m r S β b₁ f hβU hβC h1U h1C
  refine ⟨extB S β b₁ f Φ, ?_, ⟨C, hC, ?_⟩, ?_, ?_, ?_⟩
  · intro u hu g
    obtain ⟨h1, h2, h3⟩ := L_projNA E (m + r + 1 + 1) S u hu
    simp only [extB, map_mul]
    rw [L_equiv E m r β b₁ f hβN h1N _ h1, hΦN _ h2, ← h3]
    ring
  · intro p hp hne
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 p hp.1
    refine hCp p hp fun h0 => hne ?_
    simp only [extB, e1, e2, h0, zero_mul]
  · let U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)) :=
      { carrier := {k | ∀ g, extB S β b₁ f Φ (g * finGL E _ k) = extB S β b₁ f Φ g}
        mul_mem' := fun {a b} ha hb g => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, ← mul_assoc, hb, ha]
        one_mem' := fun g => by simp only [map_one, mul_one]
        inv_mem' := fun {a} ha g => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          have := ha (g * finGL E _ a⁻¹)
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
          exact this.symm }
    refine ⟨U, Subgroup.isOpen_of_mem_nhds U (g := 1) ?_, fun u hu g => hu g⟩
    have hV' : (UΦ : Set _) ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)) := hUΦo.mem_nhds UΦ.one_mem
    filter_upwards [L_projFin E _ S W _ hW hV'] with k hk
    obtain ⟨⟨k', hk'W, hk'⟩, ⟨k'', hk''V, hk''⟩⟩ := hk
    intro g
    simp only [extB, map_mul, hk', hk'']
    rw [hWk k' hk'W (hk' ▸ (L_projSupS E _ S).2 _) _ ((L_projSupS E _ S).2 g), hUΦ k'' hk''V]
  · intro g
    have hs := (L_smooth E m r β b₁ f hβS h1S h1C f.contDiff (prS S _ g)).mul
      (contDiffOn_const (c := Φ (prO S _ g)))
    refine hs.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    obtain ⟨e1, e2⟩ := L_projInf E _ S g hx'.unit
    simp only [chart, dif_pos hx', extB, e1, e2]
  · intro h hh
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 _ (L_blockSupS E m r S h hh)
    have hf0 : f 0 = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    simp only [extB, e1, e2, hΦ1, mul_one, L_block, h1one, hf0, Complex.ofReal_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext) | (exact GlobalTheory.SchurExt.exists_ext) | (intros; apply GlobalTheory.SchurExt.exists_ext <;> assumption)
end
