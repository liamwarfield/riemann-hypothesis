module

public import ReciprocityTheory.SemistableReduction.SemiDeg
public import Lemmata.GeneralBFactSecond.Imports
public import ReciprocityTheory.SemistableReduction.LatAll

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SemiContract
section -- merged from ReciprocityTheory.SemistableReduction.SemiContractC
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

theorem sc_scale {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (x : Fin r → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)

theorem sc_li_scale {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hv : LinearIndependent K v) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    LinearIndependent K (fun i => a i • v i) := by
  have := hv.units_smul (fun i => Units.mk0 (a i) (ha i))
  convert this using 1
  funext i
  simp [Units.smul_def]

theorem sc_kerfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by
  set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)
  choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0 := fun i h =>
    hd0 i (hinj (by rw [h, map_zero]))
  refine ⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L
    rw [algebraMap_smul]; exact hdL i
  · have h := (b0 i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [mulVec_smul, h, smul_zero]
  · exact sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
  · intro y hy
    have hy' : y ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hy
    have hsum := b0.sum_repr ⟨y, hy'⟩
    have hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K) := by
      calc y = ((⟨y, hy'⟩ : LinearMap.ker N.mulVecLin) : Fin r → K) := rfl
        _ = ((∑ i, b0.repr ⟨y, hy'⟩ i • b0 i : LinearMap.ker N.mulVecLin) : Fin r → K) := by
          rw [hsum]
        _ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
    rw [hsum']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hb : (b0 i : Fin r → K) =
        (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K)) := by
      rw [inv_smul_smul₀ (ha i)]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem sc_imfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ c : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin r → K,
      (∀ j, c j ∈ L) ∧ LinearIndependent K (fun j => N *ᵥ c j) := by
  set e := Module.finBasis K (LinearMap.range N.mulVecLin)
  have hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (e j).2
    exact ⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩
  choose y hy using hex
  choose d hd0 hdL using fun j => sc_scale L hL (y j)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0 := fun j h =>
    hd0 j (hinj (by rw [h, map_zero]))
  refine ⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d j) • y j ∈ L
    rw [algebraMap_smul]; exact hdL j
  · have := sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
    have heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j =>
        algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j := by
      funext j; simp [mulVec_smul, hy]
    rw [heq]; exact this

theorem sc_append_li {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0 := by
    have := congrArg N.mulVecLin hg
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_add (f := _), map_sum, map_smul, Matrix.mulVecLin_apply, hbN] using this
  have hc0 := Fintype.linearIndependent_iff.mp hc _ h1
  have hb0 : ∀ i, g (Fin.castAdd m i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa [hc0] using hg
  intro i
  exact Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i

theorem sc_rank_pos {K : Type} [Field K] [NumberField K] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (hN : N ≠ 0) : 0 < finrank K (LinearMap.range N.mulVecLin) := by
  refine Nat.pos_of_ne_zero fun h0 => hN ?_
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := LinearMap.toMatrix'_toLin' N
  rw [Matrix.toLin'_apply', h0, map_zero] at this
  exact this.symm

theorem sc_index {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (N : Matrix (Fin r) (Fin r) K)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) (hcL : ∀ j, c j ∈ L)
    (hbN : ∀ i, N *ᵥ b i = 0) (hker : ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).toAddSubgroup.relIndex
        (L.map (N.mulVecLin.restrictScalars (𝓞 K))).toAddSubgroup =
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex L.toAddSubgroup := by
  set f := N.mulVecLin.restrictScalars (𝓞 K) with hf
  have hfx : ∀ x, f x = N *ᵥ x := fun x => rfl
  have hspanb : Submodule.span K (Set.range b) ≤ LinearMap.ker N.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [hbN i]
  have hspanc : Submodule.span (𝓞 K) (Set.range c) ≤
      (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).comap f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, (hfx (c j)).symm⟩
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right (AddSubgroup.comap _ _),
    ← AddSubgroup.inf_relIndex_right (Submodule.toAddSubgroup _)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
    AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun (𝓞 K) |>.mp hx
    set z := ∑ j, a j • c j with hz
    have hzc : z ∈ Submodule.span (𝓞 K) (Set.range c) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hzL : z ∈ L := Submodule.sum_mem _ fun j _ => L.smul_mem _ (hcL j)
    have hfz : f (x - z) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hz, map_sum]
      simp only [map_smul]
      simp only [hfx] at ha ⊢
      rw [ha, sub_self]
    have hsat : x - z ∈ satSub L b := by
      refine ⟨L.sub_mem hxL hzL, ?_⟩
      exact hker _ (by rw [← hfx]; exact hfz)
    exact Submodule.mem_sup.mpr ⟨x - z, hsat, z, hzc, sub_add_cancel x z⟩
  · rintro ⟨hx, hxL⟩
    refine ⟨?_, hxL⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : f y = 0 := by
      have h := hspanb hy.2
      rw [LinearMap.mem_ker] at h
      exact h
    rw [map_add (f := _), hy0, zero_add]
    exact hspanc hz

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.SemiContractB
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

def embCols {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} (σ : K →+* ℂ)
    (v : ι → Fin r → K) : Matrix (Fin r) ι ℂ :=
  Matrix.of fun a i => σ (v i a)

theorem sc_gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embCols σ b)ᴴ * H * embCols σ b := by
  ext i j
  simp only [gramC, embCols, embVec, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem sc_gramX_eq {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embCols σ b)ᴴ * H * embCols σ c := by
  ext i j
  simp only [gramX, embCols, embVec, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem sc_col_mul {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K) (c : ι → Fin r → K) :
    embCols σ (fun j => N *ᵥ c j) = N.map σ * embCols σ c := by
  ext a j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [embCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem sc_col_inj {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] (σ : K →+* ℂ) {v : ι → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embCols σ v).mulVec := by
  classical
  let V : Matrix (Fin r) ι K := Matrix.of fun a i => v i a
  have hinj : Function.Injective (Matrix.toLin' V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ i, x i • v i = 0 := by
      funext a
      have := congrFun hx a
      simpa [V, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    funext i
    exact Fintype.linearIndependent_iff.mp hv x h0 i
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' V) (LinearMap.ker_eq_bot.mpr hinj)
  let W : Matrix ι (Fin r) K := LinearMap.toMatrix' h
  have hWV : W * V = 1 := by
    have := congrArg LinearMap.toMatrix' hh
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hV : embCols σ v = V.map σ := by ext a i; rfl
  have hWV' : W.map σ * V.map σ = 1 := by
    rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have h2 := congrArg (fun z => (W.map σ) *ᵥ z) hxy
  simp only [hV, Matrix.mulVec_mulVec, hWV', Matrix.one_mulVec] at h2
  exact h2

theorem sc_gram_lt {K : Type} [Field K] [NumberField K] {r k m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ u : Fin r → ℂ, u ≠ 0 → hq H (N.map σ *ᵥ u) < hq H u)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbc : LinearIndependent K (Fin.append b c)) (hb : ∀ i, N *ᵥ b i = 0)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) :
    0 < (gramC H σ (fun j => N *ᵥ c j)).det.re ∧
      (gramC H σ (fun j => N *ᵥ c j)).det.re < (quotGramC H σ b c).det.re := by
  classical
  have detlt : ∀ P Q : Matrix (Fin m) (Fin m) ℂ, P.PosDef → Q.PosDef → P.det.re < (P + Q).det.re := by
    intro P Q hP hQ
    have hPh := hP.isHermitian
    set U : Matrix (Fin m) (Fin m) ℂ := (hPh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
    have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hPh.eigenvectorUnitary.2
    have hspec : P = U * Matrix.diagonal (RCLike.ofReal ∘ hPh.eigenvalues) * star U := by
      have h := hPh.spectral_theorem
      rwa [Unitary.conjStarAlgAut_apply] at h
    rw [Matrix.star_eq_conjTranspose] at hspec hUU
    set Dh : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => ((Real.sqrt (hPh.eigenvalues i) : ℝ) : ℂ) with hDhdef
    have hDh : Dh * Dhᴴ = Matrix.diagonal (RCLike.ofReal ∘ hPh.eigenvalues) := by
      rw [hDhdef, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hP.eigenvalues_pos i).le, Function.comp_apply]
      rfl
    set T := U * Dh with hTdef
    have hTT : T * Tᴴ = P := by
      rw [hTdef, Matrix.conjTranspose_mul, hspec]
      calc U * Dh * (Dhᴴ * Uᴴ) = U * (Dh * Dhᴴ) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDh]
    have hPdet : P.det ≠ 0 := hP.det_pos.ne'
    have hTdet : IsUnit T.det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply hPdet
      rw [← hTT, Matrix.det_mul, h0, zero_mul]
    have hinjT : Function.Injective ((T⁻¹)ᴴ).mulVec := by
      intro x y hxy
      have h := congrArg (fun z => Tᴴ *ᵥ z) hxy
      simp only [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hTdet,
        Matrix.conjTranspose_one, Matrix.one_mulVec] at h
      exact h
    have hF : (T⁻¹ * Q * (T⁻¹)ᴴ).PosDef := by
      have h := hQ.conjTranspose_mul_mul_same hinjT
      rwa [Matrix.conjTranspose_conjTranspose] at h
    have hA : P + Q = T * (1 + T⁻¹ * Q * (T⁻¹)ᴴ) * Tᴴ := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTT]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTdet, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hTdet, Matrix.conjTranspose_one, Matrix.mul_one]
    have hdet : (P + Q).det = P.det * (1 + T⁻¹ * Q * (T⁻¹)ᴴ).det := by
      have e1 : (P + Q).det = T.det * (1 + T⁻¹ * Q * (T⁻¹)ᴴ).det * Tᴴ.det := by
        rw [hA, Matrix.det_mul, Matrix.det_mul]
      have e2 : P.det = T.det * Tᴴ.det := by
        rw [← Matrix.det_mul, hTT]
      rw [e1, e2]
      ring
    set F := T⁻¹ * Q * (T⁻¹)ᴴ with hFdef
    have hFh := hF.isHermitian
    set V : Matrix (Fin m) (Fin m) ℂ := (hFh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hV
    have hVV : V * star V = 1 := Unitary.mul_star_self_of_mem hFh.eigenvectorUnitary.2
    have hFs : F = V * Matrix.diagonal (RCLike.ofReal ∘ hFh.eigenvalues) * star V := by
      have h := hFh.spectral_theorem
      rwa [Unitary.conjStarAlgAut_apply] at h
    have h1F : (1 + F).det = ((∏ i, (1 + hFh.eigenvalues i) : ℝ) : ℂ) := by
      have e : 1 + F = V * Matrix.diagonal (fun i => ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * star V := by
        have hd : Matrix.diagonal (fun i => ((1 + hFh.eigenvalues i : ℝ) : ℂ)) =
            1 + Matrix.diagonal (RCLike.ofReal ∘ hFh.eigenvalues) := by
          rw [← Matrix.diagonal_one, Matrix.diagonal_add]
          congr 1
          funext i
          simp [Complex.ofReal_add]
        rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hVV, ← hFs]
      have hdV : V.det * (star V).det = 1 := by rw [← Matrix.det_mul, hVV, Matrix.det_one]
      rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      calc V.det * (∏ i, ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * (star V).det
          = (∏ i, ((1 + hFh.eigenvalues i : ℝ) : ℂ)) * (V.det * (star V).det) := by ring
        _ = _ := by rw [hdV, mul_one, Complex.ofReal_prod]
    have hμ : ∀ i, 0 < hFh.eigenvalues i := hF.eigenvalues_pos
    have hprod : 1 < ∏ i, (1 + hFh.eigenvalues i) := by
      have h := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := fun _ => (1 : ℝ))
        (g := fun i => 1 + hFh.eigenvalues i) (fun i _ => one_pos) (fun i _ => by linarith [hμ i])
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      simpa using h
    have hPpos : 0 < P.det.re := by
      have h := (Complex.lt_def.mp hP.det_pos).1
      simpa using h
    rw [hdet, h1F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact lt_mul_of_one_lt_right hPpos hprod
  set Bm := embCols σ b with hBm
  set Cm := embCols σ c with hCm
  set Nσ := N.map σ with hNσ
  have hE : ∀ (x : Fin k → ℂ) (z : Fin m → ℂ),
      embCols σ (Fin.append b c) *ᵥ Fin.append x z = Bm *ᵥ x + Cm *ᵥ z := by
    intro x z
    funext a
    simp only [hBm, hCm, Matrix.mulVec, dotProduct, embCols, Matrix.of_apply, Pi.add_apply, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
  have hEinj := sc_col_inj σ hbc
  have hBinj : Function.Injective Bm.mulVec := by
    intro x y hxy
    have h : Fin.append x (0 : Fin m → ℂ) = Fin.append y 0 := hEinj (by rw [hE, hE, hxy])
    funext i
    simpa using congrFun h (Fin.castAdd m i)
  have hH' : Hᴴ = H := hH.isHermitian
  have hGdef : gramC H σ b = Bmᴴ * H * Bm := sc_gramC_eq H σ b
  have hXbc : gramX H σ b c = Bmᴴ * H * Cm := sc_gramX_eq H σ b c
  have hXcb : gramX H σ c b = Cmᴴ * H * Bm := sc_gramX_eq H σ c b
  have hCC : gramC H σ c = Cmᴴ * H * Cm := sc_gramC_eq H σ c
  have hGpd : (gramC H σ b).PosDef := by
    rw [hGdef]
    exact hH.conjTranspose_mul_mul_same hBinj
  have hGu : IsUnit (gramC H σ b).det := isUnit_iff_ne_zero.mpr hGpd.det_pos.ne'
  set Y := (gramC H σ b)⁻¹ * gramX H σ b c with hYdef
  have hY : Bmᴴ * H * Bm * Y = Bmᴴ * H * Cm := by
    rw [hYdef, ← hGdef, Matrix.mul_nonsing_inv_cancel_left _ _ hGu, hXbc]
  set C' := Cm - Bm * Y with hC'def
  have hquot : quotGramC H σ b c = C'ᴴ * H * C' := by
    rw [quotGramC, Matrix.mul_assoc (gramX H σ c b), ← hYdef, hCC, hXcb]
    have hY' : Bmᴴ * (H * (Bm * Y)) = Bmᴴ * (H * Cm) := by simpa only [Matrix.mul_assoc] using hY
    simp only [hC'def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hY', sub_self, sub_zero]
    abel
  have hC'inj : Function.Injective C'.mulVec := by
    intro x y hxy
    have h0 : C' *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h0' : Cm *ᵥ (x - y) - Bm *ᵥ (Y *ᵥ (x - y)) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]
      exact h0
    have h1 : embCols σ (Fin.append b c) *ᵥ Fin.append (-(Y *ᵥ (x - y))) (x - y) =
        embCols σ (Fin.append b c) *ᵥ Fin.append 0 0 := by
      rw [hE, hE, Matrix.mulVec_neg, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, neg_add_eq_sub]
      exact h0'
    have h2 := hEinj h1
    funext j
    have h3 := congrFun h2 (Fin.natAdd k j)
    simpa [sub_eq_zero] using h3
  have hNB : Nσ * Bm = 0 := by
    rw [hNσ, hBm, ← sc_col_mul σ N b]
    ext a j
    simp [embCols, hb j]
  have hNC : Nσ * C' = embCols σ (fun j => N *ᵥ c j) := by
    rw [hC'def, Matrix.mul_sub, ← Matrix.mul_assoc, hNB, Matrix.zero_mul, sub_zero, hNσ, hCm, sc_col_mul]
  set K := Nσᴴ * H * Nσ with hK
  have hPq : gramC H σ (fun j => N *ᵥ c j) = C'ᴴ * K * C' := by
    rw [sc_gramC_eq, ← hNC, Matrix.conjTranspose_mul, hK]
    simp only [Matrix.mul_assoc]
  have hPqpd : (gramC H σ (fun j => N *ᵥ c j)).PosDef := by
    rw [sc_gramC_eq]
    exact hH.conjTranspose_mul_mul_same (sc_col_inj σ hc)
  have hMpd : (H - K).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hH', Matrix.mul_assoc]
    · have hdot : star x ⬝ᵥ ((H - K) *ᵥ x) =
          star x ⬝ᵥ (H *ᵥ x) - star (Nσ *ᵥ x) ⬝ᵥ (H *ᵥ (Nσ *ᵥ x)) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, hK, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec (star x) Nσᴴ, ← Matrix.star_mulVec]
      rw [hdot]
      have h1 := hN x hx
      simp only [hq] at h1
      have him1 : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
        have h := (Complex.lt_def.mp (hH.dotProduct_mulVec_pos hx)).2
        rw [Complex.zero_im] at h
        exact h.symm
      have him2 : (star (Nσ *ᵥ x) ⬝ᵥ (H *ᵥ (Nσ *ᵥ x))).im = 0 := by
        by_cases hy : Nσ *ᵥ x = 0
        · simp [hy]
        · have h := (Complex.lt_def.mp (hH.dotProduct_mulVec_pos hy)).2
          rw [Complex.zero_im] at h
          exact h.symm
      rw [Complex.lt_def]
      refine ⟨?_, ?_⟩
      · rw [Complex.sub_re, Complex.zero_re]
        linarith
      · rw [Complex.sub_im, him1, him2, Complex.zero_im, sub_zero]
  have hEpd := hMpd.conjTranspose_mul_mul_same hC'inj
  have hsplit : quotGramC H σ b c = gramC H σ (fun j => N *ᵥ c j) + C'ᴴ * (H - K) * C' := by
    rw [hquot, hPq, Matrix.mul_sub C'ᴴ H K, Matrix.sub_mul]
    abel
  refine ⟨?_, ?_⟩
  · have h := (Complex.lt_def.mp hPqpd.det_pos).1
    simpa using h
  · rw [hsplit]
    exact detlt _ _ hPqpd hEpd

end ReciprocityTheory.MultiplicativeHeights
end

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Module

theorem semiContract_holds (hP : SemiPointStatement) (hD : DegAddStatement) :
    SemistableStatement := by
  intro K _ _ r S L hLat hSD
  obtain ⟨M, hM⟩ := hP K r S L hLat hSD
  refine ⟨M, hM, fun N hNL hN => ?_⟩
  by_contra hN0
  obtain ⟨b, hbL, hbN, hbli, hker⟩ := sc_kerfam L hLat.2 N
  obtain ⟨c, hcL, hcli⟩ := sc_imfam L hLat.2 N
  have hm := sc_rank_pos N hN0
  have hli := sc_append_li N b c hbN hbli hcli
  have hkm : finrank K (LinearMap.ker N.mulVecLin) + finrank K (LinearMap.range N.mulVecLin) = r := by
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at this
    omega
  have hspan : Submodule.span K (Set.range (Fin.append b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun, hkm])
  have happL : ∀ i, Fin.append b c i ∈ L := by
    intro i
    induction i using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hbL i
    | right j => rw [Fin.append_right]; exact hcL j
  have hspanL : ∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
    intro x _; rw [hspan]; exact Submodule.mem_top

  have hdegL := hM.1 _ (Fin.append b c) ⟨happL, hli, hspanL⟩
  have hdegK := hM.2 (satSub L b) inf_le_left _ b
    ⟨fun i => ⟨hbL i, Submodule.subset_span ⟨i, rfl⟩⟩, hbli, fun x hx => hx.2⟩
  have hadd := hD K r _ _ M.H L b c M.posDef hLat.1 hbL hcL hli hspanL

  set NL := L.map (N.mulVecLin.restrictScalars (𝓞 K)) with hNLdef
  have hNLle : NL ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNL x hx
  have hNspan : ∀ y, N *ᵥ y ∈ Submodule.span K (Set.range fun j => N *ᵥ c j) := by
    intro y
    have hy : y ∈ Submodule.span K (Set.range (Fin.append b c)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction i using Fin.addCases with
      | left i => rw [Fin.append_left, hbN i]; exact Submodule.zero_mem _
      | right j => rw [Fin.append_right]; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hdegN := hM.2 NL hNLle _ (fun j => N *ᵥ c j)
    ⟨fun j => ⟨c j, hcL j, rfl⟩, hcli, by rintro _ ⟨x, _, rfl⟩; exact hNspan x⟩

  have hidx := sc_index L N b c hcL hbN hker
  have hσ := fun σ => sc_gram_lt hm (M.H σ) (M.posDef σ) σ N (hN σ) b c hli hbN hcli
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramC (M.H σ) σ fun j => N *ᵥ c j).det.re <
      ∑ σ : K →+* ℂ, Real.log (quotGramC (M.H σ) σ b c).det.re :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun σ _ =>
      Real.log_lt_log (hσ σ).1 (hσ σ).2
  have hlt : quotDeg M.H L b c < latDeg M.H NL (fun j => N *ᵥ c j) := by
    rw [quotDeg, latDeg, ← hidx]
    linarith
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
