module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Partial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.BlkMulVecCat

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.AdelClassFinOfSvReal
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorGramDet
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section GD

variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem gd_qsmul (q : ℚ) (x : Fin m → E) : q • x = ((q : E)) • x := by
  ext i
  simp [Rat.smul_def]

theorem gd_star_rat (q : ℚ) : star ((q : E)) = (q : E) := by
  first
    | exact star_ratCast q
    | simpa [starRingEnd_apply] using map_ratCast (starRingEnd E) q

def gdLeft (y : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun x := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' x x' := by rw [hform_add_left', map_add (f := _)]
  map_smul' q x := by
    rw [gd_qsmul, hform_smul_left', gd_star_rat, RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul,
      smul_eq_mul]

def gdRight (x : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun y := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' y y' := by rw [hform_add_right', map_add (f := _)]
  map_smul' q y := by
    rw [gd_qsmul, hform_smul_right', RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul, smul_eq_mul]

theorem gd_int_smul (c : ℤ) (x : Fin m → E) : ((c : E)) • x = ((c : ℚ)) • x := by
  rw [gd_qsmul, Rat.cast_intCast]

end GD

theorem successive_vector_gram_det : SvGramDet := by
  classical
  intro F E _ _ _ _ _ _ cm m d δ hd hδ hcod p hp e hli he hspan
  simp only [Lat, Set.mem_setOf_eq] at hp
  obtain ⟨hJh, hJdet, -, -, hMint, hMdual⟩ := hp
  set J := p.1 with hJdef
  set M := p.2 with hMdef
  have hO : ∀ b : E, b ∈ (algebraMap (𝓞 E) E).range → star b ∈ (algebraMap (𝓞 E) E).range := by
    intro b hb
    obtain ⟨β, rfl⟩ := RingHom.mem_range.mp hb
    have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E β)) :=
      IsIntegral.map (starRingEnd E).toIntAlgHom β.isIntegral_coe
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint)
  have F1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hsingle : ∀ (i : Fin m) (v : Fin m → E), hform (starRingEnd E) J (Pi.single i 1) v = (J *ᵥ v) i := by
    intro i v
    rw [F1]
    have hs : (fun a => starRingEnd E ((Pi.single i (1 : E) : Fin m → E) a)) = Pi.single i 1 := by
      funext a
      by_cases h : a = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    rw [hs]
    first
      | rw [single_dotProduct, one_mul]
      | simp [dotProduct, Pi.single_apply]
  have hnd : ∀ y : Fin m → E, (∀ x, hform (starRingEnd E) J x y = 0) → y = 0 := by
    intro y hy
    have hJy : J *ᵥ y = 0 := by
      funext i
      rw [← hsingle, Pi.zero_apply]
      exact hy _
    have h6 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec y J⁻¹ J, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJdet),
        Matrix.one_mulVec]
    rw [h6, hJy, Matrix.mulVec_zero]
  have htr : ∀ z : E, (∀ b : E, Algebra.trace ℚ E (b * z) = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz z⁻¹
    rw [inv_mul_cancel₀ hne, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one, Nat.cast_eq_zero] at h1
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne' h1
  have hRt : ∀ x y, gdRight J x y = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have hLt : ∀ x y, gdLeft J y x = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have Br : ∀ (x : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J x (∑ k, q k • e k)) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J x (e k)) := by
    intro x q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hRt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hRt]
  have Bl : ∀ (y : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J (∑ k, q k • e k) y) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J (e k) y) := by
    intro y q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hLt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hLt]
  have hGe : ∀ i j, gramTr J e i j = Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j)) :=
    fun i j => rfl
  have hdetG : (gramTr J e).det ≠ 0 := by
    rcases isEmpty_or_nonempty (Fin (m * Module.finrank ℚ E)) with hE | hE
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Module.finrank ℚ (Fin m → E) := by
      rw [Fintype.card_fin]
      first
        | simp [Module.finrank_pi_fintype]
        | rw [Module.finrank_pi_fintype]; simp
    let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbs : ∀ i, bs i = e i := fun i => by simp [bs]
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv0, hv⟩
    have hy : ∑ j, v j • e j = 0 := by
      apply hnd
      intro x
      apply htr
      intro b
      have e1 : b * hform (starRingEnd E) J x (∑ j, v j • e j) =
          hform (starRingEnd E) J (star b • x) (∑ j, v j • e j) := by
        rw [hform_smul_left', star_star]
      rw [e1]
      have hf : gdLeft J (∑ j, v j • e j) = 0 := by
        refine bs.ext fun i => ?_
        rw [hbs, LinearMap.zero_apply, hLt, Br]
        have h2 := congrFun hv i
        rw [Pi.zero_apply] at h2
        refine Eq.trans ?_ h2
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
      have h3 := LinearMap.congr_fun hf (star b • x)
      rw [LinearMap.zero_apply, hLt] at h3
      exact h3
    apply hv0
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) v hy i
  refine ⟨hdetG, ?_⟩
  set Gi := (gramTr J e)⁻¹ with hGi
  have hGGi : gramTr J e * Gi = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)
  obtain ⟨w, hw⟩ : ∃ w : Fin (m * Module.finrank ℚ E) → Fin m → E,
      ∀ j, w j = ∑ k, Gi k j • e k := ⟨_, fun j => rfl⟩
  have hBw : ∀ i j, Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (w j)) =
      (1 : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℚ) i j := by
    intro i j
    rw [hw, Br, ← hGGi, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
  have hint : ∀ x ∈ M, ∀ j, Algebra.trace ℚ E (hform (starRingEnd E) J x (w j)) ∈
      (algebraMap ℤ ℚ).range := by
    intro x hx j
    obtain ⟨c, rfl⟩ := hspan x hx
    have e2 : ∑ i, ((c i : ℤ) : E) • e i = ∑ i, ((c i : ℚ)) • e i :=
      Finset.sum_congr rfl fun i _ => gd_int_smul _ _
    rw [e2, Bl]
    simp only [hBw, Matrix.one_apply]
    refine RingHom.mem_range.mpr ⟨c j, ?_⟩
    simp
  have hdual : ∀ j, (d : E) • ((δ : E) • w j) ∈ M := by
    intro j
    apply hMdual
    intro x hx
    rw [hform_smul_right']
    apply hcod
    intro a
    have hsa : star (algebraMap (𝓞 E) E a) • x ∈ M := by
      obtain ⟨a', ha'⟩ := RingHom.mem_range.mp (hO _ (RingHom.mem_range.mpr ⟨a, rfl⟩))
      rw [← ha', algebraMap_smul]
      exact M.smul_mem a' hx
    have e3 : algebraMap (𝓞 E) E a * hform (starRingEnd E) J x (w j) =
        hform (starRingEnd E) J (star (algebraMap (𝓞 E) E a) • x) (w j) := by
      rw [hform_smul_left', star_star]
    rw [e3]
    exact hint _ hsa j
  have hn : ∀ (n : ℕ) (v : Fin m → E), (n : E) • v = (n : ℚ) • v := fun n v => by
    rw [gd_qsmul, Rat.cast_natCast]
  have hC : ∀ j, ∃ C : Fin (m * Module.finrank ℚ E) → ℤ,
      ∀ k, (C k : ℚ) = (d : ℚ) * (δ : ℚ) * Gi k j := by
    intro j
    obtain ⟨C, hCe⟩ := hspan _ (hdual j)
    refine ⟨C, ?_⟩
    have e4 : (d : E) • ((δ : E) • w j) = ∑ k, ((d : ℚ) * (δ : ℚ) * Gi k j) • e k := by
      rw [hn, hn, hw, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    have e5 : ∑ k, ((C k : ℚ) - (d : ℚ) * (δ : ℚ) * Gi k j) • e k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← e4, hCe]
      exact Finset.sum_congr rfl fun k _ => (gd_int_smul _ _).symm
    intro k
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ e5 k)
  choose C hCj using hC
  set C' : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℤ :=
    Matrix.of fun k j => C j k with hC'
  have hdq : (0 : ℚ) < (d : ℚ) * (δ : ℚ) := by
    have h1 : (0 : ℚ) < d := Nat.cast_pos.mpr hd
    have h2 : (0 : ℚ) < δ := Nat.cast_pos.mpr hδ
    positivity
  have hCm : C'.map (Int.cast : ℤ → ℚ) = ((d : ℚ) * (δ : ℚ)) • Gi := by
    ext k j
    simp [hC', hCj]
  have hdetC : ((C'.det : ℤ) : ℚ) =
      ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) * ((gramTr J e).det)⁻¹ := by
    have h1 : ((C'.det : ℤ) : ℚ) = (C'.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det C'
    rw [h1, hCm, Matrix.det_smul, Fintype.card_fin, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hCne : C'.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdetC
    exact mul_ne_zero (pow_ne_zero _ hdq.ne') (inv_ne_zero hdetG) hdetC.symm
  have h1 : (1 : ℚ) ≤ |((C'.det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hCne
  have hpos : 0 < |(gramTr J e).det| := abs_pos.mpr hdetG
  set X := ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) with hX
  have hXpos : 0 < X := pow_pos hdq _
  rw [hdetC, abs_mul, abs_inv, abs_of_pos hXpos] at h1
  have key : |(gramTr J e).det| ≤ X := by
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_comm X, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
  rw [hX] at key
  push_cast
  exact key

end PIW.AdelClassFin

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorBasis
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_basis : SvBasis := by
  intro E _ _ m M hfg hspan
  classical
  let M' : Submodule ℤ (Fin m → E) := M.restrictScalars ℤ
  have hfg' : M'.FG := hfg.restrictScalars
  have : Module.Finite ℤ M' := Module.Finite.iff_fg.2 hfg'
  have : Module.Free ℤ M' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M'
  let e0 : Module.Free.ChooseBasisIndex ℤ M' → Fin m → E := fun i => (b i : Fin m → E)
  have hli : LinearIndependent ℤ e0 := b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ e0 := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hrep : ∀ x (hx : x ∈ M), x = ∑ i, (b.repr ⟨x, hx⟩ i) • e0 i := by
    intro x hx
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : M')).symm
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul] using h1
  have hmemM : ∀ x ∈ M, x ∈ Submodule.span ℚ (Set.range e0) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstab : ∀ c : E, ∀ v ∈ Submodule.span ℚ (Set.range e0), c • v ∈ Submodule.span ℚ (Set.range e0) := by
    intro c v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
      let α : 𝓞 E := ⟨y • c, hyi⟩
      have hαv : α • e0 i ∈ M := M.smul_mem α (b i).2
      have hyQ : (y : ℚ) ≠ 0 := Int.cast_ne_zero.2 hy0
      have : c • e0 i = ((y : ℚ)⁻¹) • (α • e0 i) := by
        have hα : (α • e0 i) = ((y : E) * c) • e0 i := by
          rw [Algebra.smul_def (A := E)] at *
          show ((y • c : E)) • e0 i = _
          rw [zsmul_eq_mul]
        rw [hα, mul_smul, ← smul_assoc]
        rw [show ((y : ℚ)⁻¹ • ((y : E))) = (1 : E) by
          rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel₀ (Int.cast_ne_zero.2 hy0)]]
        rw [one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (hmemM _ hαv)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  have hspanQ : Submodule.span ℚ (Set.range e0) = ⊤ := by
    let W : Submodule E (Fin m → E) :=
      { toAddSubmonoid := (Submodule.span ℚ (Set.range e0)).toAddSubmonoid
        smul_mem' := fun c v hv => hstab c v hv }
    have hle : Submodule.span E (M : Set (Fin m → E)) ≤ W := Submodule.span_le.2 fun x hx => hmemM x hx
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    exact hle (Submodule.mem_top)
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M') ℚ (Fin m → E) :=
    Module.Basis.mk hliQ (by rw [hspanQ])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M') = m * Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi_fintype]
    simp
  let σ : Fin (m * Module.finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ M' := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e0 ∘ σ, hliQ.comp σ σ.injective, fun i => (b (σ i)).2, fun x hx => ?_⟩
  refine ⟨fun i => b.repr ⟨x, hx⟩ (σ i), ?_⟩
  conv_lhs => rw [hrep x hx]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

end PIW.AdelClassFin

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorMajorantE
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

theorem svM_conj_form {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ) :
    star z ⬝ᵥ ((U * diagonal d * star U) *ᵥ z) =
      ∑ i, star ((star U *ᵥ z) i) * (d i * (star U *ᵥ z) i) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have h : star z ᵥ* U = star (Uᴴ *ᵥ z) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]

theorem svM_term (r : ℝ) (w : ℂ) : star w * ((r : ℂ) * w) = ((r * ‖w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [mul_left_comm, Complex.conj_mul']

theorem successive_vector_majorant : SvMaj := by
  intro n J hJ hdet
  set U : Matrix (Fin n) (Fin n) ℂ := (hJ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set ev := hJ.eigenvalues with hev
  have hspec : J = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    have h := hJ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hJ.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hJ.eigenvectorUnitary.2
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hdet
    rw [hJ.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h]; simp)
  refine ⟨U * diagonal (fun i => ((|ev i| : ℝ) : ℂ)) * star U, ?_, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|ev i| : ℝ) : ℂ))).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      exact Complex.zero_lt_real.2 (abs_pos.2 (hev0 i))
    have hinj : Function.Injective (star U).mulVec := by
      intro x y hxy
      have := congrArg (fun v => U *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec, hUU'] using this
    have h2 := hD.conjTranspose_mul_mul_same hinj
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← Matrix.star_eq_conjTranspose] at h2
  · have hdU : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, hUU', Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdU, one_mul, Matrix.det_diagonal,
      hJ.det_eq_prod_eigenvalues, norm_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    simp [hev]
  · intro z
    rw [hspec, svM_conj_form, svM_conj_form]
    simp only [svM_term]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.norm_real, Complex.ofReal_re,
      Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_sq]

theorem successive_vector_majorant_e : SvMajE := by
  intro F E _ _ _ _ _ _ hCM m J hJ hdet
  have hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hCM.cmUnram.2.1
  have hTC : NumberField.IsTotallyComplex E := hCM.cmUnram.1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := by
    intro φ h
    have hc := hTC.isComplex (InfinitePlace.mk φ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hJe : ∀ i j, star (J j i) = J i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian := by
    intro φ
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hJe i j, hstar]
    rfl
  have hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0 := by
    intro φ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).2 hdet
  have hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ := by
    intro M hM
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]
    rfl
  have hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ),
      star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z)) := by
    intro N z
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, mulVec, map_sum, map_mul]
  choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)
  let ι := Fintype.equivFin (E →+* ℂ)
  refine ⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ
    else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩
  intro φ
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
  by_cases hp : ι φ < ι (ComplexEmbedding.conjugate φ)
  · have hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ := lt_asymm hp
    simp only [if_pos hp]
    refine ⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩
    rw [hcc, if_neg hp']
  · set ψ := ComplexEmbedding.conjugate φ with hψ
    have hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ) := by
      rw [hψ, hcc]
      refine lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)
    have hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ) := by
      ext i j
      simp [hψ, ComplexEmbedding.conjugate_coe_eq]
    have hM := hH0 ψ
    simp only [if_neg hp, if_pos hψφ, ← hψ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmapT _ hM.1.1]
      exact hM.1.transpose
    · have hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ,
          (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det := fun N => by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]
    · intro z
      have h1 := hM.2.2 (star z)
      rw [star_star] at h1
      rw [hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]
      exact h1
    · rw [Matrix.map_map]
      ext i j
      simp

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorCodifferent
noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem successive_vector_codifferent : SvCodiff := by
  intro E _ _
  refine ⟨(NumberField.discr E).natAbs, Int.natAbs_pos.2 (NumberField.discr_ne_zero E), fun y hy => ?_⟩
  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hy a'
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E)
    (fun i => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
    (Submodule.mem_one.2 ⟨1, map_one _⟩) hmem
  rw [← NumberField.coe_discr] at hint
  have hx : IsIntegral ℤ (((NumberField.discr E : ℤ) : E) * y) := by
    convert hint using 1
    rw [Algebra.smul_def, mul_one, map_intCast]
  obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (NumberField.discr E).natAbs := ⟨_, rfl⟩
  rw [← hn]
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · rw [← hn] at h
    refine ⟨z, ?_⟩
    rw [hz, h, Int.cast_natCast]
  · rw [← hn] at h
    refine ⟨-z, ?_⟩
    rw [map_neg, hz, h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]

end PIW.AdelClassFin

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.ExistsBoundedMultiplier
noncomputable section

namespace PIW.AdelClassFin

open NumberField
open scoped nonZeroDivisors

private lemma exists_mem_ne_zero_mul_dvd_of_mul_isPrincipal {R : Type*} [CommRing R] (I J : Ideal R)
    (hIJ : I * J ≠ ⊥) (hP : Submodule.IsPrincipal (I * J)) :
    ∃ c ∈ I, c ≠ 0 ∧ ∀ e ∈ J, ∀ g ∈ I, ∃ q : R, e * g = c * q := by
  obtain ⟨⟨c, hc⟩⟩ := hP
  have hcmem : c ∈ I * J := by
    rw [hc]; exact Submodule.mem_span_singleton_self c
  refine ⟨c, Ideal.mul_le.2 (fun a ha b _ => I.mul_mem_right b ha) hcmem, ?_, ?_⟩
  · rintro rfl
    apply hIJ
    rw [hc]; exact Submodule.span_singleton_eq_bot.2 rfl
  · intro e he g hg
    have hmem : e * g ∈ I * J := by
      rw [mul_comm I J]; exact Ideal.mul_mem_mul he hg
    rw [hc] at hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hmem
    exact ⟨q, hq⟩

private lemma ideal_mem_nonZeroDivisors_of_ne_bot {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    I ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
  mem_nonZeroDivisors_iff_ne_zero.2 (by rwa [Ideal.zero_eq_bot])

private lemma coe_nonZeroDivisors_ideal_ne_bot {E : Type} [Field E] [NumberField E] (K : ↥(nonZeroDivisors (Ideal (𝓞 E)))) :
    (K : Ideal (𝓞 E)) ≠ ⊥ := by
  have h := nonZeroDivisors.coe_ne_zero K
  rwa [Ideal.zero_eq_bot] at h

private lemma mul_isPrincipal_of_classGroup_mk0_eq_inv {E : Type} [Field E] [NumberField E] (I K : ↥(nonZeroDivisors (Ideal (𝓞 E))))
    (hK : ClassGroup.mk0 K = (ClassGroup.mk0 I)⁻¹) :
    Submodule.IsPrincipal ((I : Ideal (𝓞 E)) * (K : Ideal (𝓞 E))) := by
  have hK1 : ClassGroup.mk0 (I * K) = 1 := by
    rw [map_mul, hK, mul_inv_cancel]
  exact (ClassGroup.mk0_eq_one_iff (I * K).2).1 hK1

private lemma exists_bounded_norm_ideal_mul_isPrincipal {E : Type} [Field E] [NumberField E] :
    ∃ B : ℕ, ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J ≤ B ∧
      I * J ≠ ⊥ ∧ Submodule.IsPrincipal (I * J) := by
  letI hF : Fintype (ClassGroup (𝓞 E)) := NumberField.RingOfIntegers.instFintypeClassGroup E
  choose rep hrep using (ClassGroup.mk0_surjective (R := 𝓞 E))
  refine ⟨Finset.univ.sup (fun x => Ideal.absNorm ((rep x : Ideal (𝓞 E)))), ?_⟩
  intro I hI
  refine ⟨rep (ClassGroup.mk0 ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩)⁻¹, coe_nonZeroDivisors_ideal_ne_bot _,
    Finset.le_sup (f := fun x => Ideal.absNorm ((rep x : Ideal (𝓞 E)))) (Finset.mem_univ _),
    coe_nonZeroDivisors_ideal_ne_bot (⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩ * rep (ClassGroup.mk0 ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩)⁻¹),
    mul_isPrincipal_of_classGroup_mk0_eq_inv ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩ _ (hrep _)⟩

theorem existsBoundedMultiplier : IdealBoundAll := by
  intro E _ _
  obtain ⟨B, hB⟩ := exists_bounded_norm_ideal_mul_isPrincipal (E := E)
  refine ⟨B, fun I hI => ?_⟩
  obtain ⟨J, hJ0, hJB, hIJ0, hP⟩ := hB I hI
  obtain ⟨c, hcI, hc0, hc⟩ := exists_mem_ne_zero_mul_dvd_of_mul_isPrincipal I J hIJ0 hP
  exact ⟨c, hcI, hc0, Ideal.absNorm J,
    Nat.one_le_iff_ne_zero.2 (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)), hJB, hc _ (Ideal.absNorm_mem J)⟩

end PIW.AdelClassFin

end
end

noncomputable section

namespace PIW.AdelClassFin

theorem adelClassFin_of_svReal (h : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_open spOne existsBoundedMultiplier successive_vector_majorant_e successive_vector_codifferent successive_vector_basis successive_vector_gram_det h

end PIW.AdelClassFin

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorReal
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

section Gen

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem svR_form {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (v : κ → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (A *ᵥ (X *ᵥ v)) = star v ⬝ᵥ ((Xᴴ * A * X) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem svR_det (eq : κ ≃ ι) (X : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) :
    (Xᴴ * B * X).det = star (X.submatrix eq id).det * B.det * (X.submatrix eq id).det := by
  have hY : Xᴴ * B * X = (X.submatrix eq id)ᴴ * B.submatrix eq eq * X.submatrix eq id := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  rw [hY, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_submatrix_equiv_self]

theorem svR_entry {o : Type*} [Fintype o] (X : Matrix o κ ℂ) (A : Matrix o o ℂ) (i j : κ) :
    (Xᴴ * A * X) i j = ∑ k, ∑ l, star (X k i) * A k l * X l j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end Gen

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def svP {m N : ℕ} (e : Fin N → Fin m → E) (φ : E →+* ℂ) : Matrix (Fin m) (Fin N) ℂ :=
  Matrix.of fun k i => φ (e i k)

def svBig {m N : ℕ} (e : Fin N → Fin m → E) : Matrix (Fin m × (E →+* ℂ)) (Fin N) ℂ :=
  Matrix.of fun p i => p.2 (e i p.1)

theorem svBig_block [DecidableEq (E →+* ℂ)] {m N : ℕ} (e : Fin N → Fin m → E)
    (A : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) :
    (svBig e)ᴴ * blockDiagonal A * svBig e = ∑ φ, (svP e φ)ᴴ * A φ * svP e φ := by
  ext i j
  rw [svR_entry, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [svBig, svP, Matrix.of_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

theorem svR_hform (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) = ∑ k, ∑ l, star (φ (x k)) * φ (J k l) * φ (y l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, starRingEnd_apply]
  simp only [hst, starRingEnd_apply]

theorem svR_hdot (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (φ : E →+* ℂ) (x y : Fin m → E) :
    φ (hform (starRingEnd E) J x y) =
      star (fun k => φ (x k)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) := by
  rw [svR_hform hst]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem svR_trace (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m N : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) :
    (gramTr J e).map (Rat.castHom ℂ) = ∑ φ, (svP e φ)ᴴ * J.map φ * svP e φ := by
  ext i j
  rw [Matrix.map_apply, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [gramTr, svP, Matrix.of_apply, Matrix.map_apply]
  have hcast : ∀ q : ℚ, (Rat.castHom ℂ) q = algebraMap ℚ ℂ q := fun q => by simp
  rw [hcast, trace_eq_sum_embeddings ℂ, ← Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ)]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  exact svR_hform hst J φ (e i) (e j)

theorem svR_conj {m N : ℕ} (e : Fin N → Fin m → E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (φ : E →+* ℂ) (hc : H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)) :
    (svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
        svP e (ComplexEmbedding.conjugate φ) = ((svP e φ)ᴴ * H φ * svP e φ).map (starRingEnd ℂ) := by
  ext i j
  rw [hc, Matrix.map_apply, svR_entry, svR_entry]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [svP, Matrix.of_apply, Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
    map_mul, starRingEnd_apply, star_star]

end Coord

theorem successive_vector_real : SvReal := by
  intro F E _ _ _ _ _ _ hcm m J hJ H hH e hdet
  classical
  have hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hcm.cmUnram.2.1

  set M : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℂ :=
    ∑ φ, (svP e φ)ᴴ * H φ * svP e φ with hM

  have hMc : ∀ i j, starRingEnd ℂ (M i j) = M i j := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hM, Matrix.sum_apply, map_sum]
    have hT : ∀ φ : E →+* ℂ, starRingEnd ℂ (((svP e φ)ᴴ * H φ * svP e φ) i j) =
        ((svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
          svP e (ComplexEmbedding.conjugate φ)) i j := by
      intro φ
      rw [svR_conj e H φ (hH φ).2.2.2, Matrix.map_apply]
    simp_rw [hT]
    exact Equiv.sum_comp ((ComplexEmbedding.involutive_conjugate E).toPerm _)
      (fun φ => ((svP e φ)ᴴ * H φ * svP e φ) i j)

  have hHh : ∀ φ, (H φ)ᴴ = H φ := fun φ => (hH φ).1.1
  have hMH : Mᴴ = M := by
    simp only [hM, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
  set R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ :=
    M.map Complex.re with hR
  have hMR : R.map (fun x : ℝ => (x : ℂ)) = M := by
    ext i j
    simp only [hR, Matrix.map_apply]
    exact Complex.conj_eq_iff_re.1 (hMc i j)

  have hsum : ∀ u, star u ⬝ᵥ (M *ᵥ u) =
      ∑ φ : E →+* ℂ, star (svP e φ *ᵥ u) ⬝ᵥ (H φ *ᵥ (svP e φ *ᵥ u)) := by
    intro u
    rw [hM, Matrix.sum_mulVec, dotProduct_sum]
    simp_rw [svR_form]
  have hq : ∀ v : Fin (m * Module.finrank ℚ E) → ℝ, v ⬝ᵥ (R *ᵥ v) =
      (star (fun i => (v i : ℂ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℂ))).re := by
    intro v
    rw [← hMR]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.im_sum, zero_mul, sub_zero, mul_zero]
  have hnn : ∀ u, 0 ≤ (star u ⬝ᵥ (M *ᵥ u)).re := by
    intro u
    rw [hsum, Complex.re_sum]
    exact Finset.sum_nonneg (fun φ _ => (norm_nonneg _).trans ((hH φ).2.2.1 _))

  have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Fintype.card (Fin m × (E →+* ℂ)) := by
    simp [Fintype.card_prod, NumberField.Embeddings.card]
  set eqv : Fin (m * Module.finrank ℚ E) ≃ Fin m × (E →+* ℂ) := Fintype.equivOfCardEq hcard
  set d := ((svBig e).submatrix eqv id).det with hd
  have hdG : ((gramTr J e).det : ℂ) = star d * (∏ φ : E →+* ℂ, (J.map φ).det) * d := by
    have h1 := congrArg Matrix.det (svR_trace hst J e)
    rw [← svBig_block e (fun φ => J.map φ), svR_det eqv, Matrix.det_blockDiagonal] at h1
    rw [← h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp
  have hdM : M.det = star d * (∏ φ : E →+* ℂ, (H φ).det) * d := by
    rw [hM, ← svBig_block e H, svR_det eqv, Matrix.det_blockDiagonal]
  have hRdet : R.det = |((gramTr J e).det : ℝ)| := by
    have h1 : ((R.det : ℝ) : ℂ) = M.det := by
      rw [← hMR]
      exact RingHom.map_det Complex.ofRealHom R
    have h2 : M.det = ((‖((gramTr J e).det : ℂ)‖ : ℝ) : ℂ) := by
      rw [hdM, hdG]
      simp only [(fun φ => (hH φ).2.1 : ∀ φ, (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ))]
      rw [norm_mul, norm_mul, norm_star, norm_prod]
      push_cast
      have hs : star d * d = ((‖d‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star d * (∏ φ : E →+* ℂ, ((‖(J.map φ).det‖ : ℝ) : ℂ)) * d
          = (star d * d) * (∏ φ : E →+* ℂ, ((‖(J.map φ).det‖ : ℝ) : ℂ)) := by ring
        _ = _ := by rw [hs]; push_cast; ring
    have h3 := h1.trans h2
    rw [Complex.ofReal_inj] at h3
    rw [h3, Complex.norm_ratCast]
  refine ⟨R, ?_, hRdet, ?_⟩
  ·
    have hRh : R.IsHermitian := by
      ext i j
      simp only [hR, Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
      have := congrFun (congrFun hMH i) j
      rw [Matrix.conjTranspose_apply] at this
      rw [← this, Complex.star_def, Complex.conj_re]
    have hPSD : R.PosSemidef := by
      refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hRh, fun v => ?_⟩
      rw [star_trivial, hq v]
      exact hnn _
    refine (hPSD.posDef_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det R).2 (isUnit_iff_ne_zero.2 ?_))
    rw [hRdet]
    exact abs_ne_zero.2 (Rat.cast_ne_zero.2 hdet)
  · intro c
    have hx : ∀ φ : E →+* ℂ, (fun k => φ ((∑ i, (c i : E) • e i) k)) =
        svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ) := by
      intro φ
      ext k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [svP, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, map_sum, map_mul, map_intCast]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    calc ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖
        ≤ ∑ φ : E →+* ℂ, (star (svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ)) ⬝ᵥ
            (H φ *ᵥ (svP e φ *ᵥ fun i => ((c i : ℝ) : ℂ)))).re := by
          refine Finset.sum_le_sum (fun φ _ => ?_)
          rw [svR_hdot hst, hx φ]
          exact (hH φ).2.2.1 _
      _ = (star (fun i => ((c i : ℝ) : ℂ)) ⬝ᵥ (M *ᵥ fun i => ((c i : ℝ) : ℂ))).re := by
          rw [hsum, Complex.re_sum]
      _ = (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ)) := (hq _).symm

end PIW.AdelClassFin
end
end

theorem adelic_class_set_finite : PI.AdelClassFin.AdelClassFin :=
  PIW.AdelClassFin.adelClassFin_of_svReal PIW.AdelClassFin.successive_vector_real
