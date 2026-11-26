module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusModulus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem TorusModulus.commute (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by
  obtain ⟨hkx, hkw⟩ := Subgroup.mem_inf.1 hk
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  refine matrix_ext_mulVec fun z => ?_
  have hH := (h2 w).1
  have hAA : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.1, map_zero]
  have hBB : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.2.1, map_zero]
  have hAB : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
    rw [hForm, ← h1 w, hp.2.2, map_one]
  have hBA : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hAB, map_one]
  have hKu : (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w :=
    mem_archUnitary.1 k.2 w
  set H := gramAt h v w
  set A := vecAt v x₀ w
  set B := vecAt v w₀ w
  set G := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set K := ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  have hKA : K *ᵥ A = A := hkx w
  have hKB : K *ᵥ B = B := hkw w
  set y := z - hForm H B z • A - hForm H A z • B with hy
  have hyA : hForm H A y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hAA, hAB]
    ring
  have hyB : hForm H B y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hBA, hBB]
    ring
  have hKyA : hForm H A (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu A y
    rw [hKA] at e
    rw [e, hyA]
  have hKyB : hForm H B (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu B y
    rw [hKB] at e
    rw [e, hyB]
  have hGy : G *ᵥ y = y := hgY w y hyA hyB
  have hGKy : G *ᵥ (K *ᵥ y) = K *ᵥ y := hgY w _ hKyA hKyB
  have hGA : G *ᵥ A = a w • A := hgx w
  have hGB : G *ᵥ B = (starRingEnd ℂ (a w))⁻¹ • B := hgw w
  have hz : z = y + hForm H B z • A + hForm H A z • B := by rw [hy]; abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz]
  simp only [mulVec_add, mulVec_smul, hKA, hKB, hGy, hGKy, hGA, hGB]

theorem TorusModulus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by
  classical
  intro x₀ w₀ hp g a hgx hgw hgY ν _ f hf
  have : FiniteDimensional E W := Module.Finite.of_basis v
  obtain ⟨h', hh'⟩ := h3 x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  obtain ⟨i, q, hic, hqc, hqi, hker, hiw, -⟩ := h4 x₀ w₀ hp h' hh' _ v'
  let τ : archUnitary h' v' →* archUnitary h v := (vecFixGroup h v x₀).subtype.comp i
  have hτc : Continuous τ := continuous_subtype_val.comp hic
  have hτmem : ∀ t, τ t ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀ :=
    fun t => Subgroup.mem_inf.2 ⟨(i t).2, hiw t⟩
  have hnorm : ∀ t, ∀ x ∈ unipRadical h v x₀, τ t * x * (τ t)⁻¹ ∈ unipRadical h v x₀ := by
    intro t x hx
    have hxP : x ∈ vecFixGroup h v x₀ := unipRadical_le_vecFixGroup h v x₀ hx
    have e := (hker (i t * ⟨x, hxP⟩ * (i t)⁻¹)).1 (by
      rw [map_mul, map_mul, map_inv, hqi, (hker ⟨x, hxP⟩).2 hx, mul_one, mul_inv_cancel])
    simpa [τ] using e
  have hinj : ∀ t, τ t ∈ unipRadical h v x₀ → t = 1 := by
    intro t ht
    rw [← hqi t]
    exact (hker (i t)).2 ht
  have hdec : ∀ p : vecFixGroup h v x₀, (p : archUnitary h v) * (τ (q p))⁻¹ ∈ unipRadical h v x₀ := by
    intro p
    have e := (hker (p * (i (q p))⁻¹)).1 (by rw [map_mul, map_inv, hqi, mul_inv_cancel])
    simpa [τ] using e
  let νN : Measure (unipRadical h v x₀) := Measure.haar
  let ρ : Measure (archUnitary h' v') := Measure.haar
  have hδ : ∀ (t : archUnitary h' v') (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂νN = ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f x ∂νN := by
    intro t f hf
    have e := h5 x₀ w₀ hp νN (τ t) (hτmem t)
    have hm : Measurable fun n : unipRadical h v x₀ => τ t * (n : archUnitary h v) * (τ t)⁻¹ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [ENNReal.coe_one, one_mul, ← lintegral_map hf hm, e, lintegral_map hf measurable_subtype_coe]
  obtain ⟨c, -, hc⟩ := h7 x₀ w₀ h' _ v' (vecFixGroup h v x₀) (unipRadical h v x₀)
    (isClosed_vecFixGroup h v x₀) (isClosed_unipRadical h v x₀) (unipRadical_le_vecFixGroup h v x₀)
    τ q (fun _ => 1) hτc hqc continuous_const (fun t => (i t).2) hnorm hinj hdec ν νN ρ hδ
  have hconj : ∀ t (n : archUnitary h v), g * (n * τ t) * g⁻¹ = g * n * g⁻¹ * τ t := by
    intro t n
    have e : τ t * g⁻¹ = g⁻¹ * τ t := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, TorusModulus.commute h v h1 h2 hp g a hgx hgw hgY _
        (hτmem t), mul_inv_cancel_right]
    calc g * (n * τ t) * g⁻¹ = g * n * (τ t * g⁻¹) := by group
      _ = g * n * (g⁻¹ * τ t) := by rw [e]
      _ = g * n * g⁻¹ * τ t := by group
  set K := ∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))
  have hφ : Measurable fun y : archUnitary h v => f (g * y * g⁻¹) :=
    hf.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have step : ∀ t, ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN =
      K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN := by
    intro t
    simp_rw [hconj t]
    exact h6 x₀ w₀ hp g a hgx hgw hgY νN (fun y => f (y * τ t))
      (hf.comp (continuous_id.mul continuous_const).measurable)
  have hmeas : Measurable fun t => ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN :=
    Measurable.lintegral_prod_right' (f := fun p : archUnitary h' v' × unipRadical h v x₀ =>
      f (p.2 * τ p.1)) (hf.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hτc.comp continuous_fst)).measurable)
  calc ∫⁻ x, f (g * x * g⁻¹) ∂ν
      = c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN ∂ρ := hc _ hφ
    _ = c * ∫⁻ t, K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ := by
        simp_rw [ENNReal.coe_one, one_mul, step]
    _ = K * (c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ) := by
        rw [lintegral_const_mul _ hmeas]
        simp only [ENNReal.coe_one, one_mul]
        ring
    _ = K * ∫⁻ x, f x ∂ν := by rw [hc f hf]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisForm (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    LinearMap.BilinForm ℝ (heisY h v x₀ w₀) :=
  LinearMap.mk₂ ℝ (fun y z => ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re)
    (fun y y' z => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_left, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_left,
        Complex.conj_ofReal, Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])
    (fun y z z' => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_right, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_right,
        Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])

omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem heisForm_apply (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re := rfl

theorem heisForm_comm (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hH, -⟩ := hyperbolic_at_place h v hp w
  rw [← hForm_conj hH, Complex.conj_re]

theorem heisForm_nondegenerate (hp : IsHyperbolicPair h x₀ w₀) :
    (heisForm h v x₀ w₀).Nondegenerate := by
  classical
  have left : ∀ y : heisY h v x₀ w₀, (∀ z, heisForm h v x₀ w₀ y z = 0) → y = 0 := by
    intro y hy
    apply Subtype.ext
    funext w
    change (y : InfinitePlace E → ι → ℂ) w = 0
    obtain ⟨hH, hd, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
    have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
      rw [← hForm_conj hH, hab, map_one]
    apply eq_zero_of_hForm hd
    intro z
    set q := z - hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w -
      hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w with hq
    have hqa : hForm (gramAt h v w) (vecAt v x₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, ha, hab]
      ring
    have hqb : hForm (gramAt h v w) (vecAt v w₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, hb, hba]
      ring
    have key : ∀ c : ℂ, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (c • q)).re = 0 := by
      intro c
      have hmem : (Pi.single w (c • q) : InfinitePlace E → ι → ℂ) ∈ heisY h v x₀ w₀ := by
        intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [Pi.single_eq_same, hForm_smul_right, hqa, hqb, mul_zero, and_self]
        · simp only [Pi.single_eq_of_ne hw, hForm_zero_right, and_self]
      have := hy ⟨_, hmem⟩
      rw [heisForm_apply, Finset.sum_eq_single w] at this
      · simpa using this
      · intro w' _ hw
        simp [Pi.single_eq_of_ne hw, hForm_zero_right]
      · simp
    have h1 := key 1
    have h2 := key Complex.I
    rw [hForm_smul_right, one_mul] at h1
    rw [hForm_smul_right, Complex.I_mul_re, neg_eq_zero] at h2
    have hyq : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) q = 0 := Complex.ext h1 h2
    have hya : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v x₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).1, map_zero]
    have hyb : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).2, map_zero]
    have hz : z = q + hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w +
        hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w := by
      rw [hq]
      abel
    rw [hz, hForm_add_right, hForm_add_right, hForm_smul_right, hForm_smul_right, hyq, hya, hyb]
    ring
  exact ⟨left, fun y hy => left y fun z => by rw [heisForm_comm hp]; exact hy z⟩

theorem heisForm_heisConjLin (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heisConjLin_apply, heisConjLin_apply, hForm_mulVec_of_unitary _ (archUnitary_at_place g w)]

end Form

theorem UnipotentModulus.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentModulus.Statement h v := by
  intro x₀ w₀ hp μ _ g hg
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (fun x' => x' ∈ (unipRadical h v x₀ : Set (archUnitary h v)))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set G := heisConjLin g hg with hG
  set c : unipRadical h v x₀ → unipRadical h v x₀ := fun n => φ ((G (φ.symm n).1, (φ.symm n).2))
    with hcdef
  have hc : ∀ n, ((c n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_conj hp g hg _).symm
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hcm : Measurable c :=
    (φ.continuous.comp ((hGc.comp (continuous_fst.comp φ.symm.continuous)).prodMk
      (continuous_snd.comp φ.symm.continuous))).measurable
  have hmap : (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) =
      Subtype.val ∘ c := by
    funext n
    exact (hc n).symm
  have hGm : MeasurePreserving G Measure.addHaar Measure.addHaar :=
    measurePreserving_of_preserves_bilin _ (heisForm h v x₀ w₀) (heisForm_nondegenerate hp) G
      (heisForm_heisConjLin g hg)
  have hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam := by
    have e : (fun x => φ.symm (c (φ x))) = Prod.map G id := by
      funext x
      simp only [hcdef, Homeomorph.symm_apply_apply, Prod.map, id]
    rw [e]
    exact hGm.prod (MeasurePreserving.id volume)
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  rw [hmap, ← Measure.map_map continuous_subtype_val.measurable hcm,
    map_eq_of_measurePreserving_coordinates lam φ hL c hC μ]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem isAddTorsionFree_of_module (K V : Type*) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] : IsAddTorsionFree V := by
  letI : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree K V
  infer_instance

theorem fg_of_fg_map_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {H : AddSubgroup A} (φ : A →+ B) (hφ : Function.Injective φ) (hH : (H.map φ).FG) : H.FG := by
  have h2 : H.toIntSubmodule.FG := by
    refine Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ ?_
    have : H.toIntSubmodule.map φ.toIntLinearMap = (H.map φ).toIntSubmodule := by
      ext x
      simp
    rw [this]
    exact (Submodule.fg_iff_addSubgroup_fg _).2 hH
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]


omit [NumberField E] in
theorem factorial_nsmul_mem_of_mem_dual {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by
  have hk : La.relIndex (dualLattice h La) • y ∈ La := by
    have := AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩
    exact AddSubgroup.mem_addSubgroupOf.1 this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
  rw [hc, mul_comm, ← smul_smul]
  exact La.nsmul_mem hk c

theorem ComplementLattice.proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by
  intro v₀ w₀ hvw h' hh' D n hn
  refine ⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩
  intro La hLa hdec
  set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP
  obtain ⟨hvv, hww, hvw1⟩ := hvw
  have hwv1 : h.toSesq w₀ v₀ = 1 := by
    rw [← h.isSymm.eq v₀ w₀, hvw1, map_one]
  have hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0 := fun x y hxy => by
    rw [← h.isSymm.eq x y, hxy, map_zero]
  have memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La := fun x => Iff.rfl

  let π₀ : W →ₗ[E] W :=
    LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀
  have hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀ := fun x => rfl
  have hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀) := by
    intro x
    rw [hπ₀, mem_hypComplement]
    constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring
  have hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y := fun y hy => by
    rw [mem_hypComplement] at hy
    rw [hπ₀, hy.1, hy.2]
    simp
  have hπv : π₀ v₀ = 0 := by
    rw [hπ₀, hwv1, hvv]
    simp
  have hπw : π₀ w₀ = 0 := by
    rw [hπ₀, hww, hvw1]
    simp

  have hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧
      n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧
      n • π₀ x = n • x - a • v₀ - b • w₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hmem⟩ := hdec x hx
    change a • v₀ ∈ La at ha
    change b • w₀ ∈ La at hb
    refine ⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩
    rw [← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]
    simp

  have hPlat : IsLattice E P := by
    refine ⟨fun a x hx => ?_, ?_, ?_⟩
    · rw [memP] at hx ⊢
      exact hLa.isLattice.smul_mem a _ hx
    · refine fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_
      exact fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg
    · let π : W →ₗ[E] (hypComplement h v₀ w₀) := π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem
      have hrange : LinearMap.range π = ⊤ :=
        LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩
      rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top,
        Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, b, -, -, -, hzLa, hkey⟩ := hz x hx
      have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hnx : (n : E) • π x ∈ P := by
        rw [memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
        change n • π₀ x ∈ La
        rw [hkey]
        exact hzLa
      have : π x = (n : E)⁻¹ • ((n : E) • π x) := by
        rw [smul_smul, inv_mul_cancel₀ hnE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)

  have hPint : IsIntegralOn h' P := fun x hx y hy => by
    rw [hh']
    exact hLa.integral _ hx _ hy
  set N := D.factorial * n with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.factorial_pos D) hn
  set G := dualLattice h' P with hG
  have hPG : P ≤ G := fun x hx y hy => hPint x hx y hy

  have hNG : G.map (nsmulAddMonoidHom N) ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have hdual : n • (y' : W) ∈ dualLattice h La := by
      intro x hx
      obtain ⟨a, b, -, -, hmem, hzLa, -⟩ := hz x hx
      have hy0 := (mem_hypComplement.1 y'.2)
      have e1 : h.toSesq (y' : W) v₀ = 0 := hsymm0 _ _ hy0.1
      have e2 : h.toSesq (y' : W) w₀ = 0 := hsymm0 _ _ hy0.2
      have hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀ := by abel
      have key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀) := by
        rw [map_nsmul, LinearMap.smul_apply, ← map_nsmul]
        conv_lhs => rw [hnx]
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, e1, e2]
        simp
      rw [key]
      have := hy' ⟨_, hmem⟩ hzLa
      rwa [hh'] at this
    have h2 := factorial_nsmul_mem_of_mem_dual hLa hdual
    rw [nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]
    exact h2

  have : IsAddTorsionFree (hypComplement h v₀ w₀) := isAddTorsionFree_of_module E (hypComplement h v₀ w₀)
  have : HasUniqueDiv (hypComplement h v₀ w₀) := HasUniqueDiv.of_isTorsionFree E _
  have hGfg : G.FG := fg_of_fg_map_of_injective (nsmulAddMonoidHom N)
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne')
    (fg_of_le_fg hNG hPlat.fg)
  have : Module.Finite ℤ G.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)
  have : Module.Finite ℤ G := inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)
  have hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W := by
    letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)
    have : IsScalarTower ℚ E W := ⟨fun q e w => by
      change (q • e) • w = algebraMap ℚ E q • e • w
      rw [Algebra.smul_def, mul_smul]⟩
    have : Module.Finite ℚ W := Module.Finite.trans E W
    let b := Module.finBasis ℤ G
    let f : G →ₗ[ℤ] W := ((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap
    have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hliZ : LinearIndependent ℤ (f ∘ b) :=
      b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
    have := hliQ.fintype_card_le_finrank
    rw [Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W] at this
    exact this
  have hidx : P.relIndex G ≤ N ^ finrank ℤ G := by
    rw [← AddSubgroup.relIndex_map_nsmul N G]
    refine AddSubgroup.relIndex_le_of_le_left hNG ?_
    rw [AddSubgroup.relIndex_map_nsmul]
    positivity
  refine ⟨hPlat, hPint, fun h0 => ?_, ?_⟩
  · have := AddSubgroup.relIndex_eq_zero_of_le_left hNG h0
    rw [AddSubgroup.relIndex_map_nsmul] at this
    exact (pow_ne_zero _ hNpos.ne') this
  · exact hidx.trans (Nat.pow_le_pow_right hNpos hrank)

end Complement

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PImaginaryLatticeCocompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem im_embedding_algebraMap (σ : E →+* ℂ) (c : F) : (σ (algebraMap F E c)).im = 0 := by
  have h := embedding_conj (F := F) σ (algebraMap F E c)
  rw [conj_algebraMap] at h
  exact Complex.conj_eq_iff_im.mp h.symm


omit [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
variable (F E) in
theorem exists_imaginary_integer : ∃ t : 𝓞 E, (t : E) ≠ 0 ∧ conj F E (t : E) = -(t : E) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  obtain ⟨y, hy0, hyi⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ ζ)).exists_integral_multiple
  have hθF : y • ζ ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    apply hζ
    refine ⟨(y : F)⁻¹ * c, ?_⟩
    have hy : (y : E) ≠ 0 := by exact_mod_cast hy0
    rw [map_mul, hc, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  have hcθ : IsIntegral ℤ (conj F E (y • ζ)) :=
    map_isIntegral_int ((conj F E : E ≃ₐ[F] E) : E →+* E) hyi
  refine ⟨⟨y • ζ - conj F E (y • ζ), hyi.sub hcθ⟩, ?_, ?_⟩
  · change y • ζ - conj F E (y • ζ) ≠ 0
    intro h
    apply hθF
    rw [← conj_eq_self_iff]
    exact (sub_eq_zero.mp h).symm
  · change conj F E (y • ζ - conj F E (y • ζ)) = -(y • ζ - conj F E (y • ζ))
    rw [map_sub, conj_conj]
    ring


omit [IsTotallyReal F] in
variable (F E) in
theorem card_infinitePlace_eq : Fintype.card (InfinitePlace E) = finrank ℚ F := by
  have h1 := IsTotallyComplex.finrank (K := E)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
  have h4 := Module.finrank_mul_finrank ℚ F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h4
  omega

theorem ImaginaryLatticeCocompact.proof : ImaginaryLatticeCocompact.Statement F E := by
  classical
  intro m hm
  obtain ⟨t, ht0, htc⟩ := exists_imaginary_integer F E
  let L : Free.ChooseBasisIndex ℤ (𝓞 F) → InfinitePlace E → ℝ := fun i w =>
    (w.embedding ((m : E) * algebraMap F E (integralBasis F i) * (t : E))).im
  let T : (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun c w => ∑ i, c i * L i w
      map_add' := by
        intro c d; ext w; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c; ext w; simp [Finset.mul_sum, mul_assoc] }

  have hr : ∀ w : InfinitePlace E, (w.embedding (t : E)).im ≠ 0 := by
    intro w h
    have hre : (w.embedding (t : E)).re = 0 := by
      have h1 := embedding_conj (F := F) w.embedding (t : E)
      rw [htc, map_neg] at h1
      have h2 := congrArg Complex.re h1
      simp only [Complex.neg_re, Complex.conj_re] at h2
      linarith
    exact ht0 ((map_eq_zero _).mp (Complex.ext hre h))
  have hL : ∀ i w, L i w =
      m * (w.embedding (algebraMap F E (integralBasis F i))).re * (w.embedding (t : E)).im := by
    intro i w
    simp only [L, map_mul, map_natCast, Complex.mul_im, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, im_embedding_algebraMap]
    ring
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ w : InfinitePlace E,
        ∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re = 0 := by
      intro w
      have h1 : ∑ i, c i * L i w = 0 := congrFun hc w
      have h2 : (∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re) *
          ((m : ℝ) * (w.embedding (t : E)).im) = 0 := by
        rw [Finset.sum_mul, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hL]; ring
      exact (mul_eq_zero.mp h2).resolve_right
        (mul_ne_zero (by exact_mod_cast hm.ne') (hr w))
    have hτ : ∀ τ : F →+* ℂ, ∑ i, (c i : ℂ) * τ (integralBasis F i) = 0 := by
      intro τ
      let _ : Algebra F ℂ := τ.toAlgebra
      let σ : E →ₐ[F] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hστ : ∀ x : F, (σ : E →+* ℂ) (algebraMap F E x) = τ x := fun x => σ.commutes x
      have hre : ∀ x : F,
          ((InfinitePlace.mk (σ : E →+* ℂ)).embedding (algebraMap F E x)).re = (τ x).re := by
        intro x
        rcases InfinitePlace.embedding_mk_eq (σ : E →+* ℂ) with h | h
        · rw [h, hστ]
        · rw [h, ComplexEmbedding.conjugate_coe_eq, hστ, Complex.conj_re]
      have him : ∀ x : F, (τ x).im = 0 := by
        intro x
        rw [← hστ]
        exact im_embedding_algebraMap (F := F) (σ : E →+* ℂ) x
      apply Complex.ext
      · rw [Complex.re_sum, Complex.zero_re, ← hw (InfinitePlace.mk (σ : E →+* ℂ))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, hre]
      · rw [Complex.im_sum, Complex.zero_im]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Complex.im_ofReal_mul, him, mul_zero]
    have hli := (canonicalEmbedding.latticeBasis F).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    have h0 := hli (fun i => (c i : ℂ)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
      exact hτ τ) i
    exact_mod_cast h0
  have hsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      card_infinitePlace_eq F E, finrank_eq_card_basis (integralBasis F)]
  refine ⟨∑ i, ∑ w, |L i w|, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hsurj s
  have hint : ∀ i, IsIntegral ℤ (algebraMap F E (integralBasis F i)) := by
    intro i
    rw [integralBasis_apply]
    exact map_isIntegral_int (algebraMap F E) (RingOfIntegers.basis F i).2
  have hk : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  let x : E := ∑ i, (⌊c i⌋ : E) * algebraMap F E (integralBasis F i) * (t : E)
  have hx : IsIntegral ℤ x :=
    IsIntegral.sum _ fun i _ => ((hk _).mul (hint i)).mul t.2
  refine ⟨⟨x, hx⟩, ?_, fun w => ?_⟩
  · change (m : E) * x + conj F E ((m : E) * x) = 0
    have : conj F E x = -x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_mul, map_intCast, conj_algebraMap, htc]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [map_mul, map_natCast, this]
    ring
  · change |(w.embedding ((m : E) * x)).im - s w| ≤ ∑ i, ∑ w, |L i w|
    have key : (w.embedding ((m : E) * x)).im = ∑ i, (⌊c i⌋ : ℝ) * L i w := by
      have e : (m : E) * x = ∑ i, (⌊c i⌋ : E) * ((m : E) * algebraMap F E (integralBasis F i) * (t : E)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_intCast]
      simp [Complex.mul_im, L]
    have hs : s w = ∑ i, c i * L i w := by rw [← hc]; rfl
    rw [key, hs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : |(⌊c i⌋ : ℝ) * L i w - c i * L i w| ≤ |L i w| := by
      rw [← sub_mul, abs_mul]
      have : |(⌊c i⌋ : ℝ) - c i| ≤ 1 := by
        rw [abs_sub_comm, abs_le]
        constructor <;> linarith [Int.floor_le (c i), Int.lt_floor_add_one (c i)]
      exact mul_le_of_le_one_left (abs_nonneg _) this
    exact h1.trans (Finset.single_le_sum (f := fun w' => |L i w'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

universe u

theorem exists_covering_of_relIndex_ne_zero {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by
  classical
  have : (A.subgroupOf B).FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def
  have hbad : μ bad = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)
  refine ⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹'
    toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage
      (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [measure_toMeasurable, hbad, add_zero]
    refine lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_
    simp only [measure_preimage_mul, measure_toMeasurable]
    exact ENNReal.sum_lt_top.2 fun _ _ => hfin
  · intro l
    by_cases hl : l ∈ bad
    · exact ⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩
    · rw [hbad_def, Set.mem_ofPred_eq, not_not] at hl
      obtain ⟨⟨γ, hγ⟩, hγl⟩ := hl
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hγ
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
      set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)
      have hcA : (((c : B) : K)) ∈ A := c.2
      refine ⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      apply subset_toMeasurable
      have e : ((Quotient.out k : B) : K) = b * ((c : B) : K) := by
        rw [hc]; rfl
      simp only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      simpa [Subgroup.smul_def] using hγl

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerCovolumeFinite.proof [FiniteDimensional E W] (h : HermitianForm F E W)
    (v : Basis ι E W) (h₁ : CovolumeFiniteBelow.{u} F E (finrank E W))
    (h₂ : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (h₃ : StabilizerLevi.Statement h v) (h₄ : UnipotentModulus.Statement h v)
    (h₅ : UnipotentCocompact.Statement h v) (h₆ : CongruenceLift.Statement h) :
    StabilizerCovolumeFinite.Statement h v := by
  classical
  intro D La x₀ hLa hx₀ hne hiso ν hν

  obtain ⟨w₀, hxw, hww⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨h', hh'⟩ := ComplementForm.proof h x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  have hlt : finrank E (hypComplement h x₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : w₀ ∈ hypComplement h x₀ w₀ := htop ▸ Submodule.mem_top
    rw [mem_hypComplement, hxw] at hmem
    exact one_ne_zero hmem.1

  obtain ⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩ := h₃ x₀ w₀ hp h' hh' _ v'

  obtain ⟨D', La', G'', hLa', hG'', hidx, hlift⟩ := h₆ D La x₀ w₀ hLa hx₀ hp h' hh'
  let μL : Measure (archUnitary h' v') := Measure.haar
  obtain ⟨FD', hFD', hFD'fin⟩ :=
    h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'
  obtain ⟨T, hTm, hTfin, hT⟩ := exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G''
    (latticeStab h' La') hidx FD' hFD' hFD'fin
  set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ
  have hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T := by
    intro l
    obtain ⟨m, hm, hml⟩ := hT l
    obtain ⟨γ₀, hγx, hγw, hγm⟩ := ComplementExtension.proof h x₀ w₀ hp h' hh' m
    have hγ₀ : γ₀ ∈ latticeStab h La := hlift m hm γ₀ hγx hγw hγm
    refine ⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩
    rw [hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]
    exact ⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩

  obtain ⟨C, hC, hcovN⟩ := h₅ D La x₀ hLa hx₀ hne hiso
  let j : unipRadical h v x₀ →* vecFixGroup h v x₀ :=
    Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _)
  have hj : IsClosedEmbedding j := by
    refine ⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩
    have : Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v)) := by
      ext g
      exact ⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_unipRadical h v x₀).preimage continuous_subtype_val
  have hjr : ∀ g, q g = 1 ↔ g ∈ j.range := fun g => (hker g).trans
    ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  let μN : Measure (unipRadical h v x₀) := Measure.haar
  have hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v) :=
    (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding
  have hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j := by
    intro l
    have key := h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩
    have hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹ :=
      (continuous_const.mul hjc).mul continuous_const
    rw [← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j),
      Measure.map_map hemb.measurable hf.measurable,
      Measure.map_map hemb.measurable hjc.measurable]
    have e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) =
        fun n : unipRadical h v x₀ =>
          ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) *
            ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹ := by
      funext n
      simp [j]
    have e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v) := by
      funext n
      rfl
    rw [e1, e2, key]
  have hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C := fun n => by
    obtain ⟨δ, hδ, hδn⟩ := hcovN n
    exact ⟨δ, hδ, hδn⟩

  obtain ⟨S, -, hSfin, hScov⟩ :=
    h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν

  have hdG : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ :
        vecStabGroup h v La x₀))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc

  have hle : ν FD ≤ ν S := by
    rw [hFD.measure_eq_tsum S]
    refine (measure_mono fun x hx => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, hγx⟩ := hScov x
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγx
  have hν0 : ν ≠ 0 := fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])
  exact ⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
