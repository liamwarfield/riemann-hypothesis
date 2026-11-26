module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FiniteImageOfEventually

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.EventuallyConjGL
noncomputable section

open Matrix Topology Filter GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

namespace Near

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem inv_cj (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * cj g x * (g : Mx k n) = x := by
  simp only [cj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (g : Mx k n)]
  simp [← Units.val_mul, Matrix.mul_assoc]

theorem eventually_conj {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ AB : Mx k n × Mx k n in 𝓝 (1, 1), ∀ y ∈ tsupport f, f (AB.1 * y * AB.2) = f y := by
  obtain ⟨hlc, hcs⟩ := hf
  apply hcs.eventually_forall_of_forall_eventually
  intro y _
  have hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2 :=
    ((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd
  have h1 := (hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  have h2 := (hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
  simp

def rE (w : Vc k n) : Mx k n := vecMulVec (eN k n) (w - eN k n)

theorem rE_mul (w : Vc k n) : rE w * rE w = (w (Fin.last n) - 1) • rE w := by
  unfold rE
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1 := by
    simp [eN, dotProduct_single]
  rw [hd]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

def sw (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k :=
  ⟨1 + rE w, 1 - (w (Fin.last n))⁻¹ • rE w, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, rE_mul,
      smul_smul, hc, sub_smul, one_smul]
    abel, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, rE_mul, smul_add, smul_smul, hc,
      sub_smul, one_smul]
    abel⟩

theorem sw_val (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) = 1 + rE w := rfl

theorem sw_last (w : Vc k n) (hw : w (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
  rw [sw_val]
  by_cases h : j = Fin.last n
  · subst h
    simp [rE, eN, vecMulVec]
  · have h' : Fin.last n ≠ j := fun e => h e.symm
    simp [rE, eN, vecMulVec, Matrix.one_apply, h, h']

end Near

private theorem conj_of_pair_lemma {f : Mx k n → ℂ} (g : GL (Fin (n + 1)) k)
    (h1 : ∀ y ∈ tsupport f, f ((g : Mx k n) * y * ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n)) = f y)
    (h2 : ∀ y ∈ tsupport f, f (((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * y * (g : Mx k n)) = f y) :
    ∀ x, f (cj g x) = f x := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  · have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    by_contra hne
    have hy : cj g x ∈ tsupport f := subset_tsupport f hne
    have := h2 _ hy
    rw [Near.inv_cj] at this
    exact hne (this.symm.trans hx0)

private theorem near_lemma_2 {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ w : Vc k n in 𝓝 (eN k n), ∀ hw : w (Fin.last n) ≠ 0,
      ∀ x, f (cj (Near.sw w hw)⁻¹ x) = f x := by
  have hr : Continuous (fun w : Vc k n => Near.rE w) := by
    refine continuous_matrix fun i j => ?_
    simp only [Near.rE, vecMulVec_apply]
    exact continuous_const.mul (((continuous_apply j).sub continuous_const))
  have h0 : Near.rE (eN k n) = 0 := by simp [Near.rE]
  have hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n))
      (𝓝 ((eN k n (Fin.last n))⁻¹)) :=
    ((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])
  have hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))
    simpa [h0] using this
  have hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))
    simpa [h0] using this
  have hS := Near.eventually_conj hf
  filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw
  have eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w := rfl
  have eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w := by
    rw [inv_inv]; exact Near.sw_val w hw
  apply conj_of_pair_lemma
  · intro y hy
    rw [eA, eB]
    exact h1 y hy
  · intro y hy
    rw [eA, eB]
    exact h2 y hy

open Near in
theorem phiNear : PhiNear k := by
  intro n Λ hΛ f₀ hf₀
  have hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])
  have hev := hne.and (near_lemma_2 hf₀)
  have ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n)) := by
    have hc : Continuous (fun v : Vc k n => eN k n + v) := by fun_prop
    simpa using hc.tendsto (0 : Vc k n)
  have hU := ht.eventually hev
  obtain ⟨t, htU⟩ := exists_box_subset hU
  refine ⟨t, fun s hst => ?_⟩
  funext w
  by_cases hw : w - eN k n ∈ box (Fin (n + 1)) s
  · have hP := htU (hst hw)
    simp only [Set.mem_setOf_eq, add_sub_cancel] at hP
    obtain ⟨hl, hc⟩ := hP
    have hw0 : w ≠ 0 := by
      intro h
      apply hl
      simp [h]
    have hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_mem hmem]
    simp only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j :=
      ⟨sw w hl, sw_last w hl⟩
    have hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
      simp only [sec, dif_pos hex]
      exact hex.choose_spec
    have hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n) := by
      intro M
      ext j
      simp [eLast, vecMul, dotProduct, Pi.single_apply]
    set p := sec w * (sw w hl)⁻¹ with hpdef
    have hp : p ∈ Mir k n := by
      show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n
      have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n)
          = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n) := by
        rw [hrow, hrow]
        funext j
        rw [hsec j, sw_last w hl j]
      rw [hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have hsecp : sec w = p * sw w hl := by simp [hpdef]
    have hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹ := by
      funext x
      rw [hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]
      exact hc hl _
    rw [hfun]
    exact hΛ p⁻¹ (inv_mem hp) f₀ hf₀
  · have hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_notMem hmem]
    simp only [phi, Set.indicator_of_notMem hmem, mul_zero]
    split_ifs
    · rfl
    · exact map_zero Λ

end PositivityTheory.RgUd.AB.Pf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetPfTrGL
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) : GL (Fin (n + 1)) k :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) :
    GeneralLinearGroup.det (pfTrGL h) = GeneralLinearGroup.det h := by
  apply Units.ext
  simp [pfTrGL, GeneralLinearGroup.val_det_apply, det_transpose]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem transpose_mulVec_dotProduct_inv_mulVec {n : ℕ} (h : GL (Fin (n + 1)) k) (x z : Vc k n) :
    ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ x) ⬝ᵥ
        (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) = x ⬝ᵥ z := by
  rw [mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    vecMul_one]

variable (k) in
theorem pfAct : PfAct k := by
  intro mk bs ν hν ψ c hc n F hF h
  funext z
  have key := integral_comp_mulVec_eq_smul ν (pfTrGL h)
    (fun u => F (cj h⁻¹ z.1, u) * ((ψ (u ⬝ᵥ (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)) : Circle) : ℂ))
  have hv : ((pfTrGL h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ := rfl
  simp only [hv, transpose_mulVec_dotProduct_inv_mulVec, det_pfTrGL] at key
  simp only [GlobalTheory.SplitDict.pf]
  rw [key, Complex.real_smul, Complex.ofReal_inv]

end PositivityTheory.RgUd.AB.Pf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.MemSBIffSupportedIn
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def cutL {n : ℕ} (U : Set k) : (Mx k n → ℂ) →ₗ[ℂ] (GL (Fin (n + 1)) k → ℂ) where
  toFun ψ x := by
    classical
    exact if (x.val).det ∈ U then ψ x.val else 0
  map_add' ψ₁ ψ₂ := funext fun x => by
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
open Classical in
theorem cutL_apply {n : ℕ} (U : Set k) (ψ : Mx k n → ℂ) (x : GL (Fin (n + 1)) k) :
    cutL U ψ x = if (x.val).det ∈ U then ψ x.val else 0 := by
  classical
  rfl

theorem mem_SB_iff_supportedIn {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ f ∈ supportedIn (Set.univ : Set X) := by
  constructor
  · intro h
    exact ⟨h, Set.subset_univ _⟩
  · intro h
    exact h.1

theorem cutL_mem {n : ℕ} (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) {ψ : Mx k n → ℂ}
    (hψ : ψ ∈ SB (Mx k n)) : cutL U ψ ∈ SB (GL (Fin (n + 1)) k) := open Topology Filter in by
  have hE : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
    · intro A hA
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_matrix_inv
      have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hd
    · intro u
      exact (Matrix.coe_units_inv u).symm
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    Units.continuous_val.matrix_det
  constructor
  · have h1 : IsLocallyConstant (fun x : GL (Fin (n + 1)) k => ψ x.val) :=
      hψ.1.comp_continuous Units.continuous_val
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    intro x
    by_cases hx : (x.val).det ∈ U
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ U :=
        hdet.continuousAt.preimage_mem_nhds (hU.isOpen.mem_nhds hx)
      filter_upwards [h2, h1 x] with x' hx' h'
      simp only [cutL_apply, if_pos hx, if_pos hx', h']
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ Uᶜ :=
        hdet.continuousAt.preimage_mem_nhds (hU.isClosed.isOpen_compl.mem_nhds hx)
      filter_upwards [h2] with x' hx'
      have hx'' : (x'.val).det ∉ U := hx'
      simp only [cutL_apply, if_neg hx, if_neg hx'']
  · have hK : IsCompact (tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U) :=
      hψ.2.isCompact.inter_right (hU.isClosed.preimage continuous_id.matrix_det)
    have hKr : tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U ⊆
        Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      intro A hA
      have hd : A.det ≠ 0 := by
        intro h
        exact h0 (h ▸ hA.2)
      exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hd)).unit,
        IsUnit.unit_spec _⟩
    have hK' := hE.isInducing.isCompact_preimage' hK hKr
    refine HasCompactSupport.intro' hK' (hK.isClosed.preimage Units.continuous_val) ?_
    intro x hx
    rw [cutL_apply]
    split_ifs with h
    · exact image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨hm, h⟩)
    · rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_cj {n : ℕ} (p x : GL (Fin (n + 1)) k) :
    ((p * x * p⁻¹ : GL (Fin (n + 1)) k).val).det = (x.val).det := by
  simp only [Units.val_mul, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one, one_mul]

theorem cutL_cj {n : ℕ} (U : Set k) (p : GL (Fin (n + 1)) k) (ψ : Mx k n → ℂ) :
    cutL U (ψ ∘ cj p) = fun x => cutL U ψ (p * x * p⁻¹) := by
  funext x
  rw [cutL_apply, cutL_apply, det_cj]
  rfl

end PositivityTheory.RgUd.AB.Pf

namespace PositivityTheory.RgUd.AB.Pf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA_of_core : CoreX k → ThmT k → ThmA k := open Topology Filter in by
  intro hC hT n Λ hP p f hf
  classical
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf.1
  let φ : SB (GL (Fin (n + 1)) k) := ⟨f, hf'⟩
  have hE : IsOpenEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    have hEmb : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
      · intro A hA
        apply ContinuousAt.continuousWithinAt
        apply continuousAt_matrix_inv
        have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ hd
      · intro u
        exact (Matrix.coe_units_inv u).symm
    refine ⟨hEmb, ?_⟩
    have hr : Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) =
        {A | A.det ≠ 0} := by
      ext A
      constructor
      · rintro ⟨u, rfl⟩
        exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit,
          IsUnit.unit_spec _⟩
    rw [hr]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let ext : Mx k n → ℂ := fun y => if h : IsUnit y then φ.1 h.unit else 0
  have ext_val (u : GL (Fin (n + 1)) k) : ext u.val = φ.1 u := by
    dsimp [ext]
    rw [dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have ext_mem : ext ∈ SB (Mx k n) := by
    have hK : IsCompact (Units.val '' tsupport φ.1) := φ.2.2.isCompact.image hE.continuous
    have hKc : IsClosed (Units.val '' tsupport φ.1) := hK.isClosed
    have hzero : ∀ y, y ∉ Units.val '' tsupport φ.1 → ext y = 0 := by
      intro y hy
      dsimp [ext]
      split_ifs with h
      · exact image_eq_zero_of_notMem_tsupport (fun hm => hy ⟨h.unit, hm, h.unit_spec⟩)
      · rfl
    refine ⟨?_, HasCompactSupport.intro' hK hKc hzero⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    by_cases hy : IsUnit y
    · obtain ⟨u, rfl⟩ := hy
      have hφ := (IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 u
      rw [← hE.map_nhds_eq, Filter.eventually_map]
      filter_upwards [hφ] with u' hu'
      rw [ext_val, ext_val, hu']
    · have hy' : y ∉ Units.val '' tsupport φ.1 := by
        rintro ⟨u, -, rfl⟩
        exact hy u.isUnit
      filter_upwards [hKc.isOpen_compl.mem_nhds hy'] with y' hy''
      rw [hzero y' hy'', hzero y hy']
  let ψ : SB (Mx k n) := ⟨ext, ext_mem⟩
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  obtain ⟨U, hU, hCU, h0⟩ := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport f)
    (hf'.2.isCompact.image hdet)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero hx)
  have hfeq : cutL U ψ.1 = f := by
    funext x
    rw [cutL_apply]
    split_ifs with h
    · exact ext_val x
    · symm
      by_contra hne
      exact h (hCU ⟨x, subset_tsupport _ hne, rfl⟩)
  let Λ' : (Mx k n → ℂ) →ₗ[ℂ] ℂ := Λ ∘ₗ cutL U
  have hPX : PInvX Λ' := by
    intro q hq g hg
    show Λ (cutL U (g ∘ cj q)) = Λ (cutL U g)
    rw [cutL_cj]
    exact hP q hq _ ((mem_SB_iff_supportedIn _).mp (cutL_mem U hU h0 hg))
  have hGX := hC hT n Λ' hPX p ψ.1 ψ.2
  have e1 : (fun g => f (p * g * p⁻¹)) = cutL U (ψ.1 ∘ cj p) := by
    rw [cutL_cj, hfeq]
  have e2 : Λ (cutL U (ψ.1 ∘ cj p)) = Λ (cutL U ψ.1) := hGX
  rw [e1, e2, hfeq]

end PositivityTheory.RgUd.AB.Pf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FormTraceDistrGL
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory PositivityTheory.PfBern.Unit

namespace PositivityTheory.RgUd.AB.Pf

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem formD_faithful [ρ.IsIrreducible] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (C : Sesq V)
    (h : ∀ f ∈ testFn G, formD μ hρ hpos hinv Pr C f = 0) : C = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun u => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, LinearMap.zero_apply]
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have huW : u ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  set W := fixedVectors ρ (K : Subgroup G)
  let vW : W := ⟨v, hvW⟩
  let uW : W := ⟨u, huW⟩
  let φ : W →ₗ[ℂ] ℂ := (B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : Module.End ℂ W := φ.smulRight vW
  obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW A
  let rf : locallyConstantCompactSupport G ℂ ℂ := (r : HeckeAlgebra μ)
  have hbi : BiInv (K : Subgroup G) (rf : G → ℂ) := fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x
  have hf := h rf rf.2
  rw [formD_apply, hPr rf] at hf
  change DF μ hρ hpos C rf = 0 at hf
  rw [DF_eq μ hρ hpos hinv C _ hKc hKo hbi] at hf
  have hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v := by
    intro x
    have e := congrArg (fun T : Module.End ℂ W => (T x : V)) hr
    rw [← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]
    rfl
  have huu : (B₀ u u) ≠ 0 := fun e => by
    have := hpos u hu0
    rw [e] at this
    simp at this
  set N := rN μ hρ hpos hKc hKo C rf with hN
  have sN := rN_spec μ hρ hpos hKc hKo C rf
  let m : W := (B₀ u u)⁻¹ • N uW
  have hm : ∀ y : W, B₀ (m : V) y = C v y := by
    intro y
    have := sN uW y
    rw [hres] at this
    show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y
    rw [map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ huu, one_mul]
  have hNe : N = φ.smulRight m := by
    refine riesz_unique hpos sN fun x y => ?_
    show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y
    rw [hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]
    rfl
  unfold DK at hf
  rw [← hN, hNe, LinearMap.trace_smulRight] at hf
  have : φ m = C v u := hm uW
  rw [← this]
  exact hf

end Faith

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem formTraceDistrGL : FormTraceDistrGL k := by
  intro n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := GL (Fin (n + 1)) k)
  exact ⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf,
    fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩

theorem theoremA_of_thmA (hA : PositivityTheory.RgUd.ThmA k) : TheoremA k := by
  intro n D hD g f hf
  have hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)) := ⟨hf, Set.subset_univ _⟩
  have hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)),
      D (fun x => f (p * x * p⁻¹)) = D f := by
    intro p hp f hf
    have := hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1
    have e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹) := by
      funext x; unfold conjFn; rw [inv_inv]
    rw [← e]; exact this
  have := hA n D hP g⁻¹ f hf'
  have e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹) := by
    funext x; unfold conjFn; rw [inv_inv]
  rw [e]; exact this

theorem thmB_of_kirillov (hK : KirillovForm k) : PositivityTheory.RgUd.ThmB k := by
  intro n V _ _ π hs hirr B hB β hβ
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)
  obtain ⟨c, hc⟩ := hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ
  exact ⟨c, fun v w => by rw [hc]; rfl⟩

theorem thmB (hA : PositivityTheory.RgUd.ThmA k) : PositivityTheory.RgUd.ThmB k :=
  thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))

end PositivityTheory.RgUd.AB.Pf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.IsLocallyConstantIndicatorOne
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker
  GlobalTheory.SplitDict

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_supportedIn_iff {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ SB X ∧ Function.support f ⊆ U := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem mem_supportedIn_univ_iff {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    f ∈ supportedIn (Set.univ : Set X) ↔ f ∈ SB X := by
  rw [mem_supportedIn_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Set.subset_univ _⟩⟩

def recCjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  right_inv x := by
    simp only [cj, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  continuous_toFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def mvHomeo {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hAB : A * B = 1) (hBA : B * A = 1) :
    Vc k n ≃ₜ Vc k n where
  toFun w := A *ᵥ w
  invFun w := B *ᵥ w
  left_inv w := by simp only [mulVec_mulVec, hBA, one_mulVec]
  right_inv w := by simp only [mulVec_mulVec, hAB, one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ SB Y) : f ∘ e ∈ SB X :=
  (bijOn_comp e).mapsTo hf

theorem cj_comp_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) : f ∘ cj g ∈ SB (Mx k n) :=
  comp_mem_SB (recCjHomeo g) hf

theorem act_mem {n : ℕ} (g : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun p : Mx k n × Vc k n => F ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
      ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) ∈ SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo g).prodCongr (mvHomeo (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Units.mul_inv g) (Units.inv_mul g))) hF

theorem tw_mem {n : ℕ} (h : GL (Fin (n + 1)) k) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) ∈
      SB (Mx k n × Vc k n) :=
  comp_mem_SB ((recCjHomeo h⁻¹).prodCongr (mvHomeo (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ
    (by rw [← transpose_mul, Units.inv_mul, transpose_one]) (by rw [← transpose_mul, Units.mul_inv, transpose_one]))) hF

theorem isLocallyConstant_indicator_one {Y : Type*} [TopologicalSpace Y] {E : Set Y} (hE : IsClopen E) :
    IsLocallyConstant (E.indicator (1 : Y → ℂ)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
  by_cases hy : y ∈ E
  · filter_upwards [hE.isOpen.mem_nhds hy] with z hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hy]
    rfl
  · filter_upwards [hE.isClosed.isOpen_compl.mem_nhds hy] with z hz
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]

theorem tens_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ}
    (hf : f ∈ SB X) {E : Set Y} (hEo : IsOpen E) (hEc : IsCompact E) :
    (fun q : X × Y => f q.1 * E.indicator 1 q.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul
    ((isLocallyConstant_indicator_one ⟨hEc.isClosed, hEo⟩).comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.isCompact.prod hEc) fun q hq => ?_⟩
  by_cases h1 : q.1 ∈ tsupport f
  · have h2 : q.2 ∉ E := fun h2 => hq ⟨h1, h2⟩
    simp [Set.indicator_of_notMem h2]
  · simp [image_eq_zero_of_notMem_tsupport h1]

theorem slice_fst_mem {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {g : X × Y → ℂ}
    (hg : g ∈ SB (X × Y)) (y : Y) : (fun x => g (x, y)) ∈ SB X :=
  ⟨hg.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hg.2.isCompact.image continuous_fst) fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩⟩

theorem zero_mem_box {m : Type*} (s : kˣ) : (0 : m → k) ∈ box m s := by
  intro i _
  simp [cball]

section Meas

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_slice (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (z : T × (n → k)) : Integrable (fun x => F (z.1, x) * (ψ (x ⬝ᵥ z.2) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hs := slice_mem_SB hF z.1
  have h2 : IsLocallyConstant fun x : n → k => ((ψ (x ⬝ᵥ z.2) : Circle) : ℂ) :=
    (hψ.isLocallyConstant.comp_continuous (continuous_id.dotProduct continuous_const)).comp _
  exact (hs.1.mul h2).continuous.integrable_of_hasCompactSupport hs.2.mul_right

theorem pf_lin (ν : Measure k) [ν.IsAddHaarMeasure] {T : Type} [TopologicalSpace T] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c) {F G : T × (n → k) → ℂ} (hF : F ∈ SB (T × (n → k)))
    (hG : G ∈ SB (T × (n → k))) (a b : ℂ) :
    pf ψ (Measure.pi fun _ => ν) (a • F + b • G) = a • pf ψ (Measure.pi fun _ => ν) F + b • pf ψ (Measure.pi fun _ => ν) G := by
  funext z
  simp only [pf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((integrable_slice ν hψ hF z).const_mul a)
    ((integrable_slice ν hψ hG z).const_mul b)]
  congr 1
  funext x
  ring

end Meas

theorem recover (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PhiIndep k → PhiLin k → PhiInt k → PhiNear k → PfAct k → LtEquiv k → Recover k := by
  intro _ hLin hInt hNear hPf hLt hT n Λ hP
  borelize k
  have := secondCountable k
  have := t2Space k
  obtain ⟨-, ⟨ψ, -, -, hψ⟩, ν, hν⟩ := conductor_exists k
  have := hν.1
  set μ : Measure (Vc k n) := Measure.pi fun _ => ν with hμ
  have hb := pf_bijOn (T := Mx k n) (n := Fin (n + 1)) ν hψ
  set Fi := Function.invFunOn (pf ψ μ) {f | f ∈ SB (Mx k n × Vc k n)} with hFi
  have Fi_mem : ∀ f ∈ SB (Mx k n × Vc k n), Fi f ∈ SB (Mx k n × Vc k n) := fun f hf => hb.surjOn.mapsTo_invFunOn hf
  have pf_Fi : ∀ f ∈ SB (Mx k n × Vc k n), pf ψ μ (Fi f) = f := fun f hf => hb.surjOn.rightInvOn_invFunOn hf
  have Fi_pf : ∀ F ∈ SB (Mx k n × Vc k n), Fi (pf ψ μ F) = F := fun F hF => hb.injOn.leftInvOn_invFunOn hF
  have pfL := fun {F G : Mx k n × Vc k n → ℂ} (hF : F ∈ SB _) (hG : G ∈ SB _) (a b : ℂ) => pf_lin ν hψ hF hG a b
  have pfS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, pf ψ μ (a • F) = a • pf ψ μ F := fun F hF a => by
    have := pfL hF hF a 0
    simpa using this
  have FiL : ∀ f ∈ SB (Mx k n × Vc k n), ∀ g ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      Fi (a • f + b • g) = a • Fi f + b • Fi g := by
    intro f hf g hg a b
    have h1 : a • Fi f + b • Fi g ∈ SB (Mx k n × Vc k n) :=
      add_mem (Submodule.smul_mem _ _ (Fi_mem f hf)) (Submodule.smul_mem _ _ (Fi_mem g hg))
    have := Fi_pf _ h1
    rw [pfL (Fi_mem f hf) (Fi_mem g hg), pf_Fi f hf, pf_Fi g hg] at this
    exact this
  have ltL : ∀ F ∈ SB (Mx k n × Vc k n), ∀ G ∈ SB (Mx k n × Vc k n), ∀ a b : ℂ,
      lt ν Λ (a • F + b • G) = a * lt ν Λ F + b * lt ν Λ G := by
    intro F hF G hG a b
    unfold lt
    rw [hLin n Λ F hF G hG a b]
    simp only [Pi.add_apply]
    rw [integral_add ((hInt ν n Λ hP F hF).smul a) ((hInt ν n Λ hP G hG).smul b)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, smul_eq_mul, smul_eq_mul]
  have ltS : ∀ F ∈ SB (Mx k n × Vc k n), ∀ a : ℂ, lt ν Λ (a • F) = a * lt ν Λ F := fun F hF a => by
    have := ltL F hF F hF a 0
    simpa using this
  let Ξ₀ : SB (Mx k n × Vc k n) →ₗ[ℂ] ℂ :=
    { toFun := fun f => lt ν Λ (Fi f)
      map_add' := fun f g => by
        have e := FiL f f.2 g g.2 1 1
        simp only [one_smul] at e
        have e2 := ltL _ (Fi_mem f f.2) _ (Fi_mem g g.2) 1 1
        simp only [one_smul, one_mul] at e2
        simp only [Submodule.coe_add, e, e2]
      map_smul' := fun c f => by
        have e := FiL f f.2 f f.2 c 0
        simp only [zero_smul, add_zero] at e
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul, e, ltS _ (Fi_mem f f.2)] }
  obtain ⟨ξ, hξ⟩ := LinearMap.exists_extend Ξ₀
  have hξf : ∀ f ∈ SB (Mx k n × Vc k n), ξ f = lt ν Λ (Fi f) := fun f hf => LinearMap.congr_fun hξ ⟨f, hf⟩
  have hinv : ∀ (g : GL (Fin (n + 1)) k), ∀ f ∈ SB (Mx k n × Vc k n),
      ξ (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) = ξ f := by
    intro g f hf
    have hF := Fi_mem f hf
    have hF' := tw_mem g⁻¹ hF
    have e1 := hPf ν ψ 1 hψ n (Fi f) hF g⁻¹
    set c : ℂ := (((nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (nabs_pos k _).ne')
    have e2 : (fun p : Mx k n × Vc k n => f ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * p.1 *
        ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ p.2)) =
        pf ψ μ (c⁻¹ • fun q : Mx k n × Vc k n => Fi f (cj g⁻¹⁻¹ q.1,
          ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) := by
      rw [pfS _ hF', e1, pf_Fi f hf]
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, cj, inv_inv]
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [e2, hξf _ (pf_mem_SB μ hψ (Submodule.smul_mem _ _ hF')), Fi_pf _ (Submodule.smul_mem _ _ hF'),
      ltS _ hF', hLt ν n Λ hP (Fi f) hF g⁻¹, hξf f hf, ← hc, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hzero : ∀ f ∈ SB (Mx k n × Vc k n), (∀ x : Mx k n, f (x, 0) = 0) → ξ f = 0 := by
    intro f hf h0
    have hsupp : Function.support f ⊆ {p : Mx k n × Vc k n | p.2 ≠ 0} := by
      intro p hp h2
      apply hp
      obtain ⟨x, w⟩ := p
      simp only at h2
      subst h2
      exact h0 x
    refine hT (n + 1) ⊥ ?_ ?_ ξ ?_ ?_ f (mem_supportedIn_iff.2 ⟨hf, hsupp⟩)
    · intro a ha b _
      obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
      exact Algebra.commutes r b
    · refine ⟨fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hx
      obtain ⟨r, hr⟩ := Algebra.mem_bot.1 x.2
      have h1 : ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ^ m = 0 := by
        simpa using congrArg Subtype.val hm
      have h2 : (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)) (r ^ m) = 0 := by
        rw [map_pow, hr, h1]
      have h3 : r ^ m = 0 := (algebraMap k (Matrix (Fin (n + 1)) (Fin (n + 1)) k)).injective (h2.trans (map_zero _).symm)
      have h4 : r = 0 := by
        by_contra hr0
        exact pow_ne_zero m hr0 h3
      exact Subtype.ext (by rw [← hr, h4, map_zero]; rfl)
    · intro f' _ hz
      have : f' = 0 := funext fun p => hz p fun a ha => by
        obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 ha
        exact Algebra.commutes r p.1
      rw [this, map_zero]
    · intro g _ f' hf'
      exact hinv g f' (mem_supportedIn_univ_iff.1 hf')
  set B : Set (Vc k n) := box (Fin (n + 1)) (1 : kˣ) with hB
  have hBo : IsOpen B := isOpen_box _
  have hBc : IsCompact B := isCompact_box _
  have hB0 : (0 : Vc k n) ∈ B := zero_mem_box _
  let T : (Mx k n → ℂ) →ₗ[ℂ] (Mx k n × Vc k n → ℂ) :=
    { toFun := fun f q => f q.1 * B.indicator 1 q.2
      map_add' := fun f g => by
        funext q
        simp only [Pi.add_apply]
        ring
      map_smul' := fun c f => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hT_apply : ∀ f q, T f q = f q.1 * B.indicator 1 q.2 := fun _ _ => rfl
  refine ⟨ξ ∘ₗ T, ?_, ?_⟩
  · intro g f hf
    have h1 : T (f ∘ cj g) ∈ SB (Mx k n × Vc k n) := tens_mem (cj_comp_mem g hf) hBo hBc
    have h2 : T f ∈ SB (Mx k n × Vc k n) := tens_mem hf hBo hBc
    have h3 := act_mem g h2
    have hd := hzero _ (sub_mem h1 h3) fun x => by
      simp only [Pi.sub_apply, hT_apply, Function.comp_apply, mulVec_zero, Set.indicator_of_mem hB0, cj]
      ring
    rw [map_sub, sub_eq_zero] at hd
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hd, hinv g _ h2]
  · intro f₀ hf₀
    obtain ⟨t, ht⟩ := hNear n Λ hP f₀ hf₀
    have hφ := ht t subset_rfl
    set E : Set (Vc k n) := {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) t} with hE
    set F : Mx k n × Vc k n → ℂ := fun q => f₀ q.1 * E.indicator 1 q.2 with hFdef
    have hEo : IsOpen E := (isOpen_box t).preimage (continuous_id.sub continuous_const)
    have hEc : IsCompact E := by
      have : E = (fun w => w + eN k n) '' box (Fin (n + 1)) t := by
        ext w
        simp only [hE, Set.mem_ofPred_eq, Set.mem_image]
        exact ⟨fun h => ⟨w - eN k n, h, by abel⟩, fun ⟨u, hu, e⟩ => by rw [← e]; simpa using hu⟩
      rw [this]
      exact (isCompact_box t).image (continuous_id.add continuous_const)
    have hE0 : eN k n ∈ E := by
      simp only [hE, Set.mem_ofPred_eq, sub_self]
      exact zero_mem_box _
    have hF : F ∈ SB (Mx k n × Vc k n) := tens_mem hf₀ hEo hEc
    have hlt : lt ν Λ F = μ.real E * Λ f₀ := by
      unfold lt
      rw [hφ, integral_indicator_const _ hEo.measurableSet, Complex.real_smul]
    have hg := pf_mem_SB μ hψ hF
    have hg0 : ∀ x, pf ψ μ F (x, 0) = μ.real E * f₀ x := by
      intro x
      simp only [pf, hFdef, dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
      rw [integral_const_mul, show (E.indicator (1 : Vc k n → ℂ)) = E.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hEo.measurableSet, Complex.real_smul, mul_one, mul_comm]
    have h1 : ξ (pf ψ μ F) = lt ν Λ F := by rw [hξf _ hg, Fi_pf F hF]
    have h2 : (fun q : Mx k n × Vc k n => pf ψ μ F (q.1, 0) * B.indicator 1 q.2) = (μ.real E : ℂ) • T f₀ := by
      funext q
      simp only [hg0, Pi.smul_apply, smul_eq_mul, hT_apply]
      ring
    have h3 := hzero _ (sub_mem hg (tens_mem (slice_fst_mem hg 0) hBo hBc)) fun x => by
      simp only [Pi.sub_apply, Set.indicator_of_mem hB0, Pi.one_apply, mul_one, sub_self]
    rw [map_sub, sub_eq_zero, h2, map_smul, h1, hlt, smul_eq_mul] at h3
    have hpos : μ.real E ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hEo.measure_pos μ ⟨_, hE0⟩).ne', hEc.measure_lt_top.ne⟩
    have hpos' : (μ.real E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact mul_left_cancel₀ hpos' h3

theorem coreX (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Recover k → CoreX k := by
  intro hR hT n Λ hP g f hf
  obtain ⟨L, hL, hΛ⟩ := hR hT n Λ hP
  rw [hΛ _ (cj_comp_mem g hf), hΛ f hf, hL g f hf]

end PositivityTheory.RgUd.AB.Pf
end
end

namespace PositivityTheory.RgUd.AB.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA : ThmT k → ThmA k :=
  Pf.thmA_of_core k (Pf.coreX k (Pf.recover k (Pf.phiIndep (k := k)) (Pf.phiLin (k := k)) (Pf.phiInt (k := k)) (Pf.phiNear (k := k)) (Pf.pfAct (k := k))
    (Pf.ltEquiv (k := k) (Pf.phiEquiv (k := k)))))

theorem thmB : ThmA k → ThmB k := Pf.thmB k

end PositivityTheory.RgUd.AB.Final
