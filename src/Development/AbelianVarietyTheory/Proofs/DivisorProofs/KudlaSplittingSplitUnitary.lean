module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationSplitUnitarySchwartzBruhStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2Space

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOne
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOneStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ), ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  first | exact @GlobalTheory.KSp.sc_eventually_eq_one | exact GlobalTheory.KSp.sc_eventually_eq_one | (intros; apply GlobalTheory.KSp.sc_eventually_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolic
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, Matrix.one_apply]

theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

theorem mat_mul_mat_inv (g : UG c (stdJ ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, form, GlobalTheory.WeilM.hTens]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

theorem continuous_mat : Continuous fun g : UG c (stdJ ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, form, GlobalTheory.WeilM.hTens]
  refine continuous_const.mul (htr.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end GlobalTheory.KSp.ParNear

theorem GlobalTheory.KSp.parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  obtain ⟨-, htop, -, -, hcc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := htop
  haveI := GlobalTheory.WeilM.nonarch_field F
  have hψl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one] at this
    exact ht.eventually (GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3
    rw [e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)),
      GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']
  funext x
  simp only [parFun]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolicStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  first | exact @GlobalTheory.KSp.parFun_fixed_near_one | exact GlobalTheory.KSp.parFun_fixed_near_one | (intros; apply GlobalTheory.KSp.parFun_fixed_near_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhds
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.OpenCrit

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

def vOf (g : UG c (stdJ ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ * (mat c g).toBlocks₂₁

theorem lower_rel (g : UG c (stdJ ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ * ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

theorem vOf_herm (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]


open scoped Classical in
def nOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then unip c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := (weyl c ν)⁻¹ * nOf c g * weyl c ν

def pOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := g * (kOf c g)⁻¹

theorem nOf_mem (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem

theorem pOf_mem (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) : pOf c g ∈ sieg c ν := by
  rw [mem_sieg]
  have hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]
    rfl
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem continuous_mat : Continuous (mat c : UG c (stdJ ν E) → Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_blk₂₂ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem continuous_blk₂₁ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem blk₂₂_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, Matrix.one_apply]

theorem blk₂₁_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dif_pos hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end GlobalTheory.KSp.OpenCrit

namespace GlobalTheory.KSp


open OpenCrit in
theorem isOpen_of_sieg_of_opp (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end GlobalTheory.KSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhdsStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmooth
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem isKW_isSmoothRep : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hKW
  intro v
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ω g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have key : ∀ u : SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → ω g u = u := by
    intro u
    filter_upwards [GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη (u : Matrix α ν E → ℂ) u.2] with g hg hs
    apply Subtype.ext
    rw [hKW.par g hs u]
    exact hg hs
  have hU : IsOpen (U : Set (UG c (stdJ ν E))) := by
    refine GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds F E c δ hE ν U (key v) ?_
    filter_upwards [key (ω (weyl c ν) v)] with g hg hs
    change ω ((weyl c ν)⁻¹ * g * weyl c ν) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg hs, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  exact hU

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmoothStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  first | exact @GlobalTheory.KSp.isKW_isSmoothRep | exact GlobalTheory.KSp.isKW_isSmoothRep | (intros; apply GlobalTheory.KSp.isKW_isSmoothRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesWeylHeisenbergSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesWeylHeisenbergSchrodinger
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_fou : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ μ _ w φ
  obtain ⟨β, hβ, hsym, -, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI : IsTopologicalAddGroup (Matrix α ν E) := (hM α ν).2.grp
  have hh : ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) (x : Matrix α ν E),
      heisFun c ψ Q w φ x = ψ (β x w.toCols₂ + 2⁻¹ * β w.toCols₁ w.toCols₂) * φ (x + w.toCols₁) := by
    intro w φ x
    show ψ (pr c Q _ _ + 2⁻¹ * pr c Q _ _) * _ = _
    rw [← hβ, ← hβ]
  have hJ : w * stdJ ν E = fromCols (-w.toCols₂) w.toCols₁ := by
    ext i (j | j) <;> simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, fromBlocks, toCols₁, toCols₂]
  funext x
  simp only [fou]
  rw [hh, hJ]
  simp only [four, hh, toCols₁_fromCols, toCols₂_fromCols, ← hβ]
  set x₁ := w.toCols₁
  set y₁ := w.toCols₂
  rw [← integral_add_right_eq_self (μ := μ) (fun y => ψ (β x y) * (ψ (β y x₁ + 2⁻¹ * β (-y₁) x₁) * φ (y + -y₁))) y₁,
    ← integral_const_mul]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add (f := _), map_neg, LinearMap.add_apply, LinearMap.neg_apply, hsym y x₁, hsym y₁ x₁]
  ring

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesWeylHeisenbergSchrodingerStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (fou c ψ Q μ φ) = fou c ψ Q μ (heisFun c ψ Q (w * stdJ ν E) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_fou | exact GlobalTheory.KSp.heisFun_fou | (intros; apply GlobalTheory.KSp.heisFun_fou <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompat
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem heisFun_parFun : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ _ χ _ _ p hp w φ
  have hc : ∀ z, c (c z) = z := hE.invol
  have hp0 : (mat c p).toBlocks₂₁ = 0 := hp
  set A := (mat c p).toBlocks₁₁ with hA
  set B := (mat c p).toBlocks₁₂ with hB
  set D := (mat c p).toBlocks₂₂ with hD
  have key : ∀ x y : Matrix α ν E, fromCols x y * mat c p = fromCols (x * A) (x * B + y * D) := by
    intro x y
    conv_lhs => rw [← fromBlocks_toBlocks (mat c p)]
    rw [fromCols_mul_fromBlocks, hp0]
    simp [hA, hB, hD]
  have spl : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp

  have h1 : ∀ x y : Matrix α ν E, form c Q (fromCols (x * A) 0) (fromCols 0 (y * D)) = form c Q (fromCols x 0) (fromCols 0 y) := by
    intro x y
    have h := form_mul c Q p (fromCols x 0) (fromCols 0 y)
    change form c Q (fromCols x 0 * mat c p) (fromCols 0 y * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x * A) (x * B), form_add_left, form_right_right, add_zero] at h
    exact h

  have h2 : ∀ x x' : Matrix α ν E, form c Q (fromCols (x' * A) 0) (fromCols 0 (x * B)) = form c Q (fromCols (x * A) 0) (fromCols 0 (x' * B)) := by
    intro x x'
    have h := form_mul c Q p (fromCols x' 0) (fromCols x 0)
    change form c Q (fromCols x' 0 * mat c p) (fromCols x 0 * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x' * A) (x' * B), spl (x * A) (x * B), form_add_left, form_add_right, form_add_right,
      form_left_left, form_left_left, form_right_right, form_swap c hc hQ (fromCols (x * A) 0) (fromCols 0 (x' * B))] at h
    linear_combination h
  have hw : w * mat c p = fromCols (w.toCols₁ * A) (w.toCols₁ * B + w.toCols₂ * D) := by
    conv_lhs => rw [← fromCols_toCols w]
    exact key _ _
  funext x
  simp only [heisFun, parFun, pr, hw, toCols₁_fromCols, toCols₂_fromCols]
  rw [← hA, ← hB]
  have key2 : ∀ (a b c d : F) (s t : ℂ), a + b = c + d → ψ a * (s * (ψ b * t)) = s * (ψ c * (ψ d * t)) := by
    intro a b c d s t h
    rw [show ψ a * (s * (ψ b * t)) = s * (ψ (a + b) * t) by rw [AddChar.map_add_eq_mul]; ring, h,
      AddChar.map_add_eq_mul]
    ring
  rw [Matrix.add_mul x w.toCols₁ A, Matrix.add_mul x w.toCols₁ B]
  simp only [e1, e2, form_add_left, form_add_right, h1]
  rw [h2 x w.toCols₁]
  apply key2
  ring

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicOperatorsHeisenbergCompatStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_operators_heisenberg_compat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  first | exact @GlobalTheory.KSp.heisFun_parFun | exact GlobalTheory.KSp.heisFun_parFun | (intros; apply GlobalTheory.KSp.heisFun_parFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenberg
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem weil_heis_intertwine : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hK
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ w : Matrix α (ν ⊕ ν) E, Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * mat c g)}
      one_mem' := by
        intro w
        have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
        rw [map_one, h1, Matrix.mul_one, mul_one, one_mul]
      mul_mem' := by
        intro g h hg hh w
        have hm : mat c (g * h) = mat c g * mat c h := rfl
        rw [map_mul, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc, hm, Matrix.mul_assoc]
      inv_mem' := by
        intro g hg w
        have h1 : mat c g⁻¹ * mat c g = 1 := by
          change (((g⁻¹ * g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
          rw [inv_mul_cancel]; rfl
        have h2 := hg (w * mat c g⁻¹)
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] at h2
        have h3 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h4 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        show Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹)
        calc Heisenberg₂ c hψ Q w * ω g⁻¹ = ω g⁻¹ * (ω g * Heisenberg₂ c hψ Q w) * ω g⁻¹ := by
              simp only [← mul_assoc, h3, one_mul]
          _ = ω g⁻¹ * (Heisenberg₂ c hψ Q (w * mat c g⁻¹) * ω g) * ω g⁻¹ := by rw [h2]
          _ = ω g⁻¹ * Heisenberg₂ c hψ Q (w * mat c g⁻¹) := by simp only [mul_assoc, h4, mul_one] }
  have hsieg : sieg c ν ≤ U := by
    intro p hp w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.par p hp]
    exact GlobalTheory.T.siegelParabolic_operators_heisenberg_compat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη p hp w φ
  have hweyl : weyl c ν ∈ U := by
    intro w
    refine LinearMap.ext fun φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, heis_apply, hK.wey]
    have hs : ∀ f : Matrix α ν E → ℂ, heisFun c ψ Q w (κ • f) = κ • heisFun c ψ Q w f := by
      intro f; funext x; simp only [heisFun, Pi.smul_apply, smul_eq_mul]; ring
    rw [hs, GlobalTheory.T.fourier_intertwines_weyl_heisenberg_schrodinger F E c δ hE α ν Q hQ ψ μ w φ]
    rfl
  have hU := GlobalTheory.T.siegelParabolic_weylElement_generate_unitary F E c δ hE ν U hsieg hweyl
  intro g w
  have hg : g ∈ U := hU ▸ Subgroup.mem_top g
  exact hg w

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationIntertwinesHeisenbergStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_intertwines_heisenberg : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (g : UG c (stdJ ν E)) (w : Matrix α (ν ⊕ ν) E), Heisenberg₂ c hψ Q w * ω g = ω g * Heisenberg₂ c hψ Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) := by
  first | exact @GlobalTheory.KSp.weil_heis_intertwine | exact GlobalTheory.KSp.weil_heis_intertwine | (intros; apply GlobalTheory.KSp.weil_heis_intertwine <;> assumption)
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α ν _ _ _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres
  letI : MeasurableSpace (Matrix α ν E) := borel _
  haveI : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, hG⟩ := hmat α ν
  haveI := hG.grp
  haveI := hG.t2
  haveI := hG.lc
  haveI := hG.sc
  obtain ⟨κ, ω, hKW⟩ := GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (Measure.addHaar)
  refine ⟨ω, GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_,
    GlobalTheory.T.weilRepresentation_intertwines_heisenberg F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_⟩
  · intro μ' hμ' g φ
    exact GlobalTheory.T.weil_representation_preserves_L2_space F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW μ' g φ
  · intro a φ x
    have hp : levi c hE.invol a ∈ sieg c ν := by
      rw [mem_sieg, mat, levi_val, toBlocks_fromBlocks₂₁]
    rw [hKW.par _ hp φ]
    have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
      simp [pr, form, GlobalTheory.WeilM.hTens]
    obtain ⟨-, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
    have hd := hsc (Matrix.GeneralLinearGroup.det a)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    simp only [parFun, mat, levi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_zero, h0,
      mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end GlobalTheory
