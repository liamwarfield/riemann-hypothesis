module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop
namespace PI.AprimeInfW

theorem expProdU_of_G (h : CayDensG) : ExpProdU := expProdU_of_cayProdU (cayProdU_of_G h)

theorem expProdU_of_hua (h1 : CayDensEx) (h2 : CayValId) : ExpProdU := expProdU_of_G (cayDensG_of h1 h2)

end PI.AprimeInfW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix NNReal

theorem injOn_nhds_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hinj : Function.Injective f') : ∃ s ∈ 𝓝 a, InjOn f s := by
  obtain ⟨K, hK, hanti⟩ := (f' : E →ₗ[ℝ] F).injective_iff_antilipschitz.mp hinj
  have hc : (0 : ℝ≥0) < (2 * K)⁻¹ := by
    apply inv_pos.2
    exact mul_pos (by norm_num) hK
  obtain ⟨s, hs, hap⟩ := hf.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (Or.inr hc)
  refine ⟨s, hs, fun x hx y hy hxy => ?_⟩
  have h1 : ‖f x - f y - f' (x - y)‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖ := hap x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 : dist x y ≤ K * dist (f' x) (f' y) := hanti.le_mul_dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h3 : ‖x - y‖ ≤ ‖x - y‖ / 2 := by
    calc ‖x - y‖ ≤ K * ‖f' (x - y)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 hK'.le
      _ = ‖x - y‖ / 2 := by
        push_cast
        field_simp
  have : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)


set_option backward.isDefEq.respectTransparency false in
theorem exp_mul_injOn {ι V : Type} [Fintype ι] [Fintype V] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)) (P : V → Matrix (Fin n) (Fin n) ℂ)
    (hker : ∀ x, (∀ v, L x v * P v = 0) → x = 0) :
    ∃ r : ℝ, 0 < r ∧ InjOn (fun x => fun v => NormedSpace.exp (L x v) * P v) (ball 0 r) := by
  open scoped Matrix.Norms.Operator in
  let Lc : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) := L.toContinuousLinearMap
  let R : V → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    fun v => (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip (P v)
  let f' : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    ContinuousLinearMap.pi fun v => (R v).comp ((ContinuousLinearMap.proj v).comp Lc)
  have hf' : ∀ x v, f' x v = L x v * P v := fun x v => rfl
  have hd : HasStrictFDerivAt (fun x => fun v => NormedSpace.exp (L x v) * P v) f' 0 := by
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    rw [hasStrictFDerivAt_pi]
    intro v
    have h0 : HasStrictFDerivAt (fun x : EuclideanSpace ℝ ι => L x v)
        ((ContinuousLinearMap.proj v).comp Lc) 0 :=
      ((ContinuousLinearMap.proj v).comp Lc).hasStrictFDerivAt
    have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L 0 v) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    have h2 : HasStrictFDerivAt (fun x => (R v) (NormedSpace.exp (L x v)))
        ((R v).comp ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ).comp
          ((ContinuousLinearMap.proj v).comp Lc))) 0 :=
      (R v).hasStrictFDerivAt.comp 0 (he.comp 0 h0)
    convert h2 using 1 <;> rfl
  have hinj : Function.Injective f' := by
    intro x y hxy
    have : x - y = 0 := hker (x - y) fun v => by
      have := congrFun (congrArg (fun g => g) (show f' (x - y) = 0 by rw [map_sub, hxy, sub_self])) v
      rwa [hf'] at this
    exact sub_eq_zero.1 this
  obtain ⟨s, hs, hsi⟩ := injOn_nhds_of_strict hd hinj
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  exact ⟨r, hr, hsi.mono hrs⟩

theorem toInf_injective {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    Function.Injective (X.toInf hb) := by
  intro s t h
  have e := PI.AprimeInfU.eq_of_ofHA X hb ((s, 1) : X.B.I.GA) ((t, 1) : X.B.I.GA)
    (PI.AprimeInfU.ofHAInf_congr X _ _ h)
    (PI.AprimeInfU.ofHAFin_congr X _ _ (by rw [PI.AprimeInfU.toHA_fin_one X hb s, PI.AprimeInfU.toHA_fin_one X hb t]))
  exact congrArg Prod.fst e

def toInfHom {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    X.B.I.Ginf →* HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  MonoidHom.mk' (X.toInf hb) (PI.AprimeInfU.toInf_mul X hb)

theorem lie_zero_of_cols {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hL : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) (hB : ∀ i ∈ S, ∀ j ∈ S, M i j = 0)
    (hC : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0) : M = 0 := by
  have hcol : ∀ r s, s ∉ S → M r s = 0 := by
    intro r s hs
    have := congrFun (congrFun hC r) s
    rw [Matrix.mul_diagonal] at this
    simpa [hs] using this
  ext r s
  by_cases hs : s ∈ S
  · by_cases hr : r ∈ S
    · exact hB r hr s hs
    · have h := congrFun (congrFun hL s) r
      simp only [Formalism.REAL.Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.conjTranspose_apply, Matrix.zero_apply, hcol s r hr, mul_zero, add_zero] at h
      have hd : (if ε r = true then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have := (mul_eq_zero.1 h).resolve_right hd
      simpa using this
  · exact hcol r s hs

theorem grpInj_holds : GrpInj := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  have hc := ctx.2.1
  have hL := ctx.2.2.1
  have hB := ctx.2.2.2
  set P : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ :=
    fun v => Matrix.diagonal (fun k => if k ∈ S v then (0 : ℂ) else 1) with hP
  have hnorm : ∀ {κ' : Type} [Fintype κ'] (x : EuclideanSpace ℝ κ')
      (M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ),
      M = 0 → ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 = ‖x‖ ^ 2 → x = 0 := by
    intro κ' _ x M hM h
    subst hM
    simp only [Pi.zero_apply, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h.symm)
  obtain ⟨r1, hr1, hi1⟩ := exp_mul_injOn L P fun x hx => by
    refine hnorm x (L x) (funext fun v => lie_zero_of_cols (X.B.I.ε v) (S v) _ (hL.1 x v).1 (hL.1 x v).2 (hx v))
      (hL.2.1 x)
  obtain ⟨r2, hr2, hi2⟩ := exp_mul_injOn L₁ (fun _ => 1) fun x hx => by
    refine hnorm x (L₁ x) (funext fun v => by simpa using hx v) (hB.2.1 x)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun a ha b hb' hm => ?_, fun y hy y' hy' he => ?_⟩
  ·
    have e1 : (kap0 X hb c L a)⁻¹ * kap0 X hb c L b =
        X.toInf hb (c * ((fun v => expU (X.B.I.ε v) (L a v))⁻¹ * (fun v => expU (X.B.I.ε v) (L b v))) * c⁻¹) := by
      unfold kap0
      change (toInfHom X hb _)⁻¹ * toInfHom X hb _ = toInfHom X hb _
      rw [← map_inv, ← map_mul]
      congr 1
      group
    rw [e1] at hm
    have hstd := (hc.2 _).1 hm
    apply hi1 (ball_subset_ball (min_le_left _ _) ha) (ball_subset_ball (min_le_left _ _) hb')
    funext v
    have hv := hstd v
    set u := expU (X.B.I.ε v) (L a v) with hu
    set w := expU (X.B.I.ε v) (L b v) with hw
    have hcol : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v = P v := by
      ext j i
      simp only [hP, Matrix.mul_diagonal, Matrix.diagonal_apply]
      by_cases hi : i ∈ S v
      · by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji, hi]
      · have := hv i hi j
        simp only [Pi.mul_apply, Pi.inv_apply] at this
        rw [this]
        by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji]
    have ea : NormedSpace.exp (L a v) = (((u : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 a v).1).symm
    have eb : NormedSpace.exp (L b v) = (((w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 b v).1).symm
    show NormedSpace.exp (L a v) * P v = NormedSpace.exp (L b v) * P v
    rw [ea, eb]
    set U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (u : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hU
    set W : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (w : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hW
    have e4 : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) =
        ((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := rfl
    rw [e4] at hcol
    calc (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v
        = (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
            (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v) := by rw [hcol]
      _ = (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  ·
    have e2 := toInf_injective X hb he
    have e3 : ((fun v => expU (X.B.I.ε v) (L₁ y v)) : X.B.I.Ginf) = fun v => expU (X.B.I.ε v) (L₁ y' v) := by
      simpa using e2
    apply hi2 (ball_subset_ball (min_le_right _ _) hy) (ball_subset_ball (min_le_right _ _) hy')
    funext v
    have := congrArg (fun g : X.B.I.Ginf => (((g v : Formalism.REAL.UJ (X.B.I.ε v)) :
      (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) e3
    rw [expU_val _ _ (hB.1 y v).1, expU_val _ _ (hB.1 y' v).1] at this
    show NormedSpace.exp (L₁ y v) * 1 = NormedSpace.exp (L₁ y' v) * 1
    rw [this]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.StdConjExOfWitt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FixIffSpan
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : Fin X.B.I.n → ℂ :=
  (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (tupH (frameOf X u') b i)

def StabInfV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Ginf), X.toInf hb x ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔
      ∀ v b, uMat (x v) *ᵥ wV X u' v b = wV X u' v b

def WittBlock : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : NumberField.InfinitePlace X.B.I.F,
    ∃ (S : Finset (Fin X.B.I.n)) (c : Formalism.REAL.UJ (X.B.I.ε v)),
      (S.card = D.R.k ∧ ∀ i ∈ S, X.B.I.ε v i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ wV X u' v b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin X.B.I.n → ℂ)) '' (↑S)ᶜ)

theorem fix_iff_span {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (u : ι → Fin n → ℂ) (S : Finset (Fin n))
    (hspan : Submodule.span ℂ (Set.range u) =
      Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)) :
    (∀ b, A *ᵥ u b = u b) ↔ ∀ i ∉ S, ∀ j, A j i = if j = i then 1 else 0 := by
  classical
  have hker : ∀ x, A *ᵥ x = x ↔ x ∈ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    intro x
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have e1 : (∀ b, A *ᵥ u b = u b) ↔ Submodule.span ℂ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    rw [Submodule.span_le]
    constructor
    · rintro h _ ⟨b, rfl⟩; exact (hker _).1 (h b)
    · intro h b; exact (hker _).2 (h ⟨b, rfl⟩)
  rw [e1, hspan, Submodule.span_le]
  constructor
  · intro h i hi j
    have h1 := (hker _).2 (h ⟨i, hi, rfl⟩)
    rw [Matrix.mulVec_single_one] at h1
    have := congrFun h1 j
    simp only [Matrix.col_apply, Pi.single_apply] at this
    exact this
  · rintro h _ ⟨i, hi, rfl⟩
    refine (hker _).1 ?_
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply, Pi.single_apply]
    exact h i hi j

theorem stdConjEx_of (h1 : StabInfV) (h2 : WittBlock) : StdConjEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  have h2' := h2 X u' ψ hT μinf νinf fibInf hP
  choose S c hS hspan using h2'
  refine ⟨c, S, fun v => hS v, fun g => ?_⟩
  rw [h1 X u' hb (c * g * c⁻¹)]
  refine forall_congr' fun v => ?_
  refine Iff.trans ?_ (fix_iff_span (uMat (g v)) (fun b => uMat (c v)⁻¹ *ᵥ wV X u' v b) (S v) (hspan v))
  refine forall_congr' fun b => ?_
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * uMat (g v) * uMat (c v)⁻¹ := by
    simp [uMat]
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  have hci' : uMat (c v) * uMat (c v)⁻¹ = 1 := by simp [uMat]
  rw [hm]
  constructor
  · intro h
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) h
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [Matrix.mulVec_mulVec]
    exact h'
  · intro h
    calc (uMat (c v) * uMat (g v) * uMat (c v)⁻¹) *ᵥ wV X u' v b
        = uMat (c v) *ᵥ (uMat (g v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = uMat (c v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b) := by rw [h]
      _ = wV X u' v b := by rw [Matrix.mulVec_mulVec, hci', Matrix.one_mulVec]

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
  Formalism.L2.SG.Measures
open scoped TensorProduct Matrix

theorem theta_lin_indep {F E : Type} [Field F] [Field E] [Algebra F E] (φ : E →+* ℂ) (σ : E →+* E)
    (hσφ : ∀ a, φ (σ a) = starRingEnd ℂ (φ a)) (hfix : ∀ a, σ a = a → a ∈ Set.range (algebraMap F E))
    (b : Module.Basis (Fin 2) F E) (r : Fin 2 → ℝ) (h : (r 0 : ℂ) * φ (b 0) + (r 1 : ℂ) * φ (b 1) = 0) :
    r 0 = 0 ∧ r 1 = 0 := by
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hφ0 : φ (b 0) ≠ 0 := (map_ne_zero φ).2 hb0
  have hr1 : r 1 = 0 := by
    by_contra hr
    have hr' : (r 1 : ℂ) ≠ 0 := by exact_mod_cast hr
    set γ := b 1 / b 0 with hγ
    have hφγ : φ γ = ((-(r 0 / r 1) : ℝ) : ℂ) := by
      rw [hγ, map_div₀, div_eq_iff hφ0]
      push_cast
      field_simp
      first | linear_combination h | linear_combination -h | linear_combination (↑(r 1) : ℂ)⁻¹ * h
    have hσγ : σ γ = γ := by
      apply φ.injective
      rw [hσφ, hφγ, Complex.conj_ofReal]
    obtain ⟨a, ha⟩ := hfix γ hσγ
    have h1 : b 1 = a • b 0 := by
      rw [Algebra.smul_def, ha, hγ, div_mul_cancel₀ _ hb0]
    exact absurd h1 (by
      intro e
      have hli := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      have := hli (fun i => if i = 0 then a else -1) (by
        rw [Fin.sum_univ_two]
        simp [e])
      simpa using this 1)
  refine ⟨?_, hr1⟩
  rw [hr1] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_eq_zero, hφ0, or_false] at h
  exact_mod_cast h

theorem thetaInf_tmul {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (c : Ainf X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (c ⊗ₜ[X.B.I.F] e) = PI.AprimeInfU.evInf X v c * X.B.I.φ v e := by
  simp only [PI.AprimeInfU.thetaInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
  rfl

theorem thetaInf_inj {D : D7} (X : HidaSetting D) (y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (h : ∀ v, PI.AprimeInfU.thetaInf X v y = 0) : y = 0 := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) b
  have hy : y = ∑ i, B.repr y i ⊗ₜ[X.B.I.F] b i := by
    conv_lhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hc : ∀ i, B.repr y i = 0 := by
    intro i
    change (B.repr y i : (v : InfinitePlace X.B.I.F) → v.Completion) = 0
    funext v
    have hvr : v.IsReal := IsTotallyReal.isReal v
    have hv := h v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, Fin.sum_univ_two, thetaInf_tmul, thetaInf_tmul] at hv
    have hev : ∀ c : Ainf X.B.I.F, PI.AprimeInfU.evInf X v c =
        ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
          ((c : (w : InfinitePlace X.B.I.F) → w.Completion) v) : ℝ) : ℂ) := by
      intro c
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      rfl
    rw [hev, hev] at hv
    have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
      (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
      (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b
      (fun i => InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v)) hv
    have hz : InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v) = 0 := by
      fin_cases i
      · exact key.1
      · exact key.2
    exact (map_eq_zero_iff _ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr).injective).1 hz
  rw [hy]
  simp [hc]

theorem thetaInf_inclR {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (inclR (Ainf X.B.I.F) e) = X.B.I.φ v e := by
  rw [show inclR (Ainf X.B.I.F) e = (1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e from rfl, thetaInf_tmul, map_one, one_mul]

theorem uMat_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) :
    uMat (x v) = (X.B.I.P v)⁻¹ * (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) :
      GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map (PI.AprimeInfU.thetaInf X v) *
      X.B.I.P v := by
  have e : uMat (x v) = ofHAInf X.B.I (toHA X.B.I hb (x, 1)) v := ((toHA_isBridge X.B.I hb) (x, 1)).1 v
  rw [e]
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, PI.AprimeInfU.thetaV_eq]
  rfl

theorem stabInfV_holds : StabInfV := by
  intro D X u' hb x
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hPu : ∀ v, IsUnit (X.B.I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hmap : ∀ v, Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹ := by
    intro v
    rw [uMat_toInf X hb x v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.mul_one]
  have hvec : ∀ v b i, PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) =
      ((Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
    intro v b i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  have hY0 : ∀ v b i, PI.AprimeInfU.thetaInf X v (Y0 X u' b i) = X.B.I.φ v (tupH (frameOf X u') b i) := by
    intro v b i
    rw [show Y0 X u' b i = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b i) from rfl, thetaInf_inclR]
  have hsmul : X.toInf hb x • Y0 X u' = fun b => Mm *ᵥ Y0 X u' b := rfl
  rw [MulAction.mem_stabilizer_iff, hsmul]
  constructor
  · intro hfix v b
    have h1 : (Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ (fun j => X.B.I.φ v (tupH (frameOf X u') b j)) =
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext i
      rw [← hvec, ← hY0]
      exact congrArg (PI.AprimeInfU.thetaInf X v) (congrFun (congrFun hfix b) i)
    rw [hmap] at h1
    unfold wV
    have h2 := congrArg (fun z => (X.B.I.P v)⁻¹ *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hPu v), Matrix.one_mul] at h2
    rw [Matrix.mulVec_mulVec]
    exact h2
  · intro hw
    funext b i
    have h0 : Mm *ᵥ Y0 X u' b - Y0 X u' b = 0 := by
      funext i'
      refine thetaInf_inj X _ fun v => ?_
      rw [Pi.sub_apply, map_sub, hvec, hY0, hmap, sub_eq_zero]
      have hv := hw v b
      unfold wV at hv
      calc ((X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i'
          = (X.B.I.P v *ᵥ (uMat (x v) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)))) i' := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (X.B.I.P v *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i' := by rw [hv]
        _ = X.B.I.φ v (tupH (frameOf X u') b i') := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mulVec]
    exact sub_eq_zero.1 (congrFun h0 i)

theorem stdConjEx_of_witt (h : WittBlock) : StdConjEx := stdConjEx_of stabInfV_holds h

end PI.AprimeInfW
end
end
