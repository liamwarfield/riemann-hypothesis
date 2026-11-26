module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyAt0PolDEquivariant
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.BasicNotions NumberField GlobalTheory.ThStr GlobalTheory.ThBe0 Classical

namespace GlobalTheory.ClassSumEquiv

open MvPolynomial

theorem polD_subst (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ τ, (γ' τ).det ≠ 0) :
    aeval (fun l : Idx D N N' => ∑ k, C ((γ' l.1)⁻¹ k l.2.1) * (X (l.1, k, l.2.2) : MvPolynomial (Idx D N N') ℂ))
      (aeval (fun l : Idx D N N' => ∑ k, C (γ l.1 l.2.2 k) * (X (l.1, l.2.1, k) : MvPolynomial (Idx D N N') ℂ))
        (polD D s Q (fun τ => γ' τ * y' τ))) =
      polD D s (aeval (fun k : FrV D N => ∑ a : Fin N, C (γ k.1 k.2.1 a) *
        (X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y' := by
  unfold polD
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun ⟨τ, a, k⟩ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hk
  · have e : y' τ b' ⟨k, hk⟩ = ∑ b, (γ' τ)⁻¹ b' b * (γ' τ * y' τ) b ⟨k, hk⟩ := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ (h τ).isUnit]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · simp

theorem applyAt0_polD_equivariant : ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ) (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (G : VC D N N' → ℂ), (∀ τ, (γ' τ).det ≠ 0) → Differentiable ℂ G → applyAt0 D (polD D s Q (fun τ => γ' τ * y' τ)) (fun z => G (fun τ => ((γ' τ)⁻¹ * Matrix.of (z τ) * γ τ : Matrix (Fin N') (Fin N) ℂ))) = applyAt0 D (polD D s (MvPolynomial.aeval (fun k : FrV D N => ∑ a : Fin N, MvPolynomial.C (γ k.1 k.2.1 a) * (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y') G := by
  intro D N N' s Q y' γ' γ G h hG
  have hd : Differentiable ℂ (fun z => G (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹) z)) :=
    hG.comp (LinearMap.toContinuousLinearMap (GlobalTheory.NormSum.Minor.mulL (a := N) (fun τ => (γ' τ)⁻¹))).differentiable
  have h1 := GlobalTheory.NormSum.Minor.applyAt0_comp hd (GlobalTheory.NormSum.Minor.mulR γ) (fun l k => γ l.1 l.2.2 k)
    (fun l k => (l.1, l.2.1, k)) (GlobalTheory.NormSum.Minor.mulR_coordV γ) (polD D s Q (fun τ => γ' τ * y' τ))
  rw [GlobalTheory.NormSum.Minor.applyAt0_comp hG (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹))
    (fun l k => (γ' l.1)⁻¹ k l.2.1) (fun l k => (l.1, k, l.2.2)) (GlobalTheory.NormSum.Minor.mulL_coordV _),
    polD_subst D N N' s Q y' γ' γ h] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]
  rfl

end GlobalTheory.ClassSumEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

open GlobalTheory.KerWt

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) (k : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : GL3Theta.applyAt0 D P (fun z => k * G z) = k * GL3Theta.applyAt0 D P G := by
  exact (GlobalTheory.NormSum.applyAt0_minorPol_linear D N N' (fun _ => 0) G hG).2.2.1 k P

theorem applyAt0_polD_eigen (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' γ : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (k : ℂ) (hγ : ∀ τ, (γ τ).det ≠ 0)
    (hG : Differentiable ℂ G) (hk : ∀ z : TaylorLogMetric.VC D N N', G (fun τ => (γ τ * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * G z) :
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q (fun τ => γ τ * y' τ)) G = k * GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  have h := GlobalTheory.ClassSumEquiv.applyAt0_polD_equivariant D N N' s Q y' γ (fun _ => 1) (fun z => k * G z) hγ (hG.const_mul k)
  have e1 : (fun z : TaylorLogMetric.VC D N N' => k * G (fun τ => ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N') (Fin N) ℂ))) = G := by
    funext z
    refine (hk _).symm.trans (congrArg G (funext fun τ => ?_))
    have : (γ τ * ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N') (Fin N) ℂ) = Matrix.of (z τ) := by
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hγ τ).isUnit]
    exact this
  have e2 : (MvPolynomial.aeval (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) Q) = Q := by
    have : (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) = MvPolynomial.X := by
      funext k
      rw [Finset.sum_eq_single k.2.1]
      · simp
      · intro b _ hb
        simp [Matrix.one_apply_ne hb.symm]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  beta_reduce at h
  rw [e1, e2, applyAt0_const_mul D _ k G hG] at h
  exact h

theorem lawAt_Kmap : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi h c c' hd g ⟨hdet, k, hk, hg⟩ f ⟨P, hP, hf⟩ y y' hy
  obtain ⟨n, hw, hn, -, -⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hs : C.sharp i f = frPoly O i (MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) (RingHom.id ℂ) _ (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    rw [hf]
    exact h1
  have hQ : MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ (nuT D u i) := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ (lamTG M i) n (MvPolynomial.map (RingHom.id ℂ) P) (map_mem_VV _ _ P hP)
    have e : (fun τ r => (lamTG M i τ).natW r + n τ) = nuT D u i := by funext τ r; exact hw τ r
    rwa [e] at h2
  generalize MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ = Q at hs hQ
  have hu : ∀ x : C.Y (i + 1), C.unf i c c' (C.sharp i f) x =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c') := fun x => by
    rw [hs]
    exact (unfolding_iff_alt D u C O i hi.le _).1 h c c' Q hQ x
  have hK : ∀ x : C.Y (i + 1), C.Kmap i c c' f x = (C.rhoDet i c * C.rhoDet' i c') *
      ((∏ τ, (O.frm (i + 1) x τ).det ^ C.sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c')) := fun x => by
    rw [← hu x]
    simp only [← O.frm_de (i + 1) hi]
    rfl
  have hdm : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det = TaylorLogMetric.embT D τ g.1.det := fun τ => ((TaylorLogMetric.embT D τ).map_det g.1).symm
  have hne : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det ≠ 0 := fun τ => by
    rw [hdm]; exact (map_ne_zero _).2 hdet
  have hy' : O.frm (i + 1) y = fun τ => g.1.map (TaylorLogMetric.embT D τ) * O.frm (i + 1) y' τ := funext hy
  rw [hK, hK, hy', applyAt0_polD_eigen D _ _ _ Q _ _ _ k hne hd hk, hg]
  simp only [Matrix.det_mul, hdm, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  ring

end GlobalTheory.KerJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLawStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kernel_term_target_stabiliser_law : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.lawAt_Kmap | exact GlobalTheory.KerJ.lawAt_Kmap | (intros; apply GlobalTheory.KerJ.lawAt_Kmap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
open IsDedekindDomain NumberField

namespace GlobalTheory

theorem antitone_zero_one_eq_of_sum_eq {n : ℕ} (d e : Fin n → ℤ) (hd : Antitone d) (he : Antitone e)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (hs : ∑ i, d i = ∑ i, e i) : d = e := by
  have key : (∀ i, d i ≤ e i) ∨ (∀ i, e i ≤ d i) := by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    have := hd0 j; have := hd1 i; have := he0 i; have := he1 j
    rcases le_total i j with hij | hij
    · have := he hij; omega
    · have := hd hij; omega
  rcases key with h | h
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs i (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs.symm i (Finset.mem_univ i)).symm

section

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem glint_entry_mem_Ov {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v := by
  obtain ⟨g, rfl⟩ := hk
  have : ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j
      = (((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)) i j : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    simp [Formalism.UG.bc, Units.coe_map]
  rw [this]
  exact Subtype.property _

theorem mul_mul_entry_mem_Ov {A B C : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) (hB : ∀ i j, B i j ∈ Formalism.UG.Ov F v)
    (hC : ∀ i j, C i j ∈ Formalism.UG.Ov F v) (i j : Fin n) : (A * B * C) i j ∈ Formalism.UG.Ov F v := by
  simp only [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _) (hB _ _)) (hC _ _)

theorem valued_det_le_one_of_entries {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) : Valued.v A.det ≤ 1 := by
  have : A.det ∈ Formalism.UG.Ov F v := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hA _ _)
  exact this

theorem valued_det_eq_one_of_glint {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  have h1 := valued_det_le_one_of_entries (glint_entry_mem_Ov hk)
  have h2 := valued_det_le_one_of_entries (glint_entry_mem_Ov (Subgroup.inv_mem _ hk))
  have h3 : Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det *
      Valued.v ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem cartan_minuscule (k : ℕ) (ϖ ϖ' : v.adicCompletion F)
    (hϖ : Formalism.UG.IsUnifV F v ϖ) (hϖ' : Formalism.UG.IsUnifV F v ϖ') (a : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h2 : ∀ i j, ϖ' * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h3 : Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k) :
    ∃ d : Fin n → ℤ, Antitone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ 1) ∧ ∑ i, d i = k ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hv' : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    show Valued.v ϖ ≤ 1
    rw [hv]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hpow : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
    intro m
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]
    simp
  have hsum : ∀ d : Fin n → ℤ, ∏ i, ϖ ^ d i = ϖ ^ ∑ i, d i := by
    intro d
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hϖ0]
  obtain ⟨d, hd, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ a
  have hD : ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDinv : ((k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ (-d) := by
    have e1 : (k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) = (k₁⁻¹ * a * k₂⁻¹)⁻¹ := by group
    rw [e1, Matrix.coe_units_inv, hD]
    apply Matrix.inv_eq_left_inv
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0]
    simp
  refine ⟨d, hd, fun i => ?_, fun i => ?_, ?_, k₁, hk₁, k₂, hk₂, hD⟩
  · have := mul_mul_entry_mem_Ov (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₁)) h1
      (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₂)) i i
    rw [← Units.val_mul, ← Units.val_mul, hD] at this
    have h : Valued.v (Formalism.UG.diagPow F v ϖ d i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, hpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h
    omega
  · have := mul_mul_entry_mem_Ov (B := ϖ' • ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F))) (glint_entry_mem_Ov hk₂) h2
      (glint_entry_mem_Ov hk₁) i i
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, ← Units.val_mul, hDinv] at this
    have h : Valued.v (ϖ' * Formalism.UG.diagPow F v ϖ (-d) i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, map_mul, hpow, hv', ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    simp only [Pi.neg_apply] at h
    omega
  · rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, valued_det_eq_one_of_glint hk₁,
      valued_det_eq_one_of_glint hk₂, one_mul, mul_one, Formalism.UG.diagPow, Matrix.det_diagonal,
      hsum, hpow, hv', ← WithZero.exp_nsmul, WithZero.exp_inj] at h3
    simp only [nsmul_eq_mul] at h3
    omega

end

theorem glint_doubleCoset_of_minuscule : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ) (ϖ ϖ' : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → Formalism.UG.IsUnifV F v ϖ' → ∀ a a' : GL (Fin n) (v.adicCompletion F), (∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ ^ k → (∀ i j, (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ' * ((a'⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k → ∃ x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ y ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), a' = x * a * y := by
  intro F _ _ v n k ϖ ϖ' hϖ hϖ' a a' h1 h2 h3 h1' h2' h3'
  obtain ⟨d, hd, hd0, hd1, hs, k₁, hk₁, k₂, hk₂, hD⟩ := cartan_minuscule k ϖ ϖ hϖ hϖ a h1 h2 h3
  obtain ⟨e, he, he0, he1, ht, l₁, hl₁, l₂, hl₂, hE⟩ :=
    cartan_minuscule k ϖ ϖ' hϖ hϖ' a' h1' h2' h3'
  obtain rfl : d = e := antitone_zero_one_eq_of_sum_eq d e hd he hd0 hd1 he0 he1 (hs.trans ht.symm)
  have h : k₁⁻¹ * a * k₂⁻¹ = l₁⁻¹ * a' * l₂⁻¹ := Units.ext (hD.trans hE.symm)
  refine ⟨l₁ * k₁⁻¹, Subgroup.mul_mem _ hl₁ (Subgroup.inv_mem _ hk₁), k₂⁻¹ * l₂,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂) hl₂, ?_⟩
  calc a' = l₁ * (l₁⁻¹ * a' * l₂⁻¹) * l₂ := by group
    _ = l₁ * (k₁⁻¹ * a * k₂⁻¹) * l₂ := by rw [h]
    _ = _ := by group

end GlobalTheory
end
