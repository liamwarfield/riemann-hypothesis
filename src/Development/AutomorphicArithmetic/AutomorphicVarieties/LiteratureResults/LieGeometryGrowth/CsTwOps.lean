module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_contDiffOn {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F} (hw : ContDiffOn ℝ ∞ w Y) :
    ContDiffOn ℝ ∞ (tp A B w) Y := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  refine altSmooth _ _ _ q _ z fun v => ?_
  have h1 : ContDiffAt ℝ ∞ (fun y : V => w (A y)) z :=
    (hw.contDiffAt (hY.mem_nhds (hA z hz))).comp z A.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun y : V => w (A y) fun i => A (v i)) z :=
    (ContinuousAlternatingMap.apply ℝ V F (fun i => A (v i))).contDiff.contDiffAt.comp z h1
  exact B.contDiff.contDiffAt.comp z h2

private theorem twOps_abs {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A A' : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) (hA' : ∀ p ∈ Y, A' p ∈ Y) (h1 : ∀ p, A (A' p) = p) (h2 : ∀ p, A' (A p) = p)
    {W : V → V} (hW : IsField Y W) :
    IsField Y (fun p => A' (W (A p))) ∧ (∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p))) ∧
    ∀ q : ℕ, (∀ w : V → V [⋀^Fin q]→L[ℝ] F, ∀ p ∈ Y,
        tp A B (pb (flow W 1) w) p = pb (flow (fun p => A' (W (A p))) 1) (tp A B w) p) ∧
      ∀ w : V → V [⋀^Fin (q + 1)]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → ∀ p ∈ Y,
        tp A B (hom W w) p = hom (fun p => A' (W (A p))) (tp A B w) p := by
  have hf : ∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p)) := fun t p => by
    simp only [flow, map_add (f := _), map_smul, h2]
  have hZ : IsField Y (fun p => A' (W (A p))) :=
    ⟨A'.contDiff.comp_contDiffOn (hW.1.comp A.contDiff.contDiffOn hA), fun p hp t ht => by
      rw [hf]; exact hA' _ (hW.2 _ (hA p hp) t ht)⟩
  refine ⟨hZ, hf, fun q => ?_⟩
  have nat := pbNat V F Y hY A' B W _ hW hZ hA' (fun p _ => by simp only [h1]) q
  have rel : ∀ (n : ℕ) (w : V → V [⋀^Fin n]→L[ℝ] F), ∀ p ∈ Y, ∀ v : Fin n → V,
      tp A B w (A' p) (fun i => A' (v i)) = B (w p v) := fun n w p _ v => by
    simp only [tp_apply, h1]
  refine ⟨fun w p hp => ?_, fun w hw p hp => ?_⟩
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := nat.1 _ _ (rel q w) 1 ⟨zero_le_one, le_rfl⟩ _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := (nat.2 _ _ (rel (q + 1) w)).2 hw (tp_contDiffOn hY A B hA hw) _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm

theorem UpperTheory.V.Lit.Geo.Cs.twOps :
    UpperTheory.V.Lit.Geo.Cs.TwOps := by
  intro E _ _ _ a ho U Ξ W hW g x
  have h1 : ∀ p : HV E a, sand g (sand g⁻¹ p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h2 : ∀ p : HV E a, sand g⁻¹ (sand g p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  obtain ⟨k1, k2, k3⟩ := twOps_abs ho (sand g) (sand g⁻¹) (mulVecL (Ξ.mat g⁻¹)) (fun p hp => sand_mem_cone g hp)
    (fun p hp => sand_mem_cone g⁻¹ hp) h1 h2 (hW.field (QuotientGroup.mk x))
  refine ⟨k1, k2, fun q => ?_⟩
  have app := omApply _ _ _ _ (geo ho U Ξ) W hW q
  refine ⟨fun w => ⟨tp_contDiffOn ho _ _ (fun p hp => sand_mem_cone g hp) (w.2 _).1, fun p hp => ?_⟩, fun w p hp => ?_⟩
  · refine Eq.trans ?_ ((k3 q).1 (w.1 _) p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.1 w _ _ (sand_mem_cone g hp)]
  · refine Eq.trans ?_ ((k3 q).2 (w.1 _) (w.2 _).1 p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.2 w _ _ (sand_mem_cone g hp)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz
open UpperTheory.V.Lit.Geo.Cs GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTSmooth
open GlobalTheory.ThetaPull (invL invL_smooth)
open scoped ContDiff Topology

private theorem sz_succ {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h0 : ‖f p‖ ≤ b) (h1 : Sz k (fderiv ℝ f) p b) : Sz (k + 1) f p b := by
  intro i hi
  cases i with
  | zero => simpa using h0
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv]
    exact h1 i (Nat.le_of_succ_le_succ hi)

theorem UpperTheory.V.Lit.Geo.Cs.chartSz :
    ChartSz := by
  intro E _ _ _ a k ρ hρ
  have h1 : oneL E a ∈ invSet E a := isUnit_one
  have hval : ∀ (φ : Sm E a), (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖chart φ.1 g (oneL E a)‖ ≤ C * ρ g := by
    intro φ hφ
    obtain ⟨C, hC⟩ := hφ []
    refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
    have e := chart_val φ.1 g 1
    rw [map_one, mul_one] at e
    have e' : chart φ.1 g (oneL E a) = φ.1 g := e
    rw [e']
    exact (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ g))
  induction k with
  | zero =>
    intro φ hφ
    obtain ⟨C, hC0, hC⟩ := hval φ hφ
    refine ⟨C, hC0, fun g i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    simpa using hC g
  | succ k ih =>
    intro φ hφ
    obtain ⟨C₀, hC0, hC⟩ := hval φ hφ
    have hi : ∀ i : Ix E a, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart (lie E a (bs E a i) φ).1 g) (oneL E a) (C * ρ g) := by
      intro i
      refine ih _ fun l => ?_
      obtain ⟨C, hC⟩ := hφ (l ++ [bs E a i])
      refine ⟨C, fun g => ?_⟩
      have := hC g
      rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply] at this
    choose D hD0 hD using hi
    let Θ : Ix E a → Lie E a → (ℂ →L[ℝ] (Lie E a →L[ℝ] ℂ)) := fun i y =>
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y))
    have hΘ : ∀ i, ContDiffAt ℝ ∞ (Θ i) (oneL E a) := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ).contDiff.contDiffAt.comp _
        ((coordL i).contDiff.contDiffAt.comp _ ((invL_smooth (E := E) (a := a)).1 _ h1))
    choose B hB using fun i => exists_sz k (Θ i) (oneL E a)
    have hS0 : 0 ≤ ∑ i, 2 ^ k * B i * D i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB i).nonneg) (hD0 i)
    refine ⟨C₀ + ∑ i, 2 ^ k * B i * D i, add_nonneg hC0 hS0, fun g => sz_succ ?_ ?_⟩
    · exact (hC g).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (hρ g))
    · have hc : ∀ i, ContDiffAt ℝ ∞ (chart (lie E a (bs E a i) φ).1 g) (oneL E a) := fun i =>
        contDiffAt_chart (lie E a (bs E a i) φ).2 g h1
      have key := (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).2.2 (Ix E a) Finset.univ
        (fun i y => Θ i y (chart (lie E a (bs E a i) φ).1 g y)) (fun i => 2 ^ k * B i * (D i * ρ g))
        (fun i _ => (hΘ i).clm_apply (hc i))
        (fun i _ => (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).1 _ _ _ _ (hΘ i) (hc i) (hB i) (hD i g))
      refine (key.congr ?_).mono ?_
      · filter_upwards [isOpen_invSet.mem_nhds h1] with y hy
        exact (fderiv_chart_eq φ g hy).symm
      · rw [add_mul, Finset.sum_mul]
        refine le_add_of_nonneg_of_le (mul_nonneg hC0 (hρ g)) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTpSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.tpSz :
    TpSz := by
  intro V F _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k c
  refine ⟨|c| * |c| ^ q * C, by positivity, fun A B w p b hA hB hw hs => ?_⟩
  have hA' : ‖A‖ ≤ |c| := hA.trans (le_abs_self c)
  have hB' : ‖B‖ ≤ |c| := hB.trans (le_abs_self c)
  have h1 : Sz k (fun y => w (A y)) p (C * b) := by
    refine h w A p b A.contDiff.contDiffAt hw (fun i hi _ => ?_) hs
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (A : V → V) = fun _ => A := funext fun x => A.fderiv
    rw [e]
    rcases j with _ | j
    · simpa using hA
    · rw [iteratedFDeriv_succ_const]
      simpa using (norm_nonneg A).trans hA
  let L₀ : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] (V [⋀^Fin q]→L[ℝ] F) :=
    { toFun := fun m => B.compContinuousAlternatingMap (m.compContinuousLinearMap A)
      map_add' := fun m n => by ext v; simp
      map_smul' := fun r m => by ext v; simp }
  have hL : ∀ m, ‖L₀ m‖ ≤ |c| * |c| ^ q * ‖m‖ := fun m => by
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have a1 : ‖m fun i => A (v i)‖ ≤ ‖m‖ * ∏ i, ‖A (v i)‖ := m.le_opNorm _
    have a2 : ∏ i, ‖A (v i)‖ ≤ ∏ i, (|c| * ‖v i‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => A.le_of_opNorm_le hA' _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at a2
    calc ‖L₀ m v‖ = ‖B (m fun i => A (v i))‖ := rfl
      _ ≤ |c| * ‖m fun i => A (v i)‖ := B.le_of_opNorm_le hB' _
      _ ≤ |c| * (‖m‖ * (|c| ^ q * ∏ i, ‖v i‖)) := by
        gcongr
        exact a1.trans (mul_le_mul_of_nonneg_left a2 (norm_nonneg _))
      _ = _ := by ring
  have hn : ‖L₀.mkContinuous _ hL‖ ≤ |c| * |c| ^ q := L₀.mkContinuous_norm_le (by positivity) hL
  have h2 := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).2.1 (L₀.mkContinuous _ hL)
    (fun y => w (A y)) (C * b) (hw.comp p A.contDiff.contDiffAt) h1
  refine Sz.mono h2 ?_
  rw [mul_assoc (|c| * |c| ^ q)]
  exact mul_le_mul_of_nonneg_right hn h1.nonneg
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (hw : ContDiffAt ℝ ∞ w (A p)) :
    ContDiffAt ℝ ∞ (Cs.tp A B w) p := by
  have h1 : ContDiffAt ℝ ∞ (fun x => w (A x)) p := hw.comp p A.contDiff.contDiffAt
  have h2 := (ContinuousAlternatingMap.compContinuousLinearMapCLM A :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)).contDiff.contDiffAt.comp p h1
  exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V F F (Fin q) B).contDiff.contDiffAt.comp p h2

theorem UpperTheory.V.Lit.Geo.Cs.move :
    UpperTheory.V.Lit.Geo.Cs.Move := by
  intro E _ _ _ a ho U Ξ q k c
  obtain ⟨B, hB, hb⟩ := matBd E a Ξ c
  obtain ⟨D, hD, hd⟩ := Cs.tpSz (HV E a) (Fin Ξ.d → ℂ) q k B
  refine ⟨D, hD, fun w g x h b hh hs => ?_⟩
  obtain ⟨h1, -, h3⟩ := hb h hh.1 hh.2
  have e : sand h⁻¹ (sand h (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [Cs.Tw_eq U Ξ w.1 g h x]
  refine hd _ _ _ _ b (ContinuousLinearMap.opNorm_le_bound _ hB h3)
    (ContinuousLinearMap.opNorm_le_bound _ hB fun y => by rw [mulVecL_apply]; exact h1 y) ?_ (by rw [e]; exact hs)
  rw [e]
  exact tp_smooth _ _ _ _ ((w.2 _).1.contDiffAt (ho.mem_nhds (sand_mem_cone _ hOne_mem_cone)))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtDiv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfProdEx
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_conj_mul (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (f x) * h x) g = fun y => Complex.conjCLE (chart f g y) * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

end

theorem UpperTheory.V.Lit.Geo.Pf.prodEx :
    UpperTheory.V.Lit.Geo.Pf.ProdEx := by
  intro E _ _ _ a φ ψ
  refine ⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩
  · rw [chart_conj_mul]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)
  · have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
      simpa using chart_val f g 1
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X =
      starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g +
        starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X
    have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a)
      (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt
    rw [chart_conj_mul]
    refine (congrArg (fun L => L X) h1.fderiv).trans ?_
    simp [hv, mul_comm, add_comm]
end
end

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Pf
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def ptForm (χ : HChar E) (g : GA E a) : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun φ ψ => starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g)
    (fun φ φ' ψ => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c φ ψ => by simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc])
    (fun φ ψ ψ' => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, mul_add])
    (fun c φ ψ => by
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

private theorem ptForm_apply (χ : HChar E) (g : GA E a) (φ ψ : Sm E a) :
    ptForm χ g φ ψ = starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g := rfl

private theorem pt_tform (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    pt χ G x y g = tform (ptForm χ g) G x y := by
  rw [(ptInv E a χ d G x y).1 g, tform_apply]
  rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private theorem sum_val {ι : Type} (s : Finset ι) (f : ι → Sm E a) (g : GA E a) :
    (∑ i ∈ s, f i).1 g = ∑ i ∈ s, (f i).1 g := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Geo.Pf.ptDiv :
    UpperTheory.V.Lit.Geo.Pf.PtDiv := by
  intro E _ _ _ a Ξ r χ G hχ hG x y
  choose θ h0 h1 using fun i j => prodEx E a (mulChi a χ (cmp i x)) (mulChi a χ (cmp j y))
  refine ⟨∑ i, ∑ j, G i j • θ i j, fun g => ?_, fun X g => ?_⟩
  · rw [(ptInv E a χ _ G x y).1 g]
    simp only [sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h0]
  · set c : ℂ := ((r * ell E a (toL X.1) : ℝ) : ℂ) with hc
    have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
    have hX : star X.1 = X.1 := X.2
    have e1 := (UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d (ptForm χ g) ⊤ G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1)) 0 0).1
      (by have := hG.adj X.1; rwa [hX] at this) x y
    have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
      simp [smB]
    have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x - smA Ξ (toL X.1) x - (2 * c) • x := by
      rw [smAdj, adj_apply, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
      congr 2
      rw [hc]
      simp [mul_assoc]
    have e5 : (lie E a (toL X.1) (∑ i, ∑ j, G i j • θ i j)).1 g =
        tform (ptForm χ g) G x (smA Ξ (toL X.1) y) + tform (ptForm χ g) G (smA Ξ (toL X.1) x) y +
          2 * c * tform (ptForm χ g) G x y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h1, tform_apply,
        smA_apply, cmp_rT, Finset.mul_sum, ← Finset.sum_add_distrib, ptForm_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hχ.2, hχ.2, ← hc]
      simp only [map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        map_mul, hcc]
      ring
    rw [e5, pt_tform, pt_tform, e3, e4, smB_apply]
    simp only [map_add (f := _), map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, e1,
      map_mul, hcc, map_ofNat]
    ring
end
