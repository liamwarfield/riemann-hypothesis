module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernConnectionCurvaturePolyRepEval
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernConnectionCurvaturePolyRepEval
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]


omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernConnectionCurvaturePolyRepEvalStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernConnection_curvature_polyRep_eval : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧ curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  first | exact @GlobalTheory.GoodMetric.conn_curvPoly_ev | exact GlobalTheory.GoodMetric.conn_curvPoly_ev | (intros; apply GlobalTheory.GoodMetric.conn_curvPoly_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpan
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpanStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (k : ℕ), (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | exact GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | (intros; apply GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMem
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trSpan_mul : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ)
    (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  intro ι m S _ _ w w' f g hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl1, hlw, rfl⟩ := hx
      obtain ⟨l', hl1', hlw', rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨l ++ l', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hl1 x h
        · exact hl1' x h
      · simp [List.map_append, List.sum_append, hlw, hlw']
      · funext A
        simp [trProd, List.map_append, List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

end GlobalTheory.GoodMetric.ChernSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMemStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePowerProductRealSpan_mul_mem : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ) (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | exact GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trSpan_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficient
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem one_mem_trSpan_zero {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    (1 : Mat m S → S) ∈ TrSpan m 0 S := by
  unfold TrSpan
  exact Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩

theorem pow_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w : ℕ)
    (f : Mat m S → S) (hf : f ∈ TrSpan m w S) (e : ℕ) : f ^ e ∈ TrSpan m (e * w) S := by
  induction e with
  | zero => simpa using one_mem_trSpan_zero m S
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S (k * w) w _ _ ih hf

theorem prod_mem_trSpan {ι κ : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (s : Finset κ)
    (w : κ → ℕ) (f : κ → Mat m S → S) (hf : ∀ x ∈ s, f x ∈ TrSpan m (w x) S) :
    ∏ x ∈ s, f x ∈ TrSpan m (∑ x ∈ s, w x) S := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using one_mem_trSpan_zero m S
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S _ _ _ _ (hf a (Finset.mem_insert_self a t))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem trSpan_le_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    TrSpan m n S ≤ Reach m n S := by
  unfold TrSpan
  rw [Submodule.span_le]
  rintro f ⟨l, hl, hs, rfl⟩
  exact GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs

theorem aeval_chern_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (R : MvPolynomial (ι × ℕ) ℝ) (hR : R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n) :
    (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  refine trSpan_le_reach m n S ?_

  have key : ∀ d ∈ R.support, (fun A : Mat m S =>
      aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)))
        ∈ TrSpan m n S := by
    intro d hd
    have hdeg : Finsupp.weight Prod.snd d = n := hR (mem_support_iff.mp hd)
    have hprod := prod_mem_trSpan m S d.support (fun x => d x * x.2)
      (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x)
      (fun x _ => pow_mem_trSpan m S x.2 _ (GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan m S x.1 x.2) (d x))
    have hw : ∑ x ∈ d.support, d x * x.2 = n := by
      rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
      simp [smul_eq_mul]
    rw [hw] at hprod
    convert Submodule.smul_mem _ (R.coeff d) hprod using 1
    funext A
    simp [aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]
  have hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) =
      ∑ d ∈ R.support, fun A : Mat m S =>
        aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)) := by
    funext A
    conv_lhs => rw [R.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ key

end GlobalTheory.GoodMetric.ChernSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficientStatement
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (R : MvPolynomial (ι × ℕ) ℝ), R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n → (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
  GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem topCoeff_sum' {n : ℕ} {κ : Type} (s : Finset κ) (P : κ → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, P i) = ∑ i ∈ s, topCoeff (P i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_real_smul {n : ℕ} (r : ℝ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (r • P) = (r : ℂ) * topCoeff P := by
  simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem topCoeff_chern_eq_sum_rep : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  intro ι _ m n R
  classical
  have hmem := GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan m n (MvPolynomial (Fin n × Fin n) ℂ)
    (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.1 hmem
  choose ρ hρ using fun i => (g i).2
  refine ⟨Fin k, inferInstance, ρ, f, fun A hA => ?_⟩
  set c : ι × ℕ → MvPolynomial (Fin n × Fin n) ℂ := fun x => (Matrix.charpolyRev (-A x.1)).coeff x.2 with hc
  have hch : ∀ x : ι × ℕ, IsWeightedHomogeneous (1 : Fin n × Fin n → ℕ) (c x) x.2 := fun x =>
    ChernDegree.charpolyRev_coeff_isHomogeneous (-A x.1) (fun i j => (hA x.1 i j).neg) x.2
  have key : ∀ d : ι × ℕ →₀ ℕ, Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d ≠ n →
      topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) = 0 := by
    intro d hd
    have h1 : IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) (monomial d (AddMonoidAlgebra.coeff R d))
        (Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    exact ChernDegree.topCoeff_eq_zero (ChernDegree.aeval_isWeightedHomogeneous h1 c hch) hd
  have e1 : topCoeff (aeval c R) = ∑ d ∈ R.support, topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by
    conv_lhs => rw [R.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, topCoeff_sum']
  have e2 : topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) =
      ∑ d ∈ R.support with Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d = n,
        topCoeff (aeval c (monomial d (AddMonoidAlgebra.coeff R d))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [weightedHomogeneousComponent_apply, map_sum, topCoeff_sum']
  have e3 : topCoeff (aeval c R) = topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) := by
    rw [e1, e2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rfl
    · exact key d h
  have hval := congrFun hfg A
  simp only [Finset.sum_apply, Pi.smul_apply] at hval
  rw [e3, ← hval, topCoeff_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topCoeff_real_smul, ← hρ i]

end GlobalTheory.GoodMetric.ChernSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentationsStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_sum_representations : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep | exact GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep | (intros; apply GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormIntegrableComplexPointsOfChernWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormIntegrableComplexPointsOfChernWeil
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodMetric

theorem hasChernIntegral_top_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  intro h F _ σ X ι _ m E H hH R
  obtain ⟨Y, E', φ, f, gr, -, hR, hg⟩ := Model.exists_flagSpace X E
  exact ⟨_, h F σ X Y ι m E E' φ f gr hR hg H hH R⟩

end GlobalTheory.GoodMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormIntegrableComplexPointsOfChernWeilStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_integrable_complexPoints_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  first | exact @GlobalTheory.GoodMetric.hasChernIntegral_top_of_chernWeil | exact GlobalTheory.GoodMetric.hasChernIntegral_top_of_chernWeil | (intros; apply GlobalTheory.GoodMetric.hasChernIntegral_top_of_chernWeil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentation
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RepBound

theorem poly_bound {σ : Type} (P : MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ‖aeval x P‖ ≤ C * B ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖(a : ℂ)‖, 0, norm_nonneg _, fun B _ x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    obtain ⟨C2, d2, h2, hq⟩ := hq
    refine ⟨C1 + C2, d1 + d2, by positivity, fun B hB x hx => ?_⟩
    rw [map_add (f := _)]
    have e1 : B ^ d1 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    have e2 : B ^ d2 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    calc ‖aeval x p + aeval x q‖ ≤ ‖aeval x p‖ + ‖aeval x q‖ := norm_add_le _ _
      _ ≤ C1 * B ^ d1 + C2 * B ^ d2 := add_le_add (hp B hB x hx) (hq B hB x hx)
      _ ≤ C1 * B ^ (d1 + d2) + C2 * B ^ (d1 + d2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * B ^ (d1 + d2) := by ring
  | mul_X p s hp =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    refine ⟨C1, d1 + 1, h1, fun B hB x hx => ?_⟩
    rw [map_mul, aeval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hp B hB x hx) (hx s) (norm_nonneg _)
      (mul_nonneg h1 (pow_nonneg (by linarith) _))

theorem poly_bound_fam {κ σ : Type} [Fintype κ] (P : κ → MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ∀ k, ‖aeval x (P k)‖ ≤ C * B ^ d := by
  choose C d hC h using fun k => poly_bound (P k)
  refine ⟨∑ k, C k, ∑ k, d k, Finset.sum_nonneg fun k _ => hC k, fun B hB x hx k => ?_⟩
  exact (h k B hB x hx).trans (mul_le_mul
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ k))
    (pow_le_pow_right₀ hB (Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ k)))
    (pow_nonneg (by linarith) _) (Finset.sum_nonneg fun k _ => hC k))

variable {ι : Type} {m : ι → ℕ}

def adjPoly (m : ι → ℕ) (w : EntIx m) : MvPolynomial (EntIx m) ℤ :=
  Matrix.adjugate (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)) w.2.1 w.2.2

theorem aeval_adjPoly (A : Mat m ℂ) (w : EntIx m) :
    aeval (fun u : EntIx m => A u.1 u.2.1 u.2.2) (adjPoly m w) = (A w.1).adjugate w.2.1 w.2.2 := by
  have e : (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)).map
      (aeval fun u : EntIx m => A u.1 u.2.1 u.2.2) = A w.1 := by
    ext p q; simp
  rw [← e]
  exact congrFun (congrFun (RingHom.map_adjugate (aeval (R := ℤ) fun u : EntIx m => A u.1 u.2.1 u.2.2).toRingHom _) w.2.1) w.2.2

variable [Fintype ι]

def lieCoeff (ρ : PolyRep m) (i j : Fin ρ.M) (w : EntIx m) : ℂ :=
  aeval (fun u : EntIx m => (1 : Mat m ℂ) u.1 u.2.1 u.2.2) (pderiv w (ρ.ent i j))

theorem lie_apply (ρ : PolyRep m) (A : Mat m ℂ) (i j : Fin ρ.M) :
    ρ.lie A i j = ∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2 := rfl

def lieNorm (ρ : PolyRep m) : ℝ := ∑ i, ∑ j, ∑ w, ‖lieCoeff ρ i j w‖

theorem lieNorm_nonneg (ρ : PolyRep m) : 0 ≤ lieNorm ρ := by unfold lieNorm; positivity

theorem norm_lie_mul_le (ρ : PolyRep m) (A : Mat m ℂ) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ w : EntIx m, ‖A w.1 w.2.1 w.2.2‖ * t ≤ c) (i j : Fin ρ.M) :
    ‖ρ.lie A i j‖ * t ≤ lieNorm ρ * |c| := by
  have h1 : ‖ρ.lie A i j‖ * t ≤ ∑ w, ‖lieCoeff ρ i j w‖ * |c| := by
    rw [lie_apply]
    calc ‖∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖ * t
        ≤ (∑ w, ‖lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖) * t :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht
      _ = ∑ w, ‖lieCoeff ρ i j w‖ * (‖A w.1 w.2.1 w.2.2‖ * t) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w _ => ?_; rw [norm_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left ((h w).trans (le_abs_self c)) (norm_nonneg _)
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg c)
  unfold lieNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖lieCoeff ρ i j w‖)
    (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ∑ w, ‖lieCoeff ρ i j w‖) (fun j _ => by positivity)
    (Finset.mem_univ j)

theorem lie_neg (ρ : PolyRep m) (A : Mat m ℂ) : ρ.lie (fun τ => -A τ) = -ρ.lie A := by
  ext i j; simp [lie_apply, Finset.sum_neg_distrib]

theorem lie_sub (ρ : PolyRep m) (A B : Mat m ℂ) : ρ.lie (fun τ => A τ - B τ) = ρ.lie A - ρ.lie B := by
  ext i j; simp [lie_apply, mul_sub, Finset.sum_sub_distrib]

theorem mdel_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdel (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdel (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdel_apply, lie_apply]
  rw [del_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [del_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem mdbar_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdbar (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdbar (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdbar_apply, lie_apply]
  rw [dbar_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem poinWt_nonneg {n : ℕ} (S : Finset (Fin n)) (v : V n) (a : Fin n) : 0 ≤ poinWt S v a := by
  unfold poinWt; split_ifs <;> positivity

end GlobalTheory.RepBound

namespace GlobalTheory.RepBound

theorem le_mul_pow_of_le {x K c' L : ℝ} {e N' : ℕ} (hx : x ≤ K * L ^ e) (hK : K ≤ c') (hK0 : 0 ≤ K)
    (hL : 1 ≤ L) (he : e ≤ N') : x ≤ c' * L ^ N' :=
  hx.trans (mul_le_mul hK (pow_le_pow_right₀ hL he) (pow_nonneg (by linarith) _) (hK0.trans hK))

theorem goodBound_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ),
    ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) →
      (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) →
        GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  intro ι _ m ρ c N
  obtain ⟨C1, d1, hC1, h1⟩ := poly_bound_fam (fun p : Fin ρ.M × Fin ρ.M => ρ.ent p.1 p.2)
  obtain ⟨C2, d2, hC2, h2⟩ := poly_bound ρ.ent.det
  obtain ⟨C3, d3, hC3, h3⟩ := poly_bound_fam (adjPoly m)
  have hc₁ : 1 ≤ max c 1 := le_max_right _ _
  have hc₀ : 0 ≤ max c 1 := by linarith
  have hK1 : 0 ≤ C1 * max c 1 ^ d1 := mul_nonneg hC1 (pow_nonneg hc₀ _)
  have hK2 : 0 ≤ C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) :=
    mul_nonneg (mul_nonneg hC2 (pow_nonneg (by linarith) _)) (pow_nonneg hc₀ _)
  have hK3 : 0 ≤ lieNorm ρ * |c| := mul_nonneg (lieNorm_nonneg ρ) (abs_nonneg c)
  refine ⟨C1 * max c 1 ^ d1 + C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) + lieNorm ρ * |c|,
    N * d1 + N * ((d3 + 1) * d2), ?_⟩
  intro n S G v hG hdet hL hB
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := by linarith
  set B := max c 1 * L ^ N with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hc₁ (one_le_pow₀ hL)
  have hx : ∀ w : EntIx m, ‖G v w.1 w.2.1 w.2.2‖ ≤ B := fun w =>
    ((hB w.1).entry w.2.1 w.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
  have hu : ∀ τ, IsUnit (G v τ).det := fun τ => isUnit_iff_ne_zero.2 (hdet τ)
  have hcv := (GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ n G v hG hdet).1
  have hcvE : ∀ ξ, (fun u => conn (fun w => ρ.ev (G w)) u ξ) =ᶠ[𝓝 v]
      (fun u => ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) := fun ξ => hcv.mono fun u hu => hu ξ
  have hc1 : ∀ τ ξ, MContDiffAt 1 (fun u => conn (fun w => G w τ) u ξ) v :=
    fun τ ξ => (hG τ).conn (hu τ) (by norm_num) ξ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change ‖ρ.ev (G v) i j‖ ≤ _
    have := h1 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx (i, j)
    refine le_mul_pow_of_le (K := C1 * max c 1 ^ d1) (e := N * d1) ?_ (by linarith) hK1 hL (by omega)
    refine this.trans_eq ?_
    rw [hBdef, mul_pow, ← pow_mul]; ring
  · change ‖(ρ.ev (G v)).det‖⁻¹ ≤ _
    set Gi : Mat m ℂ := fun τ => (G v τ)⁻¹ with hGi
    have hmul : ρ.ev (G v) * ρ.ev Gi = 1 := by
      have e : G v * Gi = 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hu τ)
      rw [PolyRep.ev, PolyRep.ev, ← ρ.mul ℂ, e]
      exact ρ.one ℂ
    have hdm : (ρ.ev (G v)).det * (ρ.ev Gi).det = 1 := by rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hinv : ‖(ρ.ev (G v)).det‖⁻¹ = ‖(ρ.ev Gi).det‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right hdm]
    have hpoly : (ρ.ev Gi).det = aeval (fun w : EntIx m => Gi w.1 w.2.1 w.2.2) ρ.ent.det :=
      (AlgHom.map_det _ _).symm
    have hy : ∀ w : EntIx m, ‖Gi w.1 w.2.1 w.2.2‖ ≤ (C3 + 1) * B ^ (d3 + 1) := by
      intro w
      have ha := h3 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx w
      rw [aeval_adjPoly (G v) w] at ha
      have hd : ‖(G v w.1).det‖⁻¹ ≤ B :=
        ((hB w.1).det).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
      have e : Gi w.1 w.2.1 w.2.2 = ((G v w.1).det)⁻¹ * (G v w.1).adjugate w.2.1 w.2.2 := by
        simp [hGi, Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e, norm_mul, norm_inv]
      have hBd : 0 ≤ B ^ d3 := pow_nonneg (by linarith) _
      calc ‖(G v w.1).det‖⁻¹ * ‖(G v w.1).adjugate w.2.1 w.2.2‖ ≤ B * (C3 * B ^ d3) :=
            mul_le_mul hd ha (norm_nonneg _) (by linarith)
        _ ≤ (C3 + 1) * B ^ (d3 + 1) := by
            rw [pow_succ]; nlinarith [mul_nonneg hBd (by linarith : (0:ℝ) ≤ B)]
    have hB2 : 1 ≤ (C3 + 1) * B ^ (d3 + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hB1)
    have hd2 := h2 _ hB2 _ hy
    rw [hinv, hpoly]
    refine le_mul_pow_of_le (K := C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2))
      (e := N * ((d3 + 1) * d2)) ?_ (by linarith) hK2 hL (by omega)
    refine hd2.trans_eq ?_
    rw [hBdef, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  · intro a i j
    change ‖conn (fun u => ρ.ev (G u)) v (coordVec a) i j‖ * poinWt S v a ≤ _
    have e := (hcvE (coordVec a)).self_of_nhds
    simp only at e
    rw [e]
    exact (norm_lie_mul_le ρ _ (poinWt_nonneg S v a) (fun w => (hB w.1).form a w.2.1 w.2.2) i j).trans
      (by linarith)
  · intro a b i j
    have e : curv (fun u => ρ.ev (G u)) v (coordVec a) (coordVec b) =
        ρ.lie (fun τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)) := by
      rw [curv, mdbar_congr (hcvE (coordVec a)), mdbar_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_neg]
      rfl
    rw [e]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).dbar a b w.2.1 w.2.2) i j).trans (by linarith)
  · intro a b i j
    rw [mdel_congr (hcvE (coordVec b)), mdel_congr (hcvE (coordVec a)),
      mdel_lie ρ (fun τ => hc1 τ (coordVec b)), mdel_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_sub]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).del a b w.2.1 w.2.2) i j).trans (by linarith)

end GlobalTheory.RepBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentationStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) → GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  first | exact @GlobalTheory.RepBound.goodBound_ev | exact GlobalTheory.RepBound.goodBound_ev | (intros; apply GlobalTheory.RepBound.goodBound_ev <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder ContDiff

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ}

theorem eventually_regAt_under {y : CxPts X.str σ} {g : X.Fn} (hg : RegAt (under y) g) :
    ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt_under (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt_under (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem CInfAt.contDiffAt_holoChart {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hy : y ∈ e.source) :
    ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  obtain ⟨W, κ, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := isOpen_over e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hl := e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev X.str σ W (g a) (e.symm w)) (e y) :=
    contDiffAt_pi.2 fun a => (contDiffOn_real ho (he W (g a))).contDiffAt (ho.mem_nhds (mem_over e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ G (fun a => ev X.str σ W (g a) (e.symm (e y))) := by
    rw [hl]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (e y) hg).congr_of_eventuallyEq ?_
  have := e.continuousAt_symm (e.map_source hy)
  rw [ContinuousAt, hl] at this
  exact this.eventually h₅

theorem IsMetricOn.mContDiffAt_two {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0} {O : X.X.Opens}
    {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ} (hH : IsMetricOn E O H) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) (τ : ι) :
    MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := fun i j => by
  obtain ⟨hre, him⟩ := hH.smooth y hy A hA τ i j
  have h1 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).re) (e y) :=
    (CInfAt.contDiffAt_holoChart hre he hye).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).im) (e y) :=
    (CInfAt.contDiffAt_holoChart him he hye).of_le (by norm_cast)
  have h3 : ContDiffAt ℝ 2 (fun v => ((H A (e.symm v) τ i j).re : ℂ) + ((H A (e.symm v) τ i j).im : ℂ) * Complex.I) (e y) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h1).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ h2).mul contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  exact (Complex.re_add_im _).symm

theorem curvPoly_polyRep {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {E : Fr (ratOf X) m 0}
    {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    {H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ} (hH : IsMetricOn E O H)
    (hρ : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y))
    {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) :
    curvPoly (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) (e y) =
      ρ.lie (fun τ => curvPoly (fun v => H A (e.symm v) τ) (e y)) := by
  have hG2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := hH.mContDiffAt_two hy hA he hye
  have hdet : ∀ τ, (H A (e.symm (e y)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hye]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y hy A hA τ).isUnit).ne_zero
  obtain ⟨-, hc⟩ := GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ X.dim (fun v => H A (e.symm v)) (e y) hG2 hdet
  rw [← hc]
  have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hye)
    rwa [ContinuousAt, e.left_inv hye] at this
  have heq : (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => ρ.ev (H A (e.symm v)) := by
    filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hy), ht.eventually (eventually_mem_frames hA)] with v h1 h2
    exact hρ _ h1 A h2
  simp only [curvPoly, curv_congr heq]

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.Bridge

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.GoodMetric.isGood_polyRep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (ρ : PolyRep m) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0) (O : X.X.Opens)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ),
    (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) → IsMetricOn E O H →
      (∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y)) →
        IsGood E O H → IsGood E' O H' := by
  intro F _ σ X ι _ m ρ E E' O H H' hS hH hρ hG y hy
  obtain ⟨e, S, he, hye, hS0, hSO, A, hA, c, N, hev⟩ := hG y hy
  obtain ⟨c', N', hgood⟩ := GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation ι m ρ c N
  refine ⟨e, S, he, hye, hS0, hSO, fun _ => ρ.ev A, hS _ A hA, c', N', ?_⟩
  obtain ⟨a₀, ha₀S, ha₀⟩ := (hSO y hye).1 hy
  have hcont : ContinuousAt (fun z => e z a₀) y :=
    (EuclideanSpace.proj (𝕜 := ℂ) a₀).continuous.continuousAt.comp (e.continuousAt hye)
  have hsmall : ∀ᶠ z in 𝓝 y, ‖e z a₀‖ < Real.exp (-1) := by
    have h0 : Tendsto (fun z => e z a₀) (𝓝 y) (𝓝 0) := by
      have := hcont.tendsto
      rwa [ha₀] at this
    exact h0.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
  filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds (e.open_source.mem_nhds hye),
    nhdsWithin_le_nhds (eventually_mem_frames hA), nhdsWithin_le_nhds hsmall] with z hz hzO hzs hzA hzsm
  rintro ⟨⟩
  have hz2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e z) := hH.mContDiffAt_two hzO hzA he hzs
  have hdet : ∀ τ, (H A (e.symm (e z)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hzs]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef z hzO A hzA τ).isUnit).ne_zero
  have hne : e z a₀ ≠ 0 := fun h0 => ((hSO z hzs).2 ⟨a₀, ha₀S, h0⟩) hzO
  have hpos : 0 < ‖e z a₀‖ := norm_pos_iff.2 hne
  have hlt : Real.log ‖e z a₀‖ < -1 := by rw [Real.log_lt_iff_lt_exp hpos]; exact hzsm
  have h1 : 1 ≤ |Real.log ‖e z a₀‖| := by rw [abs_of_neg (by linarith)]; linarith
  have hlog : 1 ≤ ∑ a ∈ S, |Real.log ‖e z a‖| :=
    h1.trans (Finset.single_le_sum (f := fun a => |Real.log ‖e z a‖|) (fun a _ => abs_nonneg _) ha₀S)
  have hb := hgood X.dim S (fun v => H A (e.symm v)) (e z) hz2 hdet hlog hz
  refine goodBound_congr_nhds X.dim (Fin ρ.M) S c' N' _ _ (e z) ?_ hb
  have ht : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    have := e.continuousAt_symm (e.map_source hzs)
    rwa [ContinuousAt, e.left_inv hzs] at this
  filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hzO), ht.eventually (eventually_mem_frames hzA)]
    with v h1 h2
  exact (hρ _ h1 A h2).symm

theorem _root_.GlobalTheory.GoodMetric.goodChernWeil_of_goodTopChernForm :
    GlobalTheory.Published.GoodTopChernForm → GlobalTheory.Published.ChernWeilNumbers → GlobalTheory.Published.FlagPushForward → GlobalTheory.Published.GoodChernWeil := by
  intro hT hCW hP
  refine ⟨?_, hP⟩
  intro F _ σ X Y ι _ m E E' φ f gr hRef hGr O H hH hG R
  obtain ⟨J, _, ρ, a, hAlg⟩ := GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_sum_representations ι m X.dim R
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety F σ X ι m E
  choose Eb hEbS hEbH using fun j => GlobalTheory.T.exists_polyRep_inducedBundle_and_metric F X ι m (ρ j) E
  choose H' hH' hH'eq using fun j => hEbH j σ O H hH
  choose H₀' hH₀' hH₀'eq using fun j => hEbH j σ ⊤ H₀ hH₀
  choose t ht using fun j => GlobalTheory.T.chernForm_integrable_complexPoints_of_chernWeil hCW F σ X Unit (fun _ => (ρ j).M) (Eb j) (H₀' j) (hH₀' j)
    (MvPolynomial.X ((), X.dim))
  have htO : ∀ j, HasChernIntegral (Eb j) O (H' j) (MvPolynomial.X ((), X.dim)) (t j) := fun j =>
    hT F σ X (ρ j).M (Eb j) O (H' j) (H₀' j) (hH' j)
      (isGood_polyRep F σ X ι m (ρ j) E (Eb j) O H (H' j) (hEbS j) hH (hH'eq j) hG) (hH₀' j) (t j) (ht j)

  have hdens : ∀ (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
      (H' : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => (ρ j).M) ℂ),
      IsMetricOn E O H →
      (∀ j, ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' j (fun _ => (ρ j).ev A) y () = (ρ j).ev (H A y)) →
      ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y),
        ∃ B : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn, (∀ j, B j ∈ (Eb j).S (under y)) ∧
          chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
            ∑ j, a j * chernTop (MvPolynomial.X ((), X.dim)) (fun v => H' j (B j) (c.e.symm v)) (c.e y) := by
    intro O H H' hH hH'eq y hy c hc
    obtain ⟨A, hA⟩ := E.nonempty (under y)
    refine ⟨A, hA, fun j _ => (ρ j).ev A, fun j => hEbS j _ A hA, ?_⟩
    have hcurv : ∀ j, curvPoly (fun v => H' j (fun _ => (ρ j).ev A) (c.e.symm v) ()) (c.e y) =
        (ρ j).lie (fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) := fun j =>
      curvPoly_polyRep (ρ j) hH (hH'eq j) hy hA c.holo hc
    have hhom : ∀ τ i j, ((fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) τ i j).IsHomogeneous 1 :=
      fun τ i j => by
        simp only [curvPoly, Matrix.of_apply]
        exact IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ _
    have key := hAlg _ hhom
    simp only [chernTop, chernPoly, aeval_X]
    rw [key]
    simp only [hcurv, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlinO := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E O H R J (fun j => (ρ j).M) Eb H' (MvPolynomial.X ((), X.dim)) a t hH hH'
    (hdens O H H' hH hH'eq) htO
  have hlinT := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E ⊤ H₀ R J (fun j => (ρ j).M) Eb H₀' (MvPolynomial.X ((), X.dim)) a t hH₀ hH₀'
    (hdens ⊤ H₀ H₀' hH₀ hH₀'eq) ht
  have hs := hCW F σ X Y ι m E E' φ f gr hRef hGr H₀ hH₀ R
  rw [hs.2.symm.trans hlinT.2]
  exact hlinO

end GlobalTheory.GoodMetric.Bridge
