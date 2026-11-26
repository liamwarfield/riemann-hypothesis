module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.BadStmt
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def Bump : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → n ≤ d → ∀ v ∈ B.P, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), φ ≠ 0 ∧ ∀ g ∈ UAt σ X (evFin F v),
      (IntAt v g ∧ Acts (evFin F v) (om (g, 1)) φ φ) ∨ ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
        Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ)

def VacFix2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def SiegelWeilStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.SecondFromFirstStatement
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def FinLevel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n), B.IsGood σ → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.EulerHalf
noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem euler_half {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      d z ≠ 0 ∧ HasProd (fun v => (1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))⁻¹) (d z) := by
  let x : ι → ℂ → ℂ := fun v z => -(c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))
  have h1 : ∀ v, (1 : ℝ) ≤ q v := fun v => by exact_mod_cast one_le_two.trans (hq v)
  have hx : ∀ v z (t : ℝ), t ≤ 2 * z.re + 1 → ‖x v z‖ ≤ (q v : ℝ) ^ (-t) := fun v z t ht => by
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (two_pos.trans_le (hq v))]
    refine (mul_le_of_le_one_left (by positivity) (hc v)).trans (Real.rpow_le_rpow_of_exponent_le (h1 v) ?_)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    linarith
  have hh : ∀ v z, 0 < z.re → ‖x v z‖ ≤ 1 / 2 := fun v z hz => by
    refine (hx v z 1 (by linarith)).trans ?_
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ two_pos (by exact_mod_cast hq v)
  have hb : ∀ v z (t : ℝ), 0 < z.re → t ≤ 2 * z.re + 1 → ‖Complex.log (1 + x v z)‖ ≤ 3 / 2 * (q v : ℝ) ^ (-t) :=
    fun v z t hz ht => (Complex.norm_log_one_add_half_le_self (hh v z hz)).trans (by gcongr; exact hx v z t ht)
  have hsl : ∀ v z, 0 < z.re → 1 + x v z ∈ Complex.slitPlane := fun v z hz =>
    Complex.mem_slitPlane_of_norm_lt_one ((hh v z hz).trans_lt (by norm_num))
  refine ⟨fun z => Complex.exp (-∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ⟨Complex.exp_ne_zero _, ?_⟩⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).neg.cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.neg.cexp
    convert this using 2 with v
    rw [Function.comp, Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

open Classical in
theorem dProd : DProd := by
  intro F E _ _ _ _ _ n T
  choose d h1 h2 using fun i => euler_half (ι := {v : Pl F // v ∉ T}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => (if Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1) then 1 else -1) ^ (n - (i + 1)))
    (fun v => by split_ifs <;> simp) i
  exact ⟨fun z => ∏ i ∈ Finset.range n, d i z, DifferentiableOn.fun_finsetProd fun i _ => h1 i, fun z hz =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h2 i z hz).1, hasProd_prod fun i _ => (h2 i z hz).2⟩⟩

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HeightGLLe
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix

namespace Ht

variable {p q : Type} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

theorem htOf_le {R : Type} [CommRing R] {N₁ : Matrix p p R → ℝ≥0} {N₂ : Matrix q q R → ℝ≥0}
    {N : Matrix (p ⊕ q) (p ⊕ q) R → ℝ≥0} (hN : ∀ a b, N (fromBlocks a 0 0 b) ≤ max (N₁ a) (N₂ b))
    {X : GL (p ⊕ q) R} {x : GL p R} {y : GL q R} (h1 : X.1 = fromBlocks x.1 0 0 y.1) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have h2 : (X⁻¹).1 = fromBlocks (x⁻¹).1 0 0 (y⁻¹).1 :=
    Units.inv_eq_of_mul_eq_one_right (by rw [h1, fromBlocks_multiply]; simp)
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    exact (hN _ _).trans (max_le ((le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))
  · rw [h2]
    exact (hN _ _).trans (max_le ((inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy))
      ((inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)))

theorem opNorm_le (a : Matrix p p ℂ) (b : Matrix q q ℂ) : opNorm (fromBlocks a 0 0 b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : p ⊕ q → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hc
  have h0 : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ v ∘ .inl) : EuclideanSpace ℂ p)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inl) : EuclideanSpace ℂ p)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_left (opNorm a) (opNorm b))) (norm_nonneg _))
  have hb : ‖(WithLp.toLp 2 (b *ᵥ v ∘ .inr) : EuclideanSpace ℂ q)‖ ≤ c * ‖(WithLp.toLp 2 (v ∘ .inr) : EuclideanSpace ℂ q)‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.2 (le_max_right (opNorm a) (opNorm b))) (norm_nonneg _))
  have kn : ∀ w : p ⊕ q → ℂ, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (p ⊕ q))‖ ^ 2 =
      ‖(WithLp.toLp 2 (w ∘ .inl) : EuclideanSpace ℂ p)‖ ^ 2 + ‖(WithLp.toLp 2 (w ∘ .inr) : EuclideanSpace ℂ q)‖ ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]; rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 ?_
  rw [Matrix.toEuclideanCLM_toLp, fromBlocks_mulVec, kn, mul_pow, kn, mul_add, ← mul_pow, ← mul_pow]
  simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

omit [DecidableEq p] [DecidableEq q] in
theorem normFin_le (v : Pl F) (a : Matrix p p (Fv F v ⊗[F] E)) (b : Matrix q q (Fv F v ⊗[F] E)) :
    normFin F v (fromBlocks a 0 0 b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 ?_
  rintro (i | i) (j | j)
  · exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_le (w : InfinitePlace F) (a : Matrix p p (w.Completion ⊗[F] E)) (b : Matrix q q (w.Completion ⊗[F] E)) :
    normInf F w (fromBlocks a 0 0 b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    exact (opNorm_le _ _).trans (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_le {X : GL (p ⊕ q) (AE F E)} {x : GL p (AE F E)} {y : GL q (AE F E)} (h : X.1 = fromBlocks x.1 0 0 y.1) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  have b : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), (Formalism.UG.bc φ X).1 = fromBlocks (Formalism.UG.bc φ x).1 0 0 (Formalism.UG.bc φ y).1 := fun φ => by
    show X.1.map φ = _
    rw [h, fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]; rfl
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => htOf_le (normInf_le F w) (b _))
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => htOf_le (normFin_le F v) (b _))
  exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)

end Ht

theorem htEmb : HtEmb := fun F _ _ _ _ _ _ _ _ _ =>
  ⟨1, fun _ _ _ h => (Ht.heightGL_le F h).trans_eq (one_mul _).symm,
    fun h h' => (heightGL_mul_le F h.1 h'.1).trans_eq (one_mul _).symm, fun h => one_le_heightGL F h.1⟩

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def Law (χ : Chr F E) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x

variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem Law.rat (h : Law χ z f) (hχ : IsHecke F E χ) {p : G2 σ Y} (a : p ∈ par2 σ Y) (b : p ∈ rat2 σ Y) (x) : f (p * x) = f x := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 a
  obtain ⟨T, hT⟩ := par_rat ht b
  obtain ⟨u, hu⟩ := det_rat hT
  rw [h p t x ht, hu, hχ.2, GlobalTheory.Doubling.absE_inclR]; simp

theorem Law.diag (h : Law χ z f) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) (g : UA σ Y.J) (x) :
    f (e (g, g) * x) * detInv χ g = f x := by
  rw [h _ _ x (he g g).par, absE_det hJ, detInv, mul_right_comm]; simp

theorem Law.hasSum (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) {x v}
    (hs : HasSum (eisTerm f x) v) : HasSum (fun δ : ratU σ Y.J => f (e (1, δ) * x)) v := by
  let i : ratU σ Y.J → Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y))) :=
    fun δ => Quotient.mk _ ⟨e (1, δ), (he _ _).rat (one_mem _) δ.2⟩
  have hi : Function.Bijective i := by
    refine ⟨fun δ δ' h => ?_, fun q => ?_⟩
    · obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 (Quotient.exact (s := QuotientGroup.rightRel
        ((par2 σ Y).subgroupOf (rat2 σ Y))) h)))
      change IsPar (e (1, δ') * (e (1, δ))⁻¹) t at ht
      rw [← map_inv, ← map_mul, isPar_iff, he] at ht
      simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add,
        Matrix.one_mul] at ht
      obtain ⟨a, b⟩ := Matrix.fromRows_inj ht
      have : (1 : UA σ Y.J) * 1⁻¹ = δ'.1 * δ.1⁻¹ := Subtype.ext (Units.ext (a.trans b.symm))
      rw [inv_one, mul_one, eq_mul_inv_iff_mul_eq, one_mul] at this
      exact Subtype.ext this
    · obtain ⟨γ, rfl⟩ := Quotient.exists_rep q
      obtain ⟨δ, hδ, hp⟩ := orbit hJ (γ⁻¹).2
      refine ⟨⟨δ, hδ⟩, (Quotient.sound (QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_))).symm⟩
      exact hp _ (he _ _)
  convert (Equiv.ofBijective i hi).hasSum_iff.2 hs using 2 with δ
  have := QuotientGroup.rightRel_apply.1 (Quotient.exact (i δ).out_eq)
  exact Eq.trans (by simp [mul_assoc]) (h.rat hχ this (mul_mem ((he _ _).rat (one_mem _) δ.2) (inv_mem (i δ).out.2)) _)

theorem Law.eis_inv (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h')))
    {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {γ δ : UA σ Y.J} (hγ : γ ∈ ratU σ Y.J) (hδ : δ ∈ ratU σ Y.J) (x) :
    Ê (e (γ, δ) * x) = Ê x := by
  refine (h.hasSum hχ hJ he (hs _)).unique ?_
  have := ((Equiv.mulLeft (⟨γ, hγ⟩ : ratU σ Y.J)⁻¹).trans (Equiv.mulRight ⟨δ, hδ⟩)).hasSum_iff.2 (h.hasSum hχ hJ he (hs x))
  convert this using 2 with η
  have := h.diag hJ he γ (e (1, γ⁻¹ * η * δ) * x)
  rw [detInv_rat hχ hγ, mul_one, ← mul_assoc, ← map_mul] at this
  rw [← mul_assoc, ← map_mul]
  simpa [mul_assoc] using this

theorem countable_ratU : Countable (ratU σ Y.J) := by
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  exact (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).preimage
    Subtype.val_injective

theorem unfold0 : Unfold0 := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := aniso_of hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf
noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def StdEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x

theorem stdEx_of (h1 : FrameConj) (h2 : HgtEx) : StdEx := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.RegOfBound
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open Filter Topology Metric
open scoped BoundedContinuousFunction

variable {X : Type} {h : X → ℝ}

theorem unif_bound (h1 : ∀ x, 1 ≤ h x) {V : Submodule ℂ (X → ℂ)} (hV : ∀ f ∈ V, ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * h x ^ N)
    {D : Set ℂ} {H : ℂ → V} (hb : ∀ μ : V →ₗ[ℂ] ℂ, (∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C) →
      ∃ C, ∀ s ∈ D, ‖μ (H s)‖ ≤ C) : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ D, ∀ x, ‖(H s).1 x‖ ≤ C * h x ^ N := by
  by_contra hn
  push Not at hn
  choose s hs g hg using fun n : ℕ => hn (n * 2 ^ n) n
  have h0 : ∀ x, 0 < h x := fun x => one_pos.trans_le (h1 x)
  let w : ℕ → ℝ := fun n => (1 / 2) ^ n / h (g n) ^ n
  have w0 : ∀ n, 0 < w n := fun n => div_pos (by positivity) (pow_pos (h0 _) _)
  have est : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ (c : ℕ →ᵇ ℂ) n,
      ‖c n * (w n * f (g n))‖ ≤ C * K * ‖c‖ * (1 / 2) ^ n := fun N => by
    refine ⟨1 + ∑ m ∈ Finset.range N, h (g m) ^ N, fun f C hf c n => ?_⟩
    have C0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf (g n))) (pow_pos (h0 _) _)
    have S0 : 0 ≤ ∑ m ∈ Finset.range N, h (g m) ^ N := Finset.sum_nonneg fun m _ => (pow_pos (h0 _) _).le
    have k : h (g n) ^ N / h (g n) ^ n ≤ 1 + ∑ m ∈ Finset.range N, h (g m) ^ N := by
      by_cases hN : n < N
      · refine (div_le_self (pow_pos (h0 _) _).le (one_le_pow₀ (h1 _))).trans (le_add_of_nonneg_of_le zero_le_one ?_)
        exact Finset.single_le_sum (f := fun m => h (g m) ^ N) (fun m _ => (pow_pos (h0 _) _).le) (Finset.mem_range.2 hN)
      · exact ((div_le_one (pow_pos (h0 _) _)).2 (pow_le_pow_right₀ (h1 _) (not_lt.1 hN))).trans (le_add_of_nonneg_right S0)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le]
    calc _ ≤ ‖c‖ * (w n * (C * h (g n) ^ N)) := by gcongr; exacts [mul_nonneg (w0 n).le (norm_nonneg _), c.norm_coe_le_norm n, (w0 n).le, hf _]
      _ = C * (h (g n) ^ N / h (g n) ^ n) * ‖c‖ * (1 / 2) ^ n := by simp only [w]; ring
      _ ≤ _ := by gcongr
  have sm : ∀ (f : V) (c : ℕ →ᵇ ℂ), Summable fun n => c n * (w n * f.1 (g n)) := fun f c => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := est N
    exact .of_norm_bounded (summable_geometric_two.mul_left _) (hK f C hf c)
  have bd : ∀ N : ℕ, ∃ K : ℝ, ∀ (f : X → ℂ) (C : ℝ), (∀ x, ‖f x‖ ≤ C * h x ^ N) → ∀ c : ℕ →ᵇ ℂ,
      ‖∑' n, c n * (w n * f (g n))‖ ≤ C * K * 2 * ‖c‖ := fun N => (est N).imp fun K hK f C hf c =>
    (tsum_of_norm_bounded (hasSum_geometric_two.mul_left _) (hK f C hf c)).trans_eq (by ring)
  let B : V →ₗ[ℂ] (ℕ →ᵇ ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun f c => ∑' n, c n * (w n * f.1 (g n)))
    (fun f f' c => by rw [← (sm f c).tsum_add (sm f' c)]; simp [mul_add])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
    (fun f c c' => by rw [← (sm f c).tsum_add (sm f c')]; simp [add_mul])
    (fun a f c => by rw [smul_eq_mul, ← tsum_mul_left]; exact tsum_congr fun n => by simp; ring)
  have ct : ∀ f : V, ∃ C, ∀ c, ‖B f c‖ ≤ C * ‖c‖ := fun f => by
    obtain ⟨C, N, hf⟩ := hV f.1 f.2
    obtain ⟨K, hK⟩ := bd N
    exact ⟨_, hK f C hf⟩
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun n : ℕ => (B (H (s n))).mkContinuousOfExistsBound (ct _)) fun c => by
    obtain ⟨C, hC⟩ := hb (B.flip c) fun N => (bd N).elim fun K hK => ⟨_, fun f hf => hK f 1 (by simpa using hf) c⟩
    exact ⟨C, fun n => hC _ (hs n)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 0)
  let c : ℕ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (Pi.single n 1) 1 fun m => by
    by_cases e : m = n <;> simp [e]
  have c1 : ‖c‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).2 fun m => by by_cases e : m = n <;> simp [c, e]
  have e1 : ‖B (H (s n)) c‖ ≤ max M 0 :=
    (ContinuousLinearMap.le_of_opNorm_le _ ((hM n).trans (le_max_left M 0)) c).trans (mul_le_of_le_one_right (le_max_right _ _) c1)
  have e2 : B (H (s n)) c = w n * (H (s n)).1 (g n) :=
    (tsum_eq_single n fun m e => by simp [c, e]).trans (by simp [c])
  rw [e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w0 n).le] at e1
  have e3 : w n * (n * 2 ^ n * h (g n) ^ n) = n := by
    have := (h0 (g n)).ne'
    simp only [w, one_div, inv_pow]; field_simp
  linarith [mul_lt_mul_of_pos_left (hg n) (w0 n)]

variable [TopologicalSpace X] {g g' : ℂ → X → ℂ} {S S' : Set ℂ} {s₀ : ℂ}


variable (h g S) in
structure RegOn : Prop where
  hol : ∀ x, DifferentiableOn ℂ (g · x) S
  cont : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (S ×ˢ Set.univ)
  grow : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N


variable (h g s₀) in
def Reg : Prop := ∃ S ∈ 𝓝 s₀, RegOn h g S

theorem RegOn.mono (a : RegOn h g S) (e : S' ⊆ S) : RegOn h g S' :=
  ⟨fun x => (a.hol x).mono e, a.cont.mono (Set.prod_mono e subset_rfl), a.grow.imp fun _ => .imp fun _ b s hs => b s (e hs)⟩

theorem Reg.congr (a : Reg h g s₀) (e : g' =ᶠ[𝓝 s₀] g) : Reg h g' s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have b := a.mono (Set.inter_subset_left (t := {s | g' s = g s}))
  exact ⟨_, inter_mem hS e, fun x => (b.hol x).congr fun s hs => congrFun hs.2 x, b.cont.congr fun y hy => congrFun hy.1.2 y.2,
    b.grow.imp fun _ => .imp fun _ b s hs x => by rw [hs.2]; exact b s hs x⟩

theorem Reg.eventually (a : Reg h g s₀) : ∀ᶠ s in 𝓝 s₀, Reg h g s :=
  let ⟨S, hS, a⟩ := a
  (eventually_mem_nhds_iff.2 hS).mono fun _ hs => ⟨S, hs, a⟩

theorem Reg.contAt (a : Reg h g s₀) (x : X) : ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x) :=
  let ⟨_, hS, a⟩ := a
  a.cont.continuousAt (prod_mem_nhds hS univ_mem)

theorem Reg.mul (h1 : ∀ x, 1 ≤ h x) (a : Reg h g s₀) {c : ℂ → ℂ} (hc : AnalyticAt ℂ c s₀) {u : X → X} (hu : Continuous u) {b : ℝ}
    (hb : ∀ x, h (u x) ≤ b * h x) : Reg h (fun s x => c s * g s (u x)) s₀ := by
  obtain ⟨S, hS, a⟩ := a
  have e : ∀ᶠ s in 𝓝 s₀, ‖c s‖ < ‖c s₀‖ + 1 := hc.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨_, inter_mem hS (hc.eventually_analyticAt.and e), fun x => DifferentiableOn.mul
    (fun s hs => hs.2.1.differentiableAt.differentiableWithinAt) ((a.hol (u x)).mono Set.inter_subset_left),
    ContinuousOn.mul (fun y hy => (hy.1.2.1.continuousAt.comp continuous_fst.continuousAt).continuousWithinAt)
      (a.cont.comp (f := fun y : ℂ × X => (y.1, u y.2)) (by fun_prop) fun y hy => ⟨hy.1.1, trivial⟩), ?_⟩
  obtain ⟨C, N, hC⟩ := a.grow
  refine ⟨(‖c s₀‖ + 1) * (max C 0 * b ^ N), N, fun s hs x => ?_⟩
  have h0 := zero_le_one.trans (h1 (u x))
  rw [norm_mul, mul_assoc, mul_assoc, ← mul_pow]
  exact mul_le_mul hs.2.2.le ((hC s hs.1 _).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (hb x) N) (pow_nonneg h0 _)
    (le_max_right _ _))) (norm_nonneg _) (by positivity)

theorem reg_of_bound (hh : Continuous h) (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) (hc : ∀ s ∈ S, Continuous (g s))
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ s ∈ S, ∀ x, ‖g s x‖ ≤ C * h x ^ N) : Reg h g s₀ := by
  refine ⟨interior S, interior_mem_nhds.2 hS, fun x => (hd x).mono interior_subset, fun y hy => ContinuousAt.continuousWithinAt ?_,
    hg.imp fun _ => .imp fun _ b s hs => b s (interior_subset hs)⟩
  obtain ⟨C, N, hC⟩ := hg
  obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy.1)
  have : Tendsto (fun z : ℂ × X => g z.1 z.2 - g y.1 z.2) (𝓝 y) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun z => 2 * (C * h z.2 ^ N) / r * dist z.1 y.1) ?_ ?_
    · filter_upwards [continuous_fst.continuousAt.eventually (ball_mem_nhds y.1 r0)] with z hz
      rw [← dist_eq_norm]
      refine Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := (g · z.2)) ((hd z.2).mono hr) (fun s hs => ?_) hz
      rw [mem_closedBall, dist_eq_norm, two_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hC s (hr hs) _) (hC _ (hr (mem_ball_self r0)) _))
    · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  simpa [ContinuousAt] using this.add ((hc _ (interior_subset hy.1)).comp continuous_snd).continuousAt

theorem Reg.punct (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x) :
    ∀ᶠ s in 𝓝[≠] s₀, Reg h g s := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds a.eventually, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_nhdsWithin_iff.1 e).eventually_nhds] with s b hs e
  refine (b.mul h1 (c := fun z => ((z - s₀) ^ k)⁻¹) (AnalyticAt.inv (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hs)))
    continuous_id (b := 1) (by simp)).congr ?_
  filter_upwards [e, isOpen_ne.mem_nhds hs] with z hz hz'
  funext x
  rw [id, hz hz', inv_mul_cancel_left₀ (pow_ne_zero _ (sub_ne_zero.2 hz'))]

theorem Reg.remove (h1 : ∀ x, 1 ≤ h x) {k : ℕ} (a : Reg h g' s₀) (e : ∀ᶠ s in 𝓝[≠] s₀, ∀ x, g' s x = (s - s₀) ^ k * g s x)
    (hS : S ∈ 𝓝 s₀) (hd : ∀ x, DifferentiableOn ℂ (g · x) S) : Reg h g s₀ := by
  obtain ⟨S', hS', b⟩ := id a
  obtain ⟨ρ, ρ0, hρ⟩ := nhds_basis_closedBall.mem_iff.1
    (inter_mem (inter_mem hS hS') (eventually_nhdsWithin_iff.1 (e.and (a.punct h1 e))))
  have dc : ∀ x, DiffContOnCl ℂ (g · x) (ball s₀ ρ) := fun x => (hd x).diffContOnCl_ball fun z hz => (hρ hz).1.1
  have sp : ∀ z ∈ sphere s₀ ρ, z ≠ s₀ := fun z hz => ne_of_mem_sphere hz ρ0.ne'
  obtain ⟨C, N, hC⟩ := b.grow
  refine ⟨_, ball_mem_nhds s₀ ρ0, fun x => (dc x).differentiableOn, fun y hy => ContinuousAt.continuousWithinAt ?_, C / ρ ^ k, N,
    fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (dc x) (fun w hw => ?_) (subset_closure hz)⟩
  · by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (((hρ (sphere_subset_closedBall hz.1)).2 (sp _ hz.1)).2.contAt z.2).continuousWithinAt) _
    · exact ((hρ (ball_subset_closedBall hy.1)).2 e0).2.contAt y.2
  · rw [frontier_ball _ ρ0.ne'] at hw
    have c := hρ (sphere_subset_closedBall hw)
    have := hC w c.1.2 x
    rw [(c.2 (sp w hw)).1, norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
    rw [div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
    exact this

theorem preconn {U : Set ℂ} (hU : ∀ s, ∀ᶠ z in 𝓝[≠] s, z ∈ U) : IsPreconnected U := by
  obtain ⟨t, ht, -, hc⟩ := isLindelof_univ.elim_nhds_subcover (fun s => insert s U) fun s _ => insert_mem_nhds_iff.2 (hU s)
  have : (Uᶜ).Countable := ht.mono fun z hz => by
    obtain ⟨s, hs, e⟩ := Set.mem_iUnion₂.1 (hc (Set.mem_univ z))
    exact e.resolve_right hz ▸ hs
  simpa using (this.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

end GlobalTheory.ThK.Dbl.An

end
end
