module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalMultiplierOfComplexMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalMultiplierOfComplexMultiplier
namespace GlobalTheory

open Module

theorem relation_descends_along_functional (K A B : Type) [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B)
    (hrd : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f) (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ W) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (φ : ℂ →+ K) (hφ : ∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c)
    {ι : Type} [Fintype ι] (x : ι → A) (hx : ∀ s, x s ∈ W) (c : ι → ℂ)
    (h : ∑ s, c s • rd (x s) = 0) : ∑ s, φ (c s) • x s = 0 := by
  classical
  obtain ⟨n, ⟨bW⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K W) := ⟨_, ⟨Module.finBasis K W⟩⟩
  have hli : LinearIndependent K (fun j => (bW j : A)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli' := hW n (fun j => (bW j : A)) (fun j => (bW j).2) hli
  have hcoord : ∃ α : ι → Fin n → K, ∀ s, x s = ∑ j, α s j • (bW j : A) := by
    refine ⟨fun s j => bW.repr ⟨x s, hx s⟩ j, fun s => ?_⟩
    have h1 := congrArg (fun v : W => (v : A)) (bW.sum_repr ⟨x s, hx s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := hcoord
  have hrdx : ∀ s, rd (x s) = ∑ j, σ (α s j) • rd (bW j : A) := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hα s, map_sum]
    simp only [hrd]
  have hcoef : ∀ j, ∑ s, c s * σ (α s j) = 0 := by
    have h' : ∑ j, (∑ s, c s * σ (α s j)) • rd (bW j : A) = 0 := by
      rw [← h]
      simp only [hrdx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => Fintype.linearIndependent_iff.mp hli' _ h' j
  have hgoal : ∑ s, φ (c s) • x s = ∑ j, (∑ s, φ (c s) * α s j) • (bW j : A) := by
    simp only [hα, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hgoal]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h5 : ∑ s, φ (c s) * α s j = φ (∑ s, c s * σ (α s j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm (c s), hφ]
    exact mul_comm _ _
  rw [h5, hcoef j, map_zero, zero_smul]

theorem exists_functional_ne_zero_of_embedding (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K ℂ, f m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff K m).mp hcon)
  refine ⟨f.toAddMonoidHom, fun a c => ?_, hf⟩
  have hsmul : σ a * c = a • c := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp only [LinearMap.toAddMonoidHom_coe, hsmul, LinearMap.map_smul, smul_eq_mul]

theorem exists_rational_multiplier_of_complex :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  classical
  intro K A B _ _ _ _ _ σ rd hrd V V' _ _ hVV h hspan hne
  have : FiniteDimensional K ↥(V * V') :=
    Module.Finite.iff_fg.mpr (Submodule.FG.mul (Module.Finite.iff_fg.mp inferInstance)
      (Module.Finite.iff_fg.mp inferInstance))
  have hrdsum : ∀ {m : ℕ} (a : Fin m → K) (v : Fin m → A),
      rd (∑ j, a j • v j) = ∑ j, σ (a j) • rd (v j) := by
    intro m a v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hrd]
  have hexp : ∀ {U : Submodule K A} {m : ℕ} (b : Basis (Fin m) K U) (u : U),
      (u : A) = ∑ j, b.repr u j • (b j : A) := by
    intro U m b u
    have h1 := congrArg (fun v : U => (v : A)) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨n, ⟨bV⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V) := ⟨_, ⟨Module.finBasis K V⟩⟩
  obtain ⟨n', ⟨bV'⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V') := ⟨_, ⟨Module.finBasis K V'⟩⟩
  have hC : ∀ i, ∃ C : Fin n' → ℂ, h * rd (bV i : A) = ∑ j, C j • rd (bV' j : A) := by
    intro i
    have hm := hspan _ (bV i).2
    have hsub : Submodule.span ℂ (rd '' (V' : Set A)) ≤
        Submodule.span ℂ (Set.range fun j => rd (bV' j : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have e : u = ∑ j, bV'.repr ⟨u, hu⟩ j • (bV' j : A) := hexp bV' ⟨u, hu⟩
      rw [e, hrdsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨C, hCe⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hsub hm)
    exact ⟨C, hCe.symm⟩
  choose C hC using hC
  have hi0 : ∃ i, h * rd (bV i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfne⟩ := hne
    apply hfne
    have e : f = ∑ j, bV.repr ⟨f, hf⟩ j • (bV j : A) := hexp bV ⟨f, hf⟩
    rw [e, hrdsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, hcon i, smul_zero]
  obtain ⟨i0, hi0⟩ := hi0
  have hj0 : ∃ j, C i0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hi0
    rw [hC i0]
    exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_smul]
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨φ, hφ, hφne⟩ := exists_functional_ne_zero_of_embedding K σ (C i0 j0) hj0
  obtain ⟨T, hT⟩ : ∃ T : V →ₗ[K] V', ∀ i, T (bV i) = ∑ j, φ (C i j) • bV' j :=
    ⟨bV.constr K (fun i => ∑ j, φ (C i j) • bV' j), fun i => bV.constr_basis K _ i⟩
  have hTA : ∀ i, ((T (bV i) : V') : A) = ∑ j, φ (C i j) • (bV' j : A) := by
    intro i
    rw [hT]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hbasis : ∀ i k, ((T (bV i) : V') : A) * (bV k : A) = (bV i : A) * ((T (bV k) : V') : A) := by
    intro i k
    have key := relation_descends_along_functional K A B σ rd hrd (V * V') hVV φ hφ
      (ι := Fin n' ⊕ Fin n')
      (Sum.elim (fun j => (bV k : A) * (bV' j : A)) (fun j => (bV i : A) * (bV' j : A)))
      (by
        rintro (j | j)
        · exact Submodule.mul_mem_mul (bV k).2 (bV' j).2
        · exact Submodule.mul_mem_mul (bV i).2 (bV' j).2)
      (Sum.elim (fun j => C i j) (fun j => - C k j))
      (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, map_mul, neg_smul, Finset.sum_neg_distrib]
        simp only [← mul_smul_comm, ← Finset.mul_sum, ← hC]
        ring)
    rw [Fintype.sum_sum_type] at key
    simp only [Sum.elim_inl, Sum.elim_inr, map_neg, neg_smul, Finset.sum_neg_distrib,
      ← mul_smul_comm, ← Finset.mul_sum] at key
    rw [hTA, hTA, mul_comm _ ((bV k : V) : A)]
    rw [mul_neg] at key
    exact add_neg_eq_zero.mp key
  have hleft : ∀ i (g : V), ((T (bV i) : V') : A) * (g : A) = (bV i : A) * ((T g : V') : A) := by
    intro i g
    have h2 := bV.ext (f₁ := (LinearMap.mulLeft K ((T (bV i) : V') : A)).comp V.subtype)
      (f₂ := (LinearMap.mulLeft K ((bV i : V) : A)).comp (V'.subtype.comp T))
      (fun k => by simpa using hbasis i k)
    simpa using LinearMap.congr_fun h2 g
  refine ⟨T, ?_, fun f g => ?_⟩
  · intro hT0
    have h1 : T (bV i0) = 0 := by rw [hT0, LinearMap.zero_apply]
    rw [hT] at h1
    exact hφne (Fintype.linearIndependent_iff.mp bV'.linearIndependent _ h1 j0)
  · have h2 := bV.ext (f₁ := (LinearMap.mulRight K (g : A)).comp (V'.subtype.comp T))
      (f₂ := (LinearMap.mulRight K ((T g : V') : A)).comp V.subtype)
      (fun i => by simpa using hleft i g)
    simpa using LinearMap.congr_fun h2 f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalMultiplierOfComplexMultiplierStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  first | exact @GlobalTheory.exists_rational_multiplier_of_complex | exact GlobalTheory.exists_rational_multiplier_of_complex | (intros; apply GlobalTheory.exists_rational_multiplier_of_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGenerator
noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section Lemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_mem {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H) (k : V.Comp) :
    relab c σ τ.1 ∈ (V.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (by
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)

theorem modelWt_shift {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H)
    {G G' : WTZ E} (hG : Even G.2) (h : exZ Dw G' = exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) (k : V.Comp)
    (hτ : relab c σ τ.1 ∈ (V.X k).Ψ) : modelWt V G' k = modelWt V G k + modelFlat r ⟨_, hτ⟩ := by
  rw [modelWt_congr V hσ hU h, modelWt_add V hG (even_wtOf _ _), modelWt_flatWt V hσ hU τ k hτ]

theorem cuspOn_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c)
    {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : cuspOn U Z G = cuspOn U Z G' := by
  ext f
  simp only [cuspOn, Submodule.mem_inf, mem_cuspW, h]
  refine and_congr_left fun _ => and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem res_indep {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c)
    (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (k0 : (U σ).Comp)
    (hk : framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → (∀ i, b i ∈ suppOn Z) →
      LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => fun y : ↥((U σ).X k0).dom => rdU (U σ) (b i) k0 y.1)) ∧
    ∀ f ∈ sec Xo c a n, f ∈ suppOn Z → f ≠ 0 → ∃ y : ↥((U σ).X k0).dom, rdU (U σ) f k0 y.1 ≠ 0 := by
  have hR := GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ H Dw l Xo c σ r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (hL.unf σ hσ) a n
  simp only [Formalism.L2.PjFree.rdU_ofPj] at hR
  have hoff : ∀ f ∈ suppOn Z, ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      rdU (U σ) f k y = 0 := fun f hf k y hz => rdU_eq_zero (U σ) hf hz
  refine ⟨fun m b hb hs hli => ?_, fun f hf hs hne => ?_⟩
  · have h0 : LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := hR.1 m b hb hli
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro w hw
    refine h0 w ?_
    funext k y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ := hz
      have := congrFun hw ⟨y, hy⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    · exact Finset.sum_eq_zero fun i _ => by rw [hoff _ (hs i) k y hz, mul_zero]
  · by_contra hall
    push_neg at hall
    refine hne (hR.2 f hf fun k y hy => ?_)
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy'⟩ := hz
      exact hall ⟨y, hy'⟩
    · exact hoff f hs k y hz

theorem horizGen_mem (X : Data E r) (τ : X.Ψ) :
    (fun y : ↥X.dom => horizGen τ y.1) ∈ holAlg X ∧ (fun y : ↥X.dom => (horizGen τ y.1)⁻¹) ∈ holAlg X ∧
      ∀ y ∈ X.dom, horizGen τ y ≠ 0 := by
  have hdet : Differentiable ℂ (fun y : Frame X.Ψ r => (mat y τ).det) := by
    have e : (fun y : Frame X.Ψ r => (mat y τ).det) =
        fun y => ∑ p : Equiv.Perm (Fin r), ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ i, y τ (p i) i := by
      funext y
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [e]
    fun_prop
  have hne : ∀ y ∈ X.dom, (mat y τ).det ≠ 0 := fun y hy => (hy τ).1
  refine ⟨⟨fun y => horizGen τ y, ?_, fun y => rfl⟩, ⟨fun y => (horizGen τ y)⁻¹, ?_, fun y => rfl⟩,
    fun y hy => inv_ne_zero (hne y hy)⟩
  · exact (hdet.differentiableOn).inv hne
  · have : (fun y => (horizGen τ y)⁻¹) = fun y : Frame X.Ψ r => (mat y τ).det := by
      funext y; simp [horizGen]
    rw [this]; exact hdet.differentiableOn

theorem resRd_mem_holAlg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (σ : c.F →+* ℂ) (hσ : GoodEmb c σ)
    (hT : AllTest Xo c) (k : (U σ).Comp) (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    resRd (U σ) hT k f ∈ holAlg ((U σ).X k) := by
  have h1 := (mem_cuspW.1 hf).2 σ hσ
  have h2 : ∀ P ∈ holSub (U σ).X (modelWt (U σ) G), DifferentiableOn ℂ (P k) ((U σ).X k).dom := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP => exact (hP k).1.1.1
    | zero => exact differentiableOn_const 0
    | add P Q _ _ hP hQ => exact hP.add hQ
    | smul a P _ hP => exact (differentiableOn_const a).mul hP
  exact ⟨rdU (U σ) f k, h2 _ h1, fun y => rfl⟩

end Lemmas

set_option synthInstance.maxHeartbeats 200000 in
theorem flat_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧
      f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨a, n, hD, h2, hn, f0, hf0, hf0ne⟩ := GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component E H Dw l Xo c r U x hL Z
  obtain ⟨a', hD', h1', hex⟩ := GlobalTheory.T.exists_dominant_weight_shift_flatLineDet E H Dw a n τ hD h2
  have h1 : ∀ ρ i, i < Dw.mult ρ → 1 ≤ a (ρ, i) := fun ρ i hi => le_trans (by norm_num) (h2 ρ i hi)
  have hT : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
  have hEv : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hVV' : cuspOn U Z (wtZ a' n) = cuspOn U Z (wtZ a n + wtOf Dw (flatWt Dw τ) 0) :=
    cuspOn_congr hL.unf Z hex

  have hsec : ∀ (b : (E →+* ℂ) × ℕ → ℕ), cuspOn U Z (wtZ b n) ≤ sec Xo c b n := fun b f hf => by
    have := cuspW_le_secZ (U := U) (wtZ b n) (cuspOn_le U Z _ hf)
    rwa [AllWt.exZ_wtZ, secZ_nat] at this
  have hsupp : ∀ (G : WTZ E), cuspOn U Z G ≤ suppOn Z := fun G => inf_le_right
  have pk : ∀ σ, GoodEmb c σ → ∃ (k0 : (U σ).Comp) (hτ : relab c σ τ.1 ∈ ((U σ).X k0).Ψ),
      framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} ∧
      (∀ f ∈ cuspOn U Z (wtZ a n), (fun y : ↥((U σ).X k0).dom => horizGen ⟨_, hτ⟩ y.1) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a' n) : Set (Rul Xo c)))) ∧
      (∀ f ∈ cuspOn U Z (wtZ a' n), (fun y : ↥((U σ).X k0).dom => (horizGen ⟨_, hτ⟩ y.1)⁻¹) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c)))) := by
    intro σ hσ
    obtain ⟨k0, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k0
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k0 hτ
    refine ⟨k0, hτ, hk, fun f hf => ?_, fun f hf => ?_⟩
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ 1 a a' n hD hD' h1' hn (by rw [hw, one_smul]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ (-1) a' a n hD' hD h1 hn
        (by rw [hw, neg_one_smul, add_neg_cancel_right]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
  obtain ⟨σ0, hσ0⟩ : ∃ σ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a n hD h1 hn).1
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a' n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a' n hD' h1' hn).1
  have hprod : ∀ f ∈ cuspOn U Z (wtZ a n), ∀ g ∈ cuspOn U Z (wtZ a' n),
      f * g ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := by
    intro f hf g hg
    have e : exZ Dw (wtZ (a + a') (n + n)) = exZ Dw (wtZ a n) + exZ Dw (wtZ a' n) := by
      rw [wtZ_add]; funext i; exact exZ_add _ _ i
    have hm := mul_mem_secZ (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hf))
      (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hg))
    rw [← e, AllWt.exZ_wtZ, secZ_nat] at hm
    refine ⟨hm, ?_⟩
    rw [mul_comm]
    exact mul_mem_suppOn g (hsupp _ hf)
  obtain ⟨k0, hτ0, hk0, hA0, -⟩ := pk σ0 hσ0
  obtain ⟨T, hT0, hTc⟩ := GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier c.F (Rul Xo c) (↥((U σ0).X k0).dom → ℂ) σ0 (resRd (U σ0) hT k0)
    (resRd_smul (U σ0) hT k0) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun m b hb hli => by
      have hb' : ∀ i, b i ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := fun i =>
        (Submodule.mul_le.2 hprod) (hb i)
      exact (res_indep hL Z σ0 hσ0 k0 hk0 (a + a') (n + n)).1 m b (fun i => (hb' i).1) (fun i => (hb' i).2) hli)
    (fun y => horizGen ⟨_, hτ0⟩ y.1) hA0 ⟨f0, hf0, fun h0 => by
      obtain ⟨y, hy⟩ := (res_indep hL Z σ0 hσ0 k0 hk0 a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
      have := congrFun h0 y
      simp only [Pi.mul_apply, resRd_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact (horizGen_mem _ _).2.2 y.1 y.2 h
      · exact hy h⟩
  refine ⟨wtZ a n, f0, T ⟨f0, hf0⟩, hEv, hf0, hVV' ▸ (T ⟨f0, hf0⟩).2, hf0ne, fun σ hσ => ?_⟩
  obtain ⟨k1, hτ, hk, hA, hA'⟩ := pk σ hσ
  obtain ⟨y0, -⟩ := (res_indep hL Z σ hσ k1 hk a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
  haveI := GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain E r ((U σ).X k1) ⟨y0.1, y0.2⟩
  obtain ⟨hh, hh', hne⟩ := horizGen_mem ((U σ).X k1) ⟨_, hτ⟩
  obtain ⟨α, hα, hαT⟩ := GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt c.F (Rul Xo c) (↥((U σ).X k1).dom → ℂ) σ (resRd (U σ) hT k1)
    (resRd_smul _ _ _) (holAlg ((U σ).X k1)) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a n).1 m b (fun i => hsec a (hb i)) (fun i => hsupp _ (hb i)) hli)
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a' n).1 m b (fun i => hsec a' (hb i)) (fun i => hsupp _ (hb i))
      hli)
    _ _ hh hh' (by funext y; exact mul_inv_cancel₀ (hne y.1 y.2)) hA' T hT0 hTc
  refine ⟨α, hα, fun k hτk y hy => ?_⟩
  rw [hk] at hy
  obtain ⟨rfl, hyd⟩ := hy
  have e := congrFun (hαT ⟨f0, hf0⟩) ⟨y, hyd⟩
  simp only [resRd_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e
  rw [e]
  ring

end GlobalTheory.FlatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGeneratorStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧ f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  first | exact @GlobalTheory.FlatPair.flat_pair | exact GlobalTheory.FlatPair.flat_pair | (intros; apply GlobalTheory.FlatPair.flat_pair <;> assumption)
end
