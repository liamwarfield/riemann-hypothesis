module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqUnitaryTransvectionMul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletionStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) *
      Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  let X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1
  have hXbot : X ⊥ = 0 := if_pos rfl
  have hXne : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => if_neg hI
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · simp [X, hI]
    by_cases hJ : J = ⊥
    · simp [X, hJ]
    rw [hXne _ (Ideal.mul_eq_bot.not.mpr (not_or.mpr ⟨hI, hJ⟩)), hXne _ hI, hXne _ hJ, one_mul]
  obtain ⟨Z, hZd, hZ, -⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K ⊤ X (fun _ => 1) top_ne_bot
    hXbot hXmul (fun I hI _ => by rw [hXne I hI, norm_one]) (fun I hI => absurd (sup_top_eq I) hI)
    (fun _ _ => (mul_one 1).symm) (fun _ _ _ => rfl) contDiffOn_const (fun _ _ => norm_one)
    (fun β hβ _ => hXne _ (by simpa using hβ))
  refine ⟨Z, hZd, fun s hs => ?_⟩
  rw [hZ s hs, _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot (hXne ⊤ top_ne_bot) hXmul
    (fun I => by by_cases hI : I = ⊥ <;> simp [X, hI]) s hs]
  have h1 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => hXne _ P.ne_bot
  simp only [h1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, AddMonoidAlgebra.coeff f' m = l (c * AddMonoidAlgebra.coeff f m) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add (f := _), h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add (f := _)]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSetStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  first | exact @GlobalTheory.ClassFin.component_mem_vanI | exact GlobalTheory.ClassFin.component_mem_vanI | (intros; apply GlobalTheory.ClassFin.component_mem_vanI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosure
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma ringEquiv_eval_eq_eval_map {σ : Type} (e : ℂ ≃+* ℂ) (x : σ → ℂ)
    (p : MvPolynomial σ ℂ) :
    e (MvPolynomial.eval x p) =
      MvPolynomial.eval (fun i => e (x i)) (MvPolynomial.map (e : ℂ →+* ℂ) p) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  exact MvPolynomial.hom_eval₂ p (RingHom.id ℂ) (e : ℂ →+* ℂ) x

private lemma ev_eq_evC_map_algebraMap {ι : Type} (p : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.ev p g =
      _root_.GlobalTheory.ClassFin.evC (MvPolynomial.map (algebraMap ℚ ℂ) p) g := by
  unfold _root_.GlobalTheory.ClassFin.ev _root_.GlobalTheory.ClassFin.evC
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]

private lemma mem_span_rational_of_vanishing {ι : Type} (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) :
    f ∈ Submodule.span ℂ {w | ∃ p ∈ _root_.GlobalTheory.ClassFin.vanI Γ,
      MvPolynomial.map (algebraMap ℚ ℂ) p = w} := by
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {w | ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC w g = 0}
      add_mem' := fun {a b} ha hb g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
        rw [ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by simp [_root_.GlobalTheory.ClassFin.evC]
      smul_mem' := fun c w hw g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, Set.mem_setOf_eq] at *
        rw [MvPolynomial.smul_eval, hw g hg, mul_zero] }
  have hstable : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr w' k =
        σ ((MvPolynomial.basisMonomials (ι × ι) ℂ).repr w k) := by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, fun g hg => ?_, fun k => MvPolynomial.coeff_map _ _ _⟩
    have h := hw (g.map σ.symm) (hΓ σ.symm g hg)
    have h2 := ringEquiv_eval_eq_eval_map σ (fun ij => (g.map σ.symm) ij.1 ij.2) w
    simp only [_root_.GlobalTheory.ClassFin.evC] at h ⊢
    rw [h, map_zero] at h2
    simpa [Matrix.map_apply] using h2.symm
  have hle := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ)
    W hstable
  refine Submodule.span_mono ?_ (hle hf)
  rintro w ⟨hwW, hrat⟩
  have hrange : w ∈ Set.range (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    obtain ⟨q, hq⟩ := hrat n
    exact ⟨q, hq.symm⟩
  obtain ⟨p, rfl⟩ := hrange
  refine ⟨p, fun g hg => ?_, rfl⟩
  rw [ev_eq_evC_map_algebraMap]
  exact hwW g hg

theorem _root_.GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) →
    ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) →
    ∀ y ∈ _root_.GlobalTheory.ClassFin.pts Γ ℂ, _root_.GlobalTheory.ClassFin.evC f y = 0 := by
  intro ι _ _ Γ hΓ f hf y hy
  have hspan := mem_span_rational_of_vanishing Γ hΓ f hf
  clear hf
  induction hspan using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    rw [← ev_eq_evC_map_algebraMap]
    exact hy p hp
  | zero => simp [_root_.GlobalTheory.ClassFin.evC]
  | add a b _ _ ha hb =>
    simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
    rw [ha, hb, add_zero]
  | smul c w _ hw =>
    simp only [_root_.GlobalTheory.ClassFin.evC] at *
    rw [MvPolynomial.smul_eval, hw, mul_zero]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosureStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ y ∈ pts Γ ℂ, evC f y = 0 := by
  first | exact @GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | exact GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | (intros; apply GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvections
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvections
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Gen

end GlobalTheory.UTrans.Gen

namespace GlobalTheory.UTrans

private theorem refl_eq_tv_sub_one_div_hf {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    _root_.GlobalTheory.UnRep.refl c G x u =
      _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((u - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
    _root_.GlobalTheory.UTrans.Model.tv_mulVec]
  change v + ((u - 1) * _root_.GlobalTheory.UTrans.hf (c : E →+* E) G v x /
    _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) • x = _
  congr 2
  ring

private theorem det_refl_eq_of_hermE_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E)
    (hx : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0) :
    (_root_.GlobalTheory.UnRep.refl c G x u).det = u := by
  unfold _root_.GlobalTheory.UnRep.refl
  have hw : (G.mulVec fun b => c (x b)) ⬝ᵥ x = _root_.GlobalTheory.UnRep.hermE c G x x :=
    (_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot c G x x).symm
  have hmat : ((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) •
      Matrix.vecMulVec x (G.mulVec fun b => c (x b)) =
      Matrix.replicateCol Unit (((u - 1) / _root_.GlobalTheory.UnRep.hermE c G x x) • x) *
        Matrix.replicateRow Unit (G.mulVec fun b => c (x b)) := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hw, smul_eq_mul]
  field_simp
  ring

theorem _root_.GlobalTheory.UTrans.isU_eq_tv_mul_tvGen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ γ, _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G γ → (∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G) := by
  intro F E _ _ _ _ _ c n G hG hiso γ hγ
  have hG' : _root_.GlobalTheory.UnRep.IsHermForm c G := by
    refine ⟨hG.invol, ?_, hG.herm,
      hG.det_ne⟩
    intro h1
    obtain ⟨a, ha⟩ := hG.ne_id
    apply ha
    rw [h1]
    rfl
  have hγ' : _root_.GlobalTheory.UnRep.IsUnE c G γ := fun v w => hγ v w
  obtain ⟨l, hl, hγl⟩ := _root_.GlobalTheory.UnRep.isUnE_eq_prod_refl F E c n G hG' γ hγ'
  have hnorm := (_root_.GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG).2
  have main : ∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 →
      ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G,
        γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x
          ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m := by
    intro x hx
    have hx' : _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 := hx
    obtain ⟨_, _, hmul, hunit⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'

    have key : ∀ l' : List ((Fin n → E) × E),
        (∀ p ∈ l', _root_.GlobalTheory.UnRep.hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
        ∃ M ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, ∃ U : E, U * c U = 1 ∧
          (l'.map fun p => _root_.GlobalTheory.UnRep.refl c G p.1 p.2).prod =
            M * _root_.GlobalTheory.UnRep.refl c G x U := by
      intro l' hl'
      induction l' with
      | nil =>
        refine ⟨1, Submonoid.one_mem _, 1, by simp, ?_⟩
        obtain ⟨_, h1, _, _⟩ := _root_.GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG' x hx'
        simp [h1]
      | cons p l' ih =>
        obtain ⟨M, hM, U, hU, hprod⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        obtain ⟨hp1, hp2⟩ := hl' p List.mem_cons_self
        obtain ⟨m₁, hm₁, hq₁⟩ := _root_.GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul E n (c : E →+* E) G hG hiso
          p.1 x p.2 hp1 hx hp2
        obtain ⟨M', hM', hcomm, _⟩ := (hnorm M hM).2.2.2 _ ((hunit p.2 hp2) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
        refine ⟨m₁ * M', Submonoid.mul_mem _ hm₁ hM', p.2 * U, ?_, ?_⟩
        · rw [map_mul]
          calc p.2 * U * (c p.2 * c U) = (p.2 * c p.2) * (U * c U) := by ring
            _ = 1 := by rw [hp2, hU, one_mul]
        · rw [List.map_cons, List.prod_cons, hprod, refl_eq_tv_sub_one_div_hf, hq₁,
            ← refl_eq_tv_sub_one_div_hf, ← hmul]
          calc m₁ * _root_.GlobalTheory.UnRep.refl c G x p.2 * (M * _root_.GlobalTheory.UnRep.refl c G x U)
              = m₁ * (_root_.GlobalTheory.UnRep.refl c G x p.2 * M) * _root_.GlobalTheory.UnRep.refl c G x U := by
                simp only [mul_assoc]
            _ = m₁ * (M' * _root_.GlobalTheory.UnRep.refl c G x p.2) * _root_.GlobalTheory.UnRep.refl c G x U := by
                rw [hcomm]
            _ = _ := by simp only [mul_assoc]
    obtain ⟨M, hM, U, hU, hprod⟩ := key l hl
    have hγM : γ = M * _root_.GlobalTheory.UnRep.refl c G x U := hγl.trans hprod
    have hdet : γ.det = U := by
      rw [hγM, Matrix.det_mul, (hnorm M hM).2.1, one_mul, det_refl_eq_of_hermE_ne_zero c G x U hx']
    obtain ⟨_, _, _, m'', hm'', hcomm⟩ := (hnorm M hM).2.2.2 _ ((hunit U hU) : _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G _)
    refine ⟨m'', hm'', ?_⟩
    rw [hdet, hγM, hcomm, refl_eq_tv_sub_one_div_hf]
  refine ⟨main, fun h1 => ?_⟩
  obtain ⟨z, hz, _⟩ := hiso
  obtain ⟨i, -⟩ := Function.ne_iff.mp hz
  obtain ⟨y, hyy, -, -⟩ := _root_.GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG'
  obtain ⟨m, hm, hγm⟩ := main (y i) (hyy i)
  have h0 : _root_.GlobalTheory.UTrans.tv (c : E →+* E) G (y i) 0 = 1 := by
    unfold _root_.GlobalTheory.UTrans.tv
    ext a b
    simp
  rw [h1, sub_self, zero_div, h0, one_mul] at hγm
  rw [hγm]
  exact hm

end GlobalTheory.UTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvectionsStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_eq_quasiReflection_mul_transvections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0) → ∀ γ, IsU (c : E →+* E) G γ → (∀ x, hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ TvGen (c : E →+* E) G, γ = tv (c : E →+* E) G x ((γ.det - 1) / hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ TvGen (c : E →+* E) G) := by
  first | exact @GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | exact GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | (intros; apply GlobalTheory.UTrans.isU_eq_tv_mul_tvGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLe
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLe
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

private theorem exists_valuation_natCast_eq_exp_neg_and_dvd {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : 0 < p) :
    ∃ e : ℕ, HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-(e : ℤ)) ∧
      v.asIdeal ^ e ∣ Ideal.span {(p : 𝓞 F)} := by
  have hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    simp
  have hne : v.intValuation (p : 𝓞 F) ≠ 0 :=
    v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')
  have hle : v.intValuation (p : 𝓞 F) ≤ 1 := v.intValuation_le_one _
  set a := v.intValuation (p : 𝓞 F) with ha
  have hlog : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log a).toNat, ?_, ?_⟩
  · rw [hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg,
      WithZero.exp_log hne]

private theorem powSub_eq_comap_pows_units_map {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) :
    _root_.GlobalTheory.CNorm.powSub p φ =
      (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).comap (Units.map φ.toMonoidHom) := by
  ext x
  rw [_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]
  unfold _root_.GlobalTheory.CNorm.pows
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(y : L), ?_⟩
    have := congrArg Units.val hy
    simpa using this

private theorem powSub_index_ne_zero_and_le_pIdx {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) (h : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) ≠ 0) :
    (_root_.GlobalTheory.CNorm.powSub p φ).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.powSub p φ).index ≤ _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) := by
  have hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index := by
    unfold _root_.GlobalTheory.CNorm.pIdx
    exact Subgroup.relIndex_top_right _
  rw [hdef] at h ⊢
  rw [powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ))
    (Units.map φ.toMonoidHom).range
  exact ⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩

private theorem pTor_units_le {L : Type} [Field L] {p : ℕ} (hp : 0 < p) :
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup Lˣ) ≤ p := by
  unfold _root_.GlobalTheory.CNorm.pTor
  classical
  have hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} =>
      (⟨(x.1 : L), by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2,
          Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by
    intro x y hxy
    exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  calc Nat.card {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1}
      ≤ Nat.card (Polynomial.nthRoots p (1 : L)).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (Polynomial.nthRoots p (1 : L)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots p (1 : L)).card := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

private theorem prod_absNorm_pow_le_pow_finrank {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ} (hp : 0 < p) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ p ^ Module.finrank ℚ F := by
  have hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ he
    intro v _ w _ hvw
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (HeightOneSpectrum.ext h)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [hnorm, map_prod] at h
  simp only [map_pow] at h
  exact Nat.le_of_dvd (pow_pos hp _) h

theorem _root_.GlobalTheory.CNorm.index_finPow_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p →
    (_root_.GlobalTheory.CNorm.finPow p F S).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.finPow p F S).index ≤
        p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  intro p F _ _ _ S hp
  choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤
          p * Ideal.absNorm v.asIdeal ^ e v * p := by
    intro v
    obtain ⟨ht, hrel⟩ :=
      _root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)
    rw [Module.finrank_self, pow_one] at hrel
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht
    obtain ⟨h1, h2⟩ := powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne
    refine ⟨h1, h2.trans ?_⟩
    rw [hrel]
    exact Nat.mul_le_mul_left _ (pTor_units_le hp)
  have hinf : _root_.GlobalTheory.CNorm.finPow p F S =
      ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p
        (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
    unfold _root_.GlobalTheory.CNorm.finPow
    rw [iInf_subtype']
  rw [hinf]
  refine ⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩
  calc ∏ v : S, (_root_.GlobalTheory.CNorm.powSub p
          (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).index
      ≤ ∏ v : S, (p * Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v * p) :=
        Finset.prod_le_prod' fun v _ => (hloc v).2
    _ = p ^ (2 * S.card) * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
        rw [Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F :=
        Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)
    _ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
        rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]
        ring_nf

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLeStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalPowersAtPlaces_index_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p → (finPow p F S).index ≠ 0 ∧ (finPow p F S).index ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  first | exact @GlobalTheory.CNorm.index_finPow_le | exact GlobalTheory.CNorm.index_finPow_le | (intros; apply GlobalTheory.CNorm.index_finPow_le <;> assumption)
end
end
