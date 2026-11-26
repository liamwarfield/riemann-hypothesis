module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem tauPt_one (τ : L →+* ℂ) : tauPt τ (1 : GL (Fin n) ℂ) = fun _ => 1 := by
  funext σ
  simp only [tauPt, inv_one, Units.val_one, Matrix.transpose_one]
  split_ifs <;> rfl

theorem tauPt_mul (τ : L →+* ℂ) (A B : GL (Fin n) ℂ) :
    tauPt τ (A * B) = fun σ => tauPt τ A σ * tauPt τ B σ := by
  funext σ
  simp only [tauPt]
  split_ifs
  · simp
  · simp [_root_.mul_inv_rev, Matrix.transpose_mul]
  · simp


open Classical in
def tauSubst (τ : L →+* ℂ) : (L →+* ℂ) × Fin n × Fin n →
    MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (Sum.inl (p.2.1, p.2.2))
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (Sum.inr (p.2.2, p.2.1))
  else MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)

theorem eval_evPt (τ : L →+* ℂ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (evPt τ B) Q =
      MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2))
        (MvPolynomial.bind₁ (tauSubst τ) Q) := by
  have e := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ)
    (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) (tauSubst τ) Q
  erw [e]
  show MvPolynomial.eval _ Q = MvPolynomial.eval _ Q
  congr 2
  funext p
  simp only [evPt_eq_upt, upt, tauPt, tauSubst]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isPolyRep_evPt (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (h : Agrees a b P) (τ : L →+* ℂ) :
    IsPolyRep (fun B => evM P (evPt τ B)) := by
  obtain ⟨h1, hm⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P h
  refine ⟨?_, ?_, ?_⟩
  · show evM P (evPt τ 1) = 1
    rw [evPt_eq_upt, tauPt_one]
    exact h1
  · intro A B
    show evM P (evPt τ (A * B)) = evM P (evPt τ A) * evM P (evPt τ B)
    rw [evPt_eq_upt, evPt_eq_upt, evPt_eq_upt, tauPt_mul]
    exact hm _ _ (isUPt_tauPt τ A) (isUPt_tauPt τ B)
  · intro i j
    refine ⟨MvPolynomial.bind₁ (tauSubst τ) (P i j), fun B => ?_⟩
    show MvPolynomial.eval (evPt τ B) (P i j) = _
    exact eval_evPt τ (P i j) B

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ τ : L →+* ℂ, IsPolyRep (fun B => evM P (evPt τ B)) := by
  first | exact @GlobalTheory.AlgWtHW.isPolyRep_evPt | exact GlobalTheory.AlgWtHW.isPolyRep_evPt | (intros; apply GlobalTheory.AlgWtHW.isPolyRep_evPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.SplitComplHomeo


open scoped WithZeroTopology in
theorem exists_complEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L,
      Continuous i ∧ Continuous i.symm ∧ ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro E _ _ _ s
  have : s.w.asIdeal.LiesOver s.v.asIdeal := ⟨s.w_under.symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (maximalRealSubfield E) E s.v s.w).continuous
  let φ : s.v.adicCompletion (maximalRealSubfield E) →+* s.w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E s.w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv (maximalRealSubfield E) s.v).toRingHom
  have hφ : ∀ x : maximalRealSubfield E, φ (algebraMap (maximalRealSubfield E) _ x) =
      algebraMap E _ (algebraMap (maximalRealSubfield E) E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E s.w).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion (maximalRealSubfield E) s.v))
  have hi : ∀ x : E, φ (s.i x) = algebraMap E (s.w.adicCompletion E) x := fun x => by
    have key : ∀ y, Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x) := fun y =>
      (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).induction_on
        (p := fun y => Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x)) y
        (isClosed_eq
          ((Valued.continuous_valuation_of_surjective (s.w.valuedAdicCompletion_surjective E)).comp
            (hcont.sub continuous_const))
          ((Valued.continuous_valuation_of_surjective (s.v.valuedAdicCompletion_surjective _)).comp
            (continuous_id.sub continuous_const))) fun k => by
        rw [hφ, ← map_sub, ← PI.CompAtExist.stepA s, map_sub, AlgHom.commutes]
    have h0 := key (s.i x)
    rw [sub_self, map_zero, map_eq_zero, sub_eq_zero] at h0
    exact h0
  letI : Algebra (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hcont
  letI : NontriviallyNormedField (s.v.adicCompletion (maximalRealSubfield E)) :=
    Valued.toNontriviallyNormedField _ _
  have hs : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E)) := Submodule.closed_of_finiteDimensional _
    intro y
    exact (HeightOneSpectrum.denseRange_algebraMap E s.w).induction_on
      (p := fun y => y ∈ (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E))) y hcl fun x => ⟨s.i x, hi x⟩
  let e : s.v.adicCompletion (maximalRealSubfield E) ≃ₗ[s.v.adicCompletion (maximalRealSubfield E)]
      s.w.adicCompletion E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨φ.injective, hs⟩
  haveI : FiniteDimensional (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    e.finiteDimensional
  have hinv : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, hcont, hinv.congr fun y => ?_, hi⟩
  exact (RingEquiv.symm_apply_eq _).2 (e.apply_symm_apply y).symm |>.symm

end GlobalTheory.SplitComplHomeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by
  have key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N =
      c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k) := by
    intro μ k
    have h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V))) := by
      rw [sub_mul, h, mul_sub, smul_sub]
      simp [smul_smul]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ', ← pow_succ]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [End.iSup_maxGenEigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    have h1 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc
      hs.isFinitelySemisimple hn
    have h2 : N v ∈ f.maxGenEigenspace (c * μ) := by
      rw [End.mem_maxGenEigenspace] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      refine ⟨k, ?_⟩
      have := LinearMap.congr_fun (key μ k) v
      simpa [hk] using this
    have h3 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc
      hs.isFinitelySemisimple hn
    simp [h1, h3, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Lin

theorem isNilpotent_pow_sub_one {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)

theorem commute_of_commute_pow {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]

theorem exists_frobenius_semisimplification : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob (h := h)))
  set f := ρ (frob (h := h)) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob (h := h))).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob (h := h))
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob (h := h)) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob (h := h)) (τ * frob (h := h) * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob (h := h)) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob (h := h)) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp

end GlobalTheory.WeilDeligne
end
