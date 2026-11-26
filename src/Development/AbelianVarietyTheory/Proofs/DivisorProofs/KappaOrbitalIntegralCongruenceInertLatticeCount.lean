module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModel
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem charpoly_mulLeft_eq_of_gen {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (Q : F[X]) (hQ : Q.Monic) (hadj : Algebra.adjoin F {u} = ⊤) (hr : aeval u Q = 0)
    (hd : Module.finrank F A = Q.natDegree) : (LinearMap.mulLeft F u).charpoly = Q := by
  set P := (LinearMap.mulLeft F u).charpoly with hPdef
  have hP : P.Monic := LinearMap.charpoly_monic _
  have hPd : P.natDegree = Q.natDegree := by rw [hPdef, LinearMap.charpoly_natDegree, hd]
  by_cases hQ1 : Q = 1
  · subst hQ1
    rw [natDegree_one] at hPd
    exact Polynomial.eq_one_of_monic_natDegree_zero hP hPd
  set d := Q.natDegree with hddef
  let v : Fin d → A := fun i => u ^ (i : ℕ)
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro a _
    have ha : a ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    show aeval u p ∈ _
    rw [← Polynomial.aeval_modByMonic_eq_self_of_root hr,
      Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_modByMonic_lt p hQ hQ1)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hd, hddef])
  have hPu : aeval u P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F u)
    have h2 : (Algebra.lmul F A) u = LinearMap.mulLeft F u := by ext; simp
    rw [← hPdef, ← h2, Polynomial.aeval_algHom_apply] at h1
    have h3 := congrArg (fun f : Module.End F A => f 1) h1
    simpa using h3
  by_contra hne
  have hR : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).degree < d := by
    have := Polynomial.degree_sub_lt (p := P) (q := Q) (by rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hQ.ne_zero, hPd]) hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hP.ne_zero, hPd] at this
  have hRd : (P - Q).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hR).2 hdeg
  have hz : aeval u (P - Q) = 0 := by simp [hPu, hr]
  rw [Polynomial.aeval_eq_sum_range' hRd, Finset.sum_range (fun i => (P - Q).coeff i • u ^ i)] at hz
  have hc := (Fintype.linearIndependent_iff.1 hli) (fun i => (P - Q).coeff i) hz ⟨_, hRd⟩
  exact hR (Polynomial.leadingCoeff_eq_zero.1 hc)

theorem charpoly_of_semilinear {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F A] [Module.Finite F A]
    (e : F ≃+* L) {n : ℕ} (u : A) (g : Matrix (Fin n) (Fin n) L) (ψ : A ≃+ (Fin n → L))
    (hψ : ∀ (c : F) (y : A), ψ (c • y) = e c • ψ y) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) :
    g.charpoly = (LinearMap.mulLeft F u).charpoly.map (e : F →+* L) := by
  let b := Module.finBasis F A
  set d := Module.finrank F A
  let v : Fin d → (Fin n → L) := fun i => ψ (b i)
  have hsum : ∀ c : Fin d → L, ∑ i, c i • v i = ψ (∑ i, e.symm (c i) • b i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, e.apply_symm_apply]
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [hsum, map_eq_zero_iff ψ ψ.injective] at hc
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hc i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, rfl⟩ := ψ.surjective x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin d) L (Fin n → L) := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i => Module.Basis.mk_apply hli hsp i
  let M := LinearMap.toMatrix b b (LinearMap.mulLeft F u)
  have key : LinearMap.toMatrix b' b' (Matrix.toLin' g) = M.map (e : F →+* L) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hb', Matrix.toLin'_apply]
    have h1 : g *ᵥ v j = ∑ k, e (b.repr (u * b j) k) • b' k := by
      show g *ᵥ ψ (b j) = _
      rw [← hu]
      conv_lhs => rw [← b.sum_repr (u * b j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hψ, hb']
    rw [h1, b'.repr_sum_self]
    simp [M, LinearMap.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc g.charpoly = (Matrix.toLin' g).charpoly := by
        rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' g) (Pi.basisFun L (Fin n)),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    _ = (M.map (e : F →+* L)).charpoly := by rw [← key, LinearMap.charpoly_toMatrix]
    _ = _ := by rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  intro E _ _ _ w K e n Q B u x γ hQ hfit hmod
  obtain ⟨hadj, hr, hd, -⟩ := hfit
  obtain ⟨ψ, hψ, hu, -⟩ := hmod
  rw [charpoly_of_semilinear e u γ.val ψ hψ hu,
    charpoly_mulLeft_eq_of_gen u (Q.map e.symm.toRingHom) (hQ.map _) hadj hr (by rw [hd, natDegree_map]),
    Polynomial.map_map]
  ext i
  simp [Polynomial.coeff_map]

end GlobalTheory.KapLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModelStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  first | exact @GlobalTheory.KapLat.charpoly_of_model | exact GlobalTheory.KapLat.charpoly_of_model | (intros; apply GlobalTheory.KapLat.charpoly_of_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNorm
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem stdH_mulVec_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (y : GLw n w) (hy : y ∈ UJ (cj w) 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (y.val *ᵥ v) (y.val *ᵥ v') = stdH w v v' := by
  have h1 : (cT (cj w) y.val) * 1 * y.val = 1 := hy
  have h2 : (y.val)ᵀ * y.val.map (cj w) = 1 := by
    have := congrArg Matrix.transpose h1
    simpa [cT, Matrix.transpose_mul] using this
  have hs : ∀ z : Fin n → w.adicCompletion E, ∀ z', stdH w z z' = z ⬝ᵥ (fun k => cj w (z' k)) := by
    intro z z'; rfl
  have hc : (fun k => cj w ((y.val *ᵥ v') k)) = y.val.map (cj w) *ᵥ (fun k => cj w (v' k)) := by
    funext k; exact RingHom.map_mulVec (cj w) y.val v' k
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h2,
    Matrix.vecMul_one]

theorem isReduced_of_adjoin_squarefree {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (hu : Algebra.adjoin F {u} = ⊤) (P : F[X]) (hP : Squarefree P) (hPu : aeval u P = 0) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := ha
  have hmem : a ∈ Algebra.adjoin F {u} := by rw [hu]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, rfl⟩ := hmem
  have hsq : Squarefree (minpoly F u) := hP.squarefree_of_dvd (minpoly.dvd F u hPu)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    have h10 : (1 : A) = 0 := by simpa using hk
    exact (subsingleton_of_zero_eq_one h10.symm).elim _ _
  have hd : minpoly F u ∣ p ^ k := minpoly.dvd F u (by rw [map_pow]; exact hk)
  have hd' : minpoly F u ∣ p := (hsq.dvd_pow_iff_dvd hk0.ne').1 hd
  obtain ⟨r, hr⟩ := hd'
  change aeval u p = 0
  rw [hr, map_mul, minpoly.aeval, zero_mul]

theorem model_conj_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X])
    (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) →
    ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  intro E _ _ _ w hw K e n Q B u x x' hQ hF γ y hy hM hM'
  obtain ⟨hadj, hroot, -, -⟩ := hF
  have hyU : y ∈ UJ (cj w) 1 := by simpa [UL, hw] using hy
  obtain ⟨ψ, hψs, hψu, hψh⟩ := hM
  obtain ⟨ψ', hψs', hψu', hψh'⟩ := hM'

  let ψ₃ : B.A → (Fin n → w.adicCompletion E) := fun a => y.val *ᵥ ψ' a
  have h3s : ∀ (c : K.E) (a : B.A), ψ₃ (c • a) = e c • ψ₃ a := by
    intro c a; simp only [ψ₃, hψs', Matrix.mulVec_smul]
  have h3u : ∀ a, ψ₃ (u * a) = γ.val *ᵥ ψ₃ a := by
    intro a
    simp only [ψ₃, hψu', Matrix.mulVec_mulVec, Units.val_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h3h : ∀ a b, stdH w (ψ₃ a) (ψ₃ b) = e (B.herm x' a b) := by
    intro a b; simp only [ψ₃]; rw [stdH_mulVec_of_mem w n y hyU, hψh']

  let φ : B.A → B.A := fun a => ψ.symm (ψ₃ a)
  have hφψ : ∀ a, ψ (φ a) = ψ₃ a := fun a => ψ.apply_symm_apply _
  have hφs : ∀ (c : K.E) (a : B.A), φ (c • a) = c • φ a := by
    intro c a; apply ψ.injective; rw [hψs, hφψ, hφψ, h3s]
  have hφu : ∀ a, φ (u * a) = u * φ a := by
    intro a; apply ψ.injective; rw [hψu, hφψ, hφψ, h3u]
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b; apply ψ.injective; rw [map_add (f := _), hφψ, hφψ, hφψ]; simp [ψ₃, Matrix.mulVec_add]

  have hφmul : ∀ a b, φ (a * b) = a * φ b := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hadj]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
    | algebraMap r =>
      intro b; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [add_mul, hφadd, h₁, h₂, add_mul]
    | mul a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [mul_assoc, h₁, h₂, mul_assoc]
  have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]

  obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := by
    refine ⟨ψ'.symm ((y⁻¹ : GLw n w).val *ᵥ ψ 1), ?_⟩
    apply ψ.injective
    rw [hφψ]
    simp only [ψ₃, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
  refine ⟨c, ?_⟩

  have hh : ∀ a b, B.herm x' a b = B.herm x (φ a) (φ b) := by
    intro a b; apply e.injective; rw [← h3h, ← hψh, hφψ, hφψ]
  have htr : ∀ z : B.A, Algebra.trace K.E B.A ((x * ((c : B.A) * B.σ (c : B.A)) - x') * z) = 0 := by
    intro z
    have := hh z 1
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_one, mul_one] at this
    rw [hφ z] at this
    have hc : (c : B.A) = φ 1 := rfl
    rw [hc, sub_mul, map_sub, sub_eq_zero, this]
    congr 1; ring
  haveI : IsReduced B.A := isReduced_of_adjoin_squarefree u hadj _ (hQ.map.squarefree) hroot
  exact (sub_eq_zero.1 (GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero _ htr)).symm

end GlobalTheory.KapLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNormStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u → ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) → ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  first | exact @GlobalTheory.KapLat.model_conj_norm | exact GlobalTheory.KapLat.model_conj_norm | (intros; apply GlobalTheory.KapLat.model_conj_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplit
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat.ExModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Herm

variable (w : Pl E) {n : ℕ}

theorem stdH_add_left (a b c : Fin n → w.adicCompletion E) :
    stdH w (a + b) c = stdH w a c + stdH w b c := by
  simp [stdH, add_mul, Finset.sum_add_distrib]

theorem stdH_add_right (a b c : Fin n → w.adicCompletion E) :
    stdH w a (b + c) = stdH w a b + stdH w a c := by
  simp [stdH, mul_add, Finset.sum_add_distrib]

theorem stdH_smul_left (r : w.adicCompletion E) (a b : Fin n → w.adicCompletion E) :
    stdH w (r • a) b = r * stdH w a b := by
  simp [stdH, Finset.mul_sum, mul_assoc]

theorem stdH_smul_right (r : w.adicCompletion E) (a b : Fin n → w.adicCompletion E) :
    stdH w a (r • b) = cj w r * stdH w a b := by
  simp only [stdH, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem stdH_single (a : Fin n → w.adicCompletion E) (k : Fin n) :
    stdH w a (Pi.single k 1) = a k := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

theorem cj_cj {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [← hB.1, ← hB.1, K.c_c]

theorem stdH_symm {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (a b : Fin n → w.adicCompletion E) : stdH w b a = cj w (stdH w a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [stdH, map_sum, map_mul, cj_cj w hB]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem stdH_unitary (γ : GLw n w) (hγ : cT (cj w) γ.val * 1 * γ.val = 1)
    (a b : Fin n → w.adicCompletion E) : stdH w (γ.val *ᵥ a) (γ.val *ᵥ b) = stdH w a b := by
  have h1 : γ.valᵀ * γ.val.map (cj w) = 1 := by
    have h0 : (γ.val.map (cj w))ᵀ * γ.val = 1 := by simpa [cT] using hγ
    have h2 : γ.val * (γ.val.map (cj w))ᵀ = 1 := mul_eq_one_comm.mp h0
    have h3 : γ.val.map (cj w) * γ.valᵀ = 1 := by
      have := congrArg Matrix.transpose h2
      simpa [Matrix.transpose_mul] using this
    exact mul_eq_one_comm.mp h3
  have hc : ∀ z : Fin n → w.adicCompletion E,
      (fun k => cj w ((γ.val *ᵥ z) k)) = γ.val.map (cj w) *ᵥ (fun k => cj w (z k)) := by
    intro z; funext k; exact RingHom.map_mulVec (cj w) γ.val z k
  have hs : ∀ a b : Fin n → w.adicCompletion E, stdH w a b = a ⬝ᵥ (fun k => cj w (b k)) :=
    fun a b => rfl
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h1,
    Matrix.vecMul_one]

end Herm

section Alg

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {n : ℕ}

theorem aeval_eq_sum_fin {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (p : R[X])
    (hp : p.degree < n) : aeval x p = ∑ i : Fin n, p.coeff i • x ^ (i : ℕ) := by
  by_cases h0 : p = 0
  · simp [h0]
  rw [aeval_eq_sum_range' ((natDegree_lt_iff_degree_lt h0).mpr hp) x,
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i • x ^ i)]

variable {u : B.A} {Q' : K.E[X]}

theorem exists_aeval_lt (hQm : Q'.Monic) (hdeg : Q'.natDegree = n)
    (hadj : Algebra.adjoin K.E {u} = ⊤) (hroot : aeval u Q' = 0) (y : B.A) :
    ∃ p : K.E[X], p.degree < n ∧ aeval u p = y := by
  have hy : y ∈ Algebra.adjoin K.E {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  refine ⟨p %ₘ Q', ?_, aeval_modByMonic_eq_self_of_root hroot⟩
  calc (p %ₘ Q').degree < Q'.degree := degree_modByMonic_lt p hQm
    _ = n := by rw [degree_eq_natDegree hQm.ne_zero, hdeg]

theorem span_pow (hQm : Q'.Monic) (hdeg : Q'.natDegree = n)
    (hadj : Algebra.adjoin K.E {u} = ⊤) (hroot : aeval u Q' = 0) :
    ⊤ ≤ Submodule.span K.E (Set.range fun i : Fin n => u ^ (i : ℕ)) := by
  intro y _
  obtain ⟨p, hp, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot y
  rw [aeval_eq_sum_fin u p hp]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem dvd_of_aeval_eq_zero (hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)))
    (hQm : Q'.Monic) (hdeg : Q'.natDegree = n) (hroot : aeval u Q' = 0) (p : K.E[X])
    (hp : aeval u p = 0) : Q' ∣ p := by
  rw [← modByMonic_eq_zero_iff_dvd hQm]
  have hr : (p %ₘ Q').degree < n :=
    (degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])
  have h0 : ∑ i : Fin n, (p %ₘ Q').coeff i • u ^ (i : ℕ) = 0 := by
    rw [← aeval_eq_sum_fin u _ hr, aeval_modByMonic_eq_self_of_root hroot, hp]
  have hc := Fintype.linearIndependent_iff.mp hli _ h0
  ext k
  rw [coeff_zero]
  by_cases hk : k < n
  · exact hc ⟨k, hk⟩
  · exact coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast not_lt.mp hk))

theorem isReduced_of (hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)))
    (hQm : Q'.Monic) (hdeg : Q'.natDegree = n) (hadj : Algebra.adjoin K.E {u} = ⊤)
    (hroot : aeval u Q' = 0) (hsep : Q'.Separable) : IsReduced B.A := by
  refine ⟨fun a ⟨k, hk⟩ => ?_⟩
  obtain ⟨p, -, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot a
  have hd : Q' ∣ p ^ k := dvd_of_aeval_eq_zero hli hQm hdeg hroot (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, rfl⟩ := hsep.squarefree.isRadical k p hd
  simp [hroot]

end Alg

end GlobalTheory.KapLat.ExModel

namespace GlobalTheory.KapLat.ExModel

theorem exists_isModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ)
    (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ : GLw n w, γ ∈ UL n w → γ.val.charpoly = Q → ∃ x : B.A, B.σ x = x ∧ IsUnit x ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hsplit K e hB n Q B u hsep hF γ hγU hQ
  obtain ⟨hadj, hroot, hrank, huσ⟩ := hF
  subst hQ
  have hU : cT (cj w) γ.val * 1 * γ.val = 1 := by
    have h := hγU
    simp only [UL, hsplit, if_false] at h
    exact h
  set Q' : K.E[X] := (γ.val.charpoly).map e.symm.toRingHom with hQ'
  have hQm : Q'.Monic := (charpoly_monic _).map _
  have hdeg : Q'.natDegree = n := by
    rw [hQ', natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hrank' : Module.finrank K.E B.A = n := by
    rw [hrank, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsep' : Q'.Separable := hsep.map
  have hspan := span_pow hQm hdeg hadj hroot
  have hli : LinearIndependent K.E (fun i : Fin n => u ^ (i : ℕ)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp [hrank'])
  let bA : Module.Basis (Fin n) K.E B.A := Module.Basis.mk hli hspan
  have hbA : ∀ i, bA i = u ^ (i : ℕ) := fun i => Module.Basis.mk_apply hli hspan i

  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field γ.val hsep
  have hliV : LinearIndependent (w.adicCompletion E) (fun j : Fin n => (γ.val ^ (j : ℕ)) *ᵥ v) := by
    have := Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv))
    convert this using 1
    funext j i
    rfl
  let bV : Module.Basis (Fin n) (w.adicCompletion E) (Fin n → w.adicCompletion E) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hliV (by simp)
  have hbV : ∀ j, bV j = (γ.val ^ (j : ℕ)) *ᵥ v := fun j => by simp [bV]
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    bA.equivFun.toAddEquiv.trans
      ((AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv).trans bV.equivFun.symm.toAddEquiv)
  have hψ : ∀ y, ψ y = bV.equivFun.symm (fun i => e (bA.equivFun y i)) := fun y => rfl
  have hψs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y := by
    intro c y
    rw [hψ, hψ, ← map_smul]
    congr 1
    funext i
    simp

  have hP1 : ∀ p : K.E[X], p.degree < n → ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v := by
    intro p hp
    have h1 : aeval u p = bA.equivFun.symm (fun i => p.coeff i) := by
      rw [aeval_eq_sum_fin u p hp, Module.Basis.equivFun_symm_apply]
      simp [hbA]
    have hp' : (p.map e.toRingHom).degree < n := (degree_map_le).trans_lt hp
    rw [hψ, h1, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_symm_apply,
      aeval_eq_sum_fin γ.val _ hp', Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbV, coeff_map, Matrix.smul_mulVec]
    rfl
  have hmapQ : Q'.map e.toRingHom = γ.val.charpoly := by
    ext i; simp [hQ']
  have hP2 : ∀ p : K.E[X], ψ (aeval u p) = aeval γ.val (p.map e.toRingHom) *ᵥ v := by
    intro p
    have hr : (p %ₘ Q').degree < n :=
      (degree_modByMonic_lt p hQm).trans_eq (by rw [degree_eq_natDegree hQm.ne_zero, hdeg])
    rw [← aeval_modByMonic_eq_self_of_root hroot, hP1 _ hr, map_modByMonic _ hQm, hmapQ,
      aeval_modByMonic_eq_self_of_root (aeval_self_charpoly γ.val)]
  have hψ1 : ψ 1 = v := by
    simpa using hP2 1
  have hmul : ∀ y, ψ (u * y) = γ.val *ᵥ ψ y := by
    intro y
    obtain ⟨p, -, rfl⟩ := exists_aeval_lt hQm hdeg hadj hroot y
    have : u * aeval u p = aeval u (X * p) := by rw [map_mul, aeval_X]
    rw [this, hP2, hP2, Polynomial.map_mul, map_X, map_mul, aeval_X, Matrix.mulVec_mulVec]

  have hadjP : ∀ a y z, stdH w (ψ (a * y)) (ψ z) = stdH w (ψ y) (ψ (B.σ a * z)) := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := hadj ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      intro y z
      have h1 : ψ z = γ.val *ᵥ ψ (B.σ u * z) := by rw [← hmul, ← mul_assoc, huσ, one_mul]
      rw [hmul, h1, stdH_unitary w γ hU]
    | algebraMap r =>
      intro y z
      rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, hψs, hψs, stdH_smul_left, stdH_smul_right,
        hB.1, cj_cj w hB]
    | add a b _ _ ha hb =>
      intro y z
      rw [add_mul, map_add ψ, stdH_add_left, ha, hb, map_add B.σ, add_mul, map_add ψ, stdH_add_right]
    | mul a b _ _ ha hb =>
      intro y z
      rw [mul_assoc, ha, hb, map_mul B.σ]
      congr 2
      ring

  let lam : B.A →ₗ[K.E] K.E :=
    { toFun := fun a => e.symm (stdH w (ψ a) v)
      map_add' := by intro a b; rw [map_add (f := _), stdH_add_left, map_add (f := _)]
      map_smul' := by
        intro r a
        rw [hψs, stdH_smul_left, map_mul, RingEquiv.symm_apply_apply]
        rfl }
  haveI := isReduced_of hli hQm hdeg hadj hroot hsep'
  have hnd : ∀ a : B.A, (∀ y, Algebra.trace K.E B.A (a * y) = 0) → a = 0 := fun a ha =>
    GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero a ha
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    intro a b hab
    rw [← sub_eq_zero]
    apply hnd
    intro y
    have := LinearMap.congr_fun hab y
    simp only [Algebra.traceForm_apply] at this
    rw [sub_mul, map_sub, this, sub_self]
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  obtain ⟨x, hx⟩ := hsurj lam
  have hxa : ∀ a, Algebra.trace K.E B.A (x * a) = e.symm (stdH w (ψ a) v) := fun a => by
    have := LinearMap.congr_fun hx a
    simpa [Algebra.traceForm_apply, lam] using this
  have hform : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z
    have h1 := hadjP (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hψ1, GlobalTheory.UnitLemma.InvAlg.herm, show x * y * B.σ z = x * (B.σ z * y) by ring, hxa,
      RingEquiv.apply_symm_apply]
  have htr : ∀ a, Algebra.trace K.E B.A (x * B.σ a) = K.c (Algebra.trace K.E B.A (x * a)) := by
    intro a
    apply e.injective
    have e1 : B.herm x 1 a = Algebra.trace K.E B.A (x * B.σ a) := by
      simp [GlobalTheory.UnitLemma.InvAlg.herm]
    have e2 : B.herm x a 1 = Algebra.trace K.E B.A (x * a) := by
      simp [GlobalTheory.UnitLemma.InvAlg.herm]
    rw [← e1, ← e2, ← hform, hB.1, ← hform]
    exact stdH_symm w hB _ _
  have htrσ : ∀ a : B.A, Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
    intro a
    have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext r; simp [B.σ_alg]) a
    rw [h, RingEquiv.apply_symm_apply]
  have hσx : B.σ x = x := by
    rw [← sub_eq_zero]
    apply hnd
    intro a
    rw [sub_mul, map_sub, sub_eq_zero]
    calc Algebra.trace K.E B.A (B.σ x * a) = Algebra.trace K.E B.A (B.σ (x * B.σ a)) := by
          rw [map_mul B.σ, B.σ_σ]
      _ = K.c (Algebra.trace K.E B.A (x * B.σ a)) := htrσ _
      _ = K.c (K.c (Algebra.trace K.E B.A (x * a))) := by rw [htr]
      _ = Algebra.trace K.E B.A (x * a) := K.c_c _
  have hxinj : Function.Injective (LinearMap.mulLeft K.E x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    simp only [LinearMap.mulLeft_apply] at ha
    have h0 : ψ a = 0 := by
      funext k
      obtain ⟨z, hz⟩ := ψ.surjective (Pi.single k 1)
      have := hform a z
      rw [hz, stdH_single] at this
      rw [this, GlobalTheory.UnitLemma.InvAlg.herm, ha, zero_mul, map_zero, map_zero]
      rfl
    exact ψ.injective (h0.trans (map_zero ψ).symm)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hxinj) 1
  exact ⟨x, hσx, ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩, ψ, hψs, hmul, hform⟩

end GlobalTheory.KapLat.ExModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplitStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A), Q.Separable → Fits w e B Q u → ∀ γ : GLw n w, γ ∈ UL n w → γ.val.charpoly = Q → ∃ x : B.A, B.σ x = x ∧ IsUnit x ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.ExModel.exists_isModel | exact GlobalTheory.KapLat.ExModel.exists_isModel | (intros; apply GlobalTheory.KapLat.ExModel.exists_isModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModel
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem models_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  intro E _ _ _ w hw K e B u x n γ γ' hγ hγ'
  obtain ⟨ψ, hψl, hψu, hψh⟩ := hγ
  obtain ⟨ψ', hψ'l, hψ'u, hψ'h⟩ := hγ'
  let f : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ (ψ'.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψ'l, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψl] }
  let g : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ' (ψ.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ a = v := ⟨ψ.symm v, ψ.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψl, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψ'l] }
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  let y : GLw n w := ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g,
    by rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_id]⟩
  have hy : ∀ v, (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ v = f v := fun v =>
    LinearMap.toMatrix'_mulVec f v

  have hinv : ∀ v v', stdH w (f v) (f v') = stdH w v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ' b = v' := ⟨ψ'.symm v', ψ'.apply_symm_apply v'⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
    rw [hψh, hψ'h]
  refine ⟨y, ?_, ?_⟩
  · unfold UL
    rw [if_neg hw]
    change Formalism.UG.cT (cj w) (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1
    set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hM
    have key : Mᵀ * M.map (cj w) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 := hinv (Pi.single i 1) (Pi.single j 1)
      rw [← hy, ← hy] at h1
      simp only [stdH, Matrix.mulVec_single_one] at h1
      have h2 : (if i = j then (1 : w.adicCompletion E) else 0) = ∑ k, M k i * cj w (M k j) := by
        simpa [Pi.single_apply, eq_comm] using h1
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact h2.symm
    have key2 := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at key2
    rw [Matrix.mul_one]
    exact key2
  ·
    have hc : (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * γ'.val = γ.val * y := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hψ'u, hy, hy]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
      rw [hψu]
    have hc' : y * γ' = γ * y := Units.ext hc
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]

end GlobalTheory.KapLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModelStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  first | exact @GlobalTheory.KapLat.models_conj | exact GlobalTheory.KapLat.models_conj | (intros; apply GlobalTheory.KapLat.models_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPair
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add (f := _), map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add (f := _), map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPairStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  first | exact @GlobalTheory.KapLat.fits_prod | exact GlobalTheory.KapLat.fits_prod | (intros; apply GlobalTheory.KapLat.fits_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCount
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem model_mul_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w), IsModel w e B u x γ → ∀ c : B.Aˣ, IsModel w e B u (x * ((c : B.A) * B.σ (c : B.A))) γ := by
  intro E _ _ _ w K e B u x n γ hM c
  obtain ⟨ψ, h1, h2, h3⟩ := hM
  let φ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    { toFun := fun y => ψ ((c : B.A) * y)
      invFun := fun v => ((c⁻¹ : B.Aˣ) : B.A) * ψ.symm v
      left_inv := fun y => by simp [← mul_assoc]
      right_inv := fun v => by simp [← mul_assoc]
      map_add' := fun y z => by simp [mul_add] }
  refine ⟨φ, fun a y => ?_, fun y => ?_, fun y z => ?_⟩
  · show ψ ((c : B.A) * (a • y)) = e a • ψ ((c : B.A) * y)
    rw [mul_smul_comm, h1]
  · show ψ ((c : B.A) * (u * y)) = γ.val *ᵥ ψ ((c : B.A) * y)
    rw [show (c : B.A) * (u * y) = u * ((c : B.A) * y) by ring, h2]
  · show stdH w (ψ ((c : B.A) * y)) (ψ ((c : B.A) * z)) = _
    rw [h3]
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 2
    rw [map_mul]
    ring

theorem kapOrb_eq_kapSum_of_fits {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w)
    {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hBr : Bridge w K e) {k : ℕ} {t : K.O} (ht : K.Small t)
    (htk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) {n : ℕ} {Q₁ Q₂ : (w.adicCompletion E)[X]}
    {B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K} {u₁ : B₁.A} {u₂ : B₂.A} (hsep : (Q₁ * Q₂).Separable) (hmon : (Q₁ * Q₂).Monic)
    (hdeg : (Q₁ * Q₂).natDegree = n) (hF₁ : Fits w e B₁ Q₁ u₁) (hF₂ : Fits w e B₂ Q₂ u₂)
    (hg : 1 + algebraMap K.O (B₁.prod B₂).A t * (B₁.prod B₂).g = (u₁, u₂)) :
    kapOrb n w Q₁ Q₂ (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) =
      ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  have hcl : Equivalence (fun x y : {x : (B₁.prod B₂).Aˣ // (B₁.prod B₂).σ (x : (B₁.prod B₂).A) = x} =>
      ∃ u : (B₁.prod B₂).Aˣ, (y.1 : (B₁.prod B₂).A) = x.1 * (u * (B₁.prod B₂).σ (u : (B₁.prod B₂).A))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one, one_mul]
      rw [hu]
      calc (x.1 : (B₁.prod B₂).A) = x.1 * (((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) := by rw [h1, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩
  have hconj : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨g, rfl⟩; exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩; exact ⟨g * h, by simp [mul_assoc]⟩
  have hF := GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair E w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂
  unfold kapOrb clSum GlobalTheory.UnitLemma.InvAlg.kapSum
  rw [cast_finsum]
  set S' : Set (TwCl (MonoidHom.id (UL n w))) := {c | c.rep.1.val.charpoly = Q₁ * Q₂} with hS'
  have hex : ∀ c : TwCl (MonoidHom.id (UL n w)), c ∈ S' → ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧
      IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 := fun c hc =>
    GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) (u₁, u₂) hsep hF c.rep.1 c.rep.2 hc
  let Φ : TwCl (MonoidHom.id (UL n w)) → (B₁.prod B₂).Cl := fun c =>
    if h : ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧ IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 then
      Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ else Quot.mk _ ⟨1, by simp⟩
  have hrep : ∀ c ∈ S', IsModel w e (B₁.prod B₂) (u₁, u₂) (GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c)) c.rep.1 := by
    intro c hc
    have h := hex c hc
    have hΦ : Φ c = Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ := dif_pos h
    have hq := Quot.eqvGen_exact ((Quot.out_eq (Φ c)).trans hΦ)
    obtain ⟨v, hv⟩ := hcl.symm (hcl.eqvGen_iff.1 hq)
    have hr : GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c) = h.choose * ((v : (B₁.prod B₂).A) * (B₁.prod B₂).σ (v : (B₁.prod B₂).A)) := by
      unfold GlobalTheory.UnitLemma.InvAlg.Cl.rep
      rw [hv]
      simp
    rw [hr]
    exact model_mul_norm E w K e (B₁.prod B₂) _ _ n _ h.choose_spec.2.2 v
  let G : (B₁.prod B₂).Cl → ℂ := fun κ =>
    ((K.eta (B₁.gramDet (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ).1) * (B₁.prod B₂).N κ.rep : ℚ) : ℂ)
  have hterm : ∀ c ∈ S', kapSign n w Q₁ c.rep.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) c.rep
      (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = G (Φ c) := by
    intro c hc
    have hm := hrep c hc
    have h7 := GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count E w hw K e hBr k t ht htk n (Q₁ * Q₂) (B₁.prod B₂) _ _ hsep hF hg.symm c.rep.1 c.rep.2 hm
    simp only [Subtype.coe_eta] at h7
    rw [GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet E w hw K e hBr n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ _ _ hm, h7]
    simp [G]
  have hinj : Set.InjOn Φ S' := by
    intro c₁ hc₁ c₂ hc₂ h12
    have m₁ := hrep c₁ hc₁
    have m₂ := hrep c₂ hc₂
    rw [h12] at m₁
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel E w hw K e (B₁.prod B₂) _ _ n _ _ m₁ m₂
    rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
    exact Quot.sound ⟨⟨y, hy⟩, Subtype.ext (by simpa [TwCl.rep] using hyc)⟩
  have hsupp : Function.support G ⊆ Φ '' S' := by
    intro κ hκ
    have hN : (B₁.prod B₂).N κ.rep ≠ 0 := by
      intro h0; apply hκ; simp [G, h0]
    have hfix : (B₁.prod B₂).σ (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) = GlobalTheory.UnitLemma.InvAlg.Cl.rep κ := (Quot.out κ).2
    have hunit : IsUnit (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) := (Quot.out κ).1.isUnit
    obtain ⟨γ, hγ, hmγ⟩ := GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) _ _ hF hdeg hfix hunit hN
    have hcp : γ.val.charpoly = Q₁ * Q₂ := GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel E w K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ γ hmon hF hmγ
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ ⟨γ, hγ⟩
    obtain ⟨g, hg'⟩ := hconj.symm
      (hconj.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq c)))
    have hcrep : c.rep.1 = g.1⁻¹ * γ * g.1 := by
      have := congrArg Subtype.val hg'
      simpa [TwCl.rep] using this
    have hc : c ∈ S' := by
      show c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcrep, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hcp]
    refine ⟨c, hc, ?_⟩
    have m := hrep c hc
    rw [hcrep] at m
    obtain ⟨v, hv⟩ := GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm E w hw K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ _ hsep hF γ g.1 g.2 hmγ m
    exact (Quot.out_eq (Φ c)).symm.trans ((Quot.sound (hcl.symm ⟨v, hv⟩)).trans (Quot.out_eq κ))
  calc _ = ∑ᶠ c, S'.indicator (fun c => G (Φ c)) c := finsum_congr fun c => by
          by_cases hc : c ∈ S'
          · rw [Set.indicator_of_mem hc, ← hterm c hc]
            exact if_pos hc
          · rw [Set.indicator_of_notMem hc]
            exact if_neg hc
    _ = ∑ᶠ c ∈ S', G (Φ c) := (finsum_mem_def _ _).symm
    _ = ∑ᶠ κ ∈ Φ '' S', G κ := (finsum_mem_image hinj).symm
    _ = ∑ᶠ κ, G κ := by
      exact (finsum_mem_inter_support_eq G (Φ '' S') Set.univ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])).trans
        (finsum_mem_univ G)

theorem kapOrb_congruence_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he1 he2 he3 he4 k t ht htk n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
    hadj₁ hae₁ hfr₁ hu₁ hadj₂ hae₂ hfr₂ hu₂
  exact kapOrb_eq_kapSum_of_fits hw ⟨he1, he2, he3, he4⟩ ht htk hsep (hm₁.mul hm₂)
    (by rw [hm₁.natDegree_mul hm₂, hd₁, hd₂, hab]) ⟨hadj₁, hae₁, hfr₁, hu₁⟩ ⟨hadj₂, hae₂, hfr₂, hu₂⟩ (Prod.ext rfl rfl)

end GlobalTheory.KapLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCountStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | exact GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | (intros; apply GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum <;> assumption)
end
