module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsNorm
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsNormP

theorem thetaGL_val' {k : Type} [CommRing k] (n : ℕ) (c : k →+* k) (g : GL (Fin n) k) :
    (thetaGL n c g).val = GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := rfl

theorem phi_mul_transpose_eq_one {k : Type} [CommRing k] (n : ℕ) : GlobalTheory.Tw.Phi n k * (GlobalTheory.Tw.Phi n k)ᵀ = 1 :=
  GlobalTheory.GramTwistNorm.phi_mul_transpose n

theorem units_map_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : (Units.map ρ.toMonoidHom t).val = ρ t := rfl

theorem units_map_inv_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : ((Units.map ρ.toMonoidHom t)⁻¹).val = ρ (↑t⁻¹ : B) := by
  rw [← map_inv]; rfl

theorem delta_theta {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type} [CommRing B]
    {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (t : Bˣ) :
    δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val = ρ (↑t⁻¹ : B) * δ.val := by
  rw [thetaGL_val', units_map_inv_val]
  calc δ.val * (GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ)
      = (δ.val * GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ) * (GlobalTheory.Tw.Phi n k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = ρ (↑t⁻¹ : B) * (δ.val * GlobalTheory.Tw.Phi n k) * (GlobalTheory.Tw.Phi n k)ᵀ := by rw [← hF.adj]
    _ = ρ (↑t⁻¹ : B) * δ.val := by rw [Matrix.mul_assoc, Matrix.mul_assoc, phi_mul_transpose_eq_one, Matrix.mul_one]

end PositivityTheory.Rg.BcB.G3.ClsNormP

namespace PositivityTheory.Rg.BcB.G3

theorem clsNorm_pf : ClsNorm := by
  intro k _ _ n c _ δ s _ _ B _ d ρ hF t
  apply Units.ext
  simp only [pt, map_mul, Units.val_mul]
  rw [ClsNormP.units_map_val]
  have h := ClsNormP.delta_theta hF t
  have h1 : ρ (t : B) * ρ (↑t⁻¹ : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  calc ρ (t : B) * δ.val * ((thetaGL n c (Units.map ρ.toMonoidHom t)).val * (thetaGL n c δ).val)
      = ρ (t : B) * (δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val) * (thetaGL n c δ).val := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * (thetaGL n c δ).val := by
        rw [h, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end PositivityTheory.Rg.BcB.G3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PQuadField
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.QuadFieldP

open QuadraticAlgebra

theorem not_sq_of_real (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E)
    (d : maximalRealSubfield E) (hs0 : s ≠ 0) (hs : IsCMField.complexConj E s = -s)
    (hd : algebraMap (maximalRealSubfield E) E d = s ^ 2) (K : Type) [Field K]
    [Algebra (maximalRealSubfield E) K] (τ : K →+* ℂ) (t : ℂ) (ht : starRingEnd ℂ t = t) :
    t ^ 2 ≠ τ (algebraMap (maximalRealSubfield E) K d) := by
  intro h
  let _ := (τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra
  let φ : E →ₐ[maximalRealSubfield E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← map_pow, ← hd, φ.commutes]; rfl
  have hu : starRingEnd ℂ (φ s) = - φ s := by
    have h' := IsCMField.complexEmbedding_complexConj E φ.toRingHom s
    simpa [hs] using h'.symm
  have hu0 : φ s ≠ 0 := by
    intro h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))
  rw [← h1] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by rw [← h2]; exact ht
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by
      have := congrArg Neg.neg ht
      rw [h2, map_neg, neg_neg, neg_neg] at this
      exact this
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3

end PositivityTheory.Rg.BcB.G3.QuadFieldP

namespace PositivityTheory.Rg.BcB.G3

open QuadFieldP QuadraticAlgebra in
theorem quadField_pf : QuadField := by
  intro E _ _ _ s d hs0 hs hd K _ _ _ hKr
  refine ⟨?_, ?_⟩
  · rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← (letI : Module.Free (maximalRealSubfield E) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) K), mul_comm]
  generalize hδ : algebraMap (maximalRealSubfield E) K d = δ
  have hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ := by
    intro τ t ht
    rw [← hδ]
    exact not_sq_of_real E s d hs0 hs hd K τ t ht
  have hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r := by
    intro r hr
    let τ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hre := ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)
    refine hkey τ (τ r) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [← map_pow, hr, zero_mul, add_zero]
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := ⟨hns⟩
  have hq := GlobalTheory.QuadSymbol.Model.isQuadratic δ
  have hnf := GlobalTheory.QuadSymbol.Model.numberField δ
  have : FiniteDimensional K (QuadraticAlgebra K δ 0) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)
  refine ⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩
  · refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro hre
    let e := w.embedding
    refine hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]; simp
  · intro x
    rw [GlobalTheory.QuadSymbol.mem_globalNorms_iff]
    have key := GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff] at key
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at key
    rw [← key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
    · rintro ⟨z, hz⟩
      refine ⟨Algebra.TensorProduct.lid K _ z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
  · intro u x
    exact GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ

end PositivityTheory.Rg.BcB.G3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PBaseFrame
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.BaseFrameP

theorem phi_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map p = GlobalTheory.Tw.Phi n S := by
  ext i k
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

end PositivityTheory.Rg.BcB.G3.BaseFrameP

open PositivityTheory.Rg.BcB.G3.BaseFrameP in
theorem PositivityTheory.Rg.BcB.G3.baseFrame_pf : BaseFrame := by
  intro F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr
  have hps0 : p s ≠ 0 := (map_ne_zero p).2 hs0
  have hcps : c' (p s) = - p s := by rw [hc, hcs, map_neg]
  have indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have h2 := congrArg c' h
    simp only [map_add (f := _), map_mul, hcj, hcps, map_zero] at h2
    have hu : j u = 0 := by
      have h3 : (2 : E') * j u = 0 := by linear_combination h + h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have hv : j v = 0 := by
      rw [hu, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hps0
    exact ⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩
  have indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h1 := congrArg p h
    simp only [map_add (f := _), map_mul, ← hj, map_zero] at h1
    obtain ⟨h2, h3⟩ := indep' _ _ h1
    exact ⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    apply indepE a b
    simp only [Algebra.smul_def] at h
    linear_combination h
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspE z
    have h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨1, rfl⟩
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)
    convert h3 using 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  obtain ⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s :=
    ⟨Module.Basis.mk hli hsp, by simp, by simp⟩
  have hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1) := by
    intro e
    conv_lhs => rw [← bE.sum_repr e]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]
    ring
  have hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E) := hfr.sq
  have hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ := hfr.adj
  have hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a := hfr.comm

  obtain ⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E',
      ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by
    let _ : Algebra F E' := (p.comp (algebraMap F E)).toAlgebra
    let pA : E →ₐ[F] E' := { p with commutes' := fun _ => rfl }
    let fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E' :=
      { (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with
        commutes' := fun x => by
          show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _
          rw [hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
          rfl }
    let gA : B →ₐ[F] Matrix (Fin n) (Fin n) E' := pA.mapMatrix.comp ρ
    have hcomm : ∀ x y, Commute (fA x) (gA y) := fun x y => by
      show Commute (Matrix.scalar (Fin n) (j x)) _
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    refine ⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
    show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p := by
    intro a; rw [hρt, map_one, one_smul]
  have hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E') := by
    intro u; rw [hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]
  have hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E') := by
    rw [hρ1, hsq]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.one_apply]
  have hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val =
      (δ * thetaGL n c δ).val.map p := by
    rw [← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]
    rfl
  refine ⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F),
        ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2 :=
      ⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2
         map_add' := fun a b => by funext i; simp [map_add (f := _)]
         map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩
    have hφ : Function.Injective φ := by
      refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
      have h1 : ρ b = 0 := by
        ext i k
        have h2 : bE.repr (ρ b i k) = 0 := by
          ext t
          have := congrFun hb (i, k, t)
          rw [hφdef] at this
          simpa using this
        simpa using h2
      exact (injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1
    have hL : Function.Injective (φ.lTensor F') := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
    have hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k =
        j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) +
        p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1)) := by
      intro X i k
      induction X using TensorProduct.induction_on with
      | zero => simp
      | tmul x b =>
        rw [hρt]
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        conv_lhs => rw [hdec (ρ b i k)]
        simp only [map_add (f := _), map_mul, ← hj]
        ring
      | add X Y hX hY =>
        simp only [map_add (f := _), Matrix.add_apply, hX, hY, Pi.add_apply]
        ring
    refine (injective_iff_map_eq_zero ρ').2 fun X hX => ?_
    have hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0 := by
      funext ⟨i, k, t⟩
      have h := hkey X i k
      rw [hX, Matrix.zero_apply] at h
      obtain ⟨h0, h1⟩ := indep' _ _ h.symm
      have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have h0 : φ.lTensor F' X = 0 :=
      (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)
    exact hL (by rw [h0, map_zero])
  ·
    intro X
    rw [show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt]
      have e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p) := by
        ext i k; simp [hcj, hc]
      rw [e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]
  ·
    intro X
    rw [hN']
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, mul_add, hX, hY]
  ·
    intro x hx
    rw [hN'] at hx
    have hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hsep.map
    obtain ⟨q, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm
    have hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) →
        (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b := by
      rintro y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [map_add (f := _), map_add (f := _), smul_add]; abel⟩
    have hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b := ⟨0, 0, by simp⟩
    have hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) →
        ∃ a b, e • y = ρ' a + p s • ρ' b := by
      rintro e y ⟨a, b, rfl⟩
      obtain ⟨u, v, rfl⟩ := hspE' e
      refine ⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b),
        (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩
      simp only [map_add (f := _), map_mul, hρu, hD, Matrix.smul_mul, one_mul]
      module
    have hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b := by
      intro k
      obtain ⟨a, b, hab⟩ := hfr.span ((δ * thetaGL n c δ).val ^ k)
        (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm
      refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩
      have hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p :=
        (map_pow p.mapMatrix _ k).symm
      rw [hpw, hρ1, hρ1, hab]
      ext i k
      simp
    rw [aeval_eq_sum_range]
    exact Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0
      (fun i _ => hTsmul _ _ (hTpow i))
end
end
