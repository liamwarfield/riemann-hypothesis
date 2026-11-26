module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperator
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem qdet_restrict {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ S) (Y : Fin n → Fin n → Module.End ℂ V)
    (h : ∀ i j (x : S), (X i j x : V) = Y i j x) (w : ℂ) (x : S) :
    (Formalism.REAL.qdet X w x : V) = Formalism.REAL.qdet Y w x := by
  let P : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ V) :=
    { carrier := {z | ∀ x : S, (z.1 x : V) = z.2 x}
      mul_mem' := fun {p q} hp hq x => by
        show ((p.1 (q.1 x) : S) : V) = p.2 (q.2 x)
        rw [hp, hq]
      add_mem' := fun {p q} hp hq x => by
        show ((p.1 x + q.1 x : S) : V) = p.2 x + q.2 x
        rw [Submodule.coe_add, hp, hq]
      algebraMap_mem' := fun c x => rfl }
  let Z : Fin n → Fin n → Module.End ℂ S × Module.End ℂ V := fun i j => (X i j, Y i j)
  have hZ : Formalism.REAL.qdet Z w ∈ P := by
    refine P.sum_mem fun σ _ => P.mul_mem (intCast_mem P _) (P.list_prod_mem fun y hy => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
    refine P.add_mem ?_ (fun x => h _ _ x)
    split_ifs
    · exact P.algebraMap_mem _
    · exact P.zero_mem
  have h1 : (Formalism.REAL.qdet Z w).1 = Formalism.REAL.qdet X w :=
    map_qdet (AlgHom.fst ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  have h2 : (Formalism.REAL.qdet Z w).2 = Formalism.REAL.qdet Y w :=
    map_qdet (AlgHom.snd ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  rw [← h1, ← h2]
  exact hZ x

theorem qdet_EopV_val : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (u : ℂ) (φ : π.V),
    (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  intro E _ _ _ a π τ u φ
  exact qdet_restrict π.V (EopV π τ) (Eop τ) (fun i j x => GlobalTheory.T.lie_operator_vector_eq E a π τ i j x) _ φ

end GlobalTheory.CompanionTheory.Clozel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperatorStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_capelli_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (u : ℂ) (φ : π.V), (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | exact GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | (intros; apply GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem glRel_EopV : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  intro E _ _ _ a π τ i j k l
  have key := GlobalTheory.CompanionTheory.ClozelPurity.EopV_val E a π τ
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end GlobalTheory.CompanionTheory.Clozel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelationsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_gl_relations : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.glRel_EopV | exact GlobalTheory.CompanionTheory.Clozel.glRel_EopV | (intros; apply GlobalTheory.CompanionTheory.Clozel.glRel_EopV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

theorem op_lie_single_neg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (i j : Fin a) (x : Cinf E) :
    π.op (.lie (toL (Matrix.single i j (-x)))) = -π.op (.lie (toL (Matrix.single i j x))) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  change lieS E a i j (-x) φ.1 = -(lieS E a i j x φ.1)
  rw [map_neg]
  rfl

theorem EopV_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V),
    B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  intro E _ _ _ a π B hB τ i j φ ψ
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  have s1 := hB.1 (toL (Matrix.single i j (atEmb τ 1))) φ ψ
  have s2 := hB.1 (toL (Matrix.single i j (atEmb τ Complex.I))) φ ψ
  simp only [EopV, e1, e2, op_lie_single_neg, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    map_smul, map_sub, map_neg, map_smulₛₗ, c2, Complex.conj_I, smul_eq_mul, s1, s2, RingHom.id_apply, smul_neg,
    sub_neg_eq_add, map_add]
  ring

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkewStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_hermitian_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V), B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | exact GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.Clozel

private theorem neg_one_pow_card_mul_prod_neg_add_conj (u : ℂ) (s : Multiset ℂ) :
    (-1 : ℂ) ^ Multiset.card s * (s.map fun w => -u + (starRingEnd ℂ) w).prod =
      (s.map fun w => u - (starRingEnd ℂ) w).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, ← ih, pow_succ]
    ring

theorem multiset_eq_map_neg_conj_of_polyEq :
    ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n →
      (∀ u : ℂ, (m.map (u + ·)).prod =
        (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) →
      m' = m.map fun z => -(starRingEnd ℂ) z := by
  intro n m m' _ hm' h
  have key : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map fun w => u - (starRingEnd ℂ) w).prod := by
    intro u
    have hc : ((starRingEnd ℂ) ∘ fun w => -(starRingEnd ℂ) u + w) =
        fun w => -u + (starRingEnd ℂ) w := by
      funext w
      simp
    rw [h u, map_mul, map_pow, map_neg, map_one, map_multiset_prod, Multiset.map_map, hc, ← hm',
      neg_one_pow_card_mul_prod_neg_add_conj]
  have hpoly : ((m.map fun z => -z).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((m'.map (starRingEnd ℂ)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.funext
    intro u
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def] using key u
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hinv : (m'.map (starRingEnd ℂ)).map (starRingEnd ℂ) = m' := by
    simp [Multiset.map_map, Function.comp_def]
  rw [← hinv, ← hroots, Multiset.map_map]
  exact Multiset.map_congr rfl fun z _ => by simp

end GlobalTheory.CompanionTheory.Clozel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProdStatement
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_conjugate_neg_of_prod : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | exact GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | (intros; apply GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine GlobalTheory.T.multiset_conjugate_neg_of_prod a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [GlobalTheory.T.quantum_det_capelli_operator E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := GlobalTheory.T.quantum_det_adjoint_form π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (GlobalTheory.T.lie_operator_gl_relations E a π _) (GlobalTheory.T.lie_operator_hermitian_skew E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add (f := _), map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugateStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | (intros; apply GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_moved (h : IsCMExt F E σ) : ∃ θ : E, σ θ ≠ θ := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc' := h.2.1
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hc y] at this
  simpa using this.symm

theorem im_ne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) (τ : E →+* ℂ) : (τ θ).im ≠ 0 := by
  intro h0
  apply hθ
  apply τ.injective
  rw [h.2.2.2]
  exact Complex.conj_eq_iff_im.2 h0

theorem linInd_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : s • (1 : E) + t • σ θ = 0 := by
    have := congrArg σ hst
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgHom.commutes, map_one, map_zero] at this ⊢
    exact this
  have h2 : t • (σ θ - θ) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact add_left_cancel (h1.trans hst.symm)
  have ht : t = 0 := by
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hθ
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst

def basisOne (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : Module.Basis (Fin 2) F E :=
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  basisOfLinearIndependentOfCardEqFinrank (linInd_one h hθ) (by rw [h.2.2.1]; simp)

theorem basisOne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 0 = 1 := by
  simp [basisOne]

theorem basisOne_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 1 = θ := by
  simp [basisOne]

end Field

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordHomeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

def planeHomeo {W : Type} (t : W → ℂ) (ht : ∀ w, (t w).im ≠ 0) : (Fin 2 → W → ℝ) ≃ₜ (W → ℂ) where
  toFun f w := (f 0 w : ℂ) + (f 1 w : ℂ) * t w
  invFun g := ![fun w => (g w).re - (g w).im / (t w).im * (t w).re, fun w => (g w).im / (t w).im]
  left_inv f := by
    funext k w
    have := ht w
    fin_cases k
    · simp
      field_simp
      ring
    · simp
      field_simp
  right_inv g := by
    funext w
    have := ht w
    apply Complex.ext
    · simp
    · simp
      field_simp
  continuous_toFun := by
    refine continuous_pi fun w => ?_
    have h0 : Continuous fun f : Fin 2 → W → ℝ => f 0 w := (continuous_apply w).comp (continuous_apply 0)
    have h1 : Continuous fun f : Fin 2 → W → ℝ => f 1 w := (continuous_apply w).comp (continuous_apply 1)
    exact (Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  continuous_invFun := by
    refine continuous_pi fun k => continuous_pi fun w => ?_
    have hr : Continuous fun g : W → ℂ => (g w).re := Complex.continuous_re.comp (continuous_apply w)
    have hi : Continuous fun g : W → ℂ => (g w).im := Complex.continuous_im.comp (continuous_apply w)
    fin_cases k
    · exact hr.sub ((hi.div_const _).mul continuous_const)
    · exact hi.div_const _

end Top

section Map

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_hom (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (hc : ∀ x w, ((e (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = τ w (algebraMap F E x)) :
    ∃ Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ),
      ∀ a x w, Θ (a ⊗ₜ[F] x) w = (e a w : ℂ) * τ w x := by
  letI : Algebra F (InfinitePlace F → ℂ) :=
    (Pi.ringHom fun w => (τ w).comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom fun w =>
        Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ => ℝ) w).comp (e : Ainf F →+* (InfinitePlace F → ℝ)))
      commutes' := fun x => funext fun w => hc x w }
  let fE : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom τ
      commutes' := fun _ => rfl }
  exact ⟨(Algebra.TensorProduct.productMap fA fE).toRingHom, fun a x w => by
    simp [Algebra.TensorProduct.productMap_apply_tmul, fA, fE]
    rfl⟩

end Map

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM in
theorem exists_isCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)),
  (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∃ (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)),
    IsCoord σ e τ Θ := by
  intro F E _ _ _ _ _ σ h ρ e hρ he hx
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨θ, hθ⟩ := exists_moved h
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph
  let b := basisOne h hθ
  let H : (Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → ℂ) :=
    (coordHomeo (Ainf F) b).trans ((Homeomorph.piCongrRight fun _ => eH).trans
      (planeHomeo (fun w => τ w θ) (fun w => im_ne_zero h hθ (τ w))))
  have hH : ∀ y, H y = Θ y := by
    intro y
    have hy : y = (Algebra.TensorProduct.basis (Ainf F) b).repr y 0 ⊗ₜ[F] (1 : E) +
        (Algebra.TensorProduct.basis (Ainf F) b).repr y 1 ⊗ₜ[F] θ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr y]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
        basisOne_zero, basisOne_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp
    funext w
    conv_rhs => rw [hy, map_add (f := _), Pi.add_apply, hΘ, hΘ, map_one, mul_one]
    rfl
  have hbij : Function.Bijective Θ := by
    have : (Θ : Ainf F ⊗[F] E → _) = H := funext fun y => (hH y).symm
    rw [this]
    exact H.bijective
  refine ⟨τ, RingEquiv.ofBijective Θ hbij, ?_, ?_, ?_, ?_⟩
  · have : ((RingEquiv.ofBijective Θ hbij : Ainf F ⊗[F] E ≃+* _) : Ainf F ⊗[F] E → _) = H :=
      funext fun y => (hH y).symm
    rw [this]
    exact H.isHomeomorph
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (Ainf F) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := by simp [sigR]
      rw [this, hΘ, hΘ, h.2.2.2, map_mul, Complex.conj_ofReal]
      rfl
    | add y y' hy hy' => simp only [map_add (f := _), Pi.add_apply, hy, hy']
  · intro x w
    simp only [RingEquiv.ofBijective_apply]
    rw [hΘ, map_one]
    simp
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have h1 : τ w x + conj (τ w x) = ((ρ w (Algebra.trace F E x) : ℝ) : ℂ) := by
        rw [hρ, ← hτ, ← GlobalTheory.GaussMean.OneVec.add_sigma h, map_add (f := _), h.2.2.2]
        rfl
      rw [GlobalTheory.GaussMean.OneVec.trace_tmul, map_mul, Pi.mul_apply, hx, hΘ, map_mul, Complex.conj_ofReal,
        Complex.ofReal_mul, ← h1]
      ring
    | add y y' hy hy' =>
      simp only [map_add (f := _), Pi.add_apply, Complex.ofReal_add, hy, hy']
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinityStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coordinates_exist_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)),
  (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∃ (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)),
    IsCoord σ e τ Θ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.exists_isCoord | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.exists_isCoord | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.exists_isCoord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScaling
noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Dilate

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem gramR_dilate {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : R ⊗[F] E)
    (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J (fun p k => u * X p k) 0 0 = (u * sigR R σ u) * gramR R σ J X 0 0 := by
  simp only [gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem half_trace_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  intro F E _ _ _ _ _ σ hσ M J hJ v u X
  beta_reduce
  have hX := GlobalTheory.CompanionTheory.SW.FibreRatio.gram_entry (Fv F v) hσ hJ X
  set r := algebraMap F (Fv F v) (1 / 2) *
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hr
  have hY : gramR (Fv F v) σ J (fun p k => u * X p k) 0 0 =
      (Algebra.norm (Fv F v) u * r) ⊗ₜ[F] (1 : E) := by
    have hN : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) u) = u * sigR (Fv F v) σ u :=
      GlobalTheory.Doubling.algebraMap_norm_eq hσ u
    rw [gramR_dilate, ← hN, hX,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  rw [hY]
  exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (Fv F v) hσ _

end GlobalTheory.CompanionTheory.AvgFree.Dilate
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScalingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_gram_unit_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate | exact GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate | (intros; apply GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIndex

theorem rStab_index_ne_zero_of_compact : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  intro G _ _ _ θ K K' d f hθ hKc ho hf y
  set W : Subgroup G := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set G) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf K : Subgroup K) : Set K) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf K).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf K ≤ rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k)) := by
    intro k' hk' k
    have hk'W : (k' : G) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : G)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : G) ∈ K' := hk'W.2
    have e : (y * ((k * k' : K) : G))⁻¹ * d * θ (y * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * (((y * (k : G))⁻¹ * d * θ (y * (k : G))) * θ (k' : G)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf _ hl _).1, (hf _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

end GlobalTheory.CompanionTheory.SplitIndex
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZeroStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_index_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | exact GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | (intros; apply GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspDiscreteDecompositionGL
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompact
noncomputable section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspGL

theorem cuspDiscreteDecompositionGL_of_compact
    (hc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f →
      IsCompactOperator (repOp (Rcusp μ) μ f)) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have : BorelSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.borelSpace_GA E a
  have : LocallyCompactSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
  have : T2Space (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
  have : CompleteSpace (L2cusp μ) := GlobalTheory.CuspRep.CuspidalL2GL.completeSpace_L2cusp μ
  have hU := GlobalTheory.CuspRep.CuspidalL2GL.isUnitaryRep_Rcusp μ
  refine GlobalTheory.CuspSpectrum.isDiscreteSum_of_repOp hU μ fun v hv => ?_
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have cc : Continuous fun g => inner ℂ v ((Rcusp μ g) v) := continuous_const.inner (hU.continuous_apply v)
  have h1pos : 0 < (inner ℂ v ((Rcusp μ 1) v)).re := by
    rw [map_one, ContinuousLinearMap.one_apply]
    have h3 : RCLike.re (inner ℂ v v) = ‖v‖ ^ 2 := inner_self_eq_norm_sq v
    have h4 : (inner ℂ v v).re = ‖v‖ ^ 2 := h3
    rw [h4]
    exact pow_pos hpos 2
  have hN : {g | 0 < (inner ℂ v ((Rcusp μ g) v)).re} ∈ 𝓝 (1 : GA E a) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp cc)).mem_nhds h1pos
  obtain ⟨φ, hφc, hφs, hφ0, hφ1, hφN⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GA E a) _ hN
  have hfc : Continuous fun g => (φ g : ℂ) := Complex.continuous_ofReal.comp hφc
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hφs.comp_left Complex.ofReal_zero
  refine ⟨fun g => (φ g : ℂ), hfc, hfs, hc E a μ _ hfc hfs, fun h0 => ?_⟩
  have key := hU.inner_repOp (μ := μ) hfc hfs v v
  rw [h0, inner_zero_right] at key
  have hint : Integrable (fun g => (φ g : ℂ) * inner ℂ v ((Rcusp μ g) v)) μ :=
    (hfc.mul cc).integrable_of_hasCompactSupport hfs.mul_right
  have h8 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at h8
  rw [← key, Complex.zero_re] at h8
  have h9 : 0 < ∫ g, φ g * (inner ℂ v ((Rcusp μ g) v)).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (hφc.mul (Complex.continuous_re.comp cc)) hφs.mul_right (fun g => ?_) (mul_ne_zero hφ1 h1pos.ne')
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (hφ0 g) (hφN hg).le
  linarith

end GlobalTheory.CompanionTheory.CuspGL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompactStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_decomposition_of_compact : (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f)) → GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  first | exact @GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | exact GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | (intros; apply GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact <;> assumption)
end
end

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRep

theorem cuspDiscreteDecompositionGL : GlobalTheory.Published.CuspDiscreteDecompositionGL :=
  GlobalTheory.T.cuspidal_decomposition_of_compact GlobalTheory.T.cuspidal_convolution_compact

end GlobalTheory.CompanionTheory.CuspRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.RegroupFin

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, GeneralLinearGroup.map, apply_ite f]

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  have h1 : ∀ x : GL (Fin n) R, GeneralLinearGroup.map f (invT n R x) = invT n S (GeneralLinearGroup.map f x) := by
    intro x
    apply Units.ext
    ext i j
    have e : (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ := (map_inv _ x).symm
    simp only [invT, MonoidHom.coe_mk, OneHom.coe_mk, e]
    rfl
  have h2 : GeneralLinearGroup.map f (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map f g) := by
    apply Units.ext
    ext i j
    exact h _
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  rw [h3, h3, map_mul, map_mul, map_inv, map_phiU, h1, h2]

theorem evw_pv (v : PlF E) (w : Above v) (y : Gf E a b) : evw w (pv a b v y) = atW w.1 y := by
  refine Prod.ext ?_ ?_ <;> · apply Units.ext; ext i j; rfl

theorem cjv_spec (hc : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hc E v
  unfold cjv
  rw [dite_eq_left h]
  exact h.choose_spec.2 x

theorem pv_thP (hc : CjEx) (v : PlF E) (y : Gf E a b) : pv a b v (thP E a b y) = thv a b v (pv a b v y) :=
  Prod.ext (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) a y.1) (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) b y.2)

theorem finprod_fibres {X Y : Type} (u : X → Y) (S : Set X) (hu : Set.InjOn u S) (F : X → ℂ) :
    ∏ᶠ w ∈ S, F w = ∏ᶠ v : Y, ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 := by
  set G : Y → ℂ := fun v => ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 with hG
  have hone : ∀ v, v ∉ u '' S → G v = 1 := by
    intro v hv
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hw : w.1 ∉ S := fun hw => hv ⟨w.1, hw, w.2⟩
    simp [hw]
  have hval : ∀ w ∈ S, G (u w) = F w := by
    intro w hw
    have hs : {i : {x : X // u x = u w} | i.1 ∈ S} = {⟨w, rfl⟩} := by
      ext i
      change i.1 ∈ S ↔ i = ⟨w, rfl⟩
      constructor
      · intro hi
        exact Subtype.ext (hu hi hw i.2)
      · rintro rfl
        exact hw
    have : G (u w) = ∏ᶠ i ∈ {i : {x : X // u x = u w} | i.1 ∈ S}, F i.1 := rfl
    rw [this, hs, finprod_mem_singleton]
  have h1 : ∏ᶠ v, G v = ∏ᶠ v ∈ u '' S, G v := by
    rw [← finprod_mem_univ]
    refine finprod_mem_inter_mulSupport_eq' _ _ _ fun v hv => ?_
    simp only [Set.mem_univ, true_iff]
    by_contra hn
    exact hv (hone v hn)
  rw [h1, finprod_mem_image hu]
  exact (finprod_mem_congr rfl hval).symm

theorem regroup_of_cjEx (hc : CjEx) : Regroup := by
  intro E _ _ _ a b S hS φ₁ φ₂ _ _ y
  have hinj : Set.InjOn (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) S := by
    intro u hu u' hu' h
    obtain ⟨x, -, hx⟩ := hS u
    exact (hx u ⟨hu, rfl⟩).trans (hx u' ⟨hu', h.symm⟩).symm
  unfold finFn
  rw [finprod_fibres _ S hinj]
  refine finprod_congr fun v => ?_
  unfold fv
  refine finprod_congr fun w => finprod_congr fun _ => ?_
  rw [evw_pv, ← pv_thP hc, evw_pv]

theorem regroup : Regroup := regroup_of_cjEx GlobalTheory.CompanionTheory.CjEx.cjEx

end GlobalTheory.CompanionTheory.RegroupFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_21 : PositivityTheory.Rg.BcB.G8.Fin.Regroup := by
  first | exact @GlobalTheory.CompanionTheory.RegroupFin.regroup | exact GlobalTheory.CompanionTheory.RegroupFin.regroup | (intros; apply GlobalTheory.CompanionTheory.RegroupFin.regroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitian
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram

theorem inner_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  intro D θ hθ V r ρ
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · change Continuous (fun y : Mx D V.rank r => GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y))
    exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  · change GlobalTheory.MixModel.adj (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)) = GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)
    rw [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  · change compAt θ ρ (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram V) * y)) = _
    rw [GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_adj hθ, GlobalTheory.CompanionTheory.WSum.compAt_rat hθ, Matrix.mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitianStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_map_continuous_hermitian : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram.inner_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : _root_.GlobalTheory.CuspRep.IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalenceStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)
end
end
