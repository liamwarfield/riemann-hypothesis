module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemNormsOfCongrEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} {X Y H : Matrix (Fin n) (Fin n) K}
    (h : X * H = H * Y) (p : K[X]) : aeval X p * H = H * aeval Y p := by
  have hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc,
      Algebra.commutes a H, Matrix.mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_norms_of_congr (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q)
    (hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e)
    (hιc : ∀ y, involBase Q k (ι y) = ι (cj w y))
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = eval₂ ι ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := Matrix.charpoly_map _ _
  obtain ⟨f, hf⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    exact this
  have hHu : IsUnit H.det := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet.isUnit).map _
  have hcT : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀)) := by
      rw [GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]
    have h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
      rw [hc2, hf, h1, Matrix.mul_assoc]
    have h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f := by
      have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hHu
      calc aeval A m = H⁻¹ * H * aeval A m := by rw [hHi, Matrix.one_mul]
        _ = H⁻¹ * H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
          rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
        _ = _ := by rw [hHi, Matrix.one_mul]
    rw [map_sub, map_mul, ← h3, sub_self]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t := by
    rw [← ht]; ring
  have h0 : Φ (atPl w γ₀.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) := by
    rw [hinvΦ, ← map_mul, hft, map_add (f := _), map_mul, h0, zero_mul, add_zero, hx]
    rfl
  have hu : IsUnit (Φ f) :=
    isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)
  exact ⟨hu.unit, Units.ext hz⟩

theorem mem_norms_of_congr_equiv (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (j : w.adicCompletion E ≃+* k ⊗[maximalRealSubfield E] E)
    (hj1 : ∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e)
    (hj2 : ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) =
      eval₂ (((inclBase Q k).toRingHom).comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  refine mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx
  · change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  · change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.CompanionTheory.NormCongr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem mem_norms_locPhi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ _ hdet hinv m c hc1 hc2 r Q hQ x hx
  exact mem_norms_of_congr_equiv hU w hw (v.adicCompletion (maximalRealSubfield E)) (locJ hU w hw v hv)
    (locJ_algebraMap hU w hw v hv) (locJ_cj hU w hw v hv) n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ x hx

end GlobalTheory.CompanionTheory.NormCongr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThirdStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_class_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi | exact GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi | (intros; apply GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacter
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Level

variable {D : D7} {r : ℕ}

def eFin (D : D7) : AF D.host.F := 1 - GlobalTheory.FinTranslate.eInf D

theorem eFin_mul (D : D7) (x : AF D.host.F) : eFin D * x = pairA D.host.F 0 (sndA D.host.F x) := by
  show ((1 : Ainf D.host.F × Af D.host.F) - (1, 0)) * (x : Ainf D.host.F × Af D.host.F) =
    ((0 : Ainf D.host.F), (x : Ainf D.host.F × Af D.host.F).2)
  refine Prod.ext ?_ ?_
  · show ((1 : Ainf D.host.F) - 1) * x.1 = 0
    rw [sub_self, zero_mul]
  · show ((1 : Af D.host.F) - 0) * x.2 = x.2
    rw [sub_zero, one_mul]

theorem finPart_eInf (D : D7) : finPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 0 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem infPart_eInf (D : D7) : infPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rs_one {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    rs σ 1 = GlobalTheory.FinTranslate.eInf D • (1 : AE D) := by
  refine sub_eq_zero.mp (hσ.ext _ ?_ ?_)
  · rw [map_sub, finPart_eInf, sub_zero]
    exact hσ.fin _
  · intro τ
    rw [map_sub, map_sub, infPart_eInf, map_one]
    simp only [rs, hσ.comp]
    simp

theorem diff_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1).1 = eFin D • a.1.map (incA D) := by
  show GlobalTheory.MixModel.rat a.1 - rs σ 1 • a.1.map (incA D) = eFin D • a.1.map (incA D)
  rw [rs_one hσ, smul_one_smul, eFin, sub_smul, one_smul]
  rfl

def S (V : HSp D) (A : Mx D r r) (y : Mx D V.rank r) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))

theorem halfTr_smul (c : AF D.host.F) (x : AE D) : halfTr (c • x) = c * halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_smul, smul_eq_mul]
  ring

theorem halfTr_nsmul (n : ℕ) (x : AE D) : halfTr (n • x) = n • halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem halfTr_trace_nsmul (n : ℕ) (M B : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (n • M) B : Mx D r r)) = n • halfTr (Matrix.trace (HMul.hMul M B : Mx D r r)) := by
  rw [Matrix.smul_mul, Matrix.trace_smul, halfTr_nsmul]

theorem pow_eq_one_of_compact {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {C : Set (Af F)} (hC : IsCompact C) : ∃ N : ℕ, 0 < N ∧ ∀ c ∈ C, ψ (pairA F 0 c) ^ N = 1 := by
  obtain ⟨N1, hN1, hK⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_mem_Oh_of_isCompact F C hC
  obtain ⟨N2, hN2, hU⟩ :=
    GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_Oh_subset F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  refine ⟨N2 * N1, Nat.mul_pos hN2 hN1, fun c hc => ?_⟩
  have h1 : ψ (pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c))) = 1 := hU _ (hK c hc)
  have h2 : (N2 * N1) • pairA F 0 c = pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c)) := by
    show (N2 * N1) • ((0 : Ainf F), c) = ((0 : Ainf F), (N2 : Af F) * ((N1 : Af F) * c))
    rw [Prod.smul_mk, smul_zero, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul]
  rw [← AddChar.map_nsmul_eq_pow, h2, h1]

private theorem supp_lemma_5 {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    ∃ K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact K ∧
      ∀ y, φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ K := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨tsupport g, (show IsLocallyConstant g ∧ HasCompactSupport g from hg).2, fun y hy => subset_tsupport g ?_⟩
    exact right_ne_zero_of_mul hy
  | zero => exact ⟨∅, isCompact_empty, fun y hy => (hy rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, h1⟩ := hx
    obtain ⟨K2, hK2, h2⟩ := hy
    refine ⟨K1 ∪ K2, hK1.union hK2, fun z hz => ?_⟩
    by_cases hxz : x z = 0
    · right
      apply h2
      simpa [hxz] using hz
    · left
      exact h1 z hxz
  | smul a x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    refine ⟨K, hK, fun y hy => h y ?_⟩
    intro h0
    apply hy
    simp [h0]

private theorem continuous_sigRf_lemma_7 : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig) := by
  let f : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
        | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap f

private theorem trace_bc_lemma_8 (z : AE D) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a e =>
    have h1 : (a ⊗ₜ[D.host.F] e : AE D) = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Formalism.L2.Theta.finPart]
    rw [h2, h1]
    simp only [map_smul, GlobalTheory.CompanionTheory.HermPoisson.trace_one_tmul', smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem level_pow {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (A : Mx D r r)
    {θ : InfFam D} {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) :
    ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (eFin D * S V A y) ^ N = 1 := by
  obtain ⟨K, hK, hKy⟩ := supp_lemma_5 hφ
  let Φ : (Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → Af D.host.F := fun w =>
    algebraMap D.host.F (Af D.host.F) (1 / 2) *
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
        (Matrix.trace (A.map (finPart D) *
          (((Matrix.of w).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
            ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of w))))
  have hΦ : Continuous Φ := by
    have hσc := continuous_sigRf_lemma_7 (D := D)
    have htr : Continuous (Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) := by fun_prop
    have hof : Continuous (fun w : Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => Matrix.of w) :=
      continuous_id
    exact continuous_const.mul (htr.comp (Continuous.matrix_trace (continuous_const.matrix_mul
      ((hof.matrix_map hσc).matrix_transpose.matrix_mul (continuous_const.matrix_mul hof)))))
  have hS : ∀ y : Mx D V.rank r, sndA D.host.F (S V A y) = Φ (fun i j => finPart D (y i j)) := by
    intro y
    have hM : (HMul.hMul A (inner V y y) : Mx D r r).map (finPart D) =
        A.map (finPart D) * (((Matrix.of fun i j => finPart D (y i j)).map
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
          ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of fun i j => finPart D (y i j))) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, GlobalTheory.MixModel.adj, GlobalTheory.StdUnn.inner, map_sum, GlobalTheory.CompanionTheory.WSum.finPart_cA]
    have ht : ∀ M : Mx D r r, finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
      intro M
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    show sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))) = _
    rw [map_mul, AlgHom.commutes, trace_bc_lemma_8, ht, hM]
  obtain ⟨N, hN, hC⟩ := pow_eq_one_of_compact hψ (hK.image hΦ)
  refine ⟨N, hN, fun y hy => ?_⟩
  rw [eFin_mul, hS y]
  exact hC _ ⟨_, hKy y hy, rfl⟩

theorem level : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  intro D r V ψ hψ θ σ hσ a φ hφ
  obtain ⟨N, hN, hy⟩ := level_pow hψ V (a.1.map (incA D)) hφ
  refine ⟨N, hN, fun y hy0 => ?_⟩
  rw [AddSubgroup.coe_nsmul, diff_eq hσ a, halfTr_trace_nsmul, Matrix.smul_mul, Matrix.trace_smul, halfTr_smul,
    AddChar.map_nsmul_eq_pow]
  exact hy y hy0

end GlobalTheory.CompanionTheory.WSum.Level
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacterStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_multiple_path_trivial_character : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Level.level | exact GlobalTheory.CompanionTheory.WSum.Level.level | (intros; apply GlobalTheory.CompanionTheory.WSum.Level.level <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeft
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.CompanionTheory.BZRes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibRes0Left

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (hσ : IsSmooth σ) :
    smoothPart (ind H σ) ≃ₗ[ℂ] W where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨⟨fun g => σ ⟨g, hH g⟩ w, by
      intro h g
      show σ ⟨(h : G) * g, hH _⟩ w = σ h (σ ⟨g, hH g⟩ w)
      rw [← Module.End.mul_apply, ← map_mul]
      rfl⟩, by
      have hop : IsOpen {g : G | σ ⟨g, hH g⟩ w = w} :=
        (hσ w).preimage (continuous_id.subtype_mk hH)
      have h1 : (1 : G) ∈ {g : G | σ ⟨g, hH g⟩ w = w} := by
        show σ ⟨1, hH 1⟩ w = w
        rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hop.mem_nhds h1) fun g hg => ?_)
      refine Subtype.ext (funext fun x => ?_)
      show σ ⟨x * g, hH _⟩ w = σ ⟨x, hH x⟩ w
      rw [show (⟨x * g, hH _⟩ : H) = ⟨x, hH x⟩ * ⟨g, hH g⟩ from rfl, map_mul, Module.End.mul_apply]
      exact congrArg _ hg⟩
  left_inv f := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show σ ⟨g, hH g⟩ (f.1.1 1) = f.1.1 g
    have := f.1.2 ⟨g, hH g⟩ 1
    rw [← this, mul_one]
  right_inv w := by
    show σ ⟨1, hH 1⟩ w = w
    rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]

theorem mem_cIndSpace_top (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    f ∈ cIndSpace H σ := by
  exact ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, Set.mem_singleton 1, (mul_one g).symm⟩⟩

def cTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) :
    cIndSpace H σ ≃ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, mem_cIndSpace_top H hH σ f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {P W₂ : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [AddCommGroup W₂] [Module ℂ W₂]

theorem equiv_of_top (ι : P →* G) (hι : Continuous ι) (Q : Subgroup G) (H : Subgroup P) (hQ : ∀ g, g ∈ Q)
    (hH : ∀ p, p ∈ H) (σ : Representation ℂ Q W) (τ : Representation ℂ H W₂) (E : W ≃ₗ[ℂ] W₂) (hσ : IsSmooth σ)
    (hE : ∀ (h : H) (v : W), τ h (E v) = E (σ ⟨ι h, hQ _⟩ v)) :
    Nonempty (Representation.Equiv ((smInd Q σ).comp ι) (cInd H τ)) := by
  have hτ : IsSmooth τ := by
    intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    have hset : {h : H | τ h (E v) = E v} =
        (fun h : H => (⟨ι h, hQ _⟩ : Q)) ⁻¹' {q : Q | σ q v = v} := by
      ext h
      show τ h (E v) = E v ↔ σ ⟨ι h, hQ _⟩ v = v
      rw [hE h v]
      exact E.injective.eq_iff
    rw [hset]
    exact (hσ v).preimage ((hι.comp continuous_subtype_val).subtype_mk _)
  let L : smoothPart (ind Q σ) ≃ₗ[ℂ] cIndSpace H τ :=
    ((evalTop Q hQ σ hσ).trans E).trans ((evalTop H hH τ hτ).symm.trans (cTop H hH τ).symm)
  refine ⟨Representation.Equiv.mk L fun p => ?_⟩
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))
  show τ ⟨x, hH x⟩ (E (f.1.1 (1 * ι p))) = τ ⟨x * p, hH _⟩ (E (f.1.1 1))
  have hf : f.1.1 (ι p) = σ ⟨ι p, hQ _⟩ (f.1.1 1) := by
    have := f.1.2 ⟨ι p, hQ _⟩ 1
    rw [mul_one] at this
    exact this
  rw [one_mul, hf, show E (σ ⟨ι p, hQ _⟩ (f.1.1 1)) = τ ⟨p, hH p⟩ (E (f.1.1 1)) from (hE ⟨p, hH p⟩ _).symm,
    ← Module.End.mul_apply, ← map_mul]
  rfl

end Abstract

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hgp_twist_tE {m j : ℕ}
    (π₁ : Representation ℂ (GL (Fin m) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : MirabolicParabolic k m j)
    (hq : ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k) ∈
      parab k (two (stdSum (rfl : m + (j + 1) = m + j + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g (tE V W v) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  set L := leviProj k (two (stdSum (rfl : m + (j + 1) = m + j + 1))) ⟨_, hq⟩ with hL
  have hL2 : leviTwo k (Fin m) (Fin (j + 1)) (L false, L true) = L := by
    funext b
    cases b <;> rfl
  have hδ := GlobalTheory.SmGL.deltaHalf_two (k := k) (a := Fin m) (b := Fin (j + 1)) (L false, L true)
  rw [hL2] at hδ
  have hc : (((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) *
      (((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) =
      ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) := by
    rw [hδ, Units.val_mul]
    simp only [dpow, GlobalTheory.SmGL.detChar_apply, Fintype.card_fin]
    congr 4 <;> push_cast <;> ring
  have key : ∀ x : (b : Bool) → TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have e1 : tE V W (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod x
    have e2 : sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x) =
        ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b)) := by
      show ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          (piTensor (twoRep π₁ π₂) L) (PiTensorProduct.tprod ℂ x) = _
      rw [GlobalTheory.SmGL.piTensor_tprod]
    have e3 : tE V W (PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b))) =
        π₁ (L false) (x false) ⊗ₜ[ℂ] π₂ (L true) (x true) :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod _
    rw [e1, e2, map_smul, e3, MonoidHom.comp_apply]
    erw [GlobalTheory.SmGL.extTensor_tmul]
    show ((((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) • π₁ (L false) (x false)) ⊗ₜ[ℂ]
        ((((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) • π₂ (L true) (x true)) = _
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, hc]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearEquiv.map_smul (tE V W) r,
      LinearMap.map_smul (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) r,
      LinearEquiv.map_smul (tE V W), ← key x]
    exact LinearMap.map_smul _ _ _
  | add a b ha hb =>
    rw [LinearEquiv.map_add (tE V W) a b,
      LinearMap.map_add (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) a b,
      LinearEquiv.map_add (tE V W), ← ha, ← hb]
    exact LinearMap.map_add _ _ _

theorem mem_parab_zero {j : ℕ} (g : GL (Fin (0 + j + 1)) k) :
    g ∈ parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) := by
  intro a b hab
  have key : ∀ x : Fin (0 + j + 1), GlobalTheory.SmGL.blk (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    rcases (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))).symm x with ⟨b, y⟩
    cases b
    · exact Fin.elim0 y
    · rfl
  rw [key, key] at hab
  exact absurd hab (lt_irrefl _)

theorem isSmooth_sQ {r t N : ℕ} (h : r + t = N) {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  refine GlobalTheory.SmGL.isSmooth_comp (GlobalTheory.SmGL.isSmooth_twist (GlobalTheory.SmGL.isSmooth_piTensor fun b => ?_)
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)) _ ?_
  · cases b
    · exact h₁
    · exact h₂
  · refine continuous_pi fun b => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix
        (fun i => (two (stdSum h)) ⟨b, i⟩) (fun i => (two (stdSum h)) ⟨b, i⟩)
    · have hinv : Continuous fun p : parab k (two (stdSum h)) =>
          (((p⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
        (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
      refine (hinv.matrix_submatrix (fun i => (two (stdSum h)) ⟨b, i⟩)
        (fun i => (two (stdSum h)) ⟨b, i⟩)).congr fun p => ?_
      rw [← Pi.inv_apply, ← map_inv]
      rfl

theorem gres_prod_zero_left (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n)
    (h₁ : IsSmooth π₁.ρ) (h₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  subst h'
  exact equiv_of_top (Mir k (0 + j)).subtype continuous_subtype_val
    (parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1)))) (MirabolicParabolic k 0 j)
    (fun g => mem_parab_zero g) (fun p => mem_parab_zero (p : GL (Fin (0 + j + 1)) k))
    (sQ (rfl : 0 + (j + 1) = 0 + j + 1) π₁.ρ π₂.ρ)
    ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((0 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k 0 j))
    (tE π₁.V π₂.V) (isSmooth_sQ rfl h₁ h₂)
    (fun hh v => hgp_twist_tE π₁.ρ π₂.ρ hh (mem_parab_zero _) v)

theorem gres_prod_zero_left' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  intro k _ _ _ _ j n π₁ π₂ h h' h₁ h₂
  exact gres_prod_zero_left j n π₁ π₂ h h' h₁ h₂

end Concrete

end GlobalTheory.CompanionTheory.LeibRes0Left

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeftStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | exact GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' | (intros; apply GlobalTheory.CompanionTheory.LeibRes0Left.gres_prod_zero_left' <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecond
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.LocPhiUnit

section Fixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem exists_inclPlus_half (z : k ⊗[maximalRealSubfield E] Fld Q) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q,
      inclPlus Q k a = ((1 : k) ⊗ₜ[maximalRealSubfield E] (2⁻¹ : Fld Q)) * (z + involBase Q k z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨(y + invol Q y) / 2, ?_⟩, ?_⟩
    · change invol Q _ = _
      simp only [map_div₀, map_add (f := _), invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
    · change s ⊗ₜ[maximalRealSubfield E] ((y + invol Q y) / 2) = _ * (s ⊗ₜ y + s ⊗ₜ invol Q y)
      rw [← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add (f := _), ha, hb, map_add (f := _)]
    ring

theorem exists_inclPlus_of_fixed {z : k ⊗[maximalRealSubfield E] Fld Q} (hz : involBase Q k z = z) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q, inclPlus Q k a = z := by
  obtain ⟨a, ha⟩ := exists_inclPlus_half Q k z
  refine ⟨a, ?_⟩
  have h2 : (2 : k ⊗[maximalRealSubfield E] Fld Q) = (1 : k) ⊗ₜ[maximalRealSubfield E] (2 : Fld Q) :=
    (map_ofNat (Algebra.TensorProduct.includeRight :
      Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q) 2).symm
  rw [ha, hz, ← two_mul, ← mul_assoc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    inv_mul_cancel₀ two_ne_zero, ← Algebra.TensorProduct.one_def, one_mul]

theorem inclPlus_injective : Function.Injective (inclPlus Q k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus Q).val.toLinearMap
    Subtype.val_injective

theorem exists_unit_of_fixed {y : k ⊗[maximalRealSubfield E] Fld Q} (hu : IsUnit y)
    (hy : involBase Q k y = y) :
    ∃ x : (k ⊗[maximalRealSubfield E] plus Q)ˣ,
      inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = y := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : involBase Q k ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) :
      k ⊗[maximalRealSubfield E] Fld Q) = (u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) := by
    have h1 : (u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
        ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) *
          ((u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
            ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  obtain ⟨a, ha⟩ := exists_inclPlus_of_fixed Q k hy
  obtain ⟨b, hb⟩ := exists_inclPlus_of_fixed Q k hinv
  have hab : a * b = 1 := inclPlus_injective Q k (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Fixed

section Matrix

theorem aeval_mul_of_intertwine {K : Type} [Field K] {n : ℕ} {B C H : Matrix (Fin n) (Fin n) K}
    (h : B * H = H * C) (g : K[X]) : aeval B g * H = H * aeval C g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial d a =>
    have e : B ^ d * H = H * C ^ d :=
      (((show SemiconjBy H C B from h.symm).pow_right d).eq).symm
    rw [aeval_monomial, aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc, e]

theorem cT_mul {K : Type} [Field K] (s : K →+* K) {n : ℕ} (B C : Matrix (Fin n) (Fin n) K) :
    cT s (B * C) = cT s C * cT s B := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

end Matrix

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem involBase_locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) {r₀ : E[X]} (hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0)
    (f : (w.adicCompletion E)[X]) :
    involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q f) =
      locPhi hU w hw v hv Q ((f.map (cj w)).comp (atPl w r₀)) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (locJ hU w hw v hv y)) =
      inclBase Q k (locJ hU w hw v hv (cj w y))
    rw [locJ_cj]
    generalize locJ hU w hw v hv y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (involBase Q k).toRingHom
  have hR : locPhi hU w hw v hv Q (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [locPhi_atPl]
    congr 1
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hr
    exact eq_inv_of_mul_eq_one_right hr
  have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm

end Local

theorem locPhi_mem_units_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ hH hdet h3 m hM hMdet r Q hQ
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
  obtain ⟨A, hA⟩ : ∃ A, A = γ₀.val.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = H₀.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  rw [← hA, ← hHd] at hM hMdet
  obtain ⟨M, hMd⟩ : ∃ M, M = aeval A m := ⟨_, rfl⟩
  rw [← hMd] at hM hMdet
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := by rw [hA]; exact Matrix.charpoly_map _ _
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hHh : cT (cj w) H = H := by
    rw [hHd, ← cT_map hU w hw]
    exact congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hH
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    rw [hA, hHd]
    exact this
  have hint : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hH0 : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at *
    exact (left_ne_zero_of_mul hMdet).isUnit
  have hM0 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hMdet
    exact (right_ne_zero_of_mul hMdet).isUnit
  have hfix : M = aeval A ((m.map (cj w)).comp (atPl w r₀)) := by
    have h1 : cT (cj w) M * H = H * M := by
      have := hM
      rw [IsHerm, cT_mul, hHh] at this
      exact this
    rw [hMd, GlobalTheory.NormInert.cT_aeval, aeval_mul_of_intertwine hint, ← aeval_comp, ← hMd] at h1
    exact (hH0.mul_left_cancel h1).symm
  have hdiv : A.charpoly ∣ (m.map (cj w)).comp (atPl w r₀) - m :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by rw [map_sub, ← hfix, ← hMd, sub_self])
  have hΦ0 : locPhi hU w hw v hv Q A.charpoly = 0 := by
    rw [hAP, locPhi_atPl]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hy : involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q m) =
      locPhi hU w hw v hv Q m := by
    obtain ⟨t, ht⟩ := hdiv
    rw [involBase_locPhi hU w hw v hv Q hr, ← sub_eq_zero, ← map_sub, ht, map_mul, hΦ0, zero_mul]
  obtain ⟨u, hu⟩ := hM0
  have hcomm : Commute A (u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hu, hMd]
    have := congrArg (aeval A) (mul_comm (X : (w.adicCompletion E)[X]) m)
    rw [map_mul, map_mul, aeval_X] at this
    exact this
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A
    ((u⁻¹ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    hAsep hcomm.units_inv_right.eq
  have hdiv2 : A.charpoly ∣ m * g - 1 :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by
      rw [map_sub, map_mul, ← hg, ← hMd, ← hu, Units.mul_inv, map_one, sub_self])
  have hone : locPhi hU w hw v hv Q m * locPhi hU w hw v hv Q g = 1 := by
    obtain ⟨t, ht⟩ := hdiv2
    rw [← map_mul, ← sub_eq_zero, ← map_one (locPhi hU w hw v hv Q), ← map_sub, ht, map_mul, hΦ0,
      zero_mul]
  exact exists_unit_of_fixed Q _ (isUnit_iff_exists_inv.2 ⟨_, hone⟩) hy

end GlobalTheory.CompanionTheory.LocPhiUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecondStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_class_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  first | exact @GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | exact GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | (intros; apply GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus <;> assumption)
end
end
