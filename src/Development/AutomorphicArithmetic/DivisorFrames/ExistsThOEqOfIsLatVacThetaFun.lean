module

public import Development.AutomorphicArithmetic.DivisorFrames.ThetaOperatorIntertwinesHeisenberg
public import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsEqPureVacuumOfLatticeInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem invTwo_mem (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

private theorem smul_mem_lat {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : HeightOneSpectrum (𝓞 F)) {c : AF F}
    (hc : evFin F v c ∈ v.adicCompletionIntegers F) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hγ : γ ∈ latAtV X W v) : c • γ ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * a, fun u hu => ?_, ?_, x, hx, y, hy, smul_smul _ _ _⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem hc hav
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg z _ h => rw [smul_neg]; exact neg_mem h

private theorem hTens_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n d : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hγ : At (evFin F v) γ) (ht : γ.map (piW t) = 0) :
    GlobalTheory.WeilM.hTens (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) JA JB γ γ = 0 := by
  have h0 := GlobalTheory.SwapAtPlace.one_sub_smul hγ
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  have ht' : ∀ i j, piW t (γ i j) = 0 := fun i j => congrFun (congrFun ht i) j
  have hσ : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj h t
  unfold GlobalTheory.WeilM.hTens
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • γ i j = γ i j := (congrFun (congrFun h0 i) j).symm
  refine GlobalTheory.SwapAtPlace.eq_zero_of_piW h t ?_ ?_ ?_
  · rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, h3]
  · rw [map_mul, map_mul, map_mul, ht', zero_mul, zero_mul, zero_mul]
  · rw [map_mul, GlobalTheory.SplitDict.piW_cA, hσ, ht', mul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
        (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
        W.IsSkew σ B r' s' → M.IsGood B.ψ →
        ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ (2 • γ) Ψ = Ψ) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v, γ.map (piW t) = 0 → M.co.rho B.ψ γ Ψ = Ψ) →
        ∃ g : SInf F (Fin n × Fin d), Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hG Ψ hΨ h2 hh
  have hstd := hB.std
  obtain ⟨f, hf⟩ := GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices M.vac (fun v => (hG.vac v).2.1) hG.std Ψ hΨ fun v y hy => by
    let gen : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
      {γ | (∃ γ' ∈ latAtV X W v, γ = 2 • γ') ∨ (γ ∈ latAtV X W v ∧ ∃ t : E →ₐ[F] Fv F v, γ.map (piW t) = 0)}
    have hsub : ∀ γ ∈ gen, γ ∈ latAtV X W v := by
      rintro γ (⟨γ', h, rfl⟩ | ⟨h, -⟩)
      · exact nsmul_mem h 2
      · exact h
    have hgen : latAtV X W v ≤ AddSubgroup.closure gen := by
      intro γ hγ
      by_cases hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w
      · haveI := hB.unram
        obtain ⟨t⟩ := GlobalTheory.SplitDict.nonempty_emb hB.cm v hv
        obtain ⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hB.cm X W v t γ hγ
        exact add_mem (AddSubgroup.subset_closure (.inr ⟨h₁, _, e₁⟩)) (AddSubgroup.subset_closure (.inr ⟨h₂, _, e₂⟩))
      · obtain ⟨w, hw⟩ := not_forall_not.1 hv
        refine AddSubgroup.subset_closure (.inl ⟨⅟(2 : AF F) • γ, smul_mem_lat X W v (invTwo_mem v (hB.inert v w hw).1) hγ, ?_⟩)
        rw [two_nsmul, ← add_smul, invOf_two_add_invOf_two, one_smul]
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat.toIsLattice hW.lat.toIsLattice
    obtain ⟨a, ha⟩ := GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) (GlobalTheory.LatVac.locCo M.co v '' gen)
      ((latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v)) c
      (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono hgen) hc0
      (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ (fun γ hγ => GlobalTheory.VacLine.at_latAtV hγ)
        (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v))
      (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ hγ) (M.vac v)
      (fun ξ => Ψ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_eq_of_acts _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) (hG.vac v).1 ?_
        obtain ⟨-, -, θ, -, hθ⟩ := hG.vac v
        have h1 := hθ γ (hsub γ hγ)
        have h3 : B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
            (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) γ γ) = 1 := by
          rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
          · exact GlobalTheory.BigDat.VacFix.psi_double _ B X W _ _ _ _ hB hX hW v θ γ' hγ'
          · unfold GlobalTheory.WeilM.symp
            rw [hTens_half hB.cm t _ _ (GlobalTheory.VacLine.at_latAtV hγ) ht, mul_zero, map_zero, mul_zero,
              AddChar.map_zero_eq_one]
        rwa [h3, one_smul] at h1)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_slice _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) ?_ hy
        rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
        · exact h2 v γ' hγ'
        · exact hh v t γ hγ ht) (hG.vac v).2.1
    exact ⟨a, congrFun ha⟩
  exact ⟨f, hf⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsSplitIdempotentMulEqOfPiWEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v),
        ∃ a : AE D, IsSplitIdem D a ∧ ∀ z : AE D, At (evFin D.host.F v) z → piW t z = 0 → a * z = z := by
  intro D v t
  refine ⟨GlobalTheory.EmbChart.idem (t.comp D.sp.cm.sig), GlobalTheory.EmbChart.isSplitIdem_idem _, fun z hz h0 => ?_⟩
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v (1 : Fv D.host.F v)) • z = 0 :=
    hz _ (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  have h2 : z = GlobalTheory.EmbChart.tensAt D.host.E v (1 * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) :=
    h1.trans (GlobalTheory.EmbChart.tensAt_mul_right v 1 z)
  have h3 : GlobalTheory.AdelicU.splitIdem (GlobalTheory.AdelicU.isCMExt_host D) t * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z = 0 :=
    (GlobalTheory.AdelicU.splitProj_eq_zero_iff _ t _).1 h0
  rw [GlobalTheory.EmbChart.idem_mul, GlobalTheory.AdelicU.splitIdem_comp, sub_mul, h3, sub_zero]
  exact h2.symm
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_crd {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    ptO G e (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)) = u := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  ext i j
  simp

private theorem ptO_two {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (2 • x) = 2 • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [two_nsmul, two_nsmul, Matrix.add_mul]
  rfl

private theorem isHalf_crd {D : D7} {m k d : ℕ} (H : Matrix (Fin m) (Fin m) (AE D)) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) (a : AE D) (h : ∀ i j, a * u i j = u i j) :
    IsHalf a (HMul.hMul (uᵀ.submatrix e.symm id) H : Matrix (Fin d) (Fin m) (AE D)) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc]
  exact congrArg (· * H l j) (h l (e.symm i))

theorem UpperTheory.exists_thO_eq_of_isLatVac_thetaFun :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        ∀ f₀ : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f₀ → IsLatVac (heisO ψ (sgn ε S) X) (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) f₀ →
        ∃ g : SInf D.host.F (Fin S.rank × Fin d), f₀ = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  intro D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL f₀ hth hvac
  obtain ⟨-, hrho, -, -, hinj, hon⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hlat, -⟩ := UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL
  obtain ⟨Ψ, hΨ, rfl⟩ := (hon f₀).1 hth
  obtain ⟨r, s, hV⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  have hψ := hP.psi
  subst hψ
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hfix : ∀ y : WO (sgn ε S) X, heisO Bs.ψ (sgn ε S) X y (thO M Bs.ψ (sgn ε S).gram e Ψ) = thO M Bs.ψ (sgn ε S).gram e Ψ →
      M.co.rho Bs.ψ (ptO (sgn ε S).gram e y) Ψ = Ψ := fun y hy =>
    hinj _ (GlobalTheory.HeisSchA.rho_mem_schA M Bs.ψ hP.base.std _ Ψ hΨ) _ hΨ ((hrho Ψ y).trans hy)
  obtain ⟨g, hg⟩ := UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant D.host.F D.host.E D.sp.cm.sig Bs S.rank d Vs Ws M r s r' s' hP.base hV hW hP.good Ψ hΨ
    (fun v γ hγ => by
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have h2 := hfix _ (hvac.1 _ h1)
      have h3 := (ptO_two (D := D) _ e _).trans (congrArg (2 • ·) h0)
      exact h3 ▸ h2)
    (fun v t γ hγ ht => by
      obtain ⟨a, ha, haz⟩ := UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero D v t
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have hat := (GlobalTheory.LatVac.latAtV_at_stable Vs Ws v).1 γ hγ
      have h2 := hfix _ (hvac.2 a ha _ h1 (isHalf_crd _ e γ a fun i j =>
        haz _ (fun u hu => congrFun (congrFun (hat u hu) i) j) (congrFun (congrFun ht i) j)))
      exact h0 ▸ h2)
  exact ⟨g, by rw [← hg]⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealDict GlobalTheory.RealDict.FockMap

private theorem finPart_ne {F : Type} [Field F] [NumberField F] {n d : ℕ}
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y, GlobalTheory.BigNZ.finPartFn φ y ≠ 0 := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)
  have hS := Filter.eventually_cofinite.1 hs
  let y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  refine ⟨y, ?_⟩
  refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
  by_cases hv : v ∈ hS.toFinset
  · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
    rw [this]
    exact hξ v
  · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
    rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
    exact one_ne_zero


set_option maxHeartbeats 1000000 in
private theorem fock_of {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
    (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj)
    (g₀ : SInf D.host.F (Fin M.rank × Fin X.rank)) (g0 : g₀ ≠ 0)
    {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (hy : ∃ y, g y ≠ 0)
    (hv : IsVacF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g))) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      LinearMap.range Φ = Mo.Pol ψ τ ∧
      ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g) = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g)) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  simp only [hΘ']
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a y)
    rw [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt] at e2
    exact mul_right_cancel₀ hy e2
  have hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ +
      Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0 := fun t z => hi (by
    have h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0 := hv.2 t z
    rw [annih, hd, hd, ← map_smul, ← map_add (f := _)] at h
    rw [h, map_zero])
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun hΦ P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t,
      eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), hΦ'⟩
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.theta_transform_fock_model_eq_of_standard_char :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
        ∀ (ε : Bool) (M X : HSp D) (k : ℕ) (hk : k = X.rank) (Xs : Spc D.host.F D.host.E M.rank) (Ws : Spc D.host.F D.host.E k)
        (Mo : Model D.sp.cm.sig Xs Ws), Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram →
        Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (finCongr hk) (finCongr hk) → Mo.IsGood ψ →
        ∀ (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w),
        (∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
          Ws.θ w = ((B.cart t).submatrix (finCongr hk) (finCongr hk)).map conj) →
        ∀ (f₀ : SInf D.host.F (Fin M.rank × Fin k)) (φ : ∀ v : Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ), f₀ ≠ 0 →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) → (∀ v, φ v ≠ 0) →
        GlobalTheory.SquareComm.IsFinF ψ θ ε A B (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) →
        ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin k), LinearMap.range Φ = Mo.Pol ψ τ ∧
          ∀ P, GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
            GlobalTheory.SquareComm.fockF ψ θ ε A B
              (GlobalTheory.TripleRead.thO Mo ψ (GlobalTheory.Grid.sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ)) P := by
  intro D ψ θ hψ hθ ε M X k hk Xs Ws Mo hX hW hM A B τ hc f₀ φ hf hφ hφ' hφ0 hv
  subst hk
  have hF : GlobalTheory.BigNZ.Fam Mo φ := ⟨hφ, hφ'⟩
  have h2X : ∀ w, Xs.θ w * Xs.θ w = 1 := fun w => by
    obtain ⟨t, -, h, -⟩ := hc w
    rw [h, Matrix.smul_mul, Matrix.mul_smul, (GlobalTheory.ChainFr.Model.isCartanInv_cart A t).1, smul_smul]
    cases ε <;> simp
  have h2W : ∀ w, Ws.θ w * Ws.θ w = 1 := fun w => by
    obtain ⟨t, -, -, h⟩ := hc w
    have h' : Ws.θ w = (B.cart t).map (starRingEnd ℂ) := h
    rw [h', ← Matrix.map_mul, (GlobalTheory.ChainFr.Model.isCartanInv_cart B t).1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact fock_of Mo hψ hθ A B (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) hX hW hM h2X h2W hc
    f₀ hf (hF.sb hM) (finPart_ne φ hφ0 (hF.std hM)) hv
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.LevChiEqOneOfGoodPlace
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.hecke_offprime_preimage {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ v ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP v) :
    ∀ k ∈ GlobalTheory.Hk3.hyp V v, ∃ h : (Formalism.L2.Theta.finHom V).rangeRestrict k ∈ (levEnv V β L).J,
      (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 v e f' he h1 hoff
  rintro a ⟨ha, e, f', he, hs⟩
  have hm := ((hl e f' he).1 a hs).2 ha
  exact ⟨hm.2, Units.ext ((hl e f' he).2.1 a hm hs)⟩

theorem UpperTheory.levChi_eq_one_of_good_place :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (v : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good p.R.toRealDat t v →
        ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) v, ∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t, levChi p j t ⟨_, h⟩ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t v hv
  exact UpperTheory.hecke_offprime_preimage (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) v hv
end
