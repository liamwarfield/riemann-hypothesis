module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleProductAlgebraWeilRepRangeEqTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitParallelDerivativeLeftFixed
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.SplitParLeft
open GlobalTheory.DblVacLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem splitParallel_derivative_fixes_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hT hunr _ _ d' hd' dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hV.2.1
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := dblFun_eigen_left hTr.base hTr.geo v hunr d' hd' dd omd hdc hws.2.1 R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v p hp t ht
  have hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F)) :=
    fun w h hm => hT (h ▸ hm)
  have ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
    rw [MonoidHom.div_apply,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t htp.1 htp.2,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t htp.1 htp.2, div_one]
  have hb := GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t htp.1 htp.2
  rw [ha, hb] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  change omd p (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ at hc
  rw [hc, map_smul, smul_eq_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]
end GlobalTheory.SplitParLeft
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_parallel_derivative_left_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | exact _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | (intros; apply _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteAdeleActsPlacewise
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LatticeVacuumFixedOutsideFiniteSet
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVprimeStabilizerFixesVacuum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitLeftScalarFactorEqOne
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConnectionFixesSplitSubspace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.NabFixSplitV
open GlobalTheory.DblVacLineTransp GlobalTheory.DblVacLine GlobalTheory.SplitParLeft in
theorem connection_fixes_split_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.V' v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  have hConj := GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 _ d' hd' dd omd hdc hws R hR0 hRv n hn
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  have hLine : ∃ c : ℂ, omd n Φ = c • Φ := by
    obtain ⟨hSB, h0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    refine dbl_line_co hTr.base.std v hψ hTr.geo.hW.lat.toIsLattice hTr.geo.hV'.lat.toIsLattice ?_ d' (G.M'.vac v)
      ⟨hSB, h0, θ, hθ, ?_⟩ dd omd hdc hws.2.1 R hRv n hn.1
    · intro z hz
      have h := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _
        hTr.base hTr.geo.hV' hTr.geo.hW v zᵀ ((at_transpose v z).2 hz)
      rw [mem_latAtV_transpose] at h
      rw [h]
      constructor
      · intro H γ hγ
        have := H γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
        rwa [symp_transpose] at this
      · intro H γ hγ
        have := H γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
        have e := symp_transpose (R := AF F) (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) z γᵀ
        rw [Matrix.transpose_transpose] at e
        rw [e]
        exact this
    · intro γ hγ
      have h := hvac γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
      have e : d'.rho B.ψ γ = G.M'.co.rho B.ψ γᵀ := by
        simp only [Darboux.rho]
        rw [← hd' γᵀ, Matrix.transpose_transpose]
      rw [e, ← symp_transpose (R := AF F) (cA σ) _ (incM F G.W.J) (incM F G.V'.J) γ γ]
      exact h
  obtain ⟨c, hc⟩ := hLine
  obtain ⟨s, hs, hsn⟩ := hConj F E σ B hTr.base a' G.V' v hsp h2 n hn
  have hs1 : omd s Φ = Φ := by
    let Ψ := tens (evFin F v) (G.M'.vac v) R
    have hΨ : Ψ ∈ schA F _ := hRv.2
    have hΦ : Φ ∈ schA F _ :=
      GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
    obtain ⟨y, hy⟩ := Function.ne_iff.mp (hTr.geo.hM'.vac v).2.1
    have hΨne : Ψ ≠ 0 := by
      intro h0
      let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
      have hRx : R x = R 0 := by
        have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
        simpa using this
      have h1 := congrFun h0 x
      simp only [Ψ, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
      exact mul_ne_zero hy hR0 h1
    obtain ⟨k, hk⟩ := dblFun_eigen_left hTr.base hTr.geo v hψ d' hd' dd omd hdc hws.2.1 R hRv s hs.1
    obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
    obtain ⟨t, ht⟩ := hs.2
    have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) s t ht _ hΦ
    have hts := GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v s hs t ht
    have hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F)) :=
      fun w h hm => hT (h ▸ hm)
    have ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
      rw [MonoidHom.div_apply,
        chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t hts.1 hts.2,
        chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t hts.1 hts.2, div_one]
    have hb := GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t hts.1 hts.2
    rw [ha, hb] at hS
    simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
    change omd s Φ = k • Φ at hk
    rw [hk, map_smul, smul_eq_mul] at hS
    have hk1 : k = 1 := (mul_eq_right₀ hl0).mp hS
    rw [hk, hk1, one_smul]
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    rw [map_mul, mul_apply_eq_comp, hc, map_smul, hc, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    rw [← this, hc, h0, zero_smul, map_zero]
  · rw [hc, h1, one_smul]
end GlobalTheory.NabFixSplitV
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_fixed_split_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.V' v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  exact _root_.GlobalTheory.NabFixSplitV.connection_fixes_split_subspace
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitScalarV
theorem scalar_eq_one_of_split_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hws, hres⟩ := hTr.weil'.2.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.V') :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (_root_.GlobalTheory.T.split_parallel_derivative_left_fixed) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
    · exact (_root_.GlobalTheory.T.nabla_fixed_split_subspace) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (k, 1) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.V' k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'
end GlobalTheory.SplitScalarV
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_left_scalar_factor_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E)
    (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left | exact _root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left | (intros; apply _root_.GlobalTheory.SplitScalarV.scalar_eq_one_of_split_left <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SplitSphVPrimeStab
theorem vacuum_fixed_by_split_spherical_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM'.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv _ k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.SphOffFinite.isUnram_of_unramified hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
    obtain ⟨hφ₁, hact⟩ := hS _ hSB
    have h1 := GlobalTheory.InertSphLeft.acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
    obtain ⟨c, hc'⟩ := _root_.GlobalTheory.SphOffFinite.spherical_vacuum_unique_off_finite_set hPr F E σ B a a' G X om om' hTr v hs hψ h2 θ hθ hvac _ hφ₁ h1
    rw [hc'] at hact
    have hc := _root_.GlobalTheory.T.split_left_scalar_factor_eq_one hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.InertSphLeft.vac_fixed_left F E σ B a a' G X om om' hTr v w hw hvT k hk
end GlobalTheory.SplitSphVPrimeStab
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | exact _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | (intros; apply _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VacuumFixedBySplitSphericalLeft
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitVacuumHeckeEigenvalueEqOne
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VDoubleEigenspaceSplitOfLine
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.VDblEigSplit
theorem vDouble_eigenfunction_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ hunr _ _
  exact vdbl_eigen_of_unr F E σ B a a' G X om om' hT v hunr
end GlobalTheory.VDblEigSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vDouble_eigenspace_split_of_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @_root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split | exact _root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split | (intros; apply _root_.GlobalTheory.VDblEigSplit.vDouble_eigenfunction_split <;> assumption)
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel
theorem split_vacuum_eigenvalue_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.T.vDouble_eigenspace_split_of_line hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr p hp
    have h1 := siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.T.vDouble_eigenspace_split_of_line hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S :=
    GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling σ B G.V _ _ hT.base hT.geo.hV v hsp₀ hψ htwo H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)
end GlobalTheory.SplitVacV
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_vacuum_hecke_eigenvalue_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @_root_.GlobalTheory.SplitVacV.split_vacuum_eigenvalue_eq_one | exact _root_.GlobalTheory.SplitVacV.split_vacuum_eigenvalue_eq_one | (intros; apply _root_.GlobalTheory.SplitVacV.split_vacuum_eigenvalue_eq_one <;> assumption)
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.SplitSphLeft
theorem vacuum_fixed_by_split_spherical_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv _ k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt
      (GlobalTheory.SplitSphLeft.isUnram_of_unramified' hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM.vac v
    obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
    have h1 := GlobalTheory.VacTransportLeft.transport_left F E σ B a a' G X om om' hTr v k hk θ hθ _ hSB φ₁ hφ₁ hvac hact
    obtain ⟨c, rfl⟩ := vac_unique_split_left F E σ B a a' G X om om' hTr v hs hψ θ hθ hvac φ₁ hφ₁ h1
    have hc := _root_.GlobalTheory.T.split_vacuum_hecke_eigenvalue_eq_one hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hTr v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
end GlobalTheory.SplitSphLeft
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  first | exact @_root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left | exact _root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left | (intros; apply _root_.GlobalTheory.SplitSphLeft.vacuum_fixed_by_split_spherical_left <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LatStabVac
theorem lattice_vacuum_fixed_outside_finite_set : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum hP F E σ B a a' G X om om' hT
  obtain ⟨S₂, hS₂⟩ := _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum hP F E σ B a a' G X om om' hT
  refine ⟨X.T ∪ S₁ ∪ S₂, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvT, hv₁⟩, hv₂⟩ := hv
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hT.base v with hs | ⟨w, hw⟩
  · exact ⟨hS₁ v hv₁ hs, hS₂ v hv₂ hs⟩
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
    · exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hT v w hw hvT k hk
end GlobalTheory.LatStabVac
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | exact _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | (intros; apply _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LocActV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM
theorem finite_adele_acts_placewise : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector hPr F E σ B a a' G X om om' hT
  have key : ∀ {n : ℕ} (Y : Spc F E n) (M : Model σ Y G.W) (χX χW : Chr F E) (ω : Rep σ Y G.W) (r s r' s' : ℕ),
      GlobalTheory.ThK.IsPair B M χX χW ω r s r' s' →
      (∀ v ∉ S₀, ∀ k ∈ GlobalTheory.InertSph.KAt σ Y v, Acts (evFin F v) (ω (k, 1)) (M.vac v) (M.vac v)) →
      ∀ g : UA σ Y.J, (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) →
      ∀ (f : SInf F (Fin n × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin n × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ SB (Fin n × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = M.vac v) ∧
          (∀ v, φ' v - φ v ∈ augAt ω v) ∧ ω (g, 1) (pure f φ) = pure f φ' := by
    intro n Y M χX χW ω r s r' s' hP hsph g hg f φ hφ hvac
    classical
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all σ Y hP.herm.lat g
    have hfin := Filter.eventually_cofinite.1 hvac
    set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := S₀ ∪ S₁ ∪ hfin.toFinset with hSdef
    obtain ⟨gS, k, hgk, hgS, hkS, hkI, hkL⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ Y g S
    obtain ⟨φ', hφ'SB, hφ'off, hφ'aug, hφ'eq⟩ := GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors σ B Y G.W M χX χW ω r s r' s' hP S gS hgS f φ hφ hvac
    have hk : ω (k, 1) (pure f φ) = pure f φ := by
      refine GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left σ B Y G.W M χX χW ω r s r' s' hP S (fun v hv => hsph v (fun h => hv (by simp [hSdef, h])))
        k (fun u hu => by rw [hkI u hu]; exact hg u hu) hkS (fun w hw z hz => ?_) f φ hφ (fun w hw => ?_)
      · have hw1 : w ∉ S₁ := fun h => hw (by simp [hSdef, h])
        rw [(hkL w hw z hz).1, (hkL w hw z hz).2]
        exact hS₁ w hw1 z hz
      · by_contra hne
        exact hw (by simp [hSdef, hne])
    refine ⟨φ', hφ'SB, ?_, hφ'aug, ?_⟩
    · filter_upwards [hvac, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [hφ'off v hvS, hv]
    · have e : ((g, 1) : UA σ Y.J × UA σ G.W.J) = (gS, 1) * (k, 1) := by
        rw [hgk, Prod.mk_mul_mk, one_mul]
      rw [e, map_mul, Module.End.mul_apply, hk, hφ'eq]
  exact ⟨fun g hg f φ hφ hvac => key G.V G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) (fun v hv => (hS₀ v hv).1) g hg f φ hφ hvac,
    fun g hg f φ hφ hvac => key G.V' G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) (fun v hv => (hS₀ v hv).2) g hg f φ hφ hvac⟩
end GlobalTheory.LocActV
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_action_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  first | exact @_root_.GlobalTheory.LocActV.finite_adele_acts_placewise | exact _root_.GlobalTheory.LocActV.finite_adele_acts_placewise | (intros; apply _root_.GlobalTheory.LocActV.finite_adele_acts_placewise <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem triple_map_comp_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC W, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (g, 1) Φ) = GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) ∧
          ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (g, 1) Φ) = GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL1 := _root_.GlobalTheory.T.triple_invariant_theta_surjective hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL2 := _root_.GlobalTheory.T.local_action_finite_places hPr D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hM.triple
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W (1 : D.host.E) h.JW g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.1 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _), hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.1 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hM.triple.geo.hM hΨ
    have e1 := hTA Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapA
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W₁ (-1 : D.host.E) h.JW₁ g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.2 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv' v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _), hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.2 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ
    have e1 := hTB Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapB
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl
end GlobalTheory.TripleAssembly
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_assembly_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC W, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (g, 1) Φ) = GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) ∧
          ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (g, 1) Φ) = GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | exact _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite <;> assumption)
end
