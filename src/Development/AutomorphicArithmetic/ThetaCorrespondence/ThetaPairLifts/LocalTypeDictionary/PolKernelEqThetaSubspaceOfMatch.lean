module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationKernelCompactVanishing
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealActs Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
private theorem hecke_character_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩
private theorem restriction_eta_pow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring
private def polarizationInductionMap {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
private theorem induced_map_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    polarizationInductionMap π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [polarizationInductionMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl
private theorem acts_zero_at_infinity {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]
theorem polarization_zero_of_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hZ
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hZ
  have hTr := hM.triple
  have hPV : IsPair Bs G.M Xc.β (Xc.β / Xc.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hTr.base, hTr.geo.hV, hTr.geo.hW, hTr.geo.hM, hTr.chars.heckeβ,
      hecke_character_div hTr.chars.heckeβ hTr.chars.heckeα, hTr.chars.resβ,
      restriction_eta_pow_div hTr.chars.resβ hTr.chars.resα rfl, hTr.weil⟩
  have actV := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs a (a + a') G.V G.W G.M _ _ om _ _ _ _ hPV
  obtain ⟨D, hDm, hDi⟩ := actV.2.2.2 k hk
  have hA : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, Acts (evI F) (⇑(om (1, k))) (⇑g) (⇑(D g)) := fun g hg =>
    (hDi g hg (D g)).2 rfl
  have hpure : ∀ i, om (1, k) (pure (f i) (φ i)) = pure (D (f i)) (φ i) := by
    intro i
    have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [T.finite_toSet.compl_mem_cofinite, hTr.geo.hM.std] with v hv hv'
      rw [(hf i).2.2 v hv, hv']
    exact hA (f i) (hf i).1 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 hstd)
  let N := G.M.Pol Bs.ψ Bs.emb
  let π : N →ₗ[ℂ] R.Pi := R.p ∘ₗ N.subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ N.map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ u : N, π u = 0 → π ((D.restrict hDm) u) = 0 := by
    intro u hu
    have := hM.real.cpt k hk u.1 u.2 0 (zero_mem _) (D u.1) 0 (hA u.1 u.2) (acts_zero_at_infinity _)
      (by rw [map_zero]; exact hu)
    rw [map_zero] at this
    exact this
  let ρ := polarizationInductionMap π hπ (D.restrict hDm) ker0
  have hρ : ∀ i, R.p (D (f i)) = ρ (R.p (f i)) := fun i =>
    (induced_map_apply π hπ (D.restrict hDm) ker0 ⟨f i, (hf i).1⟩).symm
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have := congrArg (LinearMap.rTensor _ ρ) hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at this
    simpa only [LinearMap.rTensor_tmul, hρ] using this
end GlobalTheory.PolKerCpt
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_kernel_compact_vanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W Bs.emb, ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, k) Φ) := by
  first | exact @_root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact | exact _root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact | (intros; apply _root_.GlobalTheory.PolKerCpt.polarization_zero_of_compact <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernelDualSpace
section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.PolKerLieV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem polynomialKernel_constTerm_lieDeriv_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  classical
  have exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
      {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
      ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
        (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
          ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
    classical
    unfold GlobalTheory.SquareAgree.algD at hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
      have hfin := Filter.eventually_cofinite.1 hv
      refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
      by_contra h
      exact hvT (hfin.mem_toFinset.2 h)
    | zero =>
      exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
      obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
      refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left]
          exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
        · simp only [Fin.append_right]
          exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
      · rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
    | smul c x _ hx =>
      obtain ⟨T, m, f, φ, h, rfl⟩ := hx
      refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext x
      simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  obtain ⟨T, m, f, φ, hfφ, rfl⟩ := exists_decomp G.M Bs.ψ Bs.emb hΦ
  obtain ⟨D, hDmem, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ G.V G.W G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).1 γ hγ
  have hstd := hM.triple.geo.hM.std
  have hacts : ∀ i, ActsD (evI F) (fun t => ⇑(om (γ (Multiplicative.ofAdd t), 1))) ⇑(f i) ⇑(D (f i)) :=
    fun i => (hD (f i) (hfφ i).1 (D (f i))).2 rfl
  have hrest : ∀ i, Rest (evI F) ⇑(f i) (GlobalTheory.EvZeroInf.finPart (φ i)) := by
    intro i
    refine GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hfφ i).2.1 ?_
    filter_upwards [hstd, (Filter.eventually_cofinite.2 (by simpa using T.finite_toSet) : ∀ᶠ v in Filter.cofinite, v ∉ T)] with v hv hvT
    rw [(hfφ i).2.2 v hvT, hv]
  have hpure : ∀ i x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := by
    intro i x
    rw [GlobalTheory.EvZeroInf.pure_eq_tens, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact hacts i _ (hrest i) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    refine (HasDerivAt.sum (u := Finset.univ) (fun i _ => hpure i x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have hΦ₁ : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  have hp0 : ∀ i, R.p (D (f i)) = 0 := fun i =>
    hM.real.quot.lie γ hγ (f i) (hfφ i).1 (D (f i)) (hacts i)
  refine ⟨T ∪ Xc.T, Finset.subset_union_right, m, fun i => D (f i), φ, fun i =>
    ⟨hDmem _ (hfφ i).1, (hfφ i).2.1, fun v hv => (hfφ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩,
    hΦ₁, ?_⟩
  simp [hp0]
end GlobalTheory.PolKerLieV
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | exact _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | (intros; apply _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MaximalCompactFixedRelPolynomialKernelConstTerm
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
theorem maximalCompact_fixed_rel_polynomialKernel_constTerm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V Bs.emb, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (k, 1) Φ - Φ) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ
  obtain ⟨D, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs a (a + a') G.V G.W G.M Xc.β (Xc.β / Xc.α) om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).2.1 k hk
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hSB hcof hg using fun i => (g i).2
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hcof i, hM.triple.geo.hM.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ i, c i • f i ∈ G.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf i)
  have key : ∀ i, om (k, 1) (pure (c i • f i) (φ i)) = pure (D (c i • f i)) (φ i) := fun i =>
    (hD _ (hmem i) _).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ (hSB i) (hstd i))
  have hp : ∀ i, R.p (D (c i • f i) - c i • f i) = 0 := fun i => by
    rw [map_sub, hM.real.quot.cpt k hk _ (hmem i) _ ((hD _ (hmem i) _).2 rfl), sub_self]
  classical
  let S : Fin n → Finset (Pl F) := fun i => (Filter.eventually_cofinite.1 (hcof i)).toFinset
  refine ⟨Xc.T ∪ Finset.univ.biUnion S, Finset.subset_union_left, n, fun i => D (c i • f i) - c i • f i, φ,
    fun i => ⟨Submodule.sub_mem _ (hDP _ (hmem i)) (hmem i), hSB i, fun v hv => ?_⟩, ?_, ?_⟩
  · by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simpa [S] using h⟩))
  · have e : ∀ i, c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) = pure (c i • f i) (φ i) := fun i => by
      rw [hg i, GlobalTheory.PolMatchLin.pure_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, key, pure_sub, Finset.sum_sub_distrib]
  · simp only [hp, TensorProduct.zero_tmul, Finset.sum_const_zero]
end GlobalTheory.PolKerCpt
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_invariants_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V Bs.emb, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (k, 1) Φ - Φ) := by
  first | exact @_root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm | exact _root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm | (intros; apply _root_.GlobalTheory.PolKerCpt.maximalCompact_fixed_rel_polynomialKernel_constTerm <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernel
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PolKer
theorem polynomialKernel_constTerm_lieDeriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ hΦ hd
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have act := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)
  obtain ⟨D, hDm, hDi⟩ := act.2.2.1 γ hγ
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [T.finite_toSet.compl_mem_cofinite, hM.triple.geo.hM.std] with v hv hs
    rw [(hf i).2.2 v hv, hs]
  have hder : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := fun i x =>
    (hDi (f i) (hf i).1 (D (f i))).2 rfl _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    have eq : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x) =
        fun t : ℝ => ∑ i ∈ Finset.univ, om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply]
    rw [eq]
    exact HasDerivAt.fun_sum (fun i _ => hder i x)
  have e1 : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, e1, ?_⟩
  let π : G.M.Pol Bs.ψ Bs.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, R.p g = 0 → R.p (D g) = 0 := fun g hg h0 => by
    have := hM.real.lie γ hγ g hg 0 (zero_mem _) (D g) 0 ((hDi g hg _).2 rfl)
      (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [h0, map_zero])
    rwa [map_zero] at this
  let A := GlobalTheory.ThK.RealUniq.induced π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu)
  have hA : ∀ i, R.p (D (f i)) = A (R.p (f i)) := fun i =>
    (GlobalTheory.ThK.RealUniq.induced_apply π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu) ⟨f i, (hf i).1⟩).symm
  have := congrArg (A.rTensor _) hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, hA] using this
end GlobalTheory.PolKerLie
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | exact _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | (intros; apply _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv <;> assumption)
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM
  have hiff := GlobalTheory.T.polynomialMatch_zero_iff_pureTensor_image_zero F E σ Bs a a' G Xc om om' R Rf hM
  obtain ⟨h00, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs G Xc om om' R Rf hM.fin
  let K : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        simpa using hlin x y 0 0 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h00⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by
        simpa using hlin 0 x 0 0 c h00 hx.2⟩ }
  have memK : ∀ Φ, Φ ∈ K ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf Φ := fun Φ =>
    ⟨fun h => (hiff Φ).1 h.2, fun h => ⟨GlobalTheory.PolKer.algD_of_polZero Bs G Xc R Rf Φ h, (hiff Φ).2 h⟩⟩
  have one_W : ∀ v, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) := by
    intro v u _; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  refine ⟨K, ⟨⟨fun Φ h => h.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v h hh Φ hΦ
    exact (memK _).2 (GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData F E σ Bs a a' G Xc om om' R Rf hM v h hh Φ ((memK Φ).1 hΦ))
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.polarization_kernel_compact_vanishing hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ ((memK Φ).1 hΦ))
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ ((memK Φ).1 hΦ) hd)
  · intro v g hg Φ hΦ
    exact (memK _).2 (GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero F E σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ)
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.maximalCompact_invariants_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ)
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd)
  · intro hK
    obtain ⟨Φ, hΦ, hn⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero F E σ Bs a a' G Xc om om' R Rf hM
    rw [← hK] at hΦ
    exact hn ((memK Φ).1 hΦ)
  · intro ΦD hΦD
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSubspace_contains_polKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  first | exact @_root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | exact _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | (intros; apply _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match <;> assumption)
end
