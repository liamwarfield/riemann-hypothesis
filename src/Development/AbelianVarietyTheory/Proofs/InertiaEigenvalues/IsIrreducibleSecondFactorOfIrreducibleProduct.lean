module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

open Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.ProdIrr

theorem exists_mem_ind_apply_one {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (hG : ∀ N ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g ∈ K, g ∈ N)
    (P : Subgroup G) (σ : Representation ℂ P W) (hσ : IsSmooth σ) (u : W) :
    ∃ f : smoothPart (ind P σ), f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ p, f.1.1 g = σ p u := by
  classical
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))
  obtain ⟨K, hKo, hKN⟩ := hG N (by simpa using hN)
  have hfix : ∀ p : P, (p : G) ∈ K → σ p u = u := fun p hp => hNS (hKN _ hp)
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩,
    ?_, ?_⟩
  · apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  · show F 1 = u
    have := hF 1 1 K.one_mem
    simpa using this
  · intro g
    show F g = 0 ∨ ∃ p, F g = σ p u
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg; exact Or.inr ⟨p, hF _ _ hc⟩
    · exact Or.inl (hF0 _ hg)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem continuous_leviProj (e : (Σ a, m a) ≃ n) : Continuous (leviProj k e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, leviProj_apply]
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have : (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) =
        fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k) := by
      funext p; rw [map_inv]; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [leviProj_apply]
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _

theorem exists_openSubgroup_GL :
    ∀ N ∈ 𝓝 (1 : GL n k), ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ ∀ g ∈ K, g ∈ N := by
  intro N hN
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset hN
  exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩

theorem exists_indSp_apply_one {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (hρ : IsSmooth ρ) (u : W) :
    ∃ f : IndSp e ρ, f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ l : Levi k m, ∃ c : ℂ, f.1.1 g = c • ρ l u := by
  obtain ⟨f, h1, h2⟩ := exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u
  exact ⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩

end Local

end GlobalTheory.SmGL.ProdIrr

namespace GlobalTheory.SmGL.ProdIrr

theorem isIrreducible_of_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  intro k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩
  classical
  have hI : (prod₂ σ₀ τ).IsIrreducible := (MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi
  obtain ⟨hV, -⟩ := (isIrreducible_iff σ₀).1 hσi
  obtain ⟨hX, hIirr⟩ := (isIrreducible_iff _).1 hI
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
  let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
  have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
  let ρ' := (extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hσs hτs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have h0 : ∀ z : V ⊗[ℂ] W, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))
  rw [isIrreducible_iff]
  refine ⟨hW, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
  have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
    rintro l _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
      exact ⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
        ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have hLR : ∀ y ∈ R, L y ∈ S := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
    { carrier := {f | ∀ g, f.1.1 g ∈ R}
      add_mem' := fun ha hb g => add_mem (ha g) (hb g)
      zero_mem' := fun g => zero_mem R
      smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
  have hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y := fun g f hf x => hf (x * g)
  have hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u := by
    intro u hu
    obtain ⟨f, h1, h2⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
    refine ⟨f, fun g => ?_, h1⟩
    rcases h2 g with h | ⟨l, c, h⟩
    · rw [h]; exact zero_mem R
    · rw [h]; exact R.smul_mem c (hR l u hu)
  have hYtop : Y = ⊤ := by
    refine (hIirr Y hYs).resolve_left fun hY => ?_
    obtain ⟨f, hf, h1⟩ := hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩
    rw [hY, Submodule.mem_bot] at hf
    have : L (x₀ ⊗ₜ s) = 0 := by rw [← h1, hf]; rfl
    rw [hL] at this
    exact smul_ne_zero hφ hs0 this
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, h1, -⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)
  have hf : f ∈ Y := hYtop ▸ Submodule.mem_top
  have h2 := hLR _ (h1 ▸ hf 1)
  rw [hL] at h2
  exact (S.smul_mem_iff hφ).1 h2

end GlobalTheory.SmGL.ProdIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProductStatement
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  first | exact @GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ | exact GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ | (intros; apply GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem hasSupport_of_isSubquotient_prinSeries :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  intro k _ _ _ _ _ n χ hχ π h

  have hd : ∑ a : Fin n, (IrrGL.ofChar (χ a) (hχ a)).1 = n := by
    simp [IrrGL.ofChar]
  refine hasSupport_of_isSubquotient π.irr (fun a => IrrGL.isCusp_ofChar (χ a) (hχ a)) (hd := hd) ?_
  refine h.trans ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ).trans ?_)

  have he : stdBlocks (fun a => (IrrGL.ofChar (χ a) (hχ a)).1) hd =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
    ext ⟨a, i⟩
    rw [stdBlocks_val]
    simp [IrrGL.ofChar, Fin.fin_one_eq_zero i]
    rfl
  unfold prodIrr
  rw [he]

  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin n) (fun _ => Fin 1))
    (fun a => equivRep (IrrRep.det (Fin 1) (χ a) (hχ a)))
  exact IsSubquotient.of_injective φ.toIntertwiningMap (fun u v huv => φ.toLinearEquiv.injective huv)

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotientStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  first | exact @GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries | exact GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries | (intros; apply GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubLoc

theorem sqrtKur_holds (l : ℕ) [Fact l.Prime] : SqrtKur l := fun p hp h4 hne y hy =>
  GlobalTheory.SqrtUnram.sqrt_neg_prime_mem_Kur l p hp h4 (Ne.symm hne) y hy

theorem kw_le_Kur_all : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  intro D i hl2 hq hd w hw
  exact kw_le_Kur_of_ne i (UpperTheory.Small.not_dvd_condN D.host (D.nd.lPrime i).out hl2 hq hd) w hw

end GlobalTheory.HubLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadicStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostCompletion_le_maxUnramified_padic : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  first | exact @GlobalTheory.HubLoc.kw_le_Kur_all | exact GlobalTheory.HubLoc.kw_le_Kur_all | (intros; apply GlobalTheory.HubLoc.kw_le_Kur_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_symm (i : k ≃+* k') (hi : Continuous i) : Continuous i.symm := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k')
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous


variable (k) in
theorem valuation_le_one_iff_ord (x : kˣ) : valuation k (x : k) ≤ 1 ↔ 0 ≤ GlobalTheory.SmGL.ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.ord, neg_nonneg, ← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp [φ]


variable (k) in
theorem valuation_le_one_iff_nabs (x : kˣ) : valuation k (x : k) ≤ 1 ↔ GlobalTheory.SplitWeil.nabs k x ≤ 1 := by
  rw [valuation_le_one_iff_ord, GlobalTheory.LGrp.nabs_eq_zpow,
    zpow_le_one_iff_right₀ (by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k)]
  omega

theorem nabs_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x :=
  GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi (continuous_symm i hi) x

theorem valuation_map_le_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := valuation_le_one_iff_nabs k' (Units.map i.toRingHom.toMonoidHom (Units.mk0 x hx))
  rw [nabs_map i hi, ← valuation_le_one_iff_nabs k] at h
  simpa using h

theorem map_integer (i : k ≃+* k') (hi : Continuous i) :
    (𝒪[k] : Subring k).map i.toRingHom = 𝒪[k'] := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Valuation.mem_integer_iff _ _).2 ((valuation_map_le_one_iff i hi x).2 ((Valuation.mem_integer_iff _ _).1 hx))
  · intro hy
    refine ⟨i.symm y, (Valuation.mem_integer_iff _ _).2 ?_, i.apply_symm_apply y⟩
    rw [← valuation_map_le_one_iff i hi, RingEquiv.apply_symm_apply]
    exact (Valuation.mem_integer_iff _ _).1 hy

theorem resCard_eq (i : k ≃+* k') (hi : Continuous i) : GlobalTheory.SplitWeil.resCard k' = GlobalTheory.SplitWeil.resCard k := by
  let e : 𝒪[k] ≃+* 𝒪[k'] := (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (map_integer i hi))
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

theorem ord_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SmGL.ord k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.ord k x := by
  have h := nabs_map i hi x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq i hi] at h
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  exact neg_inj.1 (zpow_right_injective₀ (by linarith) hq.ne' h)

theorem absPow_map (i : k ≃+* k') (hi : Continuous i) (s : ℂ) (x : kˣ) :
    GlobalTheory.SmGL.absPow k' s (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.absPow k s x := by
  ext
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.SmGL.val_absPow, nabs_map i hi]

end GlobalTheory.LocalFieldIso

theorem GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact ⟨GlobalTheory.LocalFieldIso.continuous_symm i hi, GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi,
    GlobalTheory.LocalFieldIso.ord_map i hi, GlobalTheory.LocalFieldIso.resCard_eq i hi, GlobalTheory.LocalFieldIso.absPow_map i hi⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  first | exact @GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | exact GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation | (intros; apply GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : WO S T, IsHalf (cA D a) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f


open Classical in
def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (f : WO S T → ℂ)
    (x : WO S T) : ℂ :=
  if IsHalf a x then ℓ (heisO ψ S T x f) else 0

def HasShape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (Φ f : WO S T → ℂ) : Prop :=
  ∀ ℓ, InvForm ψ S T a ℓ → ∃ c : ℂ, ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = c * Φ x

def locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {φ | ∃ u : WO S T, IsHalf (a + cA D a) u ∧ φ = heisO ψ S T u f}


open Classical in
def adjDat (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D)
    (ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ) (x : WO S T) : ℂ :=
  if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then ω (fun PP => redM PP (frMapAdj S T βS βT x)) else 0

def translT (S T : HSp D) (a : AE D) (Φ : WO S T → ℂ) : Set (WO S T → ℂ) :=
  {Ψ | ∃ g : GA D T, SuppAt a T g ∧ Ψ = fun x => Φ (actO S T 1 g x)}

abbrev latH (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True

def LevChart (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) : Prop :=
  Function.Surjective φ ∧ (∀ z, φ z = 0 ↔ toEAf D e * z = 0) ∧
    (∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F) ∧
    ∀ (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (o : GlobalTheory.SplitHecke.Ov D v), (o : Fv D.host.F v) = φ s →
      ι (resS D.host.F PP s) = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o

def rdAdj (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) :=
  (frMapAdj S T βS βT x).map φ

end GlobalTheory.DownLift.SplitCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
noncomputable section

namespace GlobalTheory.TopSteps.CrysRules

open GlobalTheory.AdmLoc Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct Module
open GlobalTheory.TwistJump GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem multV_of_only_zero {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (h : ∀ a, IsJumpV PD ρ τ a → a = 0) (a : ℤ) :
    multV PD ρ τ a = if a = 0 then (finrank LL (DdRE PD ρ τ) : ℤ) else 0 := by
  have hs : ∀ a : ℤ, a ≠ 0 → FildR PD ρ τ (a + 1) = FildR PD ρ τ a := fun a ha => by
    by_contra hne
    exact ha (h a hne)
  split_ifs with ha
  · subst ha
    have h0 : ∀ b ≤ (0 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 0 := fun b hb => by
      induction b, hb using Int.leInductionDown with
      | base => rfl
      | pred n hn ih => rw [← hs (n - 1) (by omega), sub_add_cancel, ih]
    have h1 : ∀ b ≥ (1 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 1 := fun b hb => by
      induction b, hb using Int.leInduction with
      | base => rfl
      | succ n hn ih => rw [hs n (by omega), ih]
    have e0 : FildR PD ρ τ 0 = DdRE PD ρ τ := by
      refine le_antisymm inf_le_left fun x hx => ?_
      obtain ⟨b, hb⟩ := filV_exh PD (LL := LL) x
      rw [← h0 (min b 0) (min_le_right _ _)]
      exact ⟨hx, filV_anti PD (min_le_left b 0) hb⟩
    have e1 : FildR PD ρ τ (0 + 1) = ⊥ := by
      rw [eq_bot_iff, zero_add]
      intro x hx
      refine filV_sep PD (LL := LL) x fun b => ?_
      rw [← h1 (max b 1) (le_max_right _ _)] at hx
      exact filV_anti PD (le_max_left b 1) hx.2
    rw [multV, e0, e1]
    simp
  · rw [multV, hs a ha, sub_self]

theorem ddRE_ne_bot [Algebra.IsSeparable Qp K] (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (ν : Representation LL G LL) (χ : G → LL) (hν : ∀ g x, ν g x = χ g • x)
    {m : ℕ} (k : Fin m → ℤ) (β : Fin m → BdR) (d : Fin m → LL ⊗[Qp] BdR)
    (hd : ∀ i, d i ∈ DdR PD ν ∧ d i ∈ FilV PD (LL := LL) (V := LL) (k i))
    (h1 : (1 : LL ⊗[Qp] BdR) =
      ∑ i, AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (LinearMap.mulLeft Qp (β i)) (d i))
    (τ : K →ₐ[Qp] LL) : DdRE PD ν τ ≠ ⊥ := by
  intro h0
  have hm := GlobalTheory.BlockJumps.multV_twist PD hs (1 : Representation LL G LL) 0 (fun g x => by simp) τ 0
  have hb : FildR PD (1 : Representation LL G LL) τ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hz : ∀ i, act LL (AlgHom.id LL LL) (d i) y = 0 := fun i => by
      have := act_maps PD (AlgHom.id LL LL) 1 ν τ (hd i).2 (fun g y hy => by
        have hi : actVdR PD ν g (d i) = d i := by
          have := (Submodule.mem_iInf _).1 (hd i).1 g
          simpa [sub_eq_zero] using this
        rw [actVdR_twist PD 1 ν g (χ g) (fun x => by simp [hν]), actVdR_act, hy, ← LinearMap.smul_apply,
          ← map_smul, ← actVdR_char PD ν g (χ g) (hν g), hi]) y hy
      have h2 := this.1
      rw [h0] at h2
      exact h2
    have : y = act LL (AlgHom.id LL LL) (1 : LL ⊗[Qp] BdR) y := by rw [map_one]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.mem_bot, this, h1, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mulLeft, map_mul, Module.End.mul_apply, hz, map_zero]
  rw [multV, hb] at hm
  simp at hm
  omega

end Generic

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K LL : FinExt l)
include T

theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD K).Fil (-1), (P.PD K).ι (P.PD K).t * s = 1 := by
  obtain ⟨s, hs, h⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  refine ⟨s, ?_, by rw [P.PD_ι, P.period_datum_t_eq, h]⟩
  rw [← SetLike.mem_coe, P.PD_Fil K (Formalism.MainNotions.LocalSituation.botExt l)]
  exact hs

theorem isDR {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  refine (GlobalTheory.DRFil.isDR_of_isCrys (P.PD K) (fun m c hc b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m c hc b ?_) ρ h2 h).1
  simpa only [P.PD_ι] using hb

theorem multV_shift {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ)
    (h : ∀ a, multV (P.PD K) (charRep θ) τ a = (({b} : Multiset ℤ).count a : ℤ)) (a : ℤ) :
    multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  haveI := (P.PD K).finK
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) (isDR T K LL _ hθ) 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  have key := finrank_twist (P.PD K) (AlgHom.id ↥LL.1 ↥LL.1) ρ ρ' (charRep θ) (fun g => (θ g : ↥LL.1))
    (fun _ _ => rfl) hρ k β d hd h1 τ b (fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl)
  rw [multV, multV, add_right_comm, key, key]

theorem isCrys_iff {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ)) :
    IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ' := by
  obtain ⟨hq, ht, hd⟩ := GlobalTheory.RegularRing.quot_tensor_dual_crys l P AI (GlobalTheory.Per.IsStd.of_tied T)
  exact GlobalTheory.TwistCrys.isCrys_twist_iff (P.PD K) (ht K LL) (hq K LL) (hd K LL) ρ ρ' (charRep θ)
    (fun g => (θ g : ↥LL.1)) LinearMap.id 1 rfl (fun _ _ => rfl) hρ hθ

variable {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))

theorem crysWith_cyc (θ : ↥(GK K) →* (↥LL.1)ˣ) (e : ℕ) (hθ : θ = cycLL (P.PD K) ↥LL.1 ^ (-(e : ℤ))) :
    CrysWith (P.PD K) emb (charRep θ) (fun _ => {(e : ℤ)}) := by
  haveI := (P.PD K).finK
  haveI := LL.2
  subst hθ
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow (P.PD K) _, fun i τ _ a => ?_⟩
  rw [GlobalTheory.BlockJumps.multV_twist (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) _ e (fun g x => ?_) τ a, Multiset.count_singleton]
  · split_ifs <;> rfl
  · simp [charRep, cycLL]

theorem crysWith_inv (θ : ↥(GK K) →* (↥LL.1)ˣ) (a : ZMod n → ℤ)
    (h : CrysWith (P.PD K) emb (charRep θ) (fun i => {a i})) :
    CrysWith (P.PD K) emb (charRep θ⁻¹) (fun i => {-a i}) := by
  have h1 := crysWith_cyc T K LL emb 1 0 (by simp)
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (θ g : ↥LL.1) • charRep θ⁻¹ g x := fun g x => by
    simp [charRep]
  refine ⟨(isCrys_iff T K LL _ _ θ hρ h.1).2 h1.1, fun i τ hτ c => ?_⟩
  rw [← multV_shift T K LL _ _ θ hρ h.1 τ (a i) (h.2 i τ hτ) c, h1.2 i τ hτ, Multiset.count_singleton,
    Multiset.count_singleton]
  congr 1
  exact if_congr (by omega) rfl rfl

theorem isCrysChar_inv (θ : ↥(GK K) →* (↥(OL LL))ˣ) (a : ZMod n → ℤ) (h : IsCrysChar (P.PD K) emb θ a) :
    IsCrysChar (P.PD K) emb θ⁻¹ (fun i => -a i) := by
  refine ⟨(h.1.comp continuous_inv).congr fun g => by
    rw [Function.comp_apply, map_inv, MonoidHom.inv_apply], ?_⟩
  have e : chiLL ↥LL.1 θ⁻¹ = (chiLL ↥LL.1 θ)⁻¹ := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.inv_apply, ← map_inv]
    exact congrArg (Units.map _) (map_inv θ g).symm
  rw [e]
  exact crysWith_inv T K LL emb _ a h.2

theorem multV_char_zero (hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (θ : ↥(GK K) →* (↥LL.1)ˣ) (hθ : IsCrys (P.PD K) (charRep θ)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (h : ∀ a, IsJumpV (P.PD K) (charRep θ) τ a → a = 0) (a : ℤ) :
    multV (P.PD K) (charRep θ) τ a = (({0} : Multiset ℤ).count a : ℤ) := by
  classical
  haveI := (P.PD K).finK
  have hdr := isDR T K LL _ hθ
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL ↥LL.1 (charRep θ)).1
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) hdr 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  set_option synthInstance.maxHeartbeats 200000 in
  have hpos : ∀ τ', 1 ≤ finrank ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') := fun τ' => by
    haveI : FiniteDimensional ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) (charRep θ)) inf_le_left
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact ddRE_ne_bot (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) (charRep θ) (fun g => (θ g : ↥LL.1)) (fun _ _ => rfl) k β d
      (fun i => ⟨(hd i).1, (hd i).2.1⟩) h1 τ'
  rw [Nat.card_eq_fintype_card] at hc
  have hsum := (GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc (charRep θ)).1
  rw [hdr, finrank_self, mul_one, ← hc, ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum
  have hone := (Finset.sum_eq_sum_iff_of_le fun τ' _ => hpos τ').1 hsum τ (Finset.mem_univ _)
  rw [multV_of_only_zero (P.PD K) _ τ h, ← hone, Multiset.count_singleton]
  split_ifs <;> rfl


omit T in
theorem card_emb {lam : ↥(OL LL)} (h : Standing P K LL emb lam) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have e : K0 K = K.1 := inf_eq_left.2 h.2.1.1
  rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
    ← Nat.card_congr (Equiv.ofBijective _ h.2.2.2.1), Nat.card_zmod, h.2.2.1]

end Tied

theorem crysCalc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (S : TopSit P) : S.CrysCalc := by
  obtain ⟨T⟩ := hT
  refine ⟨fun A A' A'' U U' e he h h' => ⟨?_, fun i τ hτ a => ?_⟩,
    fun A U θ a h hθ => ⟨⟨?_, fun i τ hτ c => ?_⟩, isCrysChar_inv T _ _ _ θ a hθ⟩, ?_, fun μ hc hμ => ?_⟩
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ e.symm (fun g x => ?_)
      (GlobalTheory.Cmp.WachMonoidal.isCrys_prod _ h.1 h'.1)
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
    rfl
  · haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T S.K S.LL _ A.ρ).1
    haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T S.K S.LL _ A'.ρ).1
    rw [GlobalTheory.HTW.SumJumps.multV_add _ e he, h.2 i τ hτ, h'.2 i τ hτ, Multiset.count_add, Nat.cast_add]
  · exact (isCrys_iff T _ _ _ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1).1 h.1
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + a i := ⟨c - a i, by ring⟩
    rw [multV_shift T _ _ A.ρ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1 τ (a i) (hθ.2.2 i τ hτ) c, h.2 i τ hτ,
      Multiset.count_map_eq_count' _ _ (add_left_injective (a i))]
  · have hε := S.hyp.2.1.2.2.2
    have e : chiLL ↥S.LL.1 S.Γ.ε = cycLL (P.PD S.K) ↥S.LL.1 := by
      ext g : 2
      exact hε g
    refine ⟨(GlobalTheory.Survey.SlowDecayFunctions.continuous_cyc P S.K S.LL).congr fun g => (hε g).symm, ?_⟩
    have := crysWith_inv T _ _ S.emb _ (fun _ => ((1 : ℕ) : ℤ))
      (crysWith_cyc T S.K S.LL S.emb (cycLL (P.PD S.K) ↥S.LL.1)⁻¹ 1 (by simp))
    rw [inv_inv, ← e] at this
    exact this
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.unramified_isCrys_and_jump_eq_zero l P AI T S.K S.LL (charLat ℚ_[l] Subtype.val_injective μ hc)
      (fun g hg x => by
        change (chiLL ↥S.LL.1 μ g : ↥S.LL.1) • x = x
        simp [hμ g hg])
    exact ⟨hc, h1, fun i τ _ a => multV_char_zero T _ _ (card_emb _ _ _ S.hyp.1) _ h1 τ (h2 τ) a⟩

end GlobalTheory.TopSteps.CrysRules
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumpsStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ S : TopSit P, S.CrysCalc := by
  first | exact @GlobalTheory.TopSteps.CrysRules.crysCalc | exact GlobalTheory.TopSteps.CrysRules.crysCalc | (intros; apply GlobalTheory.TopSteps.CrysRules.crysCalc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.DefU

theorem exists_hasWeightAt_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam :=
  fun E _ _ _ n _ π hπ τ => (GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.DefU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam := by
  first | exact @GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | exact GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | (intros; apply GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

abbrev OI (v : FinPl D) : Type := v.adicCompletionIntegers D.host.F

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u, IsHalf e u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

def InPow {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, x i j = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)

def Bdd {v : FinPl D} (ϖ : OI v) (N : ℕ) {m n : Type} (x : Matrix m n (Fv D.host.F v)) : Prop :=
  ∀ i j, ∃ o : OI v, algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * x i j = algebraMap (OI v) (Fv D.host.F v) o

def comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  c.sum fun u z => z • heisO ψ S T u f

def RelOff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (p f : WO S T → ℂ) : Prop :=
  ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) → comb ψ S T c p = 0 → comb ψ S T c f = 0

def CoEig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p f : WO S T → ℂ) (u : WO S T) : Prop :=
  ∃ c : ℂ, heisO ψ S T u p = c • p ∧ heisO ψ S T u f = c • f

def Shape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (A : Set (WO S T)) (x₀ : WO S T) (f : WO S T → ℂ) : Prop :=
  (∀ z ∈ A, heisO ψ S T z f = f) ∧
    ∀ y, IsHalf e y → (∀ z ∈ A, ψ (symplO S T z y) = 1) → heisO ψ S T y f = ψ (symplO S T x₀ y) • f

def halfPow {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) (ϖ : OI v) (N : ℕ) : Set (WO S T) :=
  {z | IsHalf (cA D e) z ∧ InPow ϖ N (adjCo φ S T BS BT z)}

def rowIx {n r t : ℕ} (h : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def co {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) {r t : ℕ} (hS : r + t = S.rank) (hT : r = T.rank) (x : WO S T) :
    Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v) :=
  (adjCo φ S T BS BT x).submatrix (rowIx hS) (finCongr hT)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rank_V (i : Fin D.R.m) : D.R.r + D.R.t = (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem rank_weight_component_eq (i : Fin D.R.m) : D.R.r = (Wc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm

def coR (R : RealDat D A Ks) (i : Fin D.R.m) {v : FinPl D} (φ : SplitProj D v) (x : WO (Vc D i) (Wc D i)) :
    Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) :=
  co φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (rank_V i) (rank_weight_component_eq i) x

def ActAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) {v : FinPl D} (φ : SplitProj D v) (e : AE D)
    (red : OI v →+* kP PP) : Prop :=
  ∀ h : GL (Fin (Vc D i).rank) (OI v), ∃ κ : GA D (Vc D i), Formalism.L2.Theta.SuppAt e (Vc D i) κ ∧ κ ∈ GfC (Vc D i) ∧
    finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) ∧
    grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h ∧
    redFn (R.βV i) PP (finE (Vc D i) κ) = Matrix.GeneralLinearGroup.map red h ∧
    (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) ∧
    ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      ℓ (R.ωP i t (κ, 1) f) = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map red h)) : ℂˣ) : ℂ) * ℓ f

theorem placeIdem_eq {v : FinPl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε = idem D (.inl v) := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', e', h1', h2'⟩ := ((GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v).2.2
  have : α = α' := by
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst hw; exact h1.trans h1'.symm
    · exact (h2 w hw).trans (h2' w hw).symm
  rw [this, ← e']
  rfl

theorem suppIn_of_suppAt {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {Sb : Finset (FinPl D)}
    (hv : v ∈ Sb) {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) : SuppIn Sb V g := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hg' : ∀ i j, idem D (.inl v) * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j := fun i j => by
    rw [← he.2.1]; exact hg i j
  refine ⟨Matrix.ext fun i j => ?_, fun w hw ε hε i j => ?_⟩
  · rw [Matrix.map_apply, ← hg', map_mul, (h4 v).1, zero_mul]; rfl
  · rw [placeIdem_eq hε, ← hg', ← mul_assoc, h2 _ _ (fun h => hw (by rw [Sum.inl.inj h]; exact hv)), zero_mul]

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.LFun.SatBridge

theorem hasSatGL_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  intro E _ _ w n V _ _ π α
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π _).2 ⟨α, rfl, h⟩)

end GlobalTheory.LFun.SatBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeriesStatement
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  first | exact @GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake | exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake | (intros; apply GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial

namespace GlobalTheory.TypeAbove

theorem conj_over_split (D : D7) {p : ℕ} {w w' : PlE D.host} (hw : w ∈ placesOver D.host.E p)
    (hs : IsSplitPl D.host w) (hc : IsConjPl D.host w w') :
    w' ∈ placesOver D.host.E p ∧ IsSplitPl D.host w' := by
  have h := (GlobalTheory.ConjPlaceOff.isConjPl_iff D w w').1 hc
  refine ⟨?_, ?_⟩
  · have e := (h ((p : ℕ) : 𝓞 D.host.E)).1 hw
    rwa [map_natCast] at e
  · obtain ⟨x, hx, hcx⟩ := (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w).1 hs
    exact (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w').2 ⟨_, (h x).1 hx, fun h' => hcx ((h _).2 h')⟩

end GlobalTheory.TypeAbove
end
