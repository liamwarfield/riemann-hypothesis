module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepLatticeHyperbolicEmbedding
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoH
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem orbit_cont : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ Λ : schwartzA θ V.rank n →ₗ[ℂ] ℂ,
      ContinuousOn (fun g : G D n => Λ (ω g Φ)) (K D n : Set (G D n)) := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ Λ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  have hcont := GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hchart
  let K' : Subgroup (GA D (dblSp A)) := (K D A.rank).comap κ.toMonoidHom
  have hK' : IsCompact (K' : Set (GA D (dblSp A))) := by
    have h1 : (K' : Set (GA D (dblSp A))) = κ.symm '' (K D A.rank : Set (G D A.rank)) := by
      ext g
      simp only [K', Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hg; exact ⟨κ g, hg, κ.symm_apply_apply g⟩
      · rintro ⟨k, hk, rfl⟩; simpa using hk
    rw [h1]
    exact (GlobalTheory.StdUnn.HeightExists.isCompact_K).image hcont.2
  have hkf : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.IsKFinVec omh K' f :=
    GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ
      (GlobalTheory.CartStd.isCartanInv_stdInv D A μ' hsk s' hstd') hs K' hK' (fun k hk τ => hcomm k hk τ) f hfock
  let Vf : Submodule ℂ (WO (dblSp A) V → ℂ) := Submodule.span ℂ {g | ∃ k ∈ K', g = omh (k, 1) f}
  have : FiniteDimensional ℂ Vf := hkf
  have hVth : ∀ v ∈ Vf, IsThetaFunO ψ₀ (dblSp A) V v := by
    intro v hv
    have hle : Vf ≤ Formalism.IndefR.Eqv.thetaSubO ψ₀ (dblSp A) V := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, -, rfl⟩
      exact hdat.om_pres _ f hf
    exact hle hv

  let Sv : Vf →ₗ[ℂ] schwartzA θ V.rank n :=
    { toFun := fun v => ⟨sch ψ₀ A V μ 𝓕 v.1, hschS v.1 (hVth v.1 v.2)⟩
      map_add' := fun v w => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 w.1 (hVth v.1 v.2) (hVth w.1 w.2) 1).2.2.1
      map_smul' := fun c v => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 v.1 (hVth v.1 v.2) (hVth v.1 v.2) c).2.2.2 }
  have hΛc : Continuous (Λ ∘ₗ Sv) := LinearMap.continuous_of_finiteDimensional _

  have hmemK : ∀ g : G D A.rank, g ∈ K D A.rank → κ.symm g ∈ K' := by
    intro g hg
    show κ (κ.symm g) ∈ K D A.rank
    rw [κ.apply_symm_apply]
    exact hg
  let o : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) → Vf := fun g =>
    ⟨omh (κ.symm g.1, 1) f, Submodule.subset_span ⟨κ.symm g.1, hmemK g.1 g.2, rfl⟩⟩
  have hκs : Continuous (fun g : G D n => κ.symm g) := hcont.2
  have hval : Continuous (fun g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) => (g.1 : G D n)) :=
    continuous_subtype_val
  have ho : Continuous o := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun w => ?_
    exact (hdat.om_cont f hf w).comp ((hκs.comp hval).prodMk continuous_const)
  have heq : ∀ g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))), Λ (ω g.1 Φ) = (Λ ∘ₗ Sv) (o g) := by
    intro g
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 1
    apply Subtype.ext
    have := htr (κ.symm g.1) f hf Φ hfΦ.symm
    rw [show κ (κ.symm g.1) = g.1 from κ.apply_symm_apply g.1] at this
    exact this
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Set.domRestrict (K D n : Set (G D n)) fun g => Λ (ω g Φ)) = (Λ ∘ₗ Sv) ∘ o := funext heq
  rw [this]
  exact hΛc.comp ho

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoA
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

theorem fock_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan D ψ₀ (dblSp A) V 1 χ⁻¹ omh hdat θ hθ s' s' s (κ.symm k)
      (fun τ => (hcomm (κ.symm k) hkk τ).symm) f hfock
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at this
  exact this.symm ▸ hmem

theorem l_ne_zero : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ τ, l τ ≠ 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl τ h0
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  have h := habs τ
  rw [h0, abs_zero] at h
  have hx : ‖tauE D τ D.host.xi0‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  have hm : ‖tauE D τ μ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 hsk.1)
  exact (div_ne_zero hx hm) h.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoE
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem eval_aeval_subst {σ τ' : Type} (x : τ' → ℂ) (f : σ → MvPolynomial τ' ℂ) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval f p) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

def intW (D : D7) (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) where
  carrier := {a | ∀ i j, a i j ∈ intAE D}
  add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => (intAE D).zero_mem
  neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j)


open Classical in
def g0 (D : D7) (m n : ℕ) : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
  if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ intW D m n) = 0 then (1 : ℂ) else 0

theorem gaussian_mem_schwartz_bruhat (D : D7) (m n : ℕ) : g0 D m n ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  classical
  have hWe : ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  convert GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0 using 1
  funext a
  unfold g0
  exact if_congr Iff.rfl rfl rfl

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  unfold g0
  split_ifs with h
  · rfl
  · exact (h ((QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem)).elim

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ :=
  fun x => gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ := by
  refine Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, ?_, ?_⟩
  · intro v hv
    simp at hv
  · funext x
    simp [psi0, evalPoly]

def xL (θ : InfFam D) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) : Mx D m n := lineAt θ τ Z 1

theorem compAt_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun τ' => compAt θ τ' (xL θ τ Z)) = GlobalTheory.FockAnnKill.dirAt τ Z := by
  have h := GlobalTheory.FockAnnKill.compAt_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext τ'
  have h0 : compAt θ τ' (0 : Mx D m n) = 0 := by
    ext i j
    simp [compAt]
  simp [h0]

theorem finPart_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun i j => finPart D ((xL θ τ Z) i j)) = 0 := by
  have h := GlobalTheory.FockAnnKill.finPart_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext i j
  simp

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem dirAt_ne {m : ℕ} {τ τ' : D.what₂.Tau} (h : τ' ≠ τ) (Z : Matrix (Fin m) (Fin n) ℂ) :
    GlobalTheory.FockAnnKill.dirAt τ Z τ' = 0 := by
  exact if_neg h

theorem dirAt_self {m : ℕ} (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin n) ℂ) : GlobalTheory.FockAnnKill.dirAt τ Z τ = Z := by
  exact if_pos rfl

theorem gAway_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin n) ℂ) : gAway V l s τ (GlobalTheory.FockAnnKill.dirAt τ Z) = 1 := by
  classical
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ' with τ' ≠ τ, ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ Z τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ Z τ').trace) = 1
  rw [Finset.sum_eq_zero fun τ' hτ' => by rw [dirAt_ne (Finset.mem_filter.mp hτ').2 Z]; simp,
    mul_zero, Complex.exp_zero]

theorem trace_conjTranspose_mul_self {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (uᴴ * u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

theorem gauss_dirAt {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (l : D.what₂.Tau → ℝ) (u : Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) = gs (cLoc l τ) u := by
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ', ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').trace) =
    Complex.exp (-(((2 * Real.pi * |l τ|) * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ))
  have key : (fr * u)ᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) = uᴴ * u := by
    rw [Matrix.conjTranspose_mul,
      show uᴴ * frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) =
        uᴴ * (frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * fr) * u by simp only [Matrix.mul_assoc],
      hfr.2.2, Matrix.mul_one]
  rw [Finset.sum_eq_single τ (fun τ' _ h => by rw [dirAt_ne h]; simp)
      (fun h => absurd (Finset.mem_univ τ) h), dirAt_self, key, trace_conjTranspose_mul_self]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000


open Classical in
def substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    PX m n :=
  aeval (fun v : D.what₂.Tau × Fin m × Fin n × Bool => if v.1 = τ then
      (if v.2.2.2 then ∑ c, C (star (fr v.2.1 c)) * X (c, v.2.2.1, true) else ∑ c, C (fr v.2.1 c) * X (c, v.2.2.1, false))
    else 0) p

theorem evX_substP {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (u : Matrix (Fin m) (Fin n) ℂ) :
    evX (substP τ fr p) u = evalPoly p (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) := by
  classical
  unfold evX substP evalPoly
  rw [eval_aeval_subst]
  refine congrArg (fun x => MvPolynomial.eval x p) (funext fun v => ?_)
  obtain ⟨τ', a, j, b⟩ := v
  by_cases hτ : τ' = τ
  · subst hτ
    rw [if_pos rfl, dirAt_self]
    cases b
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Bool.false_eq_true, ↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [↓reduceIte, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, map_sum, Complex.star_def]
  · rw [if_neg hτ, dirAt_ne hτ]
    cases b <;> simp

theorem slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) :
    ∀ F ∈ fockA θ V n l s, ∃ Q : PX V.rank n, ∀ u : Matrix (Fin V.rank) (Fin n) ℂ,
      F (xL θ τ (fr * u)) = evX Q u * gs (cLoc l τ) u := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, g, -, rfl⟩ := hF
    refine ⟨C (g 0) * substP τ fr p, fun u => ?_⟩
    show evalPoly p (fun τ' => compAt θ τ' (xL θ τ (fr * u))) * gauss V l s (fun τ' => compAt θ τ' (xL θ τ (fr * u))) *
        g (fun i j => finPart D ((xL θ τ (fr * u)) i j)) = _
    rw [compAt_xL hθ, finPart_xL hθ, gauss_dirAt hfr, ← evX_substP]
    simp only [evX, map_mul, eval_C]
    ring
  | zero => exact ⟨0, fun u => by simp [evX]⟩
  | add F G _ _ hF hG =>
    obtain ⟨Q₁, h₁⟩ := hF
    obtain ⟨Q₂, h₂⟩ := hG
    refine ⟨Q₁ + Q₂, fun u => ?_⟩
    simp only [Pi.add_apply, h₁, h₂, evX, map_add (f := _)]
    ring
  | smul a F _ hF =>
    obtain ⟨Q, h⟩ := hF
    refine ⟨C a * Q, fun u => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, h, evX, map_mul, eval_C]
    ring

theorem tens_slice {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) (f : (Fin V.rank → Fin n → ℂ) → ℂ)
    (hf : tens θ τ fr f (psi0 θ V n l s τ) ∈ fockA θ V n l s) : ∃ Q : PX V.rank n, f = fP (cLoc l τ) Q := by
  obtain ⟨Q, hQ⟩ := slice hθ hfr l _ hf
  refine ⟨Q, funext fun (u : Matrix (Fin V.rank) (Fin n) ℂ) => ?_⟩
  have h := hQ u
  have hinv : fr⁻¹ * (fr * u) = u := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
  have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
    have := congrFun (compAt_xL hθ τ (fr * u)) τ
    simpa [dirAt_self] using this
  have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
    unfold psi0
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
    simp only [one_mul]
    exact gaussian_at_zero_eq_one D V.rank n
  simp only [tens] at h
  rw [hc, hinv, hp, mul_one] at h
  exact h

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoB
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem compFin_eq_finPart (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v z =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem reidx_conjTranspose_mul (y : M2 n) : (reidx y)ᴴ * reidx y = reidx (yᴴ * y) := by
  simp only [reidx, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := by
  simp [reidx]

theorem compAt_cT_mul {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (τ' : D.what₂.Tau) :
    compAt θ τ' (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) =
      (compAt θ τ' M)ᴴ * compAt θ τ' M := by
  obtain ⟨-, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact hcA (M l i) τ'

theorem cT_one {m : ℕ} : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (1 : Matrix (Fin m) (Fin m) (AE D)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem iota_mem_K {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι)
    (k : GR n) (hk : InK (mR k)) : ι k ∈ K D n := by
  obtain ⟨hinf0, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  obtain ⟨-, hcomp⟩ := hι
  obtain ⟨hτ, hτ', hfin⟩ := hcomp k
  rw [K, GlobalTheory.RegSch.EmbLevel.mem_levelAll_iff]
  set M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (ι k)).1 with hM
  have hMm : M = mat (ι k) := rfl
  refine ⟨fun v y => ?_, fun w => ?_⟩
  · have h1 : M.map (compFin D.host.F D.host.E v) = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      rw [compFin_eq_finPart]
      have := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply] at this
      rw [← hMm] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1, Matrix.one_mulVec]
  ·
    have key : ∀ i j, compInf D.host.F D.host.E w
        ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) M * M) i j - (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)) i j) = 0 := by
      intro i j
      refine ((hinf0 _).2 ?_) w
      intro τ'
      have hc := compAt_cT_mul hθ M τ'
      have hrow : θ τ' (infPart D ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) i j)) =
          ((compAt θ τ' M)ᴴ * compAt θ τ' M) i j := congrFun (congrFun hc i) j
      rw [map_sub, map_sub, hrow]
      by_cases hττ : τ' = τ
      · subst hττ
        have e : compAt θ τ' M = reidx (mR k) := hτ
        rw [e, reidx_conjTranspose_mul, hk.2, reidx_one]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
      · have e : compAt θ τ' M = 1 := hτ' τ' hττ
        rw [e, Matrix.conjTranspose_one, Matrix.one_mul]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
    simp only [inv_one, Units.val_one, cT_one, Matrix.mul_one]
    ext i j
    have := key i j
    rw [map_sub, sub_eq_zero] at this
    simpa only [Matrix.map_apply] using this

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {n : ℕ}

def reIm {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
  else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def reImInv {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
  else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem evX_eq_zero {m : ℕ} (P : PX m n) (h : ∀ u : Fin m → Fin n → ℂ, evX P u = 0) : P = 0 := by
  have h2 : (C (1 / 2 : ℂ) + C (1 / 2) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = 1 := by
    rw [← C_add, ← C_1]
    norm_num
  have hI : (C Complex.I * C (1 / (2 * Complex.I)) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = C (1 / 2) := by
    rw [← C_mul]
    congr 1
    field_simp
  have hinv : ∀ k, bind₁ reImInv (reIm (n := n) (m := m) k) = X k := by
    rintro ⟨a, i, b⟩
    cases b
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination (X (a, i, false) - X (a, i, true)) * hI + X (a, i, false) * h2
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hI + X (a, i, true) * h2
  have hQ : bind₁ reIm P = 0 := by
    apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
    intro u
    let z : Fin m → Fin n → ℂ := fun a i => (u (a, i, false) : ℂ) + Complex.I * (u (a, i, true) : ℂ)
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ reIm P) = 0
    rw [eval₂Hom_bind₁]
    have hf : (fun k => eval₂Hom (RingHom.id ℂ) (fun v => ((u v : ℝ) : ℂ)) (reIm (n := n) (m := m) k)) =
        fun k => if k.2.2 = true then star (z k.1 k.2.1) else z k.1 k.2.1 := by
      funext ⟨a, i, b⟩
      cases b
      · simp [reIm, z]
      · apply Complex.ext <;> simp [reIm, z]
    rw [hf]
    exact h z
  calc P = bind₁ reImInv (bind₁ reIm P) := by
        rw [bind₁_bind₁]
        simp only [hinv]
        rw [bind₁_X_left]
        rfl
    _ = 0 := by rw [hQ, map_zero]

theorem gs_ne_zero {m : ℕ} (c : ℝ) (u : Fin m → Fin n → ℂ) : gs c u ≠ 0 := Complex.exp_ne_zero _

theorem fP_inj {m : ℕ} (c : ℝ) {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  have h0 : P - Q = 0 := by
    apply evX_eq_zero
    intro u
    have := congrFun h u
    unfold fP at this
    have h2 := mul_right_cancel₀ (gs_ne_zero c u) this
    unfold evX at h2 ⊢
    rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 h0

theorem fP_add_smul {m : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  delta PositivityTheory.Rg.Sw.Glob.phiS
  rw [dite_eq_left h]

theorem tens_add_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (a : ℂ)
    (f g : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) :
    tens θ τ fr (a • f + g) Ψ = a • tens θ τ fr f Ψ + tens θ τ fr g Ψ := by
  funext x
  delta PositivityTheory.Rg.Sw.Glob.tens
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (a * f (fr⁻¹ * compAt θ τ x) + g (fr⁻¹ * compAt θ τ x)) * Ψ x = _
  ring

theorem tensor_gaussian_vacuum_injective {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr g (psi0 θ V n l s τ)) : f = g := by
  have hdet : IsUnit fr.det := hfr.1
  suffices hU : ∀ U : Matrix (Fin V.rank) (Fin n) ℂ, f U = g U from funext hU
  intro U
  have hx := congrFun h (xL θ τ (fr * U))
  have hc : compAt θ τ (xL θ τ (fr * U)) = fr * U := by
    have h1 := congrFun (compAt_xL hθ τ (fr * U)) τ
    simpa [dirAt_self] using h1
  have hp : psi0 θ V n l s τ (xL θ τ (fr * U)) = 1 := by
    show gAway V l s τ (fun τ' => compAt θ τ' (xL θ τ (fr * U))) *
      g0 D V.rank n (fun i j => finPart D (xL θ τ (fr * U) i j)) = 1
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ, gaussian_at_zero_eq_one, one_mul]
  have hinv : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hdet, Matrix.one_mul]
  change f (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) =
    g (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) at hx
  rw [hc, hp, hinv, mul_one, mul_one] at hx
  exact hx

end PositivityTheory.Rg.Sw.Glob.RhoH
