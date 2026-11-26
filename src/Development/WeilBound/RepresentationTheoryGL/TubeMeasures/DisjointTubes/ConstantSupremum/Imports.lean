module

public import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.VolumeSignatureIndependent
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.BoxExistence.ExistsBox
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.CovolFrame

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MeasureSumBounds.SumMuFLe
section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.CompSt
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace MainStatements.Tam

def CompSt : Prop := ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (MainStatements.Tam.massLev2 D.host.E D.R.r l.M)

end MainStatements.Tam

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HolomorphicSectionSignatureOneOne
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Local

open ReciprocityTheory.ChartRestriction.G.FD

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

end Local

section Adelic

variable {D : D7}

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩

end Adelic

section Dict

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member

variable {D : D7}


end Dict

section Forms

variable {D : D7}


end Forms

end GlobalTheory.HolDictModel
end
end

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.C

theorem sum_muF_le (hT : TubeSt) (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) [Fintype Comp]
    (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) (hM : 3 ≤ M)
    (hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ)
    (P Q : ℕ) (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = (P, Q)) (h2 : 2 ≤ r)
    (x0 : ∀ k, Frame (X k).Ψ r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))))
    (hF : ∀ k, IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) :
    ∑ k, muF (X k) (x0 k) (FF k) ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * r ^ 2) * (M : ℝ) ^ (2 * D.R.f * r ^ 2) *
      (ReciprocityTheory.ChartRestriction.DS.volU r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D r)) := by
  subst hr
  classical
  obtain ⟨x1, hx1, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx1 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E V.rank M (X k) (Λk k) hM (hΛk k).2.1 (hΛk k).2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E V.rank (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF (X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E V.rank (X k) (X' k) (hX'Ψ k)
      (fun τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) ?_ ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro τ hτ
      simp only [dif_pos hτ]
      rw [hG k]
      exact GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', (hX'Γ k γ').2 (by rw [hG k]; exact h1), fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      have h1 := (hX'Γ k γ').1 hγ'
      rw [hG k] at h1
      obtain ⟨γ, hγ, h2⟩ := GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup D V Comp X dict Kf th M x1 hK hth hD (fun c => (hx1 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' h1
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
  have hdist := GlobalTheory.T.componentRepresentatives_injective_doubleCoset D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])
  have hΓ' : ∀ k γ, γ ∈ (X' k).Γ ↔ IsUStab (X' k).Gm (X' k).Λ γ ∧ ∀ x ∈ (X' k).Λ, ∃ z ∈ (X' k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • z := by
    intro k γ
    rw [hX'Γ k γ, hX'Gm k, hX'Λ k]
  have hdet : ∀ k, ∀ γ ∈ (X' k).Γ, (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := fun k =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three D.host.E V.rank M (X' k) hM (hΓ' k)
  have hCc := fun k => GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass D.host.E V.rank (X' k) (y k) (FF' k) (by omega) (hdet k) (hy k) (hFF' k)
  have hTube := hT D V P Q hs hsig h2 M hM Comp X' gA y hdist (fun k => ⟨(hX'Gm k).trans (hG k),
    fun τ => by rw [hX'Ψ k]; exact hΨ k τ, by rw [hX'Λ k]; exact (hΛk k).1, hΓ' k, hy k⟩)
  have hC1 : (1 : ℝ) ≤ ((2 : ℝ) ^ (V.rank * (V.rank - 1) / 2) * (2 * Real.pi) ^ (V.rank - 1) *
      Real.sqrt V.rank) ^ fdeg D.host.E := by
    apply one_le_pow₀
    have h1 : (1 : ℝ) ≤ 2 ^ (V.rank * (V.rank - 1) / 2) := one_le_pow₀ (by norm_num)
    have h2' : (1 : ℝ) ≤ (2 * Real.pi) ^ (V.rank - 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
    have h3 : (1 : ℝ) ≤ Real.sqrt V.rank := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ V.rank))
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2') h3
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hTube
  rw [← hCc k]
  exact le_mul_of_one_le_left' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC1)

end MainStatements.Tam.C

open MainStatements.Tam

theorem MainStatements.Tam.comp : TubeSt → NumSt → CompSt := by
  intro hT hN D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  have hunf := hL.unf σ hσ
  have hΨ : ∀ k (τ : D.host.E →+* ℂ), τ ∈ ((U σ).X k).Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro k τ
    have hf := GlobalTheory.HolDictModel.fix_iff (D := D) τ
    rw [← hL.host.2.2.1, ← hL.host.2.1] at hf
    rw [(hunf.2.1 k).2 τ]
    simpa using hf
  have h2r : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have key := MainStatements.Tam.C.sum_muF_le hT D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
    l.three_le hΨ (D.R.sigW j).1 (D.R.sigW j).2 (D.sp.W_sig j) (fun τ => D.sp.W_sigval j hL.inR.1 hL.inR.2 τ) h2r
    x0 FF hF
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hv0, hv1⟩ := hN D.R.r h2r
  have hvnn : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r := le_trans (by positivity) hv0
  have hA : ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f ≤ (13 : ℝ) ^ (D.R.f * D.R.r ^ 2) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ hvnn hv1 _
  have hAnn : 0 ≤ ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f := pow_nonneg hvnn _
  have hB : Formalism.MainNotions.StandardLattice.massI D D.R.r ≤ massB D.host.E D.R.r := GlobalTheory.mass_stdLat_le D.host.E (fun _ => rfl) D.R.r
  have hBnn : 0 ≤ massB D.host.E D.R.r := by unfold massB; positivity
  have hAB : ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D D.R.r ≤
      (13 : ℝ) ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r := by
    rcases le_total 0 (Formalism.MainNotions.StandardLattice.massI D D.R.r) with h | h
    · exact mul_le_mul hA hB h (by positivity)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hAnn h) (by positivity)
  unfold massLev2
  rw [hfin]
  have h15 : (15 : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) = 225 ^ (D.R.f * D.R.r ^ 2) := by
    rw [mul_assoc, pow_mul]; norm_num
  rw [h15]
  have h208 : (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * 13 ^ (D.R.f * D.R.r ^ 2) ≤ 225 ^ (D.R.f * D.R.r ^ 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
        (ReciprocityTheory.ChartRestriction.DS.volU D.R.r ^ D.R.f * Formalism.MainNotions.StandardLattice.massI D D.R.r)
      ≤ (16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) *
        ((13 : ℝ) ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r) := by gcongr
    _ = (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) * ((16 : ℝ) ^ (D.R.f * D.R.r ^ 2) * 13 ^ (D.R.f * D.R.r ^ 2)) *
        massB D.host.E D.R.r := by ring
    _ ≤ (l.M : ℝ) ^ (2 * D.R.f * D.R.r ^ 2) * 225 ^ (D.R.f * D.R.r ^ 2) * massB D.host.E D.R.r := by gcongr

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FormalDegreeRankTwo.FinrankEqTwoFdeg
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.Z

theorem finrank_eq_two_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ E = 2 * fdeg E := by
  have h := NumberField.IsTotallyComplex.finrank (K := E)
  rw [fdeg, h]
  omega

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  rw [dE]
  have h0 := NumberField.discr_ne_zero E
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs h0
  exact_mod_cast h

theorem massLev2_eq (E : Type) [Field E] [NumberField E] (r M : ℕ) :
    massLev2 E r M = (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) * 15 ^ (Module.finrank ℚ E * r ^ 2) *
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (r : ℝ) ^ 4 *
        (dE E ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * r ^ 2) := rfl

theorem log_consts : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) ≤ 21 := by
  have hx : (0 : ℝ) < 15 ^ 2 * (3 * 2 ^ 2) ^ 6 := by norm_num
  have heq : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) =
      Real.log (15 ^ 2 * (3 * 2 ^ 2) ^ 6) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [heq, Real.log_le_iff_le_exp hx]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h21 : Real.exp 1 ^ 21 = Real.exp 21 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← h21]
  calc (15 : ℝ) ^ 2 * (3 * 2 ^ 2) ^ 6 ≤ 2.7 ^ 21 := by norm_num
    _ ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num) he 21

end MainStatements.Tam.Z

namespace MainStatements.Tam

end MainStatements.Tam

theorem MainStatements.Tam.size : SizeSt := by
  unfold MainStatements.Tam.SizeSt
  intro E _ _ _ r M L hr hM hL hfr hMl hd
  have hn := MainStatements.Tam.Z.finrank_eq_two_fdeg E
  have hd1 := MainStatements.Tam.Z.one_le_dE E
  have hc := MainStatements.Tam.Z.log_consts
  rw [MainStatements.Tam.Z.massLev2_eq]
  set n := Module.finrank ℚ E with hn_def
  set f := fdeg E with hf_def
  have hnpos' : 0 < n := Module.finrank_pos
  have hf1 : 1 ≤ f := by omega
  have hnR : (n : ℝ) = 2 * f := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by rw [hnR]; linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hdpos : 0 < dE E := by linarith
  set X := dE E ^ ((1 : ℝ) / (n : ℝ)) with hX_def
  have hX1 : 1 ≤ X := Real.one_le_rpow hd1 (by positivity)
  have hXpos : 0 < X := by linarith
  have hlogX : Real.log X = (1 / (n : ℝ)) * Real.log (dE E) := Real.log_rpow hdpos _
  have hnX : (n : ℝ) * Real.log X = Real.log (dE E) := by
    rw [hlogX]
    field_simp
  set B : ℝ := 3 * ((n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2) with hB_def
  have hn1 : (1 : ℝ) ≤ n := by rw [hnR]; linarith
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have h2 : 1 ≤ (r : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    have h4 : 1 ≤ (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    rw [hB_def]
    linarith
  have hBpos : 0 < B := by linarith
  have h15 : (1 : ℝ) ≤ 15 := by norm_num
  constructor
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMR) (one_le_pow₀ h15)) (one_le_pow₀ hB1)
  · have ha : (n : ℝ) ^ 2 ≠ 0 := (pow_pos hnpos 2).ne'
    have hb : (r : ℝ) ^ 4 ≠ 0 := (pow_pos hrpos 4).ne'
    have hx : X ^ 2 ≠ 0 := (pow_pos hXpos 2).ne'
    have hab : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 ≠ 0 := mul_ne_zero ha hb
    have habx : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 ≠ 0 := mul_ne_zero hab hx
    have hlogB : Real.log B = Real.log 3 + 2 * Real.log n + 4 * Real.log r + 2 * Real.log X := by
      rw [hB_def, Real.log_mul (by norm_num) habx, Real.log_mul hab hx, Real.log_mul ha hb,
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hm1 : (M : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos hMpos _).ne'
    have hm2 : (15 : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos (by norm_num) _).ne'
    have hm3 : B ^ (3 * n * r ^ 2) ≠ 0 := (pow_pos hBpos _).ne'
    rw [Real.log_mul (mul_ne_zero hm1 hm2) hm3, Real.log_mul hm1 hm2, Real.log_pow, Real.log_pow,
      Real.log_pow, hlogB]
    have hlogn : Real.log n = Real.log 2 + Real.log f := by
      rw [hnR, Real.log_mul (by norm_num) hfpos.ne']
    have hlfr : Real.log ((f : ℝ) * r) = Real.log f + Real.log r :=
      Real.log_mul hfpos.ne' hrpos.ne'
    rw [hlfr] at hfr
    rw [hlogn]
    push_cast
    rw [hnR] at hnX ⊢
    have hlf : 0 ≤ Real.log f := Real.log_nonneg hfR
    have hK : 0 ≤ (f : ℝ) * r ^ 2 := by positivity
    have pa := mul_le_mul_of_nonneg_left hMl hK
    have pb := mul_le_mul_of_nonneg_left hc hK
    have pc := mul_le_mul_of_nonneg_left hfr hK
    have pd := mul_nonneg hK hlf
    have pe := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L - 1)
    have pf := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L)
    have ph : (r : ℝ) ^ 2 * (2 * f * Real.log X) ≤ (r : ℝ) ^ 2 * (4 * f * L) := by
      rw [hnX]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith [pa, pb, pc, pd, pe, pf, ph]

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal

noncomputable section

namespace MainStatements.Tam.N

theorem fac_le (r i : ℕ) (hi : i < r) : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
  have h1 : i.factorial ≤ i ^ i := Nat.factorial_le_pow i
  have h2 : i ^ i ≤ r ^ i := Nat.pow_le_pow_left hi.le i
  have h3 : r ^ i ≤ r ^ r := Nat.pow_le_pow_right (by omega) hi.le
  exact_mod_cast h1.trans (h2.trans h3)

theorem factor_lower (r i : ℕ) (hi : i < r) :
    ((r : ℝ) ^ r)⁻¹ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by
  have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hp : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hnum : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by linarith
  calc ((r : ℝ) ^ r)⁻¹ = 1 / (r : ℝ) ^ r := by rw [one_div]
    _ ≤ 1 / (i.factorial : ℝ) := one_div_le_one_div_of_le hf (fac_le r i hi)
    _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := div_le_div_of_nonneg_right hnum hf.le

theorem factor_upper (r i : ℕ) (hi : i < r) :
    2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) ≤ (13 : ℝ) ^ r := by
  have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hpos : (0 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by positivity
  have h1 : 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) ≤ 2 * Real.pi ^ (i + 1) := div_le_self hpos hf
  have h2 : Real.pi ^ (i + 1) ≤ (4 : ℝ) ^ (i + 1) := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four _
  have h3 : (4 : ℝ) ^ (i + 1) ≤ (4 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : (2 : ℝ) * 4 ^ r ≤ 2 ^ r * 4 ^ r := by
    have : (0 : ℝ) ≤ 4 ^ r := by positivity
    nlinarith
  have h6 : (2 : ℝ) ^ r * 4 ^ r ≤ 13 ^ r := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  nlinarith

end MainStatements.Tam.N

namespace MainStatements.Tam

theorem num : NumSt := by
  intro r hr
  constructor
  · have e : ((r : ℝ) ^ (r ^ 2))⁻¹ = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ := by
      rw [Finset.prod_const, Finset.card_range, inv_pow, ← pow_mul, sq]
    rw [e]
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i hi => MainStatements.Tam.N.factor_lower r i (Finset.mem_range.mp hi))
  · have e : (13 : ℝ) ^ (r ^ 2) = ∏ _i ∈ Finset.range r, (13 : ℝ) ^ r := by
      rw [Finset.prod_const, Finset.card_range, ← pow_mul, sq]
    rw [e]
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i hi => MainStatements.Tam.N.factor_upper r i (Finset.mem_range.mp hi))

end MainStatements.Tam
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LevelStabilisers.MemStabOfLev
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.S

theorem latHat_eq_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Set (Fin n → E)) :
    (Formalism.MainNotions.StandardLattice.latHat F E L : Set (Fin n → RA F E)) = (GlobalTheory.AdLat.hat F L : Set (Fin n → RA F E)) := by
  ext z
  constructor
  · intro hz
    refine (AddSubgroup.closure_le _).2 ?_ hz
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, fun v => ha v, x, hx, rfl⟩
  · intro hz
    refine (AddSubgroup.closure_le _).2 ?_ hz
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ?_, x, hx, rfl⟩
    intro v
    exact ha v

variable {D : D7}

theorem mem_latHat_iff (V : HSp D) (y : Fin V.rank → RA D.host.F D.host.E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  rw [← SetLike.mem_coe, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V, latHat_eq_hat, SetLike.mem_coe]

theorem mem_Stab_iff (V : HSp D) (h : GA D V) :
    h ∈ Stab V ↔ ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ↔
      (finHom V h).1 *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  constructor
  · intro H y
    have H' : ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) := H
    have := H' y
    rw [mem_latHat_iff, mem_latHat_iff] at this
    exact this
  · intro H
    show ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)
    intro y
    rw [mem_latHat_iff, mem_latHat_iff]
    exact H y

theorem stab_eq_KM_one (V : HSp D) : Stab V = KM V 1 := by
  ext h
  rw [mem_Stab_iff]
  constructor
  · intro hs
    show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    refine ⟨GlobalTheory.FinUA.isUA_finHom D V h, fun x hx => ⟨(finHom V h).1 *ᵥ x - x, sub_mem ((hs x).1 hx) hx,
      by rw [one_nsmul]⟩, fun x hx => ⟨((finHom V h)⁻¹).1 *ᵥ x, (hs _).2 ?_, ?_⟩⟩
    · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      exact hx
    · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  · intro hK y
    have hK' : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1
        ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := hK
    obtain ⟨-, h2, h3⟩ := hK'
    constructor
    · intro hy
      obtain ⟨z, hz, e⟩ := h2 y hy
      rw [one_nsmul, sub_eq_iff_eq_add] at e
      rw [e]
      exact add_mem hz hy
    · intro hy
      obtain ⟨z, hz, e⟩ := h3 _ hy
      have e2 := congrArg (fun w => ((finHom V h)⁻¹).1 *ᵥ w) e
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec] at e2
      rw [← e2]
      exact hz

theorem mem_KM_iff (V : HSp D) (M : ℕ) (h : GA D V) : h ∈ KM V M ↔ GlobalTheory.Member.FinCong V M h := by
  have h1 := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  constructor
  · intro hK
    have hK' : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := hK
    intro z hz
    rw [h1] at hz ⊢
    exact hK'.2.1 z hz
  · intro hc
    have hinv := GlobalTheory.Member.PrincLevel.finCong_map (GlobalTheory.Member.PrincLevel.finCong_inv hc)
    show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    refine ⟨GlobalTheory.FinUA.isUA_finHom D V h, fun z hz => ?_, fun x hx => ?_⟩
    · have hz' : z ∈ Formalism.L2.Pj.latHat V := by rw [h1]; exact hz
      obtain ⟨y, hy, e⟩ := hc z hz'
      rw [h1] at hy
      exact ⟨y, hy, e⟩
    · have hx' : x ∈ Formalism.L2.Pj.latHat V := by rw [h1]; exact hx
      have hm := hinv x hx'
      rw [h1] at hm
      refine ⟨(finHom V h⁻¹).1 *ᵥ x, hm, ?_⟩
      rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem isOpen_KM (V : HSp D) (M : ℕ) (hM : 1 ≤ M) : IsOpen (KM V M) := by
  let K : Subgroup (GA D V) :=
    { carrier := {h | GlobalTheory.Member.FinCong V M h}
      one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V M
      mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
      inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha }
  have e : KM V M = (K : Set (GA D V)) := Set.ext fun h => mem_KM_iff V M h
  rw [e]
  have hG : Continuous fun x : GA D V => finHom V x := by
    refine Units.continuous_iff.2 ⟨GlobalTheory.Member.continuous_finHom_val D V, ?_⟩
    have h := (GlobalTheory.Member.continuous_finHom_val D V).comp continuous_inv
    refine h.congr fun x => ?_
    simp [map_inv]
  have hF : Continuous fun x : GA D V => (finHom V).rangeRestrict x := hG.subtype_mk _
  have hO := (GlobalTheory.SmoothVac.isOpen_map_levelGroup V (show 0 < M by omega)).preimage hF
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) (Filter.mem_of_superset (hO.mem_nhds ?_) ?_)
  · exact Subgroup.mem_map.2 ⟨1, one_mem _, by simp⟩
  · intro x hx
    obtain ⟨k', hk', e'⟩ := Subgroup.mem_map.1 hx
    have e'' : finHom V k' = finHom V x := congrArg Subtype.val e'
    show GlobalTheory.Member.FinCong V M x
    have hc := hk'.2
    unfold GlobalTheory.Member.FinCong at hc ⊢
    rw [← e'']
    exact hc


open Formalism.IndefR.Links in
theorem mem_Stab_of_lev (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.LevelP C.Pg D.R.r ℂ) (h : GA D (Wc D i))
    (hh : finE (Wc D i) h ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) : h ∈ Stab (Wc D i) := by
  have hβ := hC.βW i
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame (C.βW i) (C.ΛW i) := by obtain ⟨c, hc, -⟩ := hβ; exact hc
  have hS : finE (Wc D i) h ∈ Formalism.L2.DIV.St (C.βW i) := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.mem_lev.1 hh).1
  have hS' : finE (Wc D i) h⁻¹ ∈ Formalism.L2.DIV.St (C.βW i) := by rw [map_inv]; exact inv_mem hS
  have m1 := GlobalTheory.MassLinkConj.mulVec_mem_hat D (C.βW i) (C.ΛW i) hfr (finHom (Wc D i) h) (by exact hS)
  have m2 := GlobalTheory.MassLinkConj.mulVec_mem_hat D (C.βW i) (C.ΛW i) hfr (finHom (Wc D i) h⁻¹) (by exact hS')
  rw [hΛ] at m1 m2
  rw [mem_Stab_iff]
  intro y
  refine ⟨fun hy => m1 y hy, fun hy => ?_⟩
  have := m2 _ hy
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end MainStatements.Tam.S

namespace MainStatements.Tam

theorem stab : StabSt :=
  ⟨fun _ V => ⟨S.stab_eq_KM_one V, fun M hM => S.isOpen_KM V M hM⟩,
    fun D Tu C t0 hC i P h hh => S.mem_Stab_of_lev D Tu C t0 hC i P h hh⟩

end MainStatements.Tam

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ProductMapEquality.PiCdEqMap
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.V

theorem pi_cd_eq_map (D : D7) (V : HSp D) (hV : V.SigOK) (μ1 : Measure (GA D V))
    (hμ1 : IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ1)
    (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hc : Continuous rp) (hrp : IsRealPart V θ A rp) :
    Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) =
      Measure.map rp (μ1.restrict (Stab V)) := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ : D.what₂.Tau, SigmaFinite (D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := fun ρ => by
    haveI := D.cd.haar (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    infer_instance
  have hφm : Measurable rp := hc.measurable
  obtain ⟨-, -, H⟩ := hμ1
  obtain ⟨-, H1⟩ := H θ hθ
  have H2 := H1 A hA
  refine Measure.pi_eq fun B hB => ?_
  have hm : MeasurableSet (rp ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
  rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm]
  refine Eq.trans ?_ (H2 B hB)
  congr 1
  ext h
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
  rw [and_comm]
  refine and_congr Iff.rfl (forall_congr' fun ρ => ⟨fun hb => ⟨rp h ρ, hb, hrp h ρ⟩, ?_⟩)
  rintro ⟨b, hb, hbe⟩
  rwa [GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ (hbe.trans (hrp h ρ).symm)] at hb

end MainStatements.Tam.V

namespace MainStatements.Tam

theorem vol : VolSt := by
  intro D V P Q hV hs μ _ 𝓕 h𝓕 θ A m rp hθ hA hm hc hrp B hB
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hlc, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _

  have hTG : VolTieG (GlobalTheory.Mem.retie D) := (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have hT : VolTie (GlobalTheory.Mem.retie D) := VolTieG.volTie hTG
  have h2 : Conclusion2 (GlobalTheory.Mem.retie D) := volumeMass_of_unfolding _ (CompanionTheory.HU.mass_ratio_under_volume _ hT)
  have hrk : V.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum V hV D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  have hvol : (GlobalTheory.Mem.retie D).vol V = massI D V.rank := by
    rw [hrk]
    exact GlobalTheory.Glob.vol_eq_massI_all_sig (GlobalTheory.Mem.retie D) hT h2 V P Q hV hs

  have hTG' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome
      (IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2)) fun μ1 : Measure (GA D V) =>
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (fun 𝓕 : Set (GA D V) => IsFundamentalDomain (GQ V) 𝓕 μ1) fun 𝓕 =>
        μ1 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol V) := hTG V hV
  obtain ⟨⟨μ1, hμ1'⟩, Hvol⟩ := hTG'
  haveI := hμ1'.1

  have hscale : μ = Measure.haarScalarFactor μ μ1 • μ1 := Measure.isMulLeftInvariant_eq_smul μ μ1
  have hc0 : ((Measure.haarScalarFactor μ μ1 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ1).ne'
  have hμX : ∀ X, μ X = (Measure.haarScalarFactor μ μ1 : ℝ≥0∞) * μ1 X := fun X => by
    conv_lhs => rw [hscale]
    first
      | rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      | simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      | simp [Measure.smul_apply]
  have hac : μ1 ≪ μ := fun X hX => by
    rw [hμX] at hX
    exact (mul_eq_zero.1 hX).resolve_left hc0
  have h𝓕1 : IsFundamentalDomain (GQ V) 𝓕 μ1 := h𝓕.mono hac
  have hF1 : μ1 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol V) := (Hvol μ1 hμ1').2 𝓕 h𝓕1

  have hpi := MainStatements.Tam.V.pi_cd_eq_map D V hV μ1 hμ1' θ A rp hθ hA hc hrp
  have hSet : μ {h | h ∈ Stab V ∧ rp h ∈ B} = (Measure.haarScalarFactor μ μ1 : ℝ≥0∞) *
      Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) B := by
    rw [hμX, hpi, Measure.map_apply hc.measurable hB, Measure.restrict_apply (hc.measurable hB)]
    congr 2
    ext h
    exact and_comm

  have hVpos : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos V.rank
  have hmeq : ∀ ρ, m ρ = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank) •
      D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 := fun ρ => by
    have e := GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd D.cd _ _ (m ρ) (hm ρ)
    rw [Formalism.BasicNotions.sig_sum V hV (tauE D ρ)] at e
    exact e
  haveI : ∀ ρ : D.what₂.Tau, SigmaFinite (D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := fun ρ => by
    haveI := D.cd.haar (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    infer_instance
  haveI : ∀ ρ, SigmaFinite (m ρ) := fun ρ => by
    haveI := (hm ρ).1
    infer_instance
  have hpim : Measure.pi m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank) ^ D.R.f •
      Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by
    refine Measure.pi_eq fun C hC => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
    simp_rw [hmeq, Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
  rw [hpim, hSet, hμX 𝓕, hF1, hvol, Measure.smul_apply, smul_eq_mul,
    ENNReal.ofReal_mul (pow_nonneg hVpos.le _), ENNReal.ofReal_pow hVpos.le]
  ring

end MainStatements.Tam

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.InverseMultiplication.IsKMInvMul
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.I

open GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isKM_inv_mul' {n M : ℕ} {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)}
    {g s : Matrix (Fin n) (Fin n) (RA F E)} (hg : GlobalTheory.UCls.IsKM c G L 1 g) (hs : GlobalTheory.UCls.IsKM c G L 1 s)
    (hgs : ∀ x ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, g *ᵥ x - s *ᵥ x = M • y) :
    GlobalTheory.UCls.IsKM c G L M (s⁻¹ * g) := by
  have hsu : IsUnit s.det := hs.1.1
  have hss : ∀ v, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mulVec]
  have hss' : ∀ v, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mulVec]
  have into : ∀ x ∈ GlobalTheory.AdLat.hat F L, s *ᵥ x ∈ GlobalTheory.AdLat.hat F L := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hs.2.1 x hx
    rw [one_smul] at h
    rw [show s *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hsu.ringInverse).mul hg.1.1
  · intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hs.1.2 (s⁻¹ *ᵥ (g *ᵥ x)) (s⁻¹ *ᵥ (g *ᵥ y)), hss, hss,
      hg.1.2]
  · intro x hx
    obtain ⟨y, hy, h⟩ := hgs x hx
    obtain ⟨w, hw, rfl⟩ := hs.2.2 y hy
    refine ⟨w, hw, ?_⟩
    have h1 : g *ᵥ x = s *ᵥ (x + M • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← h]; abel
    rw [← Matrix.mulVec_mulVec, h1, hss']
    abel
  · intro x hx
    obtain ⟨y, hy, h⟩ := hg.2.2 (s *ᵥ x) (into x hx)
    exact ⟨y, hy, by rw [← Matrix.mulVec_mulVec, h, hss']⟩

end MainStatements.Tam.I

namespace MainStatements.Tam

open GlobalTheory.UCls.IdxK

theorem idx : IdxSt := by
  intro E _ _ _ r M G Λ hM hSD
  classical
  have hFG : Λ.FG := hSD.2.2.1
  obtain ⟨e, heΛ, he⟩ := GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField E r M Λ hM hFG
  obtain ⟨T, hTc, hTΛ, hT⟩ := GlobalTheory.T.exists_reps_mod_lattice_card_le E r M Λ hM hFG
  have hLo : ∀ o : 𝓞 E, ∀ x ∈ (Λ : Set (Fin r → E)), o • x ∈ (Λ : Set (Fin r → E)) :=
    fun o x hx => Λ.smul_mem o hx
  have hLb : ∀ b : 𝓞 (maximalRealSubfield E), ∀ x ∈ (Λ : Set (Fin r → E)),
      algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E) • x ∈ (Λ : Set (Fin r → E)) := by
    intro b x hx
    have hi : IsIntegral ℤ (algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E)) :=
      b.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    exact Λ.smul_mem (⟨_, hi⟩ : 𝓞 E) hx
  have hQ : ∀ z ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), ∃ t ∈ T,
      ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), z = GlobalTheory.AdLat.fv _ t + M • y := by
    intro z hz
    obtain ⟨t0, ht0, y0, hy0, rfl⟩ := hat_approx hM hLb Λ.zero_mem (fun x hx y hy => Λ.add_mem hx hy)
      (fun x hx => Λ.neg_mem hx) z hz
    obtain ⟨t, ht, y1, hy1, rfl⟩ := hT t0 ht0
    refine ⟨t, ht, GlobalTheory.AdLat.fv _ y1 + y0, add_mem (fv_mem hy1) hy0, ?_⟩
    rw [fv_add, fv_nsmul, smul_add, add_assoc]
  have into : ∀ g, GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
      ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
        g *ᵥ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) := by
    intro g hg x hx
    obtain ⟨y, hy, h⟩ := hg.2.1 x hx
    rw [one_smul] at h
    rw [show g *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  let K1 := {g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) //
    GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g}
  have hex : ∀ g : K1, ∀ i, ∃ t ∈ T, ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
      g.1 *ᵥ GlobalTheory.AdLat.fv _ (e i) = GlobalTheory.AdLat.fv _ t + M • y :=
    fun g i => hQ _ (into g.1 g.2 _ (fv_mem (heΛ i)))
  choose τ hτT yy hyy hτ using hex
  let σ : (Fin r → Fin r → E) → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun t => if h : ∃ g : K1, τ g = t then h.choose.1 else 1
  refine ⟨(Fintype.piFinset fun _ : Fin r => T).image σ, ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin r => T).card := Finset.card_image_le
      _ = T.card ^ r := by simp
      _ ≤ (M ^ (2 * fdeg E * r)) ^ r := Nat.pow_le_pow_left hTc r
      _ = _ := by rw [← pow_mul]; ring_nf
  · intro g hg
    let g' : K1 := ⟨g, hg⟩
    have hex' : ∃ g'' : K1, τ g'' = τ g' := ⟨g', rfl⟩
    have hσ : σ (τ g') = hex'.choose.1 := dif_pos hex'
    have hsτ : τ hex'.choose = τ g' := hex'.choose_spec
    set s' := hex'.choose with hs'
    refine ⟨s'.1, Finset.mem_image.2 ⟨τ g', Fintype.mem_piFinset.2 fun i => hτT g' i, hσ⟩, s'.2,
      s'.1⁻¹ * g, ?_, ?_⟩
    · refine MainStatements.Tam.I.isKM_inv_mul' hg s'.2 ?_
      refine cong_of_gens hLo e he g s'.1 (into g hg) (into s'.1 s'.2) fun i => ?_
      refine ⟨yy g' i - yy s' i, sub_mem (hyy g' i) (hyy s' i), ?_⟩
      have h1 := hτ g' i
      have h2 := hτ s' i
      rw [hsτ] at h2
      change g *ᵥ GlobalTheory.AdLat.fv _ (e i) = _ at h1
      rw [h1, h2, smul_sub]
      abel
    · rw [← mul_assoc, Matrix.mul_nonsing_inv _ s'.2.1.1, one_mul]

end MainStatements.Tam

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Tube0
theorem MainStatements.Tam.Plug.tube0 : MainStatements.Tam.VolSt → MainStatements.Tam.StabSt → MainStatements.Tam.IdxSt → MainStatements.Tam.TubeSt := MainStatements.Tam.tube
end

namespace MainStatements.Tam.Plug

theorem low : LowSt := MainStatements.Tam.low MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num

theorem comp : CompSt := MainStatements.Tam.comp (tube0 MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.idx) MainStatements.Tam.num

theorem size : SizeSt := MainStatements.Tam.size

end MainStatements.Tam.Plug
