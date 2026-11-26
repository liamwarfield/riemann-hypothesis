module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalCharacterPowerConductorBound
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize ValuativeRel
open Formalism.L2.Host GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
private theorem additive_character_pow_conductor {W : G.Weil} {w : Pl D.host.E} (hc : HasConductor (psiAt W w) 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ^ (Ideal.absNorm w.asIdeal ^ n) = 1 := by
  have e := GivenAdm.isEquiv_val w
  set q := Ideal.absNorm w.asIdeal
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
private theorem congruence_le_given_level {μ₀ : T} (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (he : depthAt G w = cosExp G w) (X : ℕ × ℕ) :
    glLatCong (unifAt w ^ depthAt G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ≤ givenLevel G t w X := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel, he]
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := GivenAdm.exists_types hL hw
      rw [GivenAdm.givenLevel_succ (hP _)]
      refine le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_)
        (TypeDatum.KOne_le _)
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)
    · exact fun g hg => (GivenAdm.mem_glLatCong.1 hg).1
private theorem local_grid_entries_unitary {K : Type} [Field K] {ι τ : K →+* ℂ} (t : T) (w : Pl D.host.E)
    (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
    (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un ι τ ((G.ch.chiH i).loc w x : ℂ))
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : Un ι τ ((locGrid G t w).nu i j u : ℂ) := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact ((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv
private theorem local_grid_rank_le (t : T) (w : Pl D.host.E) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    (locGrid G t w).rank (i + 1, j + 1) ≤ 2 * bigN D := by
  change D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : 1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have h4 : D.R.r ≤ sLen D := Nat.le_add_right _ _
  unfold bigN
  rw [mul_add D.R.m, mul_add D.R.m]
  omega
end
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize in
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw in
theorem _root_.GlobalTheory.T.local_character_power_conductor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch C := by
  refine fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z
  obtain ⟨w, hw⟩ := w₀
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard A.μ0
  have hg := (Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hW : w ∈ ch.G.pl.W0 := (GivenAdm.mem_locPl.1 hw).resolve_right fun h =>
    (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)
  have he : depthAt ch.G w = cosExp ch.G w := by
    obtain ⟨h1, h2⟩ := GivenAdm.under_mem_and_place_above_eq_of_mem hW
    have := depthAt_w ch.G h1
    rw [h2] at this
    rw [this.1, this.2]
  have hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ) := fun j x => by
    obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 j).inf
    exact UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ) := fun x => by
    rw [hL.xi_base]; exact Un.one
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ) :=
    fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL := fun u =>
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w
      (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)
  have hq0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hψ := fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h)
    (additive_character_pow_conductor (W := ch.W) h00.cond (depthAt ch.G w) x hx)
  have hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G A.μ0 w).alpha_div_beta i j
    exact ⟨local_grid_rank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, local_grid_entries_unitary _ w hmu hxi hchi hi hj⟩
  have key := sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m)
    (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1
    (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, congruence_le_given_level hL hw he X⟩)
    hadm.tensor (UpperTheory.localGrid_tensor_size_le_one_of_unimodular _ _ ch.S.B A.μ0 Φ w hmu hxi) z
  refine key.mono ?_
  rw [mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he,
    ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]
  have h1 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w
  have h2 := placeSz_nonneg ch.G w
  calc _ ≤ ((6 * cosExp ch.G w * (2 * bigN D) ^ 2 * D.R.m ^ 2 : ℕ) : ℝ) *
        (2 * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = 48 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w := by rw [placeSz]; push_cast; ring
    _ ≤ _ := by gcongr
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorVolumeCoefficient
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
namespace GlobalTheory.ArchTens.VolSize
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
theorem archimedean_tensor_volume_coefficient : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => CoefAt ch C := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => by
      have hL := s.core.lev
      have hde := Test.pde_ne_q s
      rintro Φ β hβ ⟨P, hl⟩
      have hP : P ∈ ch.G.pl.W0 := by
        classical
        rcases Finset.mem_union.1 hl with h | h
        · exact h
        · exact absurd h (fun hP => (hL.Q_ram A.μ0 P).2 (Or.inl hP) (by rw [hL.xi_base]; exact fun _ _ => rfl))
      exact (coef_le_of_chosen hL ch.S.toGridChoice A.μ0 Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard A.μ0) hP hl hβ).trans
        (Real.exp_le_exp.2 (exponent_le P hC))⟩⟩⟩

end GlobalTheory.ArchTens.VolSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_tensor_volume_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => CoefAt ch C := by
  first | exact @_root_.GlobalTheory.ArchTens.VolSize.archimedean_tensor_volume_coefficient | exact _root_.GlobalTheory.ArchTens.VolSize.archimedean_tensor_volume_coefficient | (intros; apply _root_.GlobalTheory.ArchTens.VolSize.archimedean_tensor_volume_coefficient <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorFactorUnfolding
section
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.ArchTens.Unfold
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj GlobalTheory.SumSize Formalism.BasicNotions
section Integral
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
end Integral
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Local
section Grid
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : D7} (σ : D.what₂.LL →+* ℂ)
variable [MeasurableSpace k] [BorelSpace k]
end Grid
end GlobalTheory.ArchTens.Unfold
namespace GlobalTheory.ArchTens.Unfold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
theorem archimedean_tensor_unfold_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  classical
  intro _
  refine ⟨0, fun CF _ => ⟨12, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ hok hF σ Φ β hβ w x y => ?_⟩⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hP : w.1 ∈ ch.G.pl.W0 := by
    rcases Finset.mem_union.1 w.2 with h | h
    · exact h
    · rw [show R.toLevCh.Q A.μ0 = ∅ from GlobalTheory.BaseScalar.Q_base R hL] at h
      exact absurd h (Finset.notMem_empty _)
  have hsz : 0 ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w :=
    mul_nonneg (by positivity) (placeSz_nonneg ch.G w)
  refine absLe_mono (absLe_datum hL ch.S.toGridChoice hok A.μ0 Φ (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard A.μ0) hP w.2 hβ σ
    (hF σ Φ w) _ _) ?_
  nlinarith
end GlobalTheory.ArchTens.Unfold
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_tensor_factor_unfolding : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  first | exact @_root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum | exact _root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum | (intros; apply _root_.GlobalTheory.ArchTens.Unfold.archimedean_tensor_unfold_datum <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
namespace GlobalTheory.ArchTens
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.ArchTens
open GlobalTheory.ArchTens in
theorem _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : InfTensK := by
  obtain ⟨F1, h1⟩ := _root_.GlobalTheory.T.local_character_power_conductor_bound hP
  obtain ⟨F2, h2⟩ := _root_.GlobalTheory.T.archimedean_tensor_factor_unfolding hP
  obtain ⟨F3, h3⟩ := _root_.GlobalTheory.T.archimedean_tensor_volume_bound hP
  refine ⟨max F1 (max F2 F3), fun CF hCF => ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hCF)
  refine ⟨max (max (4 * C1) (2 * C2)) (max (2 * C3) 0), fun ε C hC => ?_⟩
  have hC1 : C1 ≤ C / 2 / 2 := by have := (le_max_left _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC2 : C2 ≤ C / 2 := by have := (le_max_right _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC3 : C3 ≤ C / 2 := by have := (le_max_left _ _).trans ((le_max_right _ _).trans hC); linarith
  have hC0 : 0 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  obtain ⟨x1, h1⟩ := h1 ε (C / 2 / 2) hC1
  obtain ⟨x2, h2⟩ := h2 ε (C / 2) hC2
  obtain ⟨x3, h3⟩ := h3 ε (C / 2) hC3
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF
  exact infTensAt_of_places ch hC0
    (h2 D large₂ he (((le_max_left _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
      (h1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF))
    (h3 D large₂ he (((le_max_right _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_archimedean_tensor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfTensK := by
  first | exact @_root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | exact _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | (intros; apply _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local <;> assumption)
end
