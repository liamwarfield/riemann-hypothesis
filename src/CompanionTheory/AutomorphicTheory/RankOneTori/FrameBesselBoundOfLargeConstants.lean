module

public import CompanionTheory.AutomorphicTheory.RankOneTori.MatGroupOf
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeBessel
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JScaleMoveB
public import CompanionTheory.AutomorphicTheory.RankOneTori.KDense
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.RankOneTori.BeRankScale
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.FourierDecayAlt.P
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

theorem be_scale {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : inWb k r z)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (c : ℂ) (u v : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be ((τ : ℂ) • z) ((κ : ℂ) * c) (fun x => π (cjI k r κ τ x)) σ (μW.map (cjT k r κ τ))
              (μN.map (cjT k r κ τ)) u v =
      Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ (dM k r κ τ) u) (σ (dM k r κ τ) v) := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  rw [Measure.map_prod_map _ _ measurable_cjT measurable_cjT]
  have e : Prod.map (cjT k r κ τ) (cjT k r κ τ) = ⇑((cjE (k := k) (r := r) hκ hτ).prodCongr (cjE hκ hτ)) := rfl
  rw [e, integral_map_equiv]
  refine integral_congr_ae ?_
  have a1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have a2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [a1, a2] with p hp1 hp2
  show Formalism.FourierDecayAlt.ThreeDimData.beInt _ _ _ σ u v (cjT k r κ τ p.1, cjT k r κ τ p.2) = _
  have hd := dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := dMi_mem_UH (k := k) (r := r) hκ hτ
  have hx : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hp1.1 hp2.1
  simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, of_cjT]
  rw [psi_cj hκ hτ hz, ← cj_inv hκ hτ, cjI_cj hκ hτ, ← cj_mul hκ hτ]
  congr 2
  unfold cj
  rw [TranslationBesselVanishing.sigma_mul hσ (WeylGroupFacts.uh_mul hdi hx) hd, TranslationBesselVanishing.sigma_mul hσ hdi hx]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MatrixMultiplicationContinuity.sigma_inner hσ hdi, dMi_inv hκ hτ]

theorem be_rank_scale (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {μW : Measure (Mt k r)}
    (hl : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (UWset k r z) μW) {κN : ℝ≥0∞} (h0 : κN ≠ 0) (h1 : κN ≠ ⊤)
    {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∃ l : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      Formalism.FourierDecayAlt.ThreeDimData.be z (cOfDpsi (κ₀ : ℂ)) π σ μW (haarLie (Nset k r) κN) w v = (innerSL ℂ (l v)).smulRight (l w) := by
  have hκ : 0 < κ₀⁻¹ := inv_pos.2 hκ₀
  have hτ : (0 : ℝ) < 1 := one_pos
  have : SigmaFinite μW := hW.1
  have : SFinite (haarLie (Nset k r) κN) := sFinite_haarLie _ _
  have hc : ((κ₀⁻¹ : ℝ) : ℂ) * cOfDpsi (κ₀ : ℂ) = cStd := by
    have : (κ₀ : ℂ) ≠ 0 := by exact_mod_cast hκ₀.ne'
    unfold cOfDpsi cStd
    push_cast
    field_simp
  have hN : IsHaarOn (Nset k r) ((haarLie (Nset k r) κN).map (cjT k r κ₀⁻¹ 1)) := by
    rw [map_haarLie_N hκ hτ]
    exact Formalism.MainNotions.BridgeCSB.haarLieN k r _ (mul_ne_zero h0 (ENNReal.ofReal_pos.2 (deltaN_pos hκ hτ)).ne')
      (ENNReal.mul_ne_top h1 ENNReal.ofReal_ne_top)
  obtain ⟨L, hL⟩ := CompanionTheory.FamilyDerivativeExpansion.M1.be_rank_one (z := ((1 : ℝ) : ℂ) • z) (π := fun x => π (cjI k r κ₀⁻¹ 1 x)) hk hl hσ hg hh
    (inWb_smul hz _) (by rw [Tz_smul]; simpa using hT) (isHCTypeW_cjI hκ hτ hz hπ) (isHaarOn_map_cjT hκ hτ hz hW) hN
  have hd := dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := dMi_mem_UH (k := k) (r := r) hκ hτ
  have hcan : ∀ x : H, σ (dM k r κ₀⁻¹ 1) (σ (dMi k r κ₀⁻¹ 1) x) = x := fun x => by
    rw [← ContinuousLinearMap.comp_apply, ← TranslationBesselVanishing.sigma_mul hσ hd hdi, dM_mul_dMi hκ hτ, (MatrixMultiplicationContinuity.sigma_facts hσ).1]
    rfl
  refine ⟨fun x => L (σ (dMi k r κ₀⁻¹ 1) x), fun w hw v hv => ?_⟩
  have e := be_scale (π := π) hσ hz (Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_sk hW) (Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN κN) hκ hτ
    (cOfDpsi (κ₀ : ℂ)) (σ (dMi k r κ₀⁻¹ 1) w) (σ (dMi k r κ₀⁻¹ 1) v)
  rw [hcan, hcan, hc] at e
  rw [← e]
  exact (hL _ (TranslationBesselVanishing.smooth_translate hσ hw hdi) _ (TranslationBesselVanishing.smooth_translate hσ hv hdi)).2

end Formalism.MainStatements.RankOne
end
end

section -- merged from CompanionTheory.AutomorphicTheory.RankOneTori.NzTranslate
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_conj (hσ : IsURepOn (UH (Hpk k r)) σ) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) :
    ∀ ws : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ ws, PI.UpqRep.InLieHpk k r X) → ∀ u : H,
      PI.UpqRep.dsigW (k := k) (r := r) σ ws (σ t u) =
        σ t (PI.UpqRep.dsigW (k := k) (r := r) σ (ws.map fun X => t⁻¹ * X * t) u)
  | [], _, _ => rfl
  | X :: w, hw, u => by
    simp only [PI.UpqRep.dsigW, List.map_cons]
    rw [dsigW_conj hσ ht w (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) u]
    exact ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB.dsig_conj hσ ht (hw X List.mem_cons_self) _

theorem nz_translate (hKD : Pv.AmpDD.KDense) (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {Bm : H → Wp} (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π Bm)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hBv : Bm v ≠ 0) :
    ∃ u : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u ∧ Bm (σ t u) ≠ 0 := by
  have hU : IsURepOn (UH (Hpk k r)) σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  have hti := WeylGroupFacts.uh_inv ht
  have hu : IsUnit t.det := (unitary_group_closed k r).unit t ht
  set x := σ t⁻¹ v with hx
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := TranslationBesselVanishing.smooth_translate hσ hv hti
  have htx : σ t x = v := by
    rw [hx, ← ContinuousLinearMap.comp_apply, ← TranslationBesselVanishing.sigma_mul hσ ht hti, Matrix.mul_nonsing_inv _ hu,
      (MatrixMultiplicationContinuity.sigma_facts hσ).1]
    rfl
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hpos : 0 < ‖Bm v‖ := norm_pos_iff.mpr hBv
  set e : ℝ := ‖Bm v‖ / (|C| + 1) with he
  have he0 : 0 < e := div_pos hpos (by positivity)
  obtain ⟨u, huK, hue⟩ := hKD k r ε lam H σ hlam hσ x hxs (Ws.map (List.map fun X => t⁻¹ * X * t))
    (fun w hw X hX => by
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hX
      exact ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB.lie_conj ht (hWs w0 hw0 X0 hX0)) e he0
  refine ⟨u, huK, fun h0 => ?_⟩
  have hus : u ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ u huK
  have hds : x - u ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ u]
    exact DDSmoothness.smooth_add hxs (DDSmoothness.smooth_smul (-1) hus)
  have hsplit : Bm v = Bm (σ t (x - u)) := by
    have := hadd _ (TranslationBesselVanishing.smooth_translate hσ hds ht) _ (TranslationBesselVanishing.smooth_translate hσ hus ht)
    rw [← map_add (f := _), sub_add_cancel, htx, h0, add_zero] at this
    exact this
  have hb := hbd _ (TranslationBesselVanishing.smooth_translate hσ hds ht)
  have hmap : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (σ t (x - u))‖) =
      (Ws.map (List.map fun X => t⁻¹ * X * t)).map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - u)‖ := by
    rw [List.map_map]
    refine List.map_congr_left fun w hw => ?_
    rw [dsigW_conj hU ht w (hWs w hw), (MatrixMultiplicationContinuity.sigma_facts hσ).2 t ht]
    rfl
  rw [hmap, ← hsplit] at hb
  set S := ((Ws.map (List.map fun X => t⁻¹ * X * t)).map
    fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - u)‖).sum with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; apply List.sum_nonneg; intro y hy
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
  have h1 : ‖Bm v‖ ≤ |C| * S := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
  have h2 : |C| * S ≤ |C| * e := mul_le_mul_of_nonneg_left hue.le (abs_nonneg C)
  have h3 : |C| * e < ‖Bm v‖ := by
    rw [he, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

theorem side_nz (hKD : Pv.AmpDD.KDense) {h : ℝ} (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hO : ThreeDimData.GapOK k r h) {w0 : H} (hw0 : PI.UpqRep.IsLowUnitH k r ε lam σ w0)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {c : ℂ} (hc : c ≠ 0) {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} (hπ : IsHCTypeW k r z u π) {μW : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW)
    (hW1 : μW Set.univ = 1) {κ : ℝ≥0∞} (h0 : κ ≠ 0) (h1 : κ ≠ ⊤) {l : H → Wp}
    (hl : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) w v = (innerSL ℂ (l v)).smulRight (l w))
    {v : H} (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) (hlv : l v ≠ 0) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) :
    ∃ y : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ y ∧ l (σ t y) ≠ 0 ∧ ∀ a : ℂ, l (a • σ t y) = a • l (σ t y) := by
  obtain ⟨μG, hμG⟩ := unitary_group_haar_exists k r
  have hGsk : IsHaarOn (UH (Hpk k r)) μG := ⟨B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩
  have hS := Formalism.L2.SG.Pf.Choice.isHaarOn_muS hz hT hW hW1 h0 h1
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists k r z hz hT μG _ hGsk hS
  have hN : IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1
  have hB := PI.WBL.S5.G.beBessel_of growth_spherical_bound
    ⟨CompanionTheory.FamilyDerivativeExpansion.DecS.decay_low_range, CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩
    k r ε lam h H σ w0 Wp z c u π μW _ μG νq ⟨hlam, hσ, hg, hO, hw0, hz, hT, hc, hπ, hW, hN, hGsk, hq⟩ v (Or.inr hv) (l v)
  have hvs := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ v hv
  have hn : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hlv
  have he : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) x v (l v) = ⟪l v, l v⟫_ℂ • l x := fun x hx => by
    rw [hl x hx v hvs]; rfl
  obtain ⟨y, hy, hne⟩ := nz_translate hKD hlam hσ hB ht hvs (by
    show ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) v v (l v) ≠ 0
    rw [he v hvs]; exact smul_ne_zero hn hlv)
  have hys := TranslationBesselVanishing.smooth_translate hσ (CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ y hy) ht
  refine ⟨y, hy, fun h0 => hne ?_, fun a => ?_⟩
  · show ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) _ v (l v) = 0
    rw [he _ hys, h0, smul_zero]
  · have h2 : ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) (a • σ t y) v (l v) =
        a • ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) (σ t y) v (l v) := hB.2.1 a _ hys
    rw [he _ hys, he _ (DDSmoothness.smooth_smul a hys), smul_comm] at h2
    exact smul_right_injective _ hn h2

end Formalism.MainStatements.RankOne
end
end

section -- merged from CompanionTheory.AutomorphicTheory.RankOneTori.Factor
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.FourierDecayAlt
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

def lamP (L : LocBessel k r) (l : L.Hs → L.Wp) (P : L.Hs →L[ℂ] L.Wp) : ℂ :=
  ∑ i, ⟪l (ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ L.Wp i)), stdOrthonormalBasis ℂ L.Wp i⟫_ℂ

def lamQ (L : LocBessel k r) (l' : L.Hs → L.Wq) (Q : L.Wq →L[ℂ] L.Hs) : ℂ :=
  ∑ j, ⟪stdOrthonormalBasis ℂ L.Wq j, l' (Q (stdOrthonormalBasis ℂ L.Wq j))⟫_ℂ

theorem coef_expand (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P.comp ((L.σ x).comp Q) = ∑ i, ∑ j, Pv.AmpDD.coefF L (ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ L.Wp i))
      (Q (stdOrthonormalBasis ℂ L.Wq j)) (stdOrthonormalBasis ℂ L.Wp i) (stdOrthonormalBasis ℂ L.Wq j) x := by
  ext η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, Pv.AmpDD.coefF,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left, smul_smul]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wp).sum_repr' (P (L.σ x (Q η)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wq).sum_repr' η]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]

theorem int_coefF (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ} (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) {ν : Measure (PairSp k r)}
    (hae : ∀ᵐ p ∂ν, InPair L p) {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Pv.AmpDD.pairMaj γ b) ν) {v v' : L.Hs}
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * B.gN g ^ (-a)) (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (Pv.AmpDD.coefF L v v' ξ ξ') γ) ν := by
  have : SigmaFinite μG := hμG.1
  set K : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG :=
      integral_nonneg fun x => Real.rpow_nonneg (P.S3dx6.gN_nonneg _) _
    positivity
  have hsm : StronglyMeasurable fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG :=
    (sm_PsiM L w0 v v' ξ ξ' γ).integral_prod_right'
  have he : ∀ p, InPair L p → ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG = ∫ x, Psi L w0 v v' ξ ξ' γ p x ∂μG := fun p hp =>
    integral_congr_ae ((ae_mem_sk hμG).mono fun x hx => PsiM_eq L w0 v v' ξ ξ' hγ hp hx)
  have hI : Integrable (fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG) ν := by
    refine (hpm.const_mul K).mono' hsm.aestronglyMeasurable (hae.mono fun p hp => ?_)
    rw [he p hp]
    have h1 := (enorm_integral_le_lintegral_enorm _).trans
      (lint_G_bound L hμG P.norm_inverse_bound hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp)
    rw [← ofReal_norm_eq_enorm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (pairMaj_nonneg γ b p))).1 h1
  refine (hI.smul (d : ℂ)).congr (hae.mono fun p hp => ?_)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Pi.smul_apply]
  rw [he p hp, (schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp).2, smul_smul, mul_inv_cancel₀ hd', one_smul]

theorem cell_factor (L : LocBessel k r) {a : ℝ} {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (Sm : Set L.Hs) (hdec : ∀ v ∈ Sm, ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C * B.gN g ^ (-a))
    (hl : ∀ v ∈ Sm, ∀ t ∈ UH (Hpk k r), ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ t w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ t w0)))
    (hl' : ∀ v ∈ Sm, ∀ t ∈ UH (Hpk k r), ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ t w0) v =
      (innerSL ℂ (l' v)).smulRight (l' (L.σ t w0)))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hc : Cell L a γ μR ν) :
    ∃ Ψ : L.Wq →L[ℂ] L.Wp, ∀ (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs),
      (∀ x, ContinuousLinearMap.adjoint P x ∈ Sm) → (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      (∀ x ∈ UH (Hpk k r), F x = P.comp ((L.σ x).comp Q)) → OrbInt L F γ ν = (lamP L l P * lamQ L l' Q) • Ψ := by
  obtain ⟨hγ, hrel, hR, hq, hinv, b, hb, hab, hpm⟩ := hc
  obtain ⟨μG, hμG0⟩ := P.unitary_group_haar_exists k r
  have hμG : IsHaarOn (UH (Hpk k r)) μG := ⟨P.B5.haar_sigmaFinite hμG0, hμG0.ne_zero, hμG0.conc, hμG0.left⟩
  obtain ⟨νR, hν⟩ := quot_exists hγ hμG hR
  obtain ⟨d, hd, hSch⟩ := P.schur_hermitian k r L.ε L.lam L.Hs L.σ μG L.hlam L.hσ hμG
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hAG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hab' : b ≤ a := by linarith
  have hIG : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (b - a)) μG := by
    have h1 := P.growth_group_bound k r μG (a - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hae := ae_inPair_nu L hR hq
  refine ⟨(d : ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ, fun P Q hP hQ F hF => ?_⟩
  set e := stdOrthonormalBasis ℂ L.Wp with he
  set e' := stdOrthonormalBasis ℂ L.Wq with he'
  choose C1 hC1 using fun i => hdec _ (hP (e i))
  choose C2 hC2 using fun j => hdec _ (hQ (e' j))
  have hI := fun i j => int_coefF L hμG hd hSch hw1 hγ hae hb hab' hIG hpm (hC1 i) (hC2 j) (e i) (e' j)
  have hA := fun i j => amp_core' L hμG hd hSch Formalism.FourierDecayAlt.P.norm_inverse_bound hw1 l l' hγ hrel hR hq hν hinv hb hab' hIG hpm
    (hl _ (hP (e i))) (hl' _ (hQ (e' j))) (hC1 i) (hC2 j) (e i) (e' j)
  have h1 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (Pv.AmpDD.coefF L (ContinuousLinearMap.adjoint P (e i)) (Q (e' j))
      (e i) (e' j)) γ ν := by
    unfold OrbInt
    simp only [← integral_finsetSum _ fun j _ => hI _ j]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    refine integral_congr_ae (hae.mono fun p hp => ?_)
    have hx := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)) hγ)
      hp.2.2.2.1) hp.2.2.1.1
    simp only [besselIntg]
    rw [hF _ hx, coef_expand]
    ext x
    simp [Finset.smul_sum, he, he']
  rw [h1, lamP, lamQ, Finset.sum_mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, hA i j, smul_smul, mul_inv_cancel₀ hd', one_smul]

end Formalism.MainStatements.RankOne
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.FourierDecayAlt Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.SG.Pf.OBT Formalism.BasicNotions
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

set_option maxHeartbeats 1600000 in
theorem gap_arith (hk : 1 ≤ k) {C : ℝ} (hC : 100 ≤ C) :
    ThreeDimData.GapOK k r (C * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
    Pv.AmpDD.GapCell k r (C * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hne : n = 2 * r + k + 1 := by rw [hn]; push_cast; ring
  set m : ℝ := 2 * ((r : ℝ) + 1) with hm
  have hme : ((2 * r + 2 : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have hm2 : 2 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  set s := Real.sqrt m with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hpow : m ^ ((9 : ℝ) / 2) = m ^ 4 * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  set X : ℝ := ((3 * (r + 1) : ℕ) : ℝ) * n ^ 2 + n ^ 3 with hX
  have hn1 : 1 ≤ n := by linarith
  have hXn : n ^ 3 ≤ X := by rw [hX]; exact le_add_of_nonneg_left (by positivity)
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  set Y : ℝ := m ^ 2 * n ^ 3 with hY
  have hY4 : 4 * n ^ 3 ≤ Y := mul_le_mul_of_nonneg_right hm4 (by positivity)
  have ha : ThreeDimData.aOf r (C * m ^ ((9 : ℝ) / 2) * X) = C * m ^ 4 * X / 8 := by
    unfold ThreeDimData.aOf
    rw [hpow, ← hm, ← hs]
    field_simp
  have hbig : 400 * Y ≤ C * m ^ 4 * X := by
    have e1 : 4 * Y ≤ m ^ 4 * X := by
      calc 4 * Y ≤ m ^ 2 * Y := mul_le_mul_of_nonneg_right hm4 (by positivity)
        _ = m ^ 4 * n ^ 3 := by rw [hY]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hXn (by positivity)
    calc 400 * Y = 100 * (4 * Y) := by ring
      _ ≤ C * (m ^ 4 * X) := mul_le_mul hC e1 (by positivity) (by linarith)
      _ = _ := by ring
  have hdN : ThreeDimData.dN k r ≤ n ^ 2 := by unfold ThreeDimData.dN; rw [hne]; nlinarith
  have hdN0 : 0 ≤ ThreeDimData.dN k r := by unfold ThreeDimData.dN; nlinarith
  have hAS : ThreeDimData.AS k r ≤ n ^ 3 := by
    unfold ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) ≤ n := by push_cast; linarith
    calc _ ≤ n * n ^ 2 := mul_le_mul this hdN hdN0 (by linarith)
      _ = _ := by ring
  have hAS0 : 0 ≤ ThreeDimData.AS k r := mul_nonneg (Nat.cast_nonneg _) hdN0
  have hAG : ThreeDimData.AG k r ≤ 4 * n ^ 3 := by
    unfold ThreeDimData.AG
    have : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ n * n := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have e : n ^ 2 = n * n := by ring
    calc _ = 4 * (((k : ℝ) + r) * ((r : ℝ) + 1)) := by ring
      _ ≤ _ := by linarith
  have hAG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hM : ThreeDimData.Mexp r ≤ m ^ 2 / 2 := by
    have e : m ^ 2 / 2 = 2 * ((r : ℝ) ^ 2 + r + 1) + 2 * r := by rw [hm]; ring
    unfold ThreeDimData.Mexp
    linarith
  have h1 : 2 * ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 5 * Y := by
    calc _ ≤ m ^ 2 * (5 * n ^ 3) := mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = _ := by rw [hY]; ring
  have h2 : 9 * ((r : ℝ) + 1) * n ^ 2 ≤ 9 * n ^ 3 := by
    have : ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc _ = 9 * (((r : ℝ) + 1) * n ^ 2) := by ring
      _ ≤ 9 * (n * n ^ 2) := by linarith
      _ = _ := by ring
  have h3 : 10 * ((r : ℝ) + 1) ^ 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 50 * Y / 4 := by
    have e : 10 * ((r : ℝ) + 1) ^ 2 = 10 * m ^ 2 / 4 := by rw [hm]; ring
    calc _ ≤ 10 * m ^ 2 / 4 * (5 * n ^ 3) := by
          rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [hY]; ring
  rw [hme]
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · rw [hpow]
    have : C * m ^ 4 * X ≤ C * (m ^ 4 * s) * X := by
      have h0 : 0 ≤ C * m ^ 4 * X := by linarith
      calc _ ≤ C * m ^ 4 * X * s := le_mul_of_one_le_right h0 hs1
        _ = _ := by ring
    linarith
  · rw [ha]; linarith
  · rw [ha]; linarith
  · unfold Pv.AmpDD.GapCell
    rw [ha]; linarith

theorem exists_low {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) : ∃ w : H, IsLowUnitH k r ε lam σ w := by
  obtain ⟨A, hA, -, -, -, -, -, ⟨S, hS⟩, -⟩ := h
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, A, hA, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · exact Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε _ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hvS)

theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {y : H}
    (hy : IsKFinHpk (k := k) (r := r) σ y) (a : ℂ) : IsKFinHpk (k := k) (r := r) σ (a • y) := by
  obtain ⟨S, h1, h2, h3⟩ := hy
  exact ⟨S, h1, S.smul_mem a h2, h3⟩

theorem rankOne_core (hKD : Pv.AmpDD.KDense) (L : LocBessel k r) {κ₀ h : ℝ} (hκ₀ : 0 < κ₀) (hc : L.c = cOfDpsi (κ₀ : ℂ))
    (h0 : L.κN ≠ 0) (h1 : L.κN ≠ ⊤) (hg : Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h) (hO : ThreeDimData.GapOK k r h)
    (hC : Pv.AmpDD.GapCell k r h) :
    ∃ (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (Ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ) (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj k r κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0) := by
  classical
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hc0 : L.c ≠ 0 := by
    rw [hc, cOfDpsi]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hκ₀.ne')
  obtain ⟨l, hl⟩ := be_rank_scale hO.1 L.hlam hσ hg hO.2.1 L.hz.1 L.hz.2 L.hπ L.hμW.1 h0 h1 hκ₀
  obtain ⟨l', hl'⟩ := be_rank_scale hO.1 L.hlam hσ hg hO.2.1 L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1 h0 h1 hκ₀
  rw [← hc] at hl hl'
  obtain ⟨w0, hw0⟩ := exists_low L.hσ
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hKS := CompanionTheory.D.gk.admitted.k_finite_smooth k r L.ε L.lam L.Hs L.σ L.hlam hσ
  have hw0s := hKS w0 hw0K
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    obtain ⟨_, _, hw⟩ := hw0
    have hnorm : ‖w0‖ = 1 := hw.1
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  set Sm := PI.UpqRep.smoothVecs (k := k) (r := r) L.σ with hSm
  have hdec : ∀ v ∈ Sm, ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C * B.gN g ^ (-(ThreeDimData.aOf r h - 1)) := by
    obtain ⟨C, Ws, -, hb⟩ := CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range k r L.ε L.lam h L.Hs L.σ L.hlam hσ hg hO w0 hw0K
    intro v hv
    refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v‖).sum, fun g hgU => ?_⟩
    have := hb v hv g⁻¹ (WeylGroupFacts.uh_inv hgU)
    rw [((P.norm_inverse_bound k r).2 g hgU).1] at this
    rw [P.MatrixMultiplicationContinuity.sigma_inner hσ hgU, norm_inner_symm, neg_sub]
    exact this
  have key := fun (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
      (hcell : Cell L (ThreeDimData.aOf r h - 1) γ μR ν) =>
    cell_factor L hw1 l l' Sm hdec (fun v hv t ht => hl _ (P.TranslationBesselVanishing.smooth_translate hσ hw0s ht) v hv)
      (fun v hv t ht => hl' _ (P.TranslationBesselVanishing.smooth_translate hσ hw0s ht) v hv) hcell
  have key2 : ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)), ∃ Ψ : L.Wq →L[ℂ] L.Wp,
      ∀ μR, Cell L (ThreeDimData.aOf r h - 1) γ μR ν → ∀ (A : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs),
      (∀ x, ContinuousLinearMap.adjoint A x ∈ Sm) → (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      (∀ x ∈ UH (Hpk k r), F x = A.comp ((L.σ x).comp Q)) → OrbInt L F γ ν = (lamP L l A * lamQ L l' Q) • Ψ := by
    intro γ ν
    by_cases hex : ∃ μR, Cell L (ThreeDimData.aOf r h - 1) γ μR ν
    · obtain ⟨μR, hμ⟩ := hex
      obtain ⟨Ψ, hΨ⟩ := key γ μR ν hμ
      exact ⟨Ψ, fun _ _ => hΨ⟩
    · exact ⟨0, fun μR hμ => absurd ⟨μR, hμ⟩ hex⟩
  choose Ψ hΨ using key2
  have hdata : ∀ (A : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs), (∀ x, ContinuousLinearMap.adjoint A x ∈ Sm) →
      (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), (∀ x ∈ UH (Hpk k r), F x = A.comp ((L.σ x).comp Q)) →
      HasBData L F (lamP L l A * lamQ L l' Q) (fun g => Ψ g (pairMeas L)) Ψ := fun A Q hA hQ F hF =>
    ⟨fun c μ hc' hμ => hΨ _ _ _ (cell_big hO.1 L h0 h1 hC c μ hc' hμ) A Q hA hQ F hF,
      fun γ g μR ν hG a1 a2 a3 a4 => hΨ _ _ _ (cell_small L hc0 h1 hO hC hG a1 a2 a3 a4) A Q hA hQ F hF⟩
  have hadj : ∀ {κ τ : ℝ}, 0 < κ → 0 < τ → ∀ (A : L.Hs →L[ℂ] L.Wp) (x : L.Wp),
      ContinuousLinearMap.adjoint (A.comp (L.σ (dMi k r κ τ))) x =
        L.σ (dM k r κ τ) (ContinuousLinearMap.adjoint A x) := by
    intro κ τ hκ hτ A x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      P.MatrixMultiplicationContinuity.sigma_inner hσ (dMi_mem_UH hκ hτ), dMi_inv hκ hτ]
  refine ⟨fun g => Ψ g (pairMeas L), Ψ, fun A Q => lamP L l A * lamQ L l' Q,
    fun A Q κ τ => lamP L l (A.comp (L.σ (dMi k r κ τ))) * lamQ L l' ((L.σ (dM k r κ τ)).comp Q),
    fun A Q hAQ => hdata A Q (fun x => hKS _ (hAQ.2 x)) (fun w => hKS _ (hAQ.1 w)) _ fun _ _ => rfl,
    fun A Q κ τ hκ hτ hAQ => hdata _ _ (fun x => ?_) (fun w => ?_) _ fun x hx => ?_, fun κ τ hκ hτ A Q hAQ hne => ?_⟩
  · rw [hadj hκ hτ]
    exact P.TranslationBesselVanishing.smooth_translate hσ (hKS _ (hAQ.2 x)) (dM_mem_UH hκ hτ)
  · exact P.TranslationBesselVanishing.smooth_translate hσ (hKS _ (hAQ.1 w)) (dM_mem_UH hκ hτ)
  · show A.comp ((L.σ (dMi k r κ τ * x * dM k r κ τ)).comp Q) = _
    rw [P.TranslationBesselVanishing.sigma_mul hσ (WeylGroupFacts.uh_mul (dMi_mem_UH hκ hτ) hx) (dM_mem_UH hκ hτ),
      P.TranslationBesselVanishing.sigma_mul hσ (dMi_mem_UH hκ hτ) hx]
    rfl
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hne)
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hne)
    obtain ⟨y, hy, hy1, hy2⟩ := side_nz hKD L.hlam hσ hg hO hw0 L.hz.1 L.hz.2 hc0 L.hπ L.hμW.1 L.hμW.2 h0 h1 hl
      (hAQ.2 _) (fun h => hi (by rw [h, inner_zero_left])) (dM_mem_UH hκ hτ)
    obtain ⟨y', hy', hy1', hy2'⟩ := side_nz hKD L.hlam hσ hg hO hw0 L.hz'.1 L.hz'.2 hc0 L.hπ' L.hμW'.1 L.hμW'.2 h0 h1 hl'
      (hAQ.1 _) (fun h => hj (by rw [h, inner_zero_right])) (dM_mem_UH hκ hτ)
    set ξ := l (L.σ (dM k r κ τ) y) with hξ
    set ξ' := l' (L.σ (dM k r κ τ) y') with hξ'
    have ha : ∀ x : L.Wp, ContinuousLinearMap.adjoint ((innerSL ℂ y).smulRight ξ) x = ⟪ξ, x⟫_ℂ • y := fun x => by
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    refine ⟨(innerSL ℂ y).smulRight ξ, (innerSL ℂ ξ').smulRight y', ⟨fun w => kfin_smul hy' _, fun x => ?_⟩,
      mul_ne_zero ?_ ?_⟩
    · rw [ha]; exact kfin_smul hy _
    · simp only [lamP, hadj hκ hτ, ha, map_smul, hy2, inner_smul_left, inner_conj_symm]
      simp only [mul_comm ⟪stdOrthonormalBasis ℂ L.Wp _, ξ⟫_ℂ]
      rw [OrthonormalBasis.sum_inner_mul_inner]
      exact inner_self_ne_zero.2 hy1
    · simp only [lamQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
        hy2', inner_smul_right]
      rw [OrthonormalBasis.sum_inner_mul_inner]
      exact inner_self_ne_zero.2 hy1'

theorem rankOneTor_of_kDense (hKD : Pv.AmpDD.KDense) (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : RankOneTor D Cgf := by
  intro L κ₀ hκ₀ hc h0 h1 _ hg
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨a1, a2⟩ := gap_arith (r := D.R.rS) hk hC
  exact rankOne_core hKD L hκ₀ hc h0.ne' h1 hg a1 a2

theorem k_finite_dense : Pv.AmpDD.KDense := KD.kDense

theorem rank_one_torus_bound (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : RankOneTor D Cgf := rankOneTor_of_kDense k_finite_dense D hC

theorem one_bessel_torus_bound (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : OneBesselTor D Cgf :=
  oneBesselTor_of_rankOne D Cgf (rank_one_torus_bound D hC)

end Formalism.MainStatements.RankOne
