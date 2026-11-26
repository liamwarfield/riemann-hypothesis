module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspAverageKFiniteDecomposition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardFormApproximationOfDecay
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SobolevApproximationByCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ENNReal
namespace GlobalTheory.SobolevCuspApprox
theorem sobolev_approximation_by_cuspForms : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB _ i _ φ hφ U hU hlev d δ hδ
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨hAut, hc, -⟩ := id hφ
  have hφg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V φ :=
    ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hAut hc, hc⟩
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h)] at hr1
    exact lt_irrefl _ hr1
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D R.θ hθ (G.P (i + 1)) φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList
    (Finset.nodup_toList _) d r hr
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D R.θ hθ hP (G.P (i + 1)) φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  let F' : ℕ → (G.P (i + 1)).Maps := fun k => if h : k < n then F ⟨k, h⟩ else 0
  let v' : ℕ → Formalism.IndefR.Links.SmT (G.P (i + 1)).M := fun k => if h : k < n then v ⟨k, h⟩ else 0
  have hval : ∀ j : Fin n, F' j (v' j) = F j (v j) := fun j => by simp [F', v', j.2]
  have hsumeq : ∑ k ∈ Finset.range n, F' k (v' k) = ∑ j, F j (v j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => F' k (v' k))]
    exact Finset.sum_congr rfl fun j _ => hval j
  refine ⟨Finset.range n, F', v', fun k hk => ?_, fun k hk u hu hu' g => ?_, ?_⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', hk'] using hF ⟨k, hk'⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', v', hk'] using hFlev ⟨k, hk'⟩ u hu hu' g
  · rw [hsumeq]
    have hsg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (∑ j, F j (v j)) :=
      Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
        (GlobalTheory.CuspApproxAll.good_zero R.θ (G.P (i + 1)).V) fun j _ =>
          GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ (G.P (i + 1)) (hF j) (v j)
    have hg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (φ - ∑ j, F j (v j)) := by
      have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
      rwa [neg_one_smul, ← sub_eq_add_neg] at this
    exact ⟨fun e' => GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1 e', lt_of_le_of_lt hgrow hr2⟩
end GlobalTheory.SobolevCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_sobolev_density : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  first | exact @_root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | exact _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | (intros; apply _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DecayIntegralBoundedBySobolevGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownConv
theorem decayIntegral_le_sobolevGrowth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi U hU M
  obtain ⟨hν, h𝓕⟩ := MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  obtain ⟨d, C₀, hC⟩ := hP.cuspDecaySobolev D R.θ hB.inf (G.P (i + 1)).V U hU 0 M
  have hfin : (G.mP (i + 1)).ν (G.mP (i + 1)).fd < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν h𝓕
  refine ⟨d, C₀ * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toNNReal, fun ψ ha hk hs hg hc => ?_⟩
  refine (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt_le _ _ M ψ).trans ?_
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin.ne, mul_right_comm]
  exact mul_le_mul' (hC ψ ha hk hs hg hc) le_rfl
end GlobalTheory.DownConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decay_integral_bounded_by_sobolev_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ := by
  first | exact @_root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth | exact _root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth | (intros; apply _root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftedGrowthBoundedByDecayIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownLiftGrowth
theorem growthSize_lift_le_decayIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  intro _ D _ G₀ _ _ Pl0 T Af Ks _ _ _ R G hB hG i hi
  obtain ⟨N, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.sgn true (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨N, fun Φ hΦ => ?_⟩
  have hω := (hG.arrows.dn i hi).weil
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real R.ψ hB.inf hU
  have hb := (hC _ _ _ hω μ 𝓕 hμ Φ hl).2
  set K := C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 ENNReal.toReal_nonneg
  have e : ∀ g h, thetaKO (G.dn i).ω g h Φ =
      thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm g) h Φ := fun g h => by
    show (G.dn i).ω (g, h) Φ 0 = (G.dn i).ω (GlobalTheory.Grid.ofSgn true _ ((GlobalTheory.Grid.ofSgn true _).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g,
      thetaKO (G.dn i).ω (γ * g) h Φ = thetaKO (G.dn i).ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hk : ∀ g h, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
      K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N := by
    intro g h
    have h1 : ∀ g, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
        (K * GlobalTheory.Grow.height (G.P i).V h ^ N) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ N := fun g => by
      rw [e]
      have h2 := hb ((GlobalTheory.Grid.ofSgn true _).symm g) h
      have hh : GlobalTheory.Grow.height (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm g) =
          GlobalTheory.Grow.height (G.P (i + 1)).V g := rfl
      rw [hh] at h2
      exact h2.trans_eq (by rw [hK, mul_pow]; ring)
    exact (GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) h1 g).trans_eq (by ring)
  refine ⟨(K * 2 ^ N).toNNReal, fun f => iSup_le fun h => ?_⟩
  have hg := pow_pos (GlobalTheory.Grow.height_pos (G.P i).V h) N
  rw [ENNReal.ofReal_div_of_pos hg, ofReal_norm_eq_enorm]
  refine ENNReal.div_le_of_le_mul ((enorm_integral_le_lintegral_enorm _).trans ?_)
  rw [mul_right_comm, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt]
  refine (lintegral_mono fun g => ?_).trans_eq
    (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
  have hq := (pow_pos (GlobalTheory.Grow.quotHeight_pos (G.P (i + 1)).V g) N).le
  rw [← ofReal_norm_eq_enorm]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (K * 2 ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]
  calc ‖thetaKO (G.dn i).ω g h Φ‖ * ‖f g‖
      ≤ (K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N) * ‖f g‖ :=
        mul_le_mul_of_nonneg_right (hk g h) (norm_nonneg _)
    _ = _ := by ring
end GlobalTheory.DownLiftGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  first | exact @_root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | exact _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | (intros; apply _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnFormApprox
variable {D : D7}
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem decay_integral_approximation (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ (M : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ M δ hδ
  obtain ⟨U, hU, hk⟩ := hφ.1.level
  obtain ⟨d, C, hC⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi U hU M
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hlev, hfin, hd⟩ := s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ U hU hk d (δ / C')
    (ENNReal.div_pos hδ.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  have hs := autSm_cusp_sum K (fun k => F k (v k)) fun k hk => autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)
  have hψ : IsAutFunSm R.θ (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) ∧ IsCuspFun (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (∑ k ∈ K, F k (v k))]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hφ.1 (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1),
      GlobalTheory.MultMem.isCuspFun_add hφ.1.toIsAutFun (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1).toIsAutFun hφ.2.1
        (GlobalTheory.MultMem.isCuspFun_smul _ hs.2)⟩
  have hlevψ : ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, (φ - ∑ k ∈ K, F k (v k)) (g * u) = (φ - ∑ k ∈ K, F k (v k)) g := by
    intro u hu hu' g
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [hk u hu hu' g]
    congr 1
    exact Finset.sum_congr rfl fun k hkK => hlev k hkK u hu hu' g
  calc GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k))
      ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        hC _ hψ.1.toIsAutFun hlevψ hψ.1.smooth hfin hψ.2
    _ ≤ C' * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (δ / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = δ := ENNReal.mul_div_cancel hC0 hCt
theorem downward_form_approximation_of_decay (s1 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f) (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ
  obtain ⟨N, hN⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  refine ⟨N, fun Φ hΦ ε hε => ?_⟩
  obtain ⟨C, hC⟩ := hN Φ hΦ
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hd⟩ := _root_.GlobalTheory.DnFormApprox.decay_integral_approximation s2 s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ N (ε / C')
    (ENNReal.div_pos hε.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  have hint : ∀ u : GA D (G.P (i + 1)).V → ℂ, IsAutFunSm R.θ (G.P (i + 1)).V u → IsCuspFun (G.P (i + 1)).V u → ∀ h,
      IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * u g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := fun u hu hc h =>
    GlobalTheory.DownConv.integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hu hc h
  have e : (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) -
      ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (F k (v k)) g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν := by
    funext h
    have hk : ∀ k ∈ K, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * (F k (v k)) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν :=
      fun k hk => hint _ (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).1 (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).2 h
    rw [← integral_finsetSum _ hk, ← integral_sub (hint φ hφ.1 hφ.2.1 h) (integrable_finsetSum _ hk)]
    congr 1
    funext g
    simp [Pi.sub_apply, Finset.sum_apply, mul_sub, Finset.mul_sum]
  rw [e]
  calc GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν)
      ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) := hC _
    _ ≤ C' * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (ε / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = ε := ENNReal.mul_div_cancel hC0 hCt
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem downward_form_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε :=
  _root_.GlobalTheory.DnFormApprox.downward_form_approximation_of_decay _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral _root_.GlobalTheory.T.decay_integral_bounded_by_sobolev_growth _root_.GlobalTheory.T.cuspForm_sobolev_density
end GlobalTheory.DnFormApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_form_downward_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DnFormApprox.downward_form_approximation | exact _root_.GlobalTheory.DnFormApprox.downward_form_approximation | (intros; apply _root_.GlobalTheory.DnFormApprox.downward_form_approximation <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedFormDownwardGrowthBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownGrowth
open GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.DownApprox
open scoped ENNReal
set_option maxHeartbeats 2000000 in
theorem downward_growth_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi
  classical
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨Ae, fun K Fm v hF Φ hΦ ε hε => ?_⟩
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : ∀ k ∈ K, GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm k (v k)) := fun k hk => by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 (Fm k) (hF k hk) (v k)
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  have hB : ∀ k ∈ K, ∃ B : ℝ, ∀ g, ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ B :=
    fun k hk => (hFv k hk).decay Ae
  choose! B hB using hB
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)
  have hker : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ g h,
        ‖thetaKO (G.dn i).ω g h f‖ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
          GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨C, hC0, hC⟩ := (H (neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU'
    refine ⟨C * 2 ^ Ae, by positivity, fun f hf g h => ?_⟩
    have hb := (hC _ _ ((G.dn i).ω.toSgn true) hω μ 𝓓 hμ f hf).2
    have hinv : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, thetaKO (G.dn i).ω (γ * g) h f = thetaKO (G.dn i).ω g h f := fun γ hγ g => by
      have e1 : (((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) : GA D (neg (G.P (i + 1)).V) × GA D (G.P i).V) =
          ((ofSgn true (G.P (i + 1)).V).symm γ, 1) * ((ofSgn true (G.P (i + 1)).V).symm g, h) := by simp
      show ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) f 0 =
        ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm g, h) f 0
      rw [e1, map_mul, Module.End.mul_apply]
      exact hω.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω.om_pres _ _ hf.1)
    have hgr : ∀ g, ‖thetaKO (G.dn i).ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        GlobalTheory.Grow.height (G.P i).V h ^ Ae) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ Ae := fun g => by
      have := hb ((ofSgn true (G.P (i + 1)).V).symm g) h
      refine this.trans_eq ?_
      show C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        (GlobalTheory.Grow.height (G.P (i + 1)).V g * GlobalTheory.Grow.height (G.P i).V h) ^ Ae = _
      ring
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO (G.dn i).ω g h f) hinv hgr g).trans_eq ?_
    ring
  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ k ∈ K, ∀ h,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm k (v k) g ∂(G.mP (i + 1)).ν‖ ≤
          Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal *
            GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨Kc, hK0, hK⟩ := hker U' hU'
    refine ⟨Kc, hK0, fun f hf k hk h => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul (hFv k hk).continuous
    have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm k (v k) g‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h3 : ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max (B k) 0 :=
        (hB k hk g).trans (le_max_left _ _)
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm k (v k) g‖
          ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm k (v k) g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae * max (B k) 0 := by
          gcongr
        _ = _ := by ring
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  obtain ⟨Kc, hK0, hMb⟩ := hbound U hU
  have hvol : 0 ≤ ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal := ENNReal.toReal_nonneg
  have hBs : 0 ≤ ∑ k ∈ K, max (B k) 0 := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hM0 : 0 ≤ Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 := by positivity
  obtain ⟨r, -, hr0', hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr0'
  set M := Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 with hMdef
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (r / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g₀, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  let f' : ℕ → (WO (G.P (i + 1)).V (G.P i).V → ℂ) := fun j => if hj : j < n then f ⟨j, hj⟩ else 0
  let p' : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) := fun j => if hj : j < n then p ⟨j, hj⟩ else 0
  refine ⟨Finset.range n, f', p', fun j hj => ?_, ?_⟩
  · have hj' := Finset.mem_range.1 hj
    simp only [f', dif_pos hj']
    exact (isVacF_negFr _ _ _).1 (hf _)
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h
      (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l k hk h
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' k hk h).1
  have hΨU := sub_mem hΦU hgU
  have e : ∀ k ∈ K, ∀ h, (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm k (v k) g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm k (v k) g
          ∂(G.mP (i + 1)).ν := by
    intro k hk h
    rw [← integral_finsetSum _ fun l _ => hint l k hk h,
      ← integral_sub (hMb Φ hΦU k hk h).1 (integrable_finsetSum _ fun l _ => hint l k hk h)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  have hsw : ∀ h, ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∑ k ∈ K, ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g ∂(G.mP (i + 1)).ν := by
    intro h
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [f', p', dif_pos l.isLt, Fin.eta]
  set s := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d
    (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hle : GlobalTheory.Size.growthSize (G.P i).V Ae (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ *
      (Fm k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * (Fm k (v k)) g ∂(G.mP (i + 1)).ν) ≤
      ENNReal.ofReal (M * s) := by
    refine (GlobalTheory.Size.growthSize_le_iff (mul_nonneg hM0 hs0)).2 fun h => ?_
    rw [hsw h, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k hk => e k hk h]
    refine (norm_sum_le _ _).trans ?_
    rw [hMdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ((hMb _ hΨU k hk h).2).trans_eq ?_
    ring
  refine hle.trans_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrε)
  have hM1 : 0 < M + 1 := by linarith
  have h1 : (M + 1) * s < r := by
    have := mul_lt_mul_of_pos_left hs hM1
    rwa [mul_div_cancel₀ _ hM1.ne'] at this
  nlinarith
end GlobalTheory.DownGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_form_downward_growth_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DownGrowth.downward_growth_approximation | exact _root_.GlobalTheory.DownGrowth.downward_growth_approximation | (intros; apply _root_.GlobalTheory.DownGrowth.downward_growth_approximation <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnCusp
variable {D : D7}
end GlobalTheory.DnCusp
namespace GlobalTheory.DnCusp
theorem downward_theta_lift_isCuspidal_of_integrable (s1 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint
  obtain ⟨N₁, h1⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  obtain ⟨N₂, h2⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ
  have hdn := (hL D hS G₀ Pl0 T A Ks R G hB hG).dn i hi
  have haut := _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hB hG i hi Φ hΦ φ hφ hint
  set L : GA D (G.P i).V → ℂ := fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν with hLdef
  set N := max N₁ N₂
  have key : ∀ n : ℕ, ∃ ψ : GA D (G.P i).V → ℂ, (IsAutFun (G.P i).V ψ ∧ IsCuspFun (G.P i).V ψ) ∧
      GlobalTheory.Size.growthSize (G.P i).V N (ψ - L) ≤ ((n : ENNReal) + 1)⁻¹ := by
    intro n
    set ε : ENNReal := ((n : ENNReal) + 1)⁻¹ / 2 with hε
    have hε0 : 0 < ε := ENNReal.div_pos (ENNReal.inv_ne_zero.2 (by simp)) (by simp)
    obtain ⟨K, F, v, hF, hK⟩ := h2 Φ hΦ ε hε0
    obtain ⟨J, f, p, hf, hJ⟩ := h1 K F v hF Φ hΦ ε hε0
    have hF' : ∀ j ∈ J, ∀ k ∈ K, ∃ F' ∈ (G.P i).Cusp R.θ, ∀ h,
        (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) h := by
      intro j hj k hk
      obtain ⟨F', hF'm, hF'e⟩ := hdn (f j) (hf j hj) (F k) (hF k hk)
      exact ⟨F', hF'm, fun h => (hF'e (p j) (v k) h).2⟩
    refine ⟨fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν, ?_, ?_⟩
    · have hterm : ∀ j ∈ J, ∀ k ∈ K, IsAutFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) ∧
          IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) := by
        intro j hj k hk
        obtain ⟨F', hF'm, hF'e⟩ := hF' j hj k hk
        have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) := funext hF'e
        rw [e]
        exact ⟨GlobalTheory.RowLift.isAutFun_of_mem_cusp _ _ hF'm _, isCuspFun_of_mem_cusp _ _ hF'm _⟩
      have h0 : IsCuspFun (G.P i).V (0 : GA D (G.P i).V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
      have hsum : ∀ (s : Finset ℕ) (u : ℕ → GA D (G.P i).V → ℂ), (∀ a ∈ s, IsAutFun (G.P i).V (u a) ∧ IsCuspFun (G.P i).V (u a)) →
          IsAutFun (G.P i).V (fun h => ∑ a ∈ s, u a h) ∧ IsCuspFun (G.P i).V (fun h => ∑ a ∈ s, u a h) := by
        intro s u hu
        have e : (fun h => ∑ a ∈ s, u a h) = ∑ a ∈ s, u a := by funext h; simp [Finset.sum_apply]
        rw [e]
        clear e
        induction s using Finset.induction_on with
        | empty => simpa using ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          have hA := hu a (Finset.mem_insert_self a s)
          have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
          exact ⟨GlobalTheory.RowLift.isAutFun_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1 hB.1 hA.2 hB.2⟩
      exact hsum J _ fun j hj => hsum K _ fun k hk => hterm j hj k hk
    · set M : GA D (G.P i).V → ℂ := fun h => ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      set Ψ : GA D (G.P i).V → ℂ := fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      have e : Ψ - L = -((L - M) + (M - Ψ)) := by abel
      have e2 : GlobalTheory.Size.growthSize (G.P i).V N (Ψ - L) = GlobalTheory.Size.growthSize (G.P i).V N ((L - M) + (M - Ψ)) := by
        rw [e]; unfold GlobalTheory.Size.growthSize; congr 1; funext g; rw [Pi.neg_apply, norm_neg]
      rw [e2]
      refine (GlobalTheory.Size.growthSize_add_le).trans ?_
      have a1 : GlobalTheory.Size.growthSize (G.P i).V N (L - M) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_right N₁ N₂)).trans hK.le)
      have a2 : GlobalTheory.Size.growthSize (G.P i).V N (M - Ψ) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_left N₁ N₂)).trans hJ.le)
      refine (add_le_add a1 a2).trans (le_of_eq ?_)
      rw [hε, ENNReal.add_halves]
  choose ψ hψ hψb using key
  have ht : Filter.Tendsto (fun n => GlobalTheory.Size.growthSize (G.P i).V N (ψ n - L)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) Filter.atTop (nhds 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => bot_le) hψb
  exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto D (G.P i).V N ψ L
    (fun n => ⟨(hψ n).1.cont, (hψ n).1.left, (hψ n).2⟩) haut.cont haut.left ht
theorem downward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) :=
  _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal_of_integrable _root_.GlobalTheory.T.twisted_form_downward_growth_bound _root_.GlobalTheory.T.twisted_form_downward_approximation
end GlobalTheory.DnCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal | exact _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal | (intros; apply _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal <;> assumption)
end
