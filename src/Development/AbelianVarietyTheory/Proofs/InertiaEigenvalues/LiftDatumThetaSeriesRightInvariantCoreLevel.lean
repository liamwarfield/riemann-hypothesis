module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.LevelInv

theorem cast_mul {D : D7} {V W : HSp D} (e : V = W) (a b : GA D V) :
    cast (congrArg (GA D) e) (a * b) = cast (congrArg (GA D) e) a * cast (congrArg (GA D) e) b := by
  subst e
  rfl

theorem apply_eq_castDict {D : D7} {V W : HSp D} (e : V = W) (φ : GA D V → ℂ) (x : GA D V) :
    φ x = castDict e φ (cast (congrArg (GA D) e) x) := by
  subst e
  rfl

theorem thetaKO_mul_right {D : D7} {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (h : GA D V)
    (g κ : GA D W) (f : WO V W → ℂ) : thetaKO om h (g * κ) f = thetaKO om h g (om (1, κ) f) := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem ser_right_inv_levelK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (h : GA D (Vc D j)), h ∈ GfC (Vc D j) → ∀ (w : (Rl.cV j).W) (a : ℂ) (φ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ), castDict hV φ = (fun g => a * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w g) → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh w a φ hφ k hk g
  have hpb : T.pb = Rl.toRealDat.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev (hpins.2.tuple ()).half
  set k' : GA D (Wc D j) := cast (congrArg (GA D) hV) k with hk'def
  have hkk : cast (congrArg (GA D) hV.symm) k' = k := by rw [hk'def]; simp
  have hlift : Formalism.IndefR.Lev.IsLevelLift (Wc D j) (Rl.toRealDat.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k' :=
    (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV k').2 (by rw [hkk]; exact hk)
  have hv : Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.vP j A3.A.μ0) = (1 : ℂ) • Rl.toRealDat.vP j A3.A.μ0 := by
    have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar Rl.toRealDat hcore.lev hcore.models.inf hcore.thP.ωP hcore.thP.vP j A3.A.μ0 1 1 k'
      (GlobalTheory.RawLift.LevelFix.realDatum_identity_lifts_identity Rl.toRealDat j A3.A.μ0) hlift
    rw [e, GlobalTheory.RawLift.LevelFix.levChi_flag_one Rl.toRealDat j A3.A.μ0, inv_one]
  have hP : ∀ P, Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.ptP j A3.A.μ0 P) = Rl.toRealDat.ptP j A3.A.μ0 P := by
    intro P
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite Rl.toRealDat.ψ Rl.toRealDat.θ (Vc D j) (Wc D j) _ _
      (Rl.toRealDat.ωP j A3.A.μ0) hcore.models.inf (hcore.thP.ωP j A3.A.μ0) _ _ _ _ _ (hcore.thP.pt_theta j A3.A.μ0) 1
      (Subgroup.one_mem _) k' hlift.1 1 hv P
    exact this.trans (one_smul ℂ _)
  have hser : ∀ x, ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w (x * k') = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w x := by
    intro x
    rw [ser_vP, ser_vP, thetaKO_mul_right, hP]
  have e1 : φ (g * k) = castDict hV φ (cast (congrArg (GA D) hV) g * k') := by
    exact (apply_eq_castDict hV φ (g * k)).trans (congrArg (castDict hV φ) (cast_mul hV g k))
  have e2 : φ g = castDict hV φ (cast (congrArg (GA D) hV) g) := apply_eq_castDict hV φ g
  rw [e1, e2, hφ]
  exact congrArg (fun z => a * z) (hser _)

end GlobalTheory.SeriesTie.LevelInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftDatum_thetaSeries_right_invariant_coreLevel : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (h : GA D (Vc D j)), h ∈ GfC (Vc D j) → ∀ (w : (Rl.cV j).W) (a : ℂ) (φ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ), castDict hV φ = (fun g => a * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w g) → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := by
  first | exact @GlobalTheory.SeriesTie.LevelInv.ser_right_inv_levelK | exact GlobalTheory.SeriesTie.LevelInv.ser_right_inv_levelK | (intros; apply GlobalTheory.SeriesTie.LevelInv.ser_right_inv_levelK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanInverseThetaIdentity
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacFixOpen


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vacO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → T.SigOK →
    ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J → om (x, 1) f₀ = f₀ := by
  intro D ψ θ S T χS χT om hW hSs hTs sS sT hcS hcT ΛS ΛT hsdS hsdT f₀ hvac
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const :
      Continuous fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial x →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n₁.factorial k → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, 1) f₀ = c • f₀ := by
    intro k hk hc
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True), u = actO S T k 1 u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ 1 u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D T) u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one T θ τ (sT τ)) hΛ f₀ hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ S T sS sT hSs hTs hcS hcT ΛS ΛT hsdS hsdT f₀ _ hvac hvac'
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D S => om (k, 1) f₀ w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k → om (k, 1) f₀ = f₀ := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, 1) f₀ = c • f₀ ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.SmoothVac.om_pow_eq om (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om ((1 : GA D S), (1 : GA D T)) f₀ w₀ = f₀ w₀ := by
      show om 1 f₀ w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖f₀ w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (f₀ w₀)]
  obtain ⟨n, hn⟩ := key
  have hN : 0 < n₁.factorial * n.factorial := Nat.mul_pos n₁.factorial_pos n.factorial_pos
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial)).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S hN, fun k hk hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S k := congrArg Subtype.val e
  refine hn k hk ?_
  have hc := hk'.2
  unfold GlobalTheory.Member.FinCong at hc ⊢
  rw [← e']
  exact hc

end GlobalTheory.VacFixOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory.RSTheta

theorem summable_tsum_norm_le_of_le_shortest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ) (hN : Module.finrank ℝ (Fin a → Cinf E) ≤ N) :
    ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A →
      (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J →
        c ξ = 0) →
      (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J →
        ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤
          A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) →
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, 0, fun _ _ _ _ _ _ => ⟨summable_empty, by simp⟩⟩
  set D := Module.finrank ℝ (Fin a → Cinf E) with hD
  have hD1 : 1 ≤ D := by rw [hD, finrank_pi_Cinf]; exact Nat.mul_pos ha Module.finrank_pos
  have hND : (D : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    hD1 (M := ((N + D + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [← hD] at hlat
  refine ⟨N + D + 1, 2 ^ N * K, fun g A c hA hsupp hdec => ?_⟩
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add (f := _)]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  have hsP : ∀ ξ, c ξ ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (by_contra fun h' => h (hsupp ξ h'))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set B : ℝ := A * (2 * r) ^ N with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ξ, ‖c ξ‖ ≤ B * (1 + ‖TI ξ‖) ^ (-(((N + D + 1 : ℕ)) : ℝ)) := fun ξ => by
    have h1 := hdec ξ ξ₀ hξ₀.2 ((hP _).1 hξ₀.1)
    have hpos : 0 < (1 + ‖TI ξ‖) ^ (N + D + 1) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact pow_le_pow_left₀ (norm_nonneg _) hlt.le _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖c ξ‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left B).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm ξ.1) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm ξ.1) hs2
    (hsum.mul_left B)).trans ?_
  rw [tsum_mul_left]
  have key : ∀ e : ℝ, r ^ ((N : ℝ) + e) ≤ 1 → B * (K * r ^ e) ≤ 2 ^ N * K * A := by
    intro e he
    calc B * (K * r ^ e) = 2 ^ N * K * A * r ^ ((N : ℝ) + e) := by
          rw [hB, Real.rpow_add hr, Real.rpow_natCast, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hB0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hB0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

end GlobalTheory.RSTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVectorStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ), Module.finrank ℝ (Fin a → Cinf E) ≤ N → ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A → (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J → c ξ = 0) → (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J → ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤ A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) → Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  first | exact @GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | exact GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | (intros; apply GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Topology
open Filter

namespace GlobalTheory.LatFixMod

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem eventually_keep_cong (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1,
      (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T p.1 p.2 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T p.1 p.2 u = u + N • l := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef
  have hfg := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  obtain ⟨G, hG, hGl, hgen⟩ := hfg
  have hev := GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  have hall := (Filter.eventually_all_finite hG).2 fun u hu =>
    hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN
  filter_upwards [hev.1, hall] with p hk hp
  refine ⟨hk, fun w hw => ?_⟩
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l}
      zero_mem' := ⟨0, L.zero_mem, by
        have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
        rw [zero_smul, zero_smul] at this
        rw [this, smul_zero, add_zero]⟩
      add_mem' := by
        rintro a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩
        refine ⟨la + lb, L.add_mem hla hlb, ?_⟩
        rw [GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]
        abel
      neg_mem' := by
        rintro a ⟨la, hla, ea⟩
        refine ⟨-la, L.neg_mem hla, ?_⟩
        have h0 := GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)
        have hz : actO S T p.1 p.2 (0 : WO S T) = 0 := by
          have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
          rw [zero_smul, zero_smul] at this
          rw [this]
        rw [add_neg_cancel, hz, ea] at h0
        rw [smul_neg]
        have : actO S T p.1 p.2 (-a) = -(a + N • la) := (neg_eq_of_add_eq_zero_right h0.symm).symm
        rw [this, neg_add] }
  refine hgen U (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
  show actO S T p.1 p.2 _ = _
  rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]

def KeepMod (S T : HSp D) (L : AddSubgroup (WO S T)) (N : ℕ) (x : GA D S) : Prop :=
  (∀ u ∈ L, actO S T x 1 u ∈ L) ∧ ∀ u ∈ L, ∃ l ∈ L, actO S T x 1 u = u + N • l

theorem exists_open_keep_cong : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J →
      (∀ u : WO S T, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
        actO S T x 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T x 1 u = u + N • l := by
  intro D S T ΛS ΛT hS hT N hN
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hev := eventually_keep_cong S T ΛS ΛT hS hT N hN
  have t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1
    exact this
  have t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1
    rwa [inv_one, Prod.mk_one_one] at this
  have hx : ∀ᶠ x in 𝓝 (1 : GA D S),
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹ :=
    (t1.eventually hev).and (t2.eventually hev)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k →
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹ := by
    by_contra hne
    have hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧
        ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
          KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹) :=
      fun n => by
        by_contra h
        exact hne ⟨n, fun k hk hc => by
          by_contra h'
          exact h ⟨k, hk, hc, h'⟩⟩
    choose k hk hkc hkne using hne'
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hx).exists
    exact hkne n hn
  obtain ⟨n, hn⟩ := key
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S x := congrArg Subtype.val e
  have hc : GlobalTheory.Member.FinCong S n.factorial x := by
    have := hk'.2
    unfold GlobalTheory.Member.FinCong at this ⊢
    rw [← e']
    exact this
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hn x hxf hc
  refine ⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩
  have e2 := GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u
  rw [inv_one] at e2
  rw [← e2]
  exact h3 _ hu

end GlobalTheory.LatFixMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal

noncomputable section
namespace GlobalTheory.RSPole.EulerPole

open Filter Topology GlobalTheory.RSPole

theorem schurAt_const_zero {n : ℕ} (a : Fin n → ℂ) : GlobalTheory.JSW.schurAt (fun _ => 0) a = 1 := by
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem one_le_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) : 1 ≤ schurDir q a x := by
  unfold schurDir
  refine le_trans ?_ (ENNReal.le_tsum ⟨fun _ => 0, antitone_const⟩)
  simp [schurAt_const_zero]

theorem hasProd_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) :
    HasProd f (⨆ s : Finset I, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup fun _ _ hst => Finset.prod_le_prod_of_subset_of_one_le' hst fun i _ _ => hf i

theorem finset_prod_le_tprod {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (s : Finset I) :
    ∏ i ∈ s, f i ≤ ∏' i, f i := by
  rw [(hasProd_of_one_le f hf).tprod_eq]; exact le_iSup (fun s : Finset I => ∏ i ∈ s, f i) s

theorem le_tprod_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (i : I) : f i ≤ ∏' i, f i := by
  simpa using finset_prod_le_tprod f hf {i}

theorem hasProd_toReal {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfin : ∏' i, f i ≠ ⊤) :
    HasProd (fun i => (f i).toReal) (∏' i, f i).toReal := by
  have h := hasProd_of_one_le f hf
  rw [← h.tprod_eq] at h
  have := (ENNReal.tendsto_toReal hfin).comp h
  simpa [HasProd, Function.comp_def, ENNReal.toReal_prod] using this

theorem schurAt_conj {n : ℕ} (l : Fin n → ℕ) (a : Fin n → ℂ) :
    GlobalTheory.JSW.schurAt l (fun i => starRingEnd ℂ (a i)) = starRingEnd ℂ (GlobalTheory.JSW.schurAt l a) := by
  rw [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schurAt, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole

def schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) : ℝ :=
  ‖GlobalTheory.JSW.schurAt l.1 a‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x))

theorem schurTerm_nonneg (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l) : 0 ≤ schurTerm q a x l := by
  unfold schurTerm; positivity

theorem schurDir_eq (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    schurDir q a x = ∑' l, ENNReal.ofReal (schurTerm q a x l) := rfl

theorem summable_schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    Summable (schurTerm q a x) := by
  rw [schurDir_eq] at hfin
  exact (ENNReal.summable_toReal hfin).congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    (schurDir q a x).toReal = ∑' l, schurTerm q a x l := by
  rw [schurDir_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem term_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo le_rfl l.1) (fun i => (α i : ℂ)) *
      GlobalTheory.JSW.schurAt l.1 (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) = ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ) := by
  rw [GlobalTheory.JSW.padTo_self]
  have h1 : (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) =
      fun j => starRingEnd ℂ (α j : ℂ) := by
    funext j; simp
  rw [h1, schurAt_conj, Complex.mul_conj']
  have h2 : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]; push_cast; rfl
  have h3 : (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) = ((q : ℝ) ^ (-x)) ^ (∑ i, l.1 i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]; ring_nf
  rw [h2, schurTerm, h3]
  push_cast
  ring

theorem locL_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (hfin : schurDir q (fun i => (α i : ℂ)) x ≠ ⊤) :
    locL q (Finset.univ.val.map α) ((Finset.univ.val.map α).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) =
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
  have hs := summable_schurTerm q _ x hfin
  rw [Multiset.map_map]
  have key := cauchy_locL le_rfl α (Units.map (starRingEnd ℂ).toMonoidHom ∘ α) q (x : ℂ) (hs.congr fun l => by
    rw [← norm_pow, ← norm_mul, term_eq, Complex.norm_real, Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)])
  have h2 : HasSum (fun l => ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ))
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
    rw [toReal_schurDir]; exact Complex.hasSum_ofReal.mpr hs.hasSum
  simp only [term_eq] at key
  exact key.unique h2

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole Set

theorem schurTerm_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) (l) :
    schurTerm q a y l ≤ schurTerm q a x l := by
  unfold schurTerm
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) ?_) (by positivity)
  have : (0 : ℝ) ≤ ((∑ i, l.1 i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem schurDir_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) :
    schurDir q a y ≤ schurDir q a x := by
  rw [schurDir_eq, schurDir_eq]
  exact ENNReal.tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal (schurTerm_anti q hq a hxy l)

theorem continuousOn_toReal_schurDir (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) (x₀ : ℝ)
    (hfin : schurDir q a x₀ ≠ ⊤) : ContinuousOn (fun x => (schurDir q a x).toReal) (Ici x₀) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ContinuousOn (fun x => ∑' l, schurTerm q a x l) (Ici x₀) := by
    refine continuousOn_tsum (u := schurTerm q a x₀) (fun l => ?_) (summable_schurTerm q a x₀ hfin) ?_
    · unfold schurTerm
      exact (continuous_const.mul (continuous_const.rpow (by fun_prop) fun _ => Or.inl hqpos.ne')).continuousOn
    · intro l x hx
      rw [Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)]
      exact schurTerm_anti q hq a hx l
  exact hc.congr fun x _ => toReal_schurDir q a x

theorem one_le_toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    1 ≤ (schurDir q a x).toReal := by
  have := ENNReal.toReal_mono hfin (one_le_schurDir q a x)
  simpa using this

section
variable {I : Type} (q : I → ℕ) {n : ℕ} (a : I → Fin n → ℂ)

theorem schurDir_ne_top (x : ℝ) (h : eulD q a x ≠ ⊤) (w : I) : schurDir (q w) (a w) x ≠ ⊤ :=
  ne_top_of_le_ne_top h (le_tprod_of_one_le (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) w)

theorem hasProd_eulD (x : ℝ) (h : eulD q a x ≠ ⊤) :
    HasProd (fun w => (schurDir (q w) (a w) x).toReal) (eulD q a x).toReal :=
  hasProd_toReal (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) h

theorem summable_log (x : ℝ) (h : eulD q a x ≠ ⊤) :
    Summable fun w => Real.log (schurDir (q w) (a w) x).toReal := by
  have h1 : ∀ w, 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w)
  refine summable_of_sum_le (c := Real.log (eulD q a x).toReal) (fun w => Real.log_nonneg (h1 w)) fun s => ?_
  rw [← Real.log_prod (fun w _ => (zero_lt_one.trans_le (h1 w)).ne')]
  refine Real.log_le_log (Finset.prod_pos fun w _ => zero_lt_one.trans_le (h1 w)) ?_
  rw [← ENNReal.toReal_prod]
  exact ENNReal.toReal_mono h (finset_prod_le_tprod (fun w => schurDir (q w) (a w) x)
    (fun w => one_le_schurDir _ _ _) s)

theorem toReal_eulD_eq_exp (x : ℝ) (h : eulD q a x ≠ ⊤) :
    (eulD q a x).toReal = Real.exp (∑' w, Real.log (schurDir (q w) (a w) x).toReal) := by
  have h1 : ∀ w, 0 < (schurDir (q w) (a w) x).toReal :=
    fun w => zero_lt_one.trans_le (one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w))
  exact (hasProd_eulD q a x h).unique (Real.hasProd_of_hasSum_log h1 (summable_log q a x h).hasSum)

theorem continuousOn_toReal_eulD (hq : ∀ w, 1 ≤ q w) (x₀ : ℝ) (hall : ∀ x, x₀ ≤ x → eulD q a x ≠ ⊤) :
    ContinuousOn (fun x => (eulD q a x).toReal) (Ici x₀) := by
  have hx₀ := hall x₀ le_rfl
  have hF : ∀ w x, x₀ ≤ x → 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w x hx => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x (hall x hx) w)
  have hc : ContinuousOn (fun x => ∑' w, Real.log (schurDir (q w) (a w) x).toReal) (Ici x₀) := by
    refine continuousOn_tsum (u := fun w => Real.log (schurDir (q w) (a w) x₀).toReal) (fun w => ?_)
      (summable_log q a x₀ hx₀) ?_
    · exact (continuousOn_toReal_schurDir (q w) (hq w) (a w) x₀ (schurDir_ne_top q a x₀ hx₀ w)).log
        fun x hx => (zero_lt_one.trans_le (hF w x hx)).ne'
    · intro w x hx
      rw [Real.norm_of_nonneg (Real.log_nonneg (hF w x hx))]
      refine Real.log_le_log (zero_lt_one.trans_le (hF w x hx)) ?_
      exact ENNReal.toReal_mono (schurDir_ne_top q a x₀ hx₀ w) (schurDir_anti (q w) (hq w) (a w) hx)
  exact (Real.continuous_exp.comp_continuousOn hc).congr fun x hx => toReal_eulD_eq_exp q a x (hall x hx)
end

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Set

theorem eulD_hasProd_locL : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  intro I q n α hq hfin
  set a : I → Fin n → ℂ := fun w i => ((α w i : ℂˣ) : ℂ) with ha
  have hq1 : ∀ w, 1 ≤ q w := fun w => le_trans (by norm_num) (hq w)
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · have h := (hasProd_eulD q a x (hfin x hx)).map Complex.ofRealHom Complex.continuous_ofReal
    have he : (fun w => locL (q w) (Finset.univ.val.map (α w))
        ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
        Complex.ofRealHom ∘ fun w => (schurDir (q w) (a w) x).toReal := by
      funext w
      exact locL_eq (q w) (α w) x (schurDir_ne_top q a x (hfin x hx) w)
    rw [he]; exact h
  · have h1 : (1 : ℝ≥0∞) ≤ eulD q a x := by
      simpa [eulD] using finset_prod_le_tprod (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) ∅
    simpa using ENNReal.toReal_mono (hfin x hx) h1
  · intro x hx
    have hx' : (1 + x) / 2 < x := by simp only [mem_Ioi] at hx; linarith
    have h := continuousOn_toReal_eulD q a hq1 ((1 + x) / 2) fun y hy => hfin y (by simp only [mem_Ioi] at hx; linarith)
    exact (h.continuousAt (Ici_mem_nhds hx')).continuousWithinAt

end GlobalTheory.RSPole.EulerPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProducStatement
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  first | exact @GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | exact GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | (intros; apply GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL <;> assumption)
end
end
