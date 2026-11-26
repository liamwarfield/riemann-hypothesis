module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaKernelFiniteDimensional
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomLayerParametersMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomStratumIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotIntertw
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
variable {D : D7}
theorem bottom_stratum_intertwining : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  intro _ _ _ hInp _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hstd i j A A' WW X δ t0 hX
  by_cases hC : Crv D ⊤ δ
  swap
  · refine ⟨1, 2 * Formalism.L2.Pj.xiR D, one_ne_zero, fun h => absurd h hC, fun τ => ?_, fun s Q P P' _ => absurd P.crv hC⟩
    rw [GlobalTheory.FockPos.norm_embedding_xi0_eq]; simp
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  refine ⟨-δ, (area (lamOf D ⊤ δ))⁻¹, neg_ne_zero.2 hδ, fun _ => rfl, fun τ => ?_, fun s Q P P' hB ea ed => ?_⟩
  · have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq]
    field_simp
  have hSet : Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hstd, W.θ_is, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hw := GlobalTheory.ConjWeilBack.weil_conjRep_of_neg W.ψ A WW _ _ (X.ω s) (hX.is.weil s)
  obtain ⟨hth, hfock⟩ := conj_datum hX s
  obtain ⟨G₀, hG₀, hR₀⟩ := reads_of_fock ea.symm ed.symm hSet hw hth hfock
  obtain ⟨hcS, hcT⟩ := bottom_finParts G hL hB
  have hTT0 : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := GlobalTheory.NormSum.VacMove.vac_TT (hInp D).g1 P.crv P.vac.1
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet _ hTT0
  refine ⟨?_, fun h g x y hg hy => ?_⟩
  · rw [xiN_of_reads W.θ_is _ _ hδ hR₀]; exact hG₀
  · have hv := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw (hInp D) t0 P.pt0
      P.even_mul P.vac hcS hcT x h y g hy hg f₀ hf₀
    have hm := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads W.ψ W.θ A WW ea.symm ed.symm ⊤ δ 1 hSet P.e0 P.W _ _ _ hw P.vac.1 x h y g hy hg 1
      f₀ hf₀ (by rw [one_smul]; exact hv) G₀ hG₀ _ hR₀
    rw [one_smul] at hm
    have e1 : (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
        GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (fun w => starRingEnd ℂ (X.f s w)) := by
      change _ = GlobalTheory.AdjTr.conjRep (X.ω s) (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (X.f s))
      rw [GlobalTheory.AdjTr.conjRep_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rfl
    rw [e1, xiN_of_reads W.θ_is _ _ hδ hm, xiN_of_reads W.θ_is _ _ hδ hR₀]
end GlobalTheory.BotIntertw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottom_stratum_intertwiner : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  first | exact @_root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining | exact _root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining | (intros; apply _root_.GlobalTheory.BotIntertw.bottom_stratum_intertwining <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StandardModuleBottomDatumExists
section
noncomputable section
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead
namespace GlobalTheory.StdRead
variable {D : D7}
variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end GlobalTheory.StdRead
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StdRead
theorem standard_module_bottom_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  intro _ _ _ hInp _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _
  have hI := hInp D
  by_cases hC : Crv D ⊤ δ
  swap
  · exact ⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩
  obtain rfl := hr hC
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hIs := hX.is
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  have hrc' : rc = (area (lamOf D ⊤ δ))⁻¹ := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    have h1 := hrc τ
    have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    have hx := GlobalTheory.NormExact.xiR_pos D
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq] at h1
    field_simp
    have : 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  subst hrc'
  have hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank := fun ρ h => by
    ext y
    rw [h.2.1]
    simp [stdL, Submodule.mem_pi, Submodule.mem_one]
  have hΛA := hΛ X.rA hX.std
  have hΛW := hΛ X.rW hX.stdW
  have hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E))
      (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w)) := by
    have h := GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
    rwa [hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1,
      show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1] at h
  obtain ⟨G0, hG0, hne, hread⟩ := GlobalTheory.T.adelicVacuum_standardLattices_readsTheta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv
  obtain ⟨κ, hκ, hc⟩ := exists_const hI δ t0 G0 hG0 hne
  have hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
      oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧
        GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 ((κ * u) • e0) (fun w => starRingEnd ℂ (X.vac w)) := by
    rintro a d rfl rfl e0 h1 h2 h3
    obtain ⟨u, hu, e⟩ := hc e0 hC h1 h2 h3
    exact ⟨u, hu, e ▸ hG0, e ▸ hread⟩
  refine ⟨κ, hκ, fun s Q P P' hB => ?_⟩
  have ea : P.a = A.rank := hB.rank.1.trans hX.rank.symm
  have ed : P.d = WW.rank := by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']
  obtain ⟨u, hu, hTh, hrd⟩ := hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz
  obtain ⟨c0, cI⟩ := GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus G hL s i j (X.c s) (hIs.expo s)
  obtain ⟨q1, q2⟩ := GlobalTheory.SqTop.BotT.pde_ne_q hR
  have hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s) := ⟨_, _, hIs.idem s, c0, cI.symm,
    GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩
  have hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep' := fun x y hxy => by
    rw [hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy]
    exact (Units.val_inv_eq_inv_val _).symm
  obtain ⟨Tm, hTm, hf⟩ := GlobalTheory.T.schrodingerModel_complexConjugate_negForm W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)
  have eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu s i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s := cI
  rw [hΛA, hΛW] at hTm
  rw [eν, eI, hβ] at hf
  obtain ⟨u', hu', hrf⟩ := reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j)
    (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf
  have hw := (hu.mul hu').conj
  refine ⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩
  rw [xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]
end GlobalTheory.StdRead
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_module_bottom_datum_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  first | exact @_root_.GlobalTheory.StdRead.standard_module_bottom_datum | exact _root_.GlobalTheory.StdRead.standard_module_bottom_datum | (intros; apply _root_.GlobalTheory.StdRead.standard_module_bottom_datum <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ReadMatch
theorem bottom_layer_parameters_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ (r : ℂ) (rc : ℝ) (κ : ℂ), r ≠ 0 ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧ κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              (κ * starRingEnd ℂ u) • P.W.Om x h P.F := by
  intro hPr hTI hLM hInp hBS
  refine gbig_and (_root_.GlobalTheory.T.exists_bottom_stratum_intertwiner hPr hTI hLM hInp hBS) (_root_.GlobalTheory.T.standard_module_bottom_datum_exists hPr hTI hLM hInp hBS) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, hr, hrδ, hrc, H1⟩ := q1 W hW i j A A' WW X δ t0 hX
  obtain ⟨κ, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ r rc hr hrδ hrc H1
  refine ⟨r, rc, κ, hr, hrc, hκ, fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy => ?_⟩
  rw [(H1 s Q P P' hB ea ed).2 h g x y hg hy, hEq ea ed,
    P.W.smul _ _ _ _ (GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P.crv P P.level_pos)]
end GlobalTheory.ReadMatch
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_parameters_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ (r : ℂ) (rc : ℝ) (κ : ℂ), r ≠ 0 ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧ κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              (κ * starRingEnd ℂ u) • P.W.Om x h P.F := by
  first | exact @_root_.GlobalTheory.ReadMatch.bottom_layer_parameters_match | exact _root_.GlobalTheory.ReadMatch.bottom_layer_parameters_match | (intros; apply _root_.GlobalTheory.ReadMatch.bottom_layer_parameters_match <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KerFin
theorem bottomTheta_kernel_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  intro hPr hTI hLM hInp hBS
  refine gbig_comb (_root_.GlobalTheory.T.theta_parameters_match hPr hTI hLM hInp hBS) GlobalTheory.BotWeights.weights_const ?_
  intro D T Lc sc G μ₀ C x b q2 q3 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, κ, hr, hrc, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨n₀, H3⟩ := q3 i j δ t0
  obtain ⟨Ω, hΩ, H1⟩ := GlobalTheory.T.bottomTriple_thetaKernel_minors_eq_const_conjJet G W hW i j A A' WW X hX r rc hr hrc n₀
  refine ⟨Ω * starRingEnd ℂ κ, mul_ne_zero hΩ ((map_ne_zero _).2 hκ), fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy Tu => ?_⟩
  have hne : κ * starRingEnd ℂ u ≠ 0 := mul_ne_zero hκ ((map_ne_zero _).2 hu0)
  rw [H1 P.a P.d P.n ea ed (H3 s Q P P' hB) s g y hg.1 hy.1 Tu, hEq ea ed h g x y hg hy,
    GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hne]
  simp only [GlobalTheory.NormSum.Pair.term, map_mul, Complex.conj_conj]
  ring
end GlobalTheory.KerFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  first | exact @_root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | exact _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | (intros; apply _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaIntegralClassSumFormula
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomKernelMulLargeLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.BotBigLevel
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar _root_.Formalism.L2.DIV GlobalTheory.BotFinLevel
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)
variable {D : D7}
end GlobalTheory.BotBigLevel
theorem GlobalTheory.BotBigLevel.bottom_kernel_mul_large_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (Pf : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (n : ℕ) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n)
        (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ y, X.ker W.ψ W.θ t Pf g (y * k) = X.ker W.ψ W.θ t Pf g y := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX t Pf g n x k hx hk y
  exact GlobalTheory.BotBigLevel.ker_mul_of_fix hX.is t hk.1
    (GlobalTheory.BotBigLevel.fix_fst_of_unram hX.is t (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ t i j _ hv) hk.1
      (GlobalTheory.BotBigLevel.mem_St_of_isFinPt hX.is.rigA hX.std hx hk)) Pf g y
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_large_level_kernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (Pf : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (n : ℕ) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n)
        (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ y, X.ker W.ψ W.θ t Pf g (y * k) = X.ker W.ψ W.θ t Pf g y := by
  first | exact @_root_.GlobalTheory.BotBigLevel.bottom_kernel_mul_large_level | exact _root_.GlobalTheory.BotBigLevel.bottom_kernel_mul_large_level | (intros; apply _root_.GlobalTheory.BotBigLevel.bottom_kernel_mul_large_level <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.InfinityTypeOfFiniteCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotKerRealInv
open Matrix
private theorem minor_polynomial_substitution {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g (GlobalTheory.NormSum.minorPol D T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.NormSum.minorPol D T := by
  unfold GlobalTheory.NormSum.minorPol
  have key : ∀ (τ : D.what₂.Tau) (r : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (g τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ r
    rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : ℂ →+* MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ), mul_comm,
      ← Matrix.det_mul]
    congr 1
    ext1 i i'
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.CompactHowe.substF_X, Matrix.one_apply]
    rw [Finset.sum_eq_single (r i)]
    · simp [mul_comm]
    · intro b _ hb
      simp [hb]
    · simp
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  refine (Finset.prod_congr rfl fun j _ => key τ (T τ j).1).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]
private theorem minor_form_substitution {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) g (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  exact minor_polynomial_substitution T g
private theorem conj_transpose_inv_unitary {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (h : uᴴ * u = 1) :
    (((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * u * 1)⁻¹)ᵀ.map (starRingEnd ℂ) = u := by
  rw [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_eq_left_inv h]
  ext i j
  simp [Matrix.conjTranspose_apply]
private theorem infinity_type_of_finite_character {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) :
    χ'.HasInf (Formalism.L2.Host.embTau D) (fun τ => e * χ.n τ) := by
  intro u
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ u / ((‖φ τ u‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left hA, _root_.inv_zpow, ← Finset.prod_zpow] at hB'
  rw [eq_inv_of_mul_eq_one_left hB', inv_inv]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← _root_.zpow_mul, mul_comm]
private theorem infinity_exponent_of_bottom_pair {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (s : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P')
    (τ : D.what₂.Tau) :
    HasInfExp D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2))) τ
      ((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
  have h1 := infinity_type_of_finite_character P.W.chV' P.W.ep' _ hB.chars.2
  have h2 : (nuH G s i j).HasInfQ (tauE D) fun τ => -((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
    refine ⟨fun τ => -(P.W.ep' * P.W.chV'.n τ), fun τ => ?_, fun k => ?_⟩
    · have : ((2 * (P.n τ : ℤ) : ℤ) : ℚ) = ((P.W.ep' * P.W.chV'.n τ - (P.d : ℤ) : ℤ) : ℚ) := by rw [P.wt τ]
      push_cast at this ⊢
      linarith
    · have h3 := h1 k
      rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val] at h3
      rw [← inv_inv (((nuH G s i j).inf k : ℂˣ) : ℂ), h3, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [_root_.zpow_neg]
      rfl
  have h4 := GlobalTheory.Chain.StepVac.hasInfExp_inv
    (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G s i j hL) h2 τ)
  rw [neg_neg] at h4
  have e : G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) =
      (G.nu s i (j + 1))⁻¹ := by
    rw [mul_div_mul_right_eq_div, ← inv_div]
    rfl
  rw [e]
  exact h4
private theorem weil_rep_fixes_compact_vector {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T)
    {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P') (ea : P.a = A.rank) (ed : P.d = WW.rank)
    (Tp : Tup D P.a P.d P.n) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GinfC A) :
    X.ω s (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
      (GlobalTheory.BotFormula.minorF ea ed Tp)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
        (GlobalTheory.BotFormula.minorF ea ed Tp) := by
  have h := hX.is
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hW := h.weil s
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst s) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem s)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f s) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst s)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  have hgA : ∀ τ, gramAt D A τ = 1 := fun τ => by rw [gramAt, hX.std.1]; simp
  have hgW : ∀ τ, gramAt D WW τ = 1 := fun τ => by rw [gramAt, hX.stdW.1]; simp
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [e1, e2, e3, e4]
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ _ τ hθ hW.hecS hW.resS
  choose e he using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecS hW.resS (ha τ)
  let k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k
  have hk' : k' ∈ GinfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])
  have hu : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A k))ᴴ * compAt W.θ τ (Formalism.L2.Theta.mt A k) = 1 := fun τ => by
    have e : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).conjTranspose * (gramAt D A τ) * compAt W.θ τ (Formalism.L2.Theta.mt A k) =
      gramAt D A τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ A k τ
    rwa [hgA, Matrix.mul_one] at e
  have key := GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ A WW _ _ ((X.ω s).toSgn true) hW hθ (fun _ => 1) (fun _ => 1)
    (fun τ => by rw [hgA]; simp) (fun τ => by rw [hgW]; simp) a (fun τ => (P.n τ : ℚ) + (P.d : ℚ) / 2) ha
    (infinity_exponent_of_bottom_pair hL G s i j hB) (fun τ => e τ - A.rank) (fun τ => -(P.n τ : ℤ))
    (fun τ => by push_cast; rw [he τ]; show _ + (A.rank : ℚ) / 2 - _ = _; ring)
    (fun τ => by rw [← ed]; push_cast; ring) (X.f s) hf hv k' hk' 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed Tp)
  have c1 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.JointHarm.compAt_mt_one' W.θ τ WW
  have ck : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') = compAt W.θ τ (Formalism.L2.Theta.mt A k) := fun τ => rfl
  have s1 : (fun τ => (((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) *
      (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ).map (starRingEnd ℂ)) = fun _ => 1 := by
    funext τ
    show ((1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * 1).map (starRingEnd ℂ) = 1
    rw [c1, inv_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have s2 : (fun τ => (((((fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹ *
      compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') * (fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹)ᵀ).map
        (starRingEnd ℂ)) = fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A k) :=
    funext fun τ => conj_transpose_inv_unitary (hu τ)
  rw [s1, s2, minor_form_substitution, map_smul, smul_smul, ← Finset.prod_mul_distrib] at key
  have hone : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k')).det ^ (-(P.n τ : ℤ)) *
      (compAt W.θ τ (Formalism.L2.Theta.mt WW 1)).det ^ (e τ - A.rank) *
        (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ^ P.n τ) = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero
    rw [ck, c1, Matrix.det_one, _root_.one_zpow, mul_one, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hne)]
  rw [hone, one_smul] at key
  exact key
end GlobalTheory.BotKerRealInv
end
theorem _root_.GlobalTheory.T.bottom_kernel_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : Formalism.L2.Theta.GA D WW) (T : Tup D P.a P.d P.n),
        ∀ k ∈ GinfC A, ∀ y, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (y * k) =
          X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X hX s Q δ t0 P P' hB ea ed g Tp k hk y
  unfold Tri.ker thetaKO
  have e : X.ω s (y * k, g) = X.ω s (y, g) * X.ω s (k, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, Module.End.mul_apply, GlobalTheory.BotKerRealInv.weil_rep_fixes_compact_vector hL hX s hB ea ed Tp hk]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotFormula.ClassSumMonotone
open GlobalTheory.SqTop
end GlobalTheory.BotFormula.ClassSumMonotone
theorem GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  intro hPr hTA hLM hInp hBS
  refine GlobalTheory.BotFormula.ClassSumMonotone.gbig_mono' (GlobalTheory.BotFormula.ClassSumMonotone.gbig_and' (_root_.GlobalTheory.T.bottom_large_level_kernel hPr hTA hLM hInp hBS) (_root_.GlobalTheory.T.bottom_kernel_real_invariant hPr hTA hLM hInp hBS)) ?_
  intro D T Lc sc G μ₀ C x b H
  obtain ⟨H3, H4⟩ := H
  intro W hW i j A A' WW X δ t0 hX
  obtain ⟨v, hv, hsum⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_vol_mul_classSum A hX.std.1 X.m X.fd hX.is.meas.1 hX.is.meas.2
  refine ⟨v, hv, fun s Q P P' hB ea ed g pt hpt T => ?_⟩
  exact hsum P.a ea pt hpt _ (GlobalTheory.T.definiteBottomTriple_thetaKernel_left_rational_invariant hX s _ g)
    (fun k hk y => H4 W hW i j A A' WW X hX s Q δ t0 P P' hB ea ed g T k hk y)
    (fun x k hx hk y => H3 W hW i j A A' WW X hX s _ g P.a x k hx hk y)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_thetaIntegral_classSum_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  first | exact @_root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum | exact _root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum | (intros; apply _root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFormula
end GlobalTheory.BotFormula
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.rallis_bottom_formula_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.bottom_thetaIntegral_classSum_formula hPr hK hM hI hB
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₀, hΩ₀, HK⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨v, hv, HC⟩ := hB' W hψ i j A A' WW X δ t0 hX
  refine ⟨(v * Ω₀)⁻¹, inv_ne_zero (mul_ne_zero hv hΩ₀), fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HK⟩ := HK s Q P P' hP
  have huQ' : u⁻¹ ∈ Qbar := inv_mem huQ
  refine ⟨u⁻¹, inv_ne_zero hu, huQ', fun p _ hp lam => ?_, fun ea ed h g hg T => ?_⟩
  · have h1 := GlobalTheory.BotFormula.lamC_mul lam huQ huQ'
    rw [mul_inv_cancel₀ hu] at h1
    have h2 : lamC lam (1 : ℂ) = 1 := by
      unfold lamC
      rw [dite_eq_left (one_mem Qbar)]
      exact (congrArg lam (Subtype.ext rfl : (⟨1, one_mem Qbar⟩ : Qbar) = 1)).trans (map_one lam)
    rw [h2] at h1
    have h3 := congrArg norm h1
    rw [norm_mul, huU p hp lam, one_mul, norm_one] at h3
    exact h3.symm
  have pts : ∀ x : GA D P.a, ∃ y : GA D A, GlobalTheory.BotFormula.IsFinPt A y x := fun x =>
    GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne A hX.std.1 x ea.symm
  choose pt hpt using pts
  rw [HC s Q P P' hP ea ed g pt hpt T]
  simp_rw [HK ea ed h g _ (pt _) hg (hpt _) T]
  rw [GlobalTheory.NormSum.Pair.coord, GlobalTheory.BotFormula.conj_finsum]
  have e1 : ∀ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * (Ω₀ * u * starRingEnd ℂ (P.term x.out h T)) =
      (Ω₀ * u) * starRingEnd ℂ (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * P.term x.out h T) := by
    intro x
    rw [map_mul, map_inv₀, map_natCast]; ring
  simp_rw [e1, ← mul_finsum]
  field_simp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_formula_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  first | exact @_root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | exact _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | (intros; apply _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank <;> assumption)
end
