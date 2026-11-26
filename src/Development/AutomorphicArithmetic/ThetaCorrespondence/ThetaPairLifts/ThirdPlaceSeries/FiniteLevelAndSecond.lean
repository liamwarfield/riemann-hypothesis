module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundOfLocalComponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelComparisonChoicesExistAtAllPlaces

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeed
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem sFino_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (h : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep := by
  refine StepW.trans h (StepW.of_all fun K B f T w _ _ H P x l S Γ hl => ?_)
  obtain ⟨Z, v, h1, h2⟩ := H P x l S Γ hl.1
  exact ⟨Z, { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
              chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨P, x, l, hl, h1, h2⟩⟩ }, h1, h2⟩
theorem exists_pre_point_with_henselian_level {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {S : SExt} {Γ : GeoP} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w Z c) (e : ExportAt (w.st Z).toD7 c.O.nch c.O.xd) :
    ∃ (P : Pre2 K w) (x : St P) (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), (ListSt cDep x ∧ SatU P) ∧ ∀ A, Nonempty (Seed (Dof x) A) := by
  obtain ⟨P, x, l, hl, hW, hk⟩ := b.nx.2.2.down
  have key := (TupTieW.tupTied_of_muIsW (w.st Z) f T c.Wt c.xi c.mu).1
  refine ⟨P, x, l, hl, GlobalTheory.HeightCounting.Up.nonempty_seed_of_kept (Dof x) (w.st Z).toD7 l.c.ch c.O.nch c.O.xd hk rfl (fun v v₀ hv ht => ?_) l.c.side.nct
    l.c.side.choice.twI_conj ?_ B.coeffGaloisSubfield_isGalois (twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.st Z).toD7 c.O.nch c.nch_tie B.coeffGaloisSubfield_isGalois) e b.nx.2.1.1.1.xd⟩
  · obtain rfl : v = v₀ := eq_of_heq hv
    exact (key v).2 (hW ▸ (twisted_st x v).1 ht)
  · exact (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).2.1.subset fun v hv => (twisted_st x v).1 hv
end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeParametersDeterminedAtUnramifiedPlaces
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
noncomputable section
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem satake_parameter_of_prime_to_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  intro hP hC hL
  have hE := _root_.GlobalTheory.T.isRayPrime_g_and_integral_range hP
  have hR := _root_.GlobalTheory.T.depth_of_repOf_of_inputs hP
  have hA := _root_.GlobalTheory.T.types_true_of_ray_class_alt hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.FirstStageExists AllSt
  refine StepW.trans (StepW.and hE hR) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x hLoc
  obtain ⟨hEl, hRw⟩ := hq
  obtain ⟨hElem, -, -, h, jE, hfr, hray⟩ := hEl P x
  have e1 : (cfOf x).P = f.P := by
    show w.I.C.P = f.P
    rw [w.C_eq]
  have e2 : (cfOf x).W = f.W := by
    show w.I.C.W = f.W
    rw [w.C_eq]
  have hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W := by
    rw [e1, e2]
    exact x.fits.grp
  obtain ⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩ :=
    hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray
  have hG : GrpTrue (nOfLay x L hZ hη) f := by
    show TypesTrue L.ntypes f.P f.W
    rw [← e1, ← e2]
    exact hTT
  obtain ⟨hGA, hCen⟩ := GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM
  obtain ⟨x', hx', hrep⟩ := GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen
  obtain ⟨Pq, hPq1, hPq2⟩ := exists_pq_sel B w.I w.ok
  have hEl' := hEl P x'
  have hRw' := hRw P x'
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at hx'
  subst hx'
  obtain ⟨fr, hfrj⟩ := omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE
  obtain ⟨Wd, hWd⟩ := PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE := { A with wd := Wd }
  have e := eq_of_heq hrep
  obtain ⟨cg⟩ := hcg
  refine ⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩,
    Pq, hPq1, hPq2⟩⟩, ⟨⟨rfl, HEq.rfl, hloc.symm, hO1.symm, hO2.symm, hO3.symm, hO4.symm, heq_of_eq hPlG.symm⟩, hplGw.symm⟩⟩
  rw [e]
  exact hrow
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.FirstStageExists hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | exact _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.satake_parameter_of_prime_to_level_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MinimalKtypeOfLocalComponents
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Bare
open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial
attribute [local instance] GlobalTheory.Mem.Top.factType
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
end GlobalTheory.Mem.R3.Rw.Bare
namespace GlobalTheory.HeightCounting.Up
open Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice GlobalTheory.Mem.R3.Rw.Bare
set_option maxHeartbeats 4000000 in
theorem minimal_ktype_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  intro hP hD
  refine StepW.of_all fun K B' f' T' w' hO _ _ P' X f hB hf hg => ?_
  obtain ⟨B₀, C₀, W₀, V₀, S₀, N₀, G₀⟩ := X
  cases B'
  cases B₀
  dsimp only at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨N, hE, hN, hN', hL, h1, h2, h3, h4, h5, h6⟩ := exists_bare_over P' N₀.nd N₀.naut hg.pl N₀.toLocStage
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk _ w'.C (Gc _ w'.px) P'.q.p P'.q.e P'.q.W₀ P'.q.n
    (fun _ _ => 0) (fun _ _ => le_rfl) (frames_unit P'.q.t) (fun u => ((w'.C.fm u).lat 0).L) (fun _ => 0)
    (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K _ w'.C (P'.q.W (fun _ _ => 0) fun _ _ => le_rfl) P'.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w'.I w'.ok w'.pins w'.l P'.hX) (rows_le P'.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState GlobalTheory.weilRepresentationUnitaryPair hD hP.hc hP.decay K _ _ T' w' P' ⟨_, _, V, S, N, P'.Z₀.G⟩
    ⟨hV, hN, (hN' V S P'.Z₀.G).1, (hN' V S P'.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  have hDx : Dof x = (w'.st (RowPk.Over.Z (q := P'.q) ⟨_, _, V, S, N, P'.Z₀.G⟩)).toD7 := by
    unfold Dof
    rw [hx]
  have hE' : IsEmpty x.o.N.nd.Loc := by
    rw [hx]
    exact hE
  refine ⟨x, hE', ?_⟩
  rw [hDx]
  exact ⟨⟨rfl, HEq.rfl, congrArg LocStage.loc hL.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩, h6.symm⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bareK_of_discreteSeriesExists : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | exact _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.minimal_ktype_of_local_components_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RigidRawPacketEqPow
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwistedCohomologyClassLift
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.Top.TwChar
theorem exists_twisted_cohomology_class_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (σ : Seed X.toD7 A) (Av : ℕ → Finset ℕ), (∀ v, TwistedAt X.toD7 v → X.B.places.resChar v ∈ pl) → (∀ v v', OverOne X.toD7 v v' → TwistedAt X.toD7 v → TwistedAt X.toD7 v') → (∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i)) → ∀ S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ, (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) → ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (h : Enl X.B B'), HEq f' f ∧ T'.pl = pl ∧ T'.Avoids Av ∧ (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ Coh B' T' ∧ TwFrom X σ h T' := by
  intro hP X f pl A σ Av hpl hsat hA S₂ h₂
  obtain ⟨art, ha⟩ := hP.what₂.art X.toD7.host.E X.toD7.nd.Om
  obtain ⟨h1, T₁, e1, hav, hT, hT', hS⟩ := exists_twDat_stagesOn X f pl {v | TwistedAt X.toD7 v} hpl
    (twistedAt_conj X.toD7) σ.s (fun w => let ⟨_, hb⟩ := σ.reads w; hb.l_eq) (fun w _ => σ.conj w) art ha A σ.Q σ.k σ.ψ
    (fun i => rootIsoAt X.toD7 i (σ.k i)) Av hA (fun w hw => σ.psiOk hw)
  obtain ⟨B', h, a, b, e⟩ := hS (S₂ X.B.toPre f (T₁.set f)) (h₂ _ _ _)
  have e2 : ∀ (P : Pre) (_ : P = X.B.toPre) (g : Fr P) (Ξ : Set (HChar P.host.E)), HEq g f → HEq Ξ (T₁.set f) →
      S₂ P g Ξ = S₂ X.B.toPre f (T₁.set f) := by
    intro P eP g Ξ h1 h2
    subst eP
    rw [eq_of_heq h1, eq_of_heq h2]
  refine ⟨B', tr h.1 Fr f, pull h T₁, h, tr_heq _ _ _, e1, avoids_pull h hav, ?_, ⟨fun v v' hv => ?_, fun v => ?_⟩,
    b, fun v => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [e2 _ h.1 _ _ (tr_heq _ _ _) e]
    exact a
  · have ho := overOne_plUnder X h v v' hv
    have key : T₁.psi (plUnder h v) = T₁.psi (plUnder h v') ∧ T₁.Q (plUnder h v) = T₁.Q (plUnder h v') ∧
        T₁.k (plUnder h v) = T₁.k (plUnder h v') := by
      by_cases hw : TwistedAt X.toD7 (plUnder h v)
      · have hw' := hsat _ _ ho hw
        obtain ⟨x, y, z⟩ := hT _ hw
        obtain ⟨x', y', z'⟩ := hT _ hw'
        rw [σ.same _ _ hw hw' ho] at x' y' z'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
      · have hw' : ¬ TwistedAt X.toD7 (plUnder h v') := fun h' => hw (hsat _ _ (fun x => (ho x).symm) h')
        obtain ⟨x, y, z⟩ := hT' _ hw
        obtain ⟨x', y', z'⟩ := hT' _ hw'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
    exact ⟨congrArg (tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E)))) key.2.1, key.2.2,
      congrArg (tr h.1 (fun P => HChar P.host.E)) key.1⟩
  · have hn : B'.places.resChar v ^ (pull h T₁).k v ≠ 0 := pow_ne_zero _ (B'.places.resChar_prime v).ne_zero
    have hz := Complex.isPrimitiveRoot_exp _ hn
    obtain ⟨x, hx⟩ := b v _ hz.pow_eq_one
    exact ⟨x, IsPrimitiveRoot.of_map_of_injective (hx ▸ hz) B'.embLL.injective⟩
  · obtain ⟨x, y, z⟩ := hT (plUnder h v) hw
    exact ⟨(tr_heq h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) _).trans (heq_of_eq y), z, _, _,
      (h1 _ (σ.psiOk hw)).2.1, (tr_heq h.1 (fun P => HChar P.host.E) _).trans (heq_of_eq x)⟩
  · exact (congrArg (tr h.1 (fun P => HChar P.host.E)) (hT' _ hw).1).trans (tr_one _)
end GlobalTheory.HeightCounting.Up
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem goodO_of_alt_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}
    (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A) (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i)
    (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'} (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y)
    (hc : Carried (Dof x) (Dof y)) (hs : ∀ v', HEq (l.c.ch.twI v') (σ.s (plUnder h v'))) {Z : w'.Lt}
    {C : NChoice (w'.st Z).toD7} {xd : ThData (w'.st Z).toD7} (hk : Kept l.c.ch C) (hx : XdAll xd)
    (hZ : ∀ v', TwistedAt (w'.st Z).toD7 v' → v' ∈ P'.Wt) : GoodO (w'.st Z).toD7 C xd := by
  classical
  refine GlobalTheory.T.goodTwist_of_seed_character_powers (Dof x) (Dof y) (w'.st Z).toD7 A σ l.c.ch C xd (plUnder h) hc.exp hk (avPrimes_st _ _) rfl hx hA
    fun v₂ v₃ hv ht => ?_
  obtain rfl : v₂ = v₃ := eq_of_heq hv
  have h1 := hZ v₂ ht
  have h2 : TwistedAt (Dof x) (plUnder h v₂) := (twisted_st x _).2 ((hW _).2 h1)
  have h3 : TwistedAt (Dof y) v₂ := (twisted_st y _).2 h1
  obtain ⟨hQ, hk', ι, χ, hF, hχ⟩ := (hT.2 v₂).1 h2
  have hg := (((σ.good _ h2).2 1 (by simp)).1)
  rw [zpow_one] at hg
  have e1 : l.c.ch.Q v₂ = T'.Q v₂ := (congrFun l.c.Q_eq v₂).trans (ite_eq_left h1)
  have e2 : l.c.ch.k' v₂ = T'.k v₂ := l.c.k_eq v₂ h3
  refine ⟨h2, _root_.GlobalTheory.HeightCounting.Rigid.rigid_raw_packet_eq_pow_alt hP (Dof x) (Dof y) (σ.pack (plUnder h v₂)) _ ι χ (cfOf y) l.c.ch l.c.tp v₂ hc.exp hg hF l.c.side.psi h3
    (hs v₂) ((heq_of_eq e1).trans hQ) (e2.trans hk') ((heq_of_eq (congrFun l.c.psi_eq v₂)).trans hχ) fun z hz => ?_⟩
  rw [e2] at hz
  exact hT.1 v₂ z hz
theorem has3_of_carried_levelB2 {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (S : SExt) (Γ : GeoP) {B' : Base} {f' : Fr B'.toPre}
    {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A)
    (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i) (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'}
    (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL y) (hc : Carried (Dof x) (Dof y)) (hl : ListSt cDep y ∧ SatU P')
    (ck : ∀ s : B'.places.Pl → (Dof y).ntw.Tw, (∀ v, ∃ b, ReadsAt (D := Dof y) (s v) b v) → (∀ v, s (B'.places.conj v) = s v) →
      ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T'.k T'.psi, c.ch.twI = s)
    (fin : ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y) (S : SExt) (Γ : GeoP), (ListSt cDep y ∧ SatU P') →
      ∃ (Z : w'.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w' Z), v.Wt = P'.Wt ∧ Kept l.c.ch v.nch) :
    Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B' f' T' w' := by
  have eT : (Dof x).ntw.Tw = (Dof y).ntw.Tw := (same_basic hc.exp.gal hc.exp.set hc.exp.frm).1
  obtain ⟨c, hs⟩ := ck (fun v' => cast eT (σ.s (plUnder h v')))
    (fun v' => (σ.reads (plUnder h v')).imp fun b hb =>
      GlobalTheory.HeightCounting.Up.readsAt_of_plUnder (w.st x.o.Z) (w'.st y.o.Z) h hc v' _ _ b (cast_heq eT _).symm hb)
    (fun v' => congrArg (cast eT) ((congrArg σ.s (TwChar.plUnder_conj h v')).trans (σ.conj _)))
  obtain ⟨Z, v, h1, h2⟩ := fin { toStrictHenselianAcyclic := l, c := c } S Γ hl
  have hg : GoodO (w'.st Z).toD7 v.nch v.xd :=
    _root_.GlobalTheory.HeightCounting.Up.goodO_of_alt_alt hP h x σ hA hT hW { toStrictHenselianAcyclic := l, c := c } hc (fun v' => (heq_of_eq (congrFun hs v')).trans (cast_heq eT _)) h2
      v.nx.2.1.1.1.xd fun v' hv' => h1 ▸ ((TupTieW.tupTied_of_muIsW (w'.st Z) f' T' v.Wt w'.I.xi v.what₂.mu).1 v').1 hv'
  exact ⟨Z, ⟨{ g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
               chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨hg⟩⟩ }⟩⟩
theorem secondNo_of_sMt_sRat_sCusp_sFinl (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : SerN) (hD : DatExt) (hH : WeightCaseCondition) (hds : GlobalTheory.Published.DiscreteSeriesExists)
    (hc : PhtCmp) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL) (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) {cDep : ℝ}
    (hF : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  classical
  intro S Γ
  have h3 := GlobalTheory.Mem.R3.Rw.Second.exists_ext_twisted_places hP.greenC hD
  have h4 := (GlobalTheory.T.constructionStartingChoices_of_fine_adelicData GlobalTheory.weilRepresentationUnitaryPair hds hP.hc hP.decay hH).and ((_root_.GlobalTheory.T.bareK_of_discreteSeriesExists hP hds).and ((_root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp hP hc hL).and
    (hMt.and (hRat.and (hCu.and ((_root_.GlobalTheory.T.moveToBase_of_inputs_serN hP hS hL).and ((_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM hP hS hL).and (_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF))))))))
  refine pass_of (p := fun _ _ _ _ => True) (Step.of_all fun _ _ _ _ _ _ _ h => h) (Step.and h3 h4)
    (EvG.imp GlobalTheory.Mem.Top.ReW.extend_pinned fun K _ _ _ _ hw2 => ?_)
  intro B f T hO hKP hT _ C W V S' N G c₀ hQ hE A S₂ hS₂
  obtain ⟨w, Z, c, ⟨b, -⟩, e⟩ := exists_of_position hQ hE
  have hSt : Start K B f T w := ⟨⟨b.pin⟩, Or.inl hT, b.coh⟩
  obtain ⟨P, x, l, hl, hσ⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_pre_point_with_henselian_level b e
  obtain ⟨A₁, S₁, a₁, hw'⟩ := hw2 B f T w hO ⟨b.pin⟩
  obtain ⟨σ⟩ := hσ fun i => avD (Dof x) (avDesign (Dof x)) i ∪ avoidPlaces B.toPre (A ((Dof x).ntw.l i) ∪ A₁ ((Dof x).ntw.l i))
  obtain ⟨B', f', T', h, hf, hpl, hAv, hS', hCoh, hTw⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_twisted_cohomology_class_lift_alt hP (w.st x.o.Z) f T.pl _ σ (fun p => A p ∪ A₁ p)
    (fun v hv => P.sub v ((twisted_st x v).1 hv))
    (fun v v' ho hv => (twisted_st x v').2 (hl.2 hT v v' ho ((twisted_st x v).1 hv)))
    (fun i p hp hp' v hv => Finset.mem_coe.2 (Finset.mem_union_right _ (subset_avoidPlaces B.toPre _ hp hp' hv)))
    (fun P g Ξ => S₂ P g Ξ ∪ S₁ P g Ξ) (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₁ P g Ξ z))
  obtain ⟨w', hPin, epx, esel, eJ, eδ⟩ := hw' B' f' T' h hf (fun v u hu hA => hAv v u hu (Finset.mem_union_right _ hA))
    fun z hz => hS' z (Finset.mem_union_right _ hz)
  have eP : B'.toPre = B.toPre := h.1
  refine ⟨B', f', T', h, hf, hpl, fun v u hu hA => hAv v u hu (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), ⟨⟨w'.δ, w'.exact⟩, eP ▸ hKP.2⟩, fun hq => ?_⟩
  obtain ⟨Z', hX', z', g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hq.1 w' hPin B f T w h hf ⟨b.pin⟩ epx hpl P.Z₀ P.hX P.Wt P.z P.grp
    P.grpAt P.kap ⟨P.exAt, P.inGeo, P.core, P.std⟩ (HoldsL.of_holds P.intersectionNumber_baseChange) P.exact P.sub
    (fun Z' v' hv => (hTw.2 v').2 fun ht => hv _ (below_plUnder h P.Z₀ Z' v') ((twisted_st x _).1 ht))
  have hSt' : Start K B' f' T' w' :=
    ⟨hPin, Or.inr ⟨Z', hX', z', g1, g2, g3, g4, g5.1, g5.2.1, g5.2.2.1, g5.2.2.2, g6, g7⟩, hCoh⟩
  obtain ⟨pre, bare, sa, mt, rat, cu, mv, ck, fin⟩ := hq.2 w' hSt'
  obtain ⟨P', -, eW, g10⟩ := pre Z' hX' z' g1 g2 g3 g4 g5 g6 g7
  have hExt : Ext P.z P'.z := GlobalTheory.T.standardReading_transport_and_extension_trans.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (enl_refl B') g8 g10
  obtain ⟨x0, hE0, s0⟩ := bare P' (w.st x.o.Z) f eP hf x.fits.grp
  obtain ⟨x1, ⟨la⟩, s1⟩ := sa P' x0 hE0
  obtain ⟨imt⟩ := mt P' x1
  obtain ⟨irat⟩ := rat P' x1 la
  obtain ⟨y, ⟨l2⟩, hcar, hlist⟩ := mv B f T w h hf hSt epx esel eJ eδ P x l.toStrictHenselianAcyclic P' hExt x1
    { toLA := la, mt := imt, rat := irat, cusp := cu P' x1 la } (s0.trans s1)
  have hWt : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt := fun v' => eW ▸ g9 _ v' (below_plUnder h P.Z₀ Z' v')
  exact ⟨w', hSt', _root_.GlobalTheory.HeightCounting.Up.has3_of_carried_levelB2 hP S Γ h x σ (fun i => Finset.subset_union_left) hTw hWt l2 hcar
    ⟨hlist cDep hl.1, fun _ v₁ v₂ ho hv => (hWt v₂).1 (hl.2 hT _ _ (overOne_plUnder_of h P.Z₀ P'.Z₀ ho) ((hWt v₁).2 hv))⟩
    (ck P' y l2) (fin P' y)⟩
theorem sFino_and_secondNo_of_rat_cusp_finl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep :=
  fun hCo hCW hHM hP hS hD hH hds hc _ hMt hRat hCu _ hF => ⟨_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF, _root_.GlobalTheory.HeightCounting.Up.secondNo_of_sMt_sRat_sCusp_sFinl hCo hCW hHM hP hS hD hH hds hc hMt hRat hCu hF⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  exact @_root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl
end
end
