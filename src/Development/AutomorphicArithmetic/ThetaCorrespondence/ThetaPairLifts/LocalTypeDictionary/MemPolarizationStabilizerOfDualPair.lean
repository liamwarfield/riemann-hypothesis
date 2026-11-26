module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraScalarAction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RestrictedTensorSphericalUniquenessOffFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace GlobalTheory.PolActsPf
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs
section Swap
variable {P Q R S : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Swap
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Graph
variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}
end Graph
theorem mem_polarizationStabilizer_of_dualPair (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines (σ := σ) JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hls : LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    change ∀ T, SA (om (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at hSA
    rw [hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA
theorem polarization_acts_of_isDualPair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩
end GlobalTheory.PolActsPf
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPair_preserves_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  first | exact @_root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | exact _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | (intros; apply _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumIsVacuumIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_isVacuumIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_vacuum_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | exact _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalFixesPureVacuumVectors
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalVectorFixedAtAlmostAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.LocVacFix
theorem vacuum_fixed_at_cofinitely_many_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  refine ⟨(bad_finite F).toFinset ∪ X.T, fun v hv k hk => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨⟨hd, h6⟩, hvT⟩ := hv
  have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hT.base.std v hd
  obtain ⟨h2, h3⟩ := two_three_of_six v h6
  by_cases hin : ∃ w, Formalism.UG.IsInertAt F E v w
  · obtain ⟨w, hw⟩ := hin
    exact GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk
  · push_neg at hin
    exact vac_fixed_split F E σ B a a' G X om om' hT v hin hvT hψ h2 h3 k hk
end GlobalTheory.LocVacFix
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_fixed_at_almost_all_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  first | exact @_root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places | exact _root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places | (intros; apply _root_.GlobalTheory.LocVacFix.vacuum_fixed_at_cofinitely_many_places <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SphFix
theorem spherical_fixes_pure_vacuum_vectors : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M'.vac w) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₁, h₁⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_at_almost_all_places P F E σ B a a' G X om om' hT
  obtain ⟨S₂, h₂⟩ := _root_.GlobalTheory.T.restricted_tensor_spherical_uniqueness_off_finite P F E σ B a a' G X om om' hT
  refine ⟨S₁ ∪ S₂, fun S hS k hinf hSk hl hl' => ⟨fun f φ hφ hv => ?_, fun f φ hφ hv => ?_⟩⟩
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om S (Nat.zero_lt_of_lt hT.geo.lt)
      hT.geo.hV.lat hT.geo.hW.lat.toIsLattice hT.geo.hM hT.weil
      (fun v hv k hk => h₁ v (fun h => hv (hS (Finset.mem_union_left _ h))) k hk) k hinf hSk hl f φ hφ hv
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' S
      (lt_of_le_of_lt (Nat.zero_le _) hT.geo.aBig) hT.geo.hV'.lat hT.geo.hW.lat.toIsLattice hT.geo.hM' hT.weil'
      (fun v hv k hk => h₂ v (fun h => hv (hS (Finset.mem_union_right _ h))) k hk) k hinf hSk hl' f φ hφ hv
end GlobalTheory.SphFix
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_fixes_vacua : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M'.vac w) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  first | exact @_root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors | exact _root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors | (intros; apply _root_.GlobalTheory.SphFix.spherical_fixes_pure_vacuum_vectors <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanThetaFamilyExistsSmooth
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
namespace GlobalTheory.ArchFamily
theorem exists_archimedean_theta_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hstd hW γ hγ
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁ :=
    fun t f => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hcm hstd hW _ (hγ.2 _) f
  choose S hS using hex
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add (f := _), key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  refine ⟨T, fun t f => hS t f, fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · show tens (evI F) ⇑(S (s + t) f) r₀ = tens (evI F) ⇑(S s (S t f)) r₀
    have hmul : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (s + t))) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) := by
      rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
    rw [← key, hmul, map_mul, Module.End.mul_apply, key, key]
  · show tens (evI F) ⇑(S 0 f) r₀ = tens (evI F) ⇑f r₀
    have h1 : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (0 : ℝ))) = 1 := by
      rw [ofAdd_zero, map_one]; rfl
    rw [← key, h1, map_one, Module.End.one_apply]
end GlobalTheory.ArchFamily
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  first | exact @_root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family | exact _root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family | (intros; apply _root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticScalarDerivativeNonempty
section
open scoped Matrix
noncomputable section
namespace GlobalTheory.MetaplecticScalarDeriv
open MeasureTheory Filter Topology GlobalTheory.RealWeil
theorem metaplectic_scalar_derivative_nonempty (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact _root_.GlobalTheory.MetaplecticScalarDeriv.metaplectic_scalar_derivative_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont
end GlobalTheory.MetaplecticScalarDeriv
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  first | exact @_root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | exact _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ILiescalar
section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.RealLift.Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
end Tensor
theorem i_liescalar_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action
theorem lieSecond_of_lieScalar_of_vacLine : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := _root_.GlobalTheory.T.real_lift_lie_second_order
section Helpers
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
end Helpers
section Exp
variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]
end Exp
section Side
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)
end Side
section SideW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)
end SideW
end GlobalTheory.RealLift.Main
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolynomialMatchingInduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.ThK.PolMatchStep
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
section Local
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end Local
theorem polynomial_matching_on_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T v hv h hh Φ Φ' hPM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hPM
  have hT := hM.triple
  have ex := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v
  have ex' := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v
  have h1 : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have h1' : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V' (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have E1 := fun x hx => (ex.1 1 h1 h hh x hx).exists
  have E1' := fun x hx => (ex'.1 1 h1' h hh x hx).exists
  let loc : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1 x hx).choose else 0
  let loc' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1' x hx).choose else 0
  have hloc : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), loc x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h)) x (loc x) := fun x hx => by
    simp only [loc, dif_pos hx]; exact (E1 x hx).choose_spec
  have hloc' : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), loc' x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)) x (loc' x) := fun x hx => by
    simp only [loc', dif_pos hx]; exact (E1' x hx).choose_spec
  have pre : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hM.fin.onto v]; trivial
    exact hy
  have pre' : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    exact hy
  let A0 : Rf.Pi v → Rf.Pi v := fun y => Rf.p v (loc (pre y).choose)
  have K : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), A0 (Rf.p v x) = Rf.p v (loc x) := by
    intro x hx
    obtain ⟨hx0, hx0e⟩ := (pre (Rf.p v x)).choose_spec
    obtain ⟨x', hx', hx'e⟩ := pre' (Rf.p v x)
    have a1 := hM.fin.equiv v h hh _ hx0 x' hx' _ (hloc _ hx0).1 _ (hloc' x' hx').1 (hloc _ hx0).2 (hloc' x' hx').2
      (hx0e.trans hx'e.symm)
    have a2 := hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2
      hx'e.symm
    exact a1.trans a2.symm
  have K' : ∀ x' ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), A0 (Rf.p' v x') = Rf.p' v (loc' x') := by
    intro x' hx'
    obtain ⟨x, hx, hxe⟩ := pre (Rf.p' v x')
    rw [← hxe, K x hx]
    exact hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hxe
  have Klin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∀ c d : ℂ, loc (c • x + d • y) = c • loc x + d • loc y := by
    intro x hx y hy c d
    have hs : c • x + d • y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((GlobalTheory.WeilM.SB _).smul_mem c hx) ((GlobalTheory.WeilM.SB _).smul_mem d hy)
    exact acts_lin_eq v (om (1, h)) hx hy (hloc x hx).2 (hloc y hy).2 c d (hloc _ hs).2
  let A : Rf.Pi v →ₗ[ℂ] Rf.Pi v :=
    { toFun := A0
      map_add' := by
        intro y z
        obtain ⟨x, hx, rfl⟩ := pre y
        obtain ⟨w, hw, rfl⟩ := pre z
        rw [← map_add (f := _), K _ (add_mem hx hw), K x hx, K w hw, ← map_add (f := _)]
        congr 1
        simpa using Klin x hx w hw 1 1
      map_smul' := by
        intro c y
        obtain ⟨x, hx, rfl⟩ := pre y
        rw [← map_smul, K _ ((GlobalTheory.WeilM.SB _).smul_mem c hx), K x hx, RingHom.id_apply, ← map_smul]
        congr 1
        simpa using Klin x hx x hx c 0 }
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ hv)
  have evc : ∀ {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y G.W) (ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, w ∉ T → ρ w = M.vac w) → M.IsGood B.ψ →
      ∀ᶠ w in Filter.cofinite, ρ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    intro n Y M ρ hρ hG
    have e0 : ∀ᶠ w in Filter.cofinite, ρ w = M.vac w :=
      Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw (hρ w hc))
    filter_upwards [e0, hG.std] with w e1 e2
    rw [e1, e2]
  let φN : Fin m → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ :=
    fun i => Function.update (φ i) v (loc (φ i v))
  let φN' : Fin m' → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun j => Function.update (φ' j) v (loc' (φ' j v))
  refine ⟨m, m', f, φN, f', φN', fun i => ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩,
    fun j => ⟨(hφ' j).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; simp only [φN, Function.update_self]; exact (hloc _ ((hφ i).2.1 w)).1
    · simp only [φN, Function.update_of_ne hw]; exact (hφ i).2.1 w
  · simp only [φN, Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w hw
  · by_cases hw : w = v
    · subst hw; simp only [φN', Function.update_self]; exact (hloc' _ ((hφ' j).2.1 w)).1
    · simp only [φN', Function.update_of_ne hw]; exact (hφ' j).2.1 w
  · simp only [φN', Function.update_of_ne (hvT w hw)]; exact (hφ' j).2.2 w hw
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hΦ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact pure_update v (om (1, h)) (f i) (φ i) (hφ i).2.1 (evc G.M (φ i) (hφ i).2.2 hT.geo.hM)
        (hloc _ ((hφ i).2.1 v)).2
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hΦ', map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact pure_update v (om' (1, h)) (f' j) (φ' j) (hφ' j).2.1 (evc G.M' (φ' j) (hφ' j).2.2 hT.geo.hM')
        (hloc' _ ((hφ' j).2.1 v)).2
  · have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map
      (Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A))) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key
    have e1 : ∀ i, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p u (φ i u))) = fun u : T => Rf.p u (φN i u) := by
      intro i; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN]; exact K _ ((hφ i).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN, Function.update_of_ne hu', LinearMap.id_apply]
    have e2 : ∀ j, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p' u (φ' j u))) = fun u : T => Rf.p' u (φN' j u) := by
      intro j; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN']; exact K' _ ((hφ' j).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN', Function.update_of_ne hu', LinearMap.id_apply]
    simp only [e1, e2] at key
    exact key
end GlobalTheory.ThK.PolMatchStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_matching_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  first | exact @_root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | exact _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | (intros; apply _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ <;> assumption)
end
end
