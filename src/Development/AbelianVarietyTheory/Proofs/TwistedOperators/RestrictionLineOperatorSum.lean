module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

end GlobalTheory.ThetaLineDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.PureImage

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_sig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor_inj {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

end GlobalTheory.TripleAssembly.PureImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.CuspApproxAll

variable {D : D7}

def avgList (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  l.foldr (fun τ f => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) f) φ

theorem avgList_nil (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (φ : GA D N.V → ℂ) :
    avgList θ N e [] φ = φ := rfl

theorem avgList_cons (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (τ : D.what₂.Tau)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) :
    avgList θ N e (τ :: l) φ = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) (avgList θ N e l φ) := rfl

theorem growthSob_zero_ne_top {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (d : ℕ) :
    growthSob θ V d 0 φ ≠ ∞ := by
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V 0 f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  have hM : φ ∈ allDer θ V M := ⟨h.smooth, fun l hl => modGrowthExp_iff.1
    ((h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp))⟩
  refine wordSum_ne_top_iff.2 fun l _ => ?_
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) hM).2 [] (fun _ h => by simp at h)

def Good (θ : InfFam D) (V : HSp D) (f : GA D V → ℂ) : Prop := RapidDecSm θ V f ∧ IsCuspFun V f

theorem good_add {θ : InfFam D} {V : HSp D} {f f' : GA D V → ℂ} (h : Good θ V f) (h' : Good θ V f') :
    Good θ V (f + f') :=
  ⟨h.1.add h'.1, GlobalTheory.MultMem.isCuspFun_add h.1.toIsAutFun h'.1.toIsAutFun h.2 h'.2⟩

theorem good_smul {θ : InfFam D} {V : HSp D} {f : GA D V → ℂ} (c : ℂ) (h : Good θ V f) : Good θ V (c • f) :=
  ⟨h.1.smul c, GlobalTheory.MultMem.isCuspFun_smul c h.2⟩

theorem good_zero (θ : InfFam D) (V : HSp D) : Good θ V 0 := by
  refine ⟨rapidDecSm_iff.2 ⟨zero_mem _, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, ?_⟩
  exact fun _ _ _ _ _ _ _ _ => by simp

theorem good_value (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) {Φ : N.Maps}
    (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) : Good θ N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, Good θ N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨rapidDecSm_of_cuspForm hP hθ (hx.aut w) (hx.cusp w), hx.cusp w⟩
    | zero => exact fun w => good_zero θ N.V
    | add x y _ _ hx hy => exact fun w => good_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => good_smul c (hx w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using good_smul r (hU' f)
  | add x y hx hy => simpa using good_add hx hy

end GlobalTheory.CuspApproxAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

theorem char_identity {ι : Type} (Pg Q : Finset ι) (a a' d xa xb xd : ι → ℂˣ) (h : ∀ i ∈ Pg, a' i = a i) :
    ((∏ i ∈ Pg, (a i * d i)⁻¹) * ∏ i ∈ Q, xa i * xd i)⁻¹ * ((∏ i ∈ Pg, (a' i)⁻¹) * ∏ i ∈ Q, xb i) =
      (∏ i ∈ Q, (xa i)⁻¹ * xb i) * (1 * (∏ i ∈ Pg, (d i)⁻¹) * ∏ i ∈ Q, xd i)⁻¹ := by
  rw [Finset.prod_congr rfl fun i hi => congrArg (·⁻¹) (h i hi)]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  generalize (∏ i ∈ Pg, a i) = A, (∏ i ∈ Pg, d i) = B, (∏ i ∈ Q, xa i) = C, (∏ i ∈ Q, xb i) = E, (∏ i ∈ Q, xd i) = F
  apply Units.ext
  push_cast
  field_simp

theorem smul_cancel {X : Type} {u v : X → ℂ} {ι : Type} {Q : Finset ι} {x : ι → ℂˣ} {m m' l : ℂˣ} {c : ℂ}
    (h : (∏ i ∈ Q, ((x i : ℂˣ) : ℂ)) • u = c • v) (hc : c = (m : ℂ)⁻¹ * m') (e : m⁻¹ * m' = (∏ i ∈ Q, x i) * l⁻¹) :
    u = (l : ℂ)⁻¹ • v := by
  rw [hc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, e, ← Units.coe_prod, Units.val_mul, mul_smul] at h
  rw [← Units.val_inv_eq_inv_val]
  exact smul_right_injective _ (Units.ne_zero _) h

variable {D : D7}

theorem om_vec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hη : ∃ η, IsEtaTilde D η) (sdS : IsSelfDualC S ΛS) (sdT : IsSelfDualC T ΛT) (frS : IsFrame βS ΛS)
    (frT : IsFrame βT ΛT) (hv : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    ∃ (P : Finset (Pl D.host.E)) (e : AE D) (he : e * e = e), (∀ PP, PP ∈ P ↔ PP ∈ Pg ∨ PP ∈ Q) ∧ IsIdemSum e P ∧
      (UnrOff (e + cA D e) χS → UnrOff (e + cA D e) χT → ∀ (r : ℕ) (hS : r ≤ S.rank) (hT : r ≤ T.rank), T.rank = r →
        ∀ g h, Stab S βS g → Stab T βT h →
        (∀ PP, PP ∈ Pg ∨ PP ∈ Q → redFn βS PP (finE S g) ∈ blockTri (blk2 r)) →
        (∀ PP ∈ Pg, upperLeftBlock hS (redFn βS PP (finE S g)) = upperLeftBlock hT (redFn βT PP (finE T h))) →
        (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hS (redFn βS PP (finE S g)))))⁻¹ *
            ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) • om (g, h) f =
          ((splitFacO χS χT (detAt e he S g) (detAt e he T h) : Circle) : ℂ) • f) := by
  obtain ⟨hvac, e, he, hth⟩ := hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  refine ⟨_, e, hee, fun PP => @Finset.mem_union _ (_) _ _ PP, he, fun u1 u2 r hS hT hr g h sS sT tri same => ?_⟩
  have h0 := GlobalTheory.T.weil_latticeVacuum_stabilizer_splitting_characters D ψ S T ΛS ΛT χS χT om hW sdS sdT hη βS βT frS frT _ e hee he u1 u2 g h sS sT f₀ hvac.2.theta
    hvac.2.lat
  exact GlobalTheory.T.weilAction_schrodingerModel_finiteIdempotent D ψ S T ΛS ΛT χS χT om hW sdS sdT (cA D e) (by rw [← RingHom.map_mul, hee])
    (GlobalTheory.PlaceVec.infPart_cA hinf) g h (mem_latO_iff frS frT sS.2 sT.2) f₀
    (adjDatum S T βS βT Pg Q ξ (cA D e)) f _ _ hvac.2.theta hth (Circle.coe_ne_zero _) h0
    (GlobalTheory.T.adjointHalfDatum_stabilizerPair_move D S T βS βT Pg Q ξ _ r hS hT hr g h sS.2 sT.2 tri same)

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem levChi_flag_V (i : Fin D.R.m) (t : T0) {κ : GA D (Vc D i)}
    (tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t)) :
    levChi _ (L.βV i) (flagL (L.datVt i t)) κ =
      ((1 * (∏ PP ∈ L.Pg, (L.chi ((i : ℕ) + 1) PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))))⁻¹) *
        ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))) : ℂˣ) : ℂ) := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  refine congrArg Units.val (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) rfl)
  · exact extendOne_of_mem _ (Subgroup.mem_top _)
  · refine Finset.prod_congr rfl fun PP h => ?_
    rw [← (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) _).2.1 rV (tg PP h)]
    exact Finset.prod_range_one _

theorem om_lifts (hL : L.Is μ0) (i : Fin D.R.m) (t : T0) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    {om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)}
    (hW : IsWeilDatumO ψ (Vc D i) (Wc D i) (L.mu t ((i : ℕ) + 1)) (L.mu t ((i : ℕ) + 1) * L.eta⁻¹) om)
    (hv : IsThPVecOf ψ θ (Vc D i) (Wc D i) sS sT (L.ΛV i) (L.ΛW i) (L.βV i) (L.βW i) L.Pg (L.Q t) (L.xiR t) f₀ f)
    {g0 : G0 L.Pg D.R.r} {κ : GA D (Vc D i)} {κ' : GA D (Wc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) g0 κ) (hκ' : IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) g0 κ') :
    om (κ, κ') f = (levChi _ (L.βV i) (flagL (L.datVt i t)) κ)⁻¹ • f := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hη : IsEtaTilde D L.eta := GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum D _ _ hL.eta L.C.isEta _ _ _ hW.resS hW.resT (by
    rw [rV, rW]
    obtain ⟨c, hc⟩ := D.R.t_odd
    exact ⟨D.R.r + c, by omega⟩)
  obtain ⟨P, e, hee, hP, he, hom⟩ := om_vec hW ⟨_, hη⟩ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hv
  obtain ⟨u1, u2⟩ := unrOff_mu hL t i hP he
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have sW : finE (Wc D i) κ' ∈ St (L.βW i) := parLev_St hκ'.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have tri : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 D.R.r) := fun PP h =>
    h.elim (fun h => blockTri_blkOf_le _ _ (tg PP h)) fun h => parLev_q hκ.2.1 h
  have same : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) =
      upperLeftBlock (r_le_rank_Wc i) (redFn (L.βW i) PP (finE (Wc D i) κ')) := fun PP h =>
    (congrFun hκ.2.2 ⟨PP, h⟩).trans (congrFun hκ'.2.2 ⟨PP, h⟩).symm
  have h1 := hom u1 (u1.mul u2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW κ κ' ⟨hκ.1, sV⟩ ⟨hκ'.1, sW⟩ tri same
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  obtain ⟨aW, haW, hrW⟩ := exists_det_int sW
  obtain ⟨mV, nV⟩ := mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP
  obtain ⟨mW, -⟩ := mu_val hL t i hP he (detAt e hee _ κ') _ aW _ (isDetAt_detAt e hee _ κ') haW fun PP _ => hrW PP
  rw [levChi_flag_V i t tg]
  refine smul_cancel h1 (by
    rw [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, nV, inv_one, mul_one, Circle.coe_mul, Circle.coe_inv,
      mV, mW]) ?_
  refine Eq.trans ?_ (char_identity L.Pg (L.Q t)
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (upperLeftBlock (r_le_V i)
      (redFn (L.βV i) PP (finE (Vc D i) κ)))))
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (redFn (L.βW i) PP (finE (Wc D i) κ')))) _ _ _ _
    fun PP h => by rw [same PP h, (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_rank_Wc i) _).2.2 rW])
  refine congrArg₂ (· * ·) (congrArg (·⁻¹) (congrArg₂ (· * ·) ?_ ?_)) rfl
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inl h)), map_mul]
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inr h)), map_mul]

theorem omega_lifts_vP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t :=
  fun _ hL _ hω hv i t _ _ _ hκ hκ' => om_lifts hL i t (hω i t) (hv i t) hκ hκ'

end GlobalTheory.VecInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t := by
  first | exact @GlobalTheory.VecInv.omega_lifts_vP | exact GlobalTheory.VecInv.omega_lifts_vP | (intros; apply GlobalTheory.VecInv.omega_lifts_vP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartz
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchUniq

variable {F : Type} [Field F] [NumberField F]

def intFinInd (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator (Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) 1

theorem intFinInd_mem_SB (κ : Type) [Fintype κ] : intFinInd F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles
  have hcI := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have ho : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => hoI
  have hc : IsClosed C :=
    isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI
  have hk : IsCompact C := isCompact_univ_pi fun _ => hcI
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 := congrArg Prod.snd h
  change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2
  rwa [one_mul] at h2

theorem exists_admissible_finite_factor : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  intro F _ _ κ _
  refine ⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩
  · have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩
  · ext y
    have h1 := congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))
    have hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y := by
      funext i
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
    have h0 : intFinInd F κ (fun _ => 0) = 1 := by
      simp only [intFinInd]
      rw [Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ
        fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]
      rfl
    simp only [tens, hy, h0, mul_one] at h1
    exact h1

end GlobalTheory.ArchUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartzStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  first | exact @GlobalTheory.ArchUniq.exists_admissible_finite_factor | exact GlobalTheory.ArchUniq.exists_admissible_finite_factor | (intros; apply GlobalTheory.ArchUniq.exists_admissible_finite_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def InK (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)

structure IsGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ τ g, InK M τ g → ∀ f ∈ A, rTr V (atTau θ V τ g) f ∈ A
  lie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f ∈ A, Rder θ V τ X f ∈ A

def IsIrrGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop :=
  IsGKSub θ M A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ (GA D V → ℂ), B ≤ A → IsGKSub θ M B → B = ⊥ ∨ B = A

def gkGen (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {A | ψ ∈ A ∧ IsGKSub θ M A}

theorem mem_gkGen (ψ : GA D V → ℂ) : ψ ∈ gkGen θ M ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isGKSub_gkGen (ψ : GA D V → ℂ) : IsGKSub θ M (gkGen θ M ψ) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)

theorem gkGen_le {ψ : GA D V → ℂ} {A : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ A) (hA : IsGKSub θ M A) :
    gkGen θ M ψ ≤ A :=
  sInf_le ⟨hψ, hA⟩

structure IsGKMult
    (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ)) : Prop where
  aut : ∀ u, IsAutFunSm θ V (F u)
  cusp : ∀ u, IsCuspFun V (F u)
  equivK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
    ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)
  equivLie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
      F (Function.update u τ w) = Rder θ V τ X (F u)

def multSpan : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {f | ∃ (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)) (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), IsGKMult θ M F ∧ f = F u}

def IsKFinCuspOfType (f : GA D V → ℂ) : Prop :=
  IsAutFunSm θ V f ∧ IsCuspFun V f ∧ (∀ τ, IsTypeAt θ V τ (S τ) f) ∧
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ f ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W

theorem IsGKMult.smul {F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)} (h : IsGKMult θ M F) (c : ℂ) : IsGKMult θ M (c • F) := by
  constructor
  · intro u
    exact Formalism.IndefR.Mult.isAutFunSm_smul θ V (h.aut u) c
  · intro u
    exact Formalism.IndefR.Mult.isCuspFun_smul V (h.cusp u) c
  · intro τ g hg hk u w hw
    rw [smul_apply, smul_apply, h.equivK τ g hg hk u w hw]
    rfl
  · intro τ X hX u w hw
    rw [smul_apply, smul_apply, h.equivLie τ X hX u w hw,
      Formalism.IndefR.Mult.rder_smul]

theorem exists_sum_of_mem_multSpan {ψ : GA D V → ℂ} (hψ : ψ ∈ multSpan θ M) :
    ∃ (n : ℕ) (F : Fin n → MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (GA D V → ℂ)) (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, IsGKMult θ M (F l)) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  obtain ⟨n, c, f, hf⟩ := Submodule.mem_span_set'.1 hψ
  choose F u hF hFu using fun i => (f i).2
  refine ⟨n, fun l => c l • F l, u, fun l => (hF l).smul θ M (c l), fun g => ?_⟩
  rw [← hf, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hFu l]
  rfl

end GlobalTheory.CuspGK

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    change f' (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a i)) * g' y = f' x₀ * g' y
    congr 1
    apply congrArg f'
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x₀ i)
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  first | exact @GlobalTheory.TwistRest.restTr | exact GlobalTheory.TwistRest.restTr | (intros; apply GlobalTheory.TwistRest.restTr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
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

noncomputable section

namespace GlobalTheory.MovedKappaEx

def OffPrime {D : D7} (e : Formalism.L2.Theta.AE D) (q : ℕ) : Prop :=
  ∀ v ε, IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε → ((q : 𝓞 D.host.F)) ∉ v.asIdeal

def splitOff {D : D7} (V : HSp D) (Q : Finset ℕ) : Subgroup (GfC V) :=
  Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧ SuppAt e V (g : GA D V)}

def RatFin {D : D7} (V : HSp D) (g : GfC V) : Prop := ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V)

def UnitAt (q : ℕ) [Fact q.Prime] (c : ℂ) : Prop := ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam c‖ = 1

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetKap (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)

end

end GlobalTheory.MovedKappaEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isTypeAt_of_finSum (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) {S : SPar}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hE : IsEnum S lam ε) (hD : Formalism.MainNotions.S.IsDS ε lam σ) (hP : IsUnit P) (hJ : Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ)
    (φ : GA D V → ℂ)
    (h : ∀ x, ∃ (n : ℕ) (L : Fin n → (H →L[ℂ] ℂ)) (v : Fin n → H),
      (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (σ (P * g * P⁻¹) (v i))) :
    IsTypeAt θ V τ S φ := by
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨n, L, v, hv, hφ⟩ := h x
  let vv : ℕ → H := fun i => if hi : i < n then v ⟨i, hi⟩ else 0
  let ll : ℕ → (H →ₗ[ℂ] ℂ) := fun i => if hi : i < n then ((L ⟨i, hi⟩ : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) else 0
  let CC : ℕ → ℝ := fun i => if hi : i < n then ‖L ⟨i, hi⟩‖ else 0
  have hb : ∀ i w, ‖ll i w‖ ≤ CC i * ‖w‖ := fun i w => by
    by_cases hi : i < n
    · simp only [ll, CC, dif_pos hi]
      exact (L ⟨i, hi⟩).le_opNorm w
    · simp [ll, CC, dif_neg hi]
  refine ⟨vv, fun i => ?_, ll, fun i => ⟨[[]], CC i, by simp, fun w _ => by simpa using hb i w⟩,
    ⟨[[]], CC, by simp, fun i w _ => by simpa using hb i w, fun S' _ => ?_, fun _ => 1, continuous_const,
      fun g hg w _ => ?_⟩, fun g hg => ?_⟩
  · by_cases hi : i < n
    · simp only [vv, dif_pos hi]
      exact hv _
    · simp only [vv, dif_neg hi]
      intro k Xs _
      simpa using contDiff_const
  · refine summable_of_ne_finset_zero (s := Finset.range n) fun i hi => ?_
    have : ¬ i < n := by simpa using hi
    simp [CC, dif_neg this]
  · simp [hD.2.2.1.2.1 _ (GlobalTheory.TypeAtCompare.conj_mem hP hJ hg) w]
  · rw [hφ g hg]
    convert hasSum_sum_of_ne_finset_zero (s := Finset.range n)
      (f := fun i => ll i (σ (P * g * P⁻¹) (vv i))) (fun i hi => by
        have : ¬ i < n := by simpa using hi
        simp [ll, dif_neg this]) using 1
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ll, vv, i.2]
    · infer_instance

def conjFun {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) : H' →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => star (ℓ (c w))
      map_add' := fun a b => by simp
      map_smul' := fun a w => by
        simp only [LinearIsometryEquiv.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]
        rw [star_mul', Complex.star_def, Complex.conj_conj] }
    ‖ℓ‖ (fun w => by simpa using ℓ.le_opNorm (c w))

theorem conjFun_apply {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) (w : H') : conjFun c ℓ w = star (ℓ (c w)) := rfl

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem conj_finSum {V : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} (M : DSModel V S) (M' : DSModel V S')
    (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] (c : M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c (M'.rep τ g w) = M.rep τ g (c w))
    (hsm : ∀ w : M'.H τ, w ∈ M'.sm τ ↔ c w ∈ M.sm τ)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (x : GA D V) (z : SmT M) :
    ∃ (n : ℕ) (L : Fin n → (M'.H τ →L[ℂ] ℂ)) (v : Fin n → M'.H τ),
      (∀ i, SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), star (PiTensorProduct.lift T z (x * atTau θ V τ g)) =
        ∑ i, L i (M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹) (v i)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hw : c.symm (f τ) ∈ M'.sm τ := (hsm _).2 (by simp)
    have hsv : SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (c.symm (f τ)) := by
      rw [GlobalTheory.SmVec.sm_eq M' τ] at hw
      exact hw
    refine ⟨1, fun _ => star r • conjFun c (LinearMap.toContinuousLinearMap ℓ), fun _ => c.symm (f τ), fun _ => hsv,
      fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    have e2 : M.rep τ g (f τ) = c (M'.rep τ g (c.symm (f τ))) := by
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply, conjFun_apply,
      smul_eq_mul, smul_eq_mul, star_mul', e3, LinearMap.coe_toContinuousLinearMap', e2]
    rfl
  | add a b ha hb =>
    obtain ⟨n₁, L₁, v₁, hv₁, h₁⟩ := ha
    obtain ⟨n₂, L₂, v₂, hv₂, h₂⟩ := hb
    refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hv₁ i
      · simpa using hv₂ i
    · rw [Fin.sum_univ_add, map_add (f := _), Pi.add_apply, star_add, h₁ g hg, h₂ g hg]
      simp

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isAutFunSm_lift {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) :
    IsAutFunSm θ V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_smul r (hT.aut f)
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem formX_props (R : RealDat D A Ks) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX)
    (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    IsAutFunSm R.θ D.sp.X' (d.formX t y) ∧ IsCuspFun D.sp.X' (d.formX t y) ∧
      ∀ τ, IsTypeAt R.θ D.sp.X' τ ((Ptw D).Dpar D.R.m τ) fun g => star (d.formX t y g) := by
  have hx := (hH t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hT := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hc hpr hx
  have e : d.formX t y =
      PiTensorProduct.lift (PiTensorProduct.lift.symm (R.cX.toMap R.prX ((R.HX t).e y))) d.v := by
    rw [LinearEquiv.apply_symm_apply]; rfl
  rw [e]
  refine ⟨isAutFunSm_lift hT _, GlobalTheory.DefiniteEnd.isCuspFun_of_definite D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _,
    fun τ => ?_⟩
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX τ
  obtain ⟨M', c, hc'⟩ := @GlobalTheory.ConjDS.exists_conjModel D D.sp.X' (parB (Ptw D) D.R.m) R.MX
  have hsm := (GlobalTheory.ConjMult.conj_mult R.θ R.MX M' c hc').1 τ
  have hE := M'.enum τ
  simp only [parB, dualPar_dualPar] at hE
  exact isTypeAt_of_finSum R.θ D.sp.X' τ hE (M'.ds τ) (M'.fr_unit τ) (M'.fr_gram τ) _
    fun x => conj_finSum R.MX M' τ (c τ) (hc' τ) hsm hT x d.v

theorem props_cast (θ : InfFam D) (S : D.what₂.Tau → SPar) {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)}
    (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩) (φ : GA D D.sp.X' → ℂ) (h1 : IsAutFunSm θ D.sp.X' φ) (h2 : IsCuspFun D.sp.X' φ)
    (h3 : ∀ τ, IsTypeAt θ D.sp.X' τ (S τ) fun g => star (φ g)) :
    IsAutFunSm θ X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      IsCuspFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ τ, IsTypeAt θ X.sp τ (S τ) fun g => star (φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact ⟨h1, h2, h3⟩

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

end GlobalTheory.EndCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmThetaLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftSmoothAut

theorem isAutFunSm_thetaLift {D : D7} (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ}
    (hφ : IsAutFunSm θ T φ) (hc : IsCuspFun T φ) :
    IsAutFunSm θ S fun h => ∫ g in 𝓕, thetaKO om h g Φ * φ g ∂ν := by
  have hκ := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont).swap
  exact (hκ.lift hP hθ ⟨hν, h𝓕⟩ ⟨hφ, hc⟩ ⟨Φ, hΦ⟩).2

end GlobalTheory.ThetaLiftSmoothAut

end
end
